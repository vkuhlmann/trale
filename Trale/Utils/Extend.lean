import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Lean.PrettyPrinter.Delaborator
import Qq

import Trale.Utils.Constructor

open Lean Qq Elab Command Tactic Term Expr Meta PrettyPrinter

namespace Trale.Utils

/-!
# Utilities for Extending Param Instances

This module provides the `tr_extend` tactic and related utilities for building
stronger Param instances from weaker ones.

The main pattern is:
```lean
instance Map2a_foo : Param2a0 α β := by
  tr_extend Map0_foo
  -- provide the additional structure needed for Map2a
```

This automates the boilerplate of extracting the base relation and coercing
to the right type while letting you focus on the new properties.
-/

/-- Attempt to recover a concrete MapType value from an expression.
    Returns `none` if the expression doesn't match any MapType constructor. -/
def recoverMapTypeFromExpr? (expr : Q(MapType)) : MetaM (Option MapType) := do
  if (← isExprDefEq expr q(MapType.Map4)) then
    return MapType.Map4

  if (← isExprDefEq expr q(MapType.Map3)) then
    return MapType.Map3

  if (← isExprDefEq expr q(MapType.Map2a)) then
    return MapType.Map2a

  if (← isExprDefEq expr q(MapType.Map2b)) then
    return MapType.Map2b

  if (← isExprDefEq expr q(MapType.Map1)) then
    return MapType.Map1

  if (← isExprDefEq expr q(MapType.Map0)) then
    return MapType.Map0

  return none

/-- Recover a concrete MapType from an expression, throwing an error if it fails. -/
def recoverMapTypeFromExpr! (expr : Q(MapType)) := do
  match (←recoverMapTypeFromExpr? expr) with
  | .none =>
      throwError s!"Failed to infer concrete map type"
  | .some a => pure a



/-- Extract field names and types from a base Param instance.
    Used by `tr_extend` to know what fields need to be filled in. -/
def get_base_tr_fill_from_template (base : Expr) (baseType : Expr) : MetaM (Name -> Option Expr) := do
  let levelU <- mkFreshLevelMVar
  let levelV <- mkFreshLevelMVar
  let levelW <- mkFreshLevelMVar

  let fromType : Q(Sort $levelU) ← mkFreshExprMVar .none (userName := `fromType)
  let toType : Q(Sort $levelV) ← mkFreshExprMVar .none (userName := `toType)

  let covMapType1 : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `covMapTypeBase)
  let conMapType1 : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `conMapTypeBase)

  let matcher1 : Q(Type (max levelU levelV levelW)) := q(Param.{levelW, levelU, levelV} $covMapType1 $conMapType1  $fromType $toType)

  unless (← isDefEq baseType matcher1) do
    Term.throwTypeMismatchError none matcher1 baseType base

  -- Attempting Instantiating MVars to avoid memory exploding (even beyond 15 GB)
  -- Did not solve the issue, but helps perhaps
  let levelU : Level ← instantiateLevelMVars levelU
  let levelV : Level ← instantiateLevelMVars levelV

  let fromType : Q(Sort $levelU) <- instantiateMVars fromType
  let toType : Q(Sort $levelV) ← instantiateMVars toType

  let covMapType1 : Q(MapType) ← instantiateMVars covMapType1
  let conMapType1 : Q(MapType) ← instantiateMVars conMapType1

  let base
    : Q(Param.{levelW, levelU, levelV} $covMapType1 $conMapType1 $fromType $toType)
    <- instantiateMVars base

  trace[debug] s!"[tr_fill_from] Looking for yield expression..."

  let result : Name -> Option Expr := (
      match . with
        | `R => q(
              fun (_ : $covMapType1 >= MapType.Map0)
              => (($base).R))
        | `right => q(
            fun (h1 : $covMapType1 >= MapType.Map1)
            => ((Param.forget (h1 := h1) (h2 := map0bottom) $base).right)
              )
        | `right_implies_R => q(
            fun (h1 : $covMapType1 ≥ MapType.Map2a) =>
                  ((Param.forget (h1 := h1) (h2 := map0bottom) $base).right_implies_R)
              )
        | `R_implies_right => q(
            fun (h1 : $covMapType1 ≥ MapType.Map2b) =>
                  ((Param.forget (h1 := h1) (h2 := map0bottom) $base).R_implies_right)
              )

        | `R_implies_rightK => q(
            fun (h1 : $covMapType1 ≥ MapType.Map4) =>
                  ((Param.forget (h1 := h1) (h2 := map0bottom) $base).R_implies_rightK)
              )

        | `left => q(
            fun (h2 : $conMapType1 ≥ MapType.Map1)
            => ((Param.forget (h1 := map0bottom) (h2 := h2) $base).left )
              )

        | `left_implies_R => q(
            fun (h2 : $conMapType1 ≥ MapType.Map2a) =>
                  -- ((Param.forget (h1 := Param.map0bottom) (h2 := h2) $base).left_implies_R)
                  ((Param.forget (h1 := map0bottom) (h2 := h2) $base).contravariant.map_in_R)
              )

        | `R_implies_left => q(
            fun (h2 : $conMapType1 ≥ MapType.Map2b) =>
                  -- ((Param.forget (h1 := Param.map0bottom) (h2 := h2) $base).R_implies_left)
                  ((Param.forget (h1 := map0bottom) (h2 := h2) $base).contravariant.R_in_map)
              )

        | `R_implies_leftK => q(
            fun (h2 : $conMapType1 ≥ MapType.Map4) =>
                  -- ((Param.forget (h1 := Param.map0bottom) (h2 := h2) $base).R_implies_leftK)
                  ((Param.forget (h1 := map0bottom) (h2 := h2) $base).contravariant.R_in_mapK)
              )

        | _ => none
    )
  return result

def getHeadConst (e : Expr) : Option Name :=
  match e with
  | .const n _ => some n
  | .app f _ => getHeadConst f
  | _ => none

def do_tr_fill_from' (mapper : Name → Option Expr) (unfoldNames : List Name := []) : TacticM Unit :=
  withMainContext do
    trace[debug] s!"[tr_fill_from] Init..."
    let goal ← Lean.Elab.Tactic.getMainGoal
    -- let goalType ← Lean.Elab.Tactic.getMainTarget

    let result := mapper (← goal.getTag)

    if result.isNone then
      IO.println s!"[tr_extend] no translation for {<- goal.getTag}"
      return

    let result := result.get!
    -- let result <- whnf result
    -- whnf
    -- Meta.reduce


    -- IO.println s!"[tr_extend] checking: {result}"

    trace[debug] s!"[tr_fill_from] Looking for yield expression..."


    let goalTypeLevel <- mkFreshLevelMVar
    let goalType <- goal.getType'
    let goalTypeType <- inferType goalType

    if !(<- isExprDefEq goalTypeType q(Sort $goalTypeLevel)) then
      throwTacticEx `tr_extend goal
        (s!"goal type type does not match for {<- goal.getTag}, got {goalType} instead of {q(Type $goalTypeLevel)}")

    let goalTypeLevel : Level ← instantiateLevelMVars goalTypeLevel
    let goalType : Q(Sort $goalTypeLevel) <- instantiateMVars goalType

    -- let result <- withNewMCtxDepth (allowLevelAssignments := true) do
    --     let mvar <- mkFreshExprMVar (.some goalType) (kind := .natural) (userName := `extendDonorValue)
    --     if (<- isExprDefEq q(TrOption.some mvar) result) then
    --       return Option.some mvar
    --     else
    --       -- mvar.mvarId!.
    --       return Option.none

    let donorCondition : Q(Prop) <- mkFreshExprMVar q(Prop) (kind := .natural) (userName := `extendDonorCondition)

    let donorValue : Q((_ : $donorCondition) → $goalType) <- mkFreshExprMVar q((_ : $donorCondition) → $goalType) (kind := .natural) (userName := `extendDonorValue)

    if !(<- isExprDefEq donorValue result) then
      --   IO.println s!"[tr_extend] found {result} with type {goalType}"
      -- else
      -- IO.println s!"[tr_extend] unavailable from base: {<- goal.getTag}, got {result}"
      return
    -- else
    --   -- mvar.mvarId!.
    --   return Option.none

    let donorValue : Q((_ : $donorCondition) → $goalType) <- instantiateMVars donorValue

    let decidableCondition : Q(Decidable $donorCondition) <- mkFreshExprMVar q(Decidable $donorCondition) (kind := .natural) (userName := `extendDonorConditionDecidable)
    if !(←synthesizeInstMVarCore decidableCondition.mvarId!) then
      throwTacticEx `tr_extend goal
        (s!"donor condition is not decidable for {<- goal.getTag}: {donorCondition}")
    -- mkFreshExprMVar q(Decidable $donorCondition) (kind := .natural) (userName := `extendDonorConditionDecidable)

    -- IO.println s!"[tr_extend] donor condition decidable value: {<- reduce decidableCondition}"
    -- IO.println s!"[tr_extend] donor condition decidable value assigned: {<- decidableCondition.mvarId!.isAssigned}"

    let donorConditionValue : Q($donorCondition) <- mkFreshExprMVar q($donorCondition) (kind := .natural) (userName := `extendDonorConditionValue)

    if !(<- isExprDefEq decidableCondition q(Decidable.isTrue $donorConditionValue)) then
      -- throwTacticEx `tr_extend goal
      --   (s!"donor condition is not decidable for {<- goal.getTag}: {donorCondition}")
      --
      trace[debug] s!"[tr_extend] donor condition not met for {<- goal.getTag}: {donorCondition}"
      return


    -- IO.println s!"[tr_extend] donor condition: {donorCondition}"
      -- dite

    let donorConditionValue : Q($donorCondition) <- instantiateMVars donorConditionValue

    let result : Q($goalType) := q($donorValue $donorConditionValue)
    -- if result.isNone then
    --   IO.println s!"[tr_extend] unavailable from base: {<- goal.getTag}"
    --   continue

    -- let result := result.get!

    let goalType <- goal.getType'
    let resultType <- inferType result

    if !(← isExprDefEq goalType resultType) then
      throwTacticEx `tr_extend goal
        (s!"result type does not match goal type for {<- goal.getTag}. got {resultType} instead of {goalType}")


    -- IO.println s!"[tr_extend] for {<- goal.getTag} found {result} with type {goalType}"
    -- goal.assign (<- reduce result)
    -- goal.assign result

    -- let result <- Meta.unfoldDefinition result

    -- Meta.unfoldLocalDecl
    -- Meta.unfoldTarget

    -- IO.println s!"[tr_extend] base: {reprStr base}"

    let mut result : Expr ← instantiateMVars result

    -- IO.println s!"[tr_extend] before unfold: {result}"


    -- let constName := base.constName?
    -- let constName := getHeadConst base
    -- IO.println s!"[tr_fill_from] constName: {constName}"

    -- if constName.isSome then
    --   let constName := constName.get!
      -- trace[debug] s!"[tr_extend] constName: {constName}"


    for constName in unfoldNames do
      trace[debug] s!"[tr_fill_from] constName: {constName}"
      -- try
      let val := (<- Meta.unfold result constName)
      result := val.expr
      -- IO.println s!"[tr_extend] after unfold: {result}"
        -- result := result.expr
      -- catch
      --   | _ => do
      --     IO.println s!"[tr_extend] unfold failed for {result}"

    -- goal.assign result

    result <- instantiateMVars result

    let constNameResult := getHeadConst result
    trace[debug] s!"[tr_fill_from] constNameResult: {constNameResult}"

    -- Meta.unfoldTarget

    if constNameResult.isSome then
      result := (<-Meta.unfold result constNameResult.get!).expr
    result := (<-Meta.unfold result ``Param.forget).expr
    result := (<-Meta.unfold result ``coeMap).expr

    (result, _) <- Meta.dsimp result (<-Simp.mkContext)

    -- IO.println s!"[tr_fill_from] result: {<-ppTerm <| <- delab result}"

    closeMainGoal `tr_fill_from result
    return


def _root_.List.whereSome (a : List (Option α)) : List α :=
  a.filterMap id

def do_tr_fill_from (base : Expr) (baseType : Expr) : TacticM Unit := do
  let mapper ← get_base_tr_fill_from_template base baseType

  do_tr_fill_from' mapper (unfoldNames := [getHeadConst base].whereSome)

-- elab "tr_fill_from_mapper" td:term : tactic =>
--   Lean.Elab.Tactic.withMainContext do
--     let mapper : Q(Name -> Option Expr) <- Tactic.elabTerm td q(Name -> Option Expr)

--     do_tr_fill_from' (fun name => q($mapper $name))


-- elab "tr_prefixed_fill" : tactic =>
--   Lean.Elab.Tactic.withMainContext do
--     let targetLevel <- mkFreshLevelMVar
--     let target : Q(Sort targetLevel) ← Lean.Elab.Tactic.getMainTarget

--     let newTarget : Q((h : Prop) -> h -> $target) ← mkFreshExprMVar q((h : Prop) -> h -> $target) (userName := `prefixedTarget)




    -- let mapper : Q(Name -> Option Expr) <- Tactic.elabTerm td q(Name -> Option Expr)

    -- do_tr_fill_from' (fun name => q($mapper $name))



elab "tr_fill_from" td:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    -- let base : Q(Param $fromType $toType $covMapType1 $conMapType1
    --              : Type (max levelU levelV levelW))
    --   ← Tactic.elabTermEnsuringType td matcher1
    let expr ← Tactic.elabTerm td none
    do_tr_fill_from expr (← inferType expr)


elab "tr_fill_from_hypothesis_using_delab" name:ident : tactic =>
  Lean.Elab.Tactic.withMainContext do
    -- let goal ← Lean.Elab.Tactic.getMainGoal
    -- let goalType ← Lean.Elab.Tactic.getMainTarget

    let hypo : LocalDecl ← getLocalDeclFromUserName name.getId
    let val : Expr := hypo.value

    -- IO.println s!"[tr_fill_from_hypothesis] val: {val}"

    -- Lean.PrettyPrinter.Unexpander
    let term ← PrettyPrinter.delab val

    -- IO.println s!"[tr_fill_from_hypothesis] term: {term}"

    replaceMainGoal (← evalTacticAt (← `(tactic| tr_fill_from $term)) (← getMainGoal))


elab "tr_fill_from_hypothesis" name:ident : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let hypo : LocalDecl ← getLocalDeclFromUserName name.getId
    let val : Expr := hypo.value

    do_tr_fill_from val hypo.type


elab "tr_add_param_base" name:ident " := " td:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget

    -- let mvarIdNew <- Lean.Meta.withNewMCtxDepth do
      -- let subgoals ← evalTacticAt (← `(tactic| tr_constructor)) (← getMainGoal)

    let levelU <- mkFreshLevelMVar
    let levelV <- mkFreshLevelMVar
    let levelW <- mkFreshLevelMVar

    let fromType : Q(Sort $levelU) ← mkFreshExprMVar .none (userName := `fromType)
    let toType : Q(Sort $levelV) ← mkFreshExprMVar .none (userName := `toType)

    let covMapType1 : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `covMapTypeBase)
    let conMapType1 : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `conMapTypeBase)

    let covMapType2 : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `covMapTypeExtended)
    let conMapType2 : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `conMapTypeExtended)

    let matcher1 : Q(Type (max levelU levelV levelW)) := q(Param.{levelW, levelU, levelV} $covMapType1 $conMapType1 $fromType $toType)
    let matcher2 : Q(Type (max levelU levelV levelW)) := q(Param.{levelW, levelU, levelV} $covMapType2 $conMapType2 $fromType $toType)

    -- profileitM

    -- pruneSolvedGoals

    if !(← isExprDefEq matcher2 goalType) then
      throwTacticEx `tr_extend goal
        ("goal should be of type Param")

    let base : Q(Param.{levelW, levelU, levelV} $covMapType1 $conMapType1 $fromType $toType)
      ← Tactic.elabTermEnsuringType td matcher1

    let matcher1 <- instantiateMVars matcher1

    -- let base := ((<-Meta.reduceRecMatcher? base) <|> .some base).get!

    -- let (base, _) <- Meta.dsimp base (<-Simp.mkContext)

    -- let base <- instantiateMVars base

    -- IO.println s!"[tr_add_param_base] base is now {base}"
    -- IO.println s!"[tr_add_param_base] matcher1 is now {matcher1}"

    -- replaceMainGoal [← goal.define `param_base matcher1 base]
    let mvarIdNew ← goal.define name.getId matcher1 base
    -- let mvarIdNew <- instantiateMVars mvarIdNew
    let (_, mvarIdNew) ← mvarIdNew.intro1P

    -- replaceMainGoal [← goal.define name.getId matcher1 base]
    replaceMainGoal [mvarIdNew]


macro "tr_extend'" td:term:10 : tactic => `(tactic|
    -- (tr_check_extendable $td; tr_constructor <;> tr_fill_from $td)
    -- (tr_add_param_base param_base := $td; tr_constructor <;> tr_fill_from $td)
    (tr_add_param_base param_base := $td; tr_constructor' <;> tr_fill_from_hypothesis param_base)
  )

macro "tr_extend" td:term:10 : tactic => `(tactic|
  tr_extend' $td
  -- <;> (try unfold $td)
  -- <;> try simp
  <;> try dsimp only [
      Param.right, Param.left, Param.R, Param.right_implies_R,
      Param.R_implies_right, Param.R_implies_left, Param.left_implies_R,
      Param.R_implies_leftK, Param.R_implies_rightK,
      Param.forget, coeMap, ]
  --  only $td
  --  <;> simp[`(Lean.Parser.Tactic.simpLemma|$td)]
  --  <;> simp[`(Lean.Parser.Tactic.simpLemma|$td)]
  )

elab "tr_extend_multiple" " [" td:term,*,? "]" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    -- let goal ← Lean.Elab.Tactic.getMainGoal
    -- let goalType ← Lean.Elab.Tactic.getMainTarget

    -- let term1 := td.toList

    let rec unfoldList (a : List (TSyntax `term)) : MetaM (TSyntax `tactic) :=
      match a with
      | List.nil => `(tactic| tr_constructor')
      | List.cons x xs => do
        let name : Name := .mkSimple s!"param_base_{xs.length}"
        let hyponame : Ident := mkIdent name
        let subtactic : TSyntax `tactic := <- unfoldList xs
        `(tactic|
            (tr_add_param_base $hyponame := $x; $subtactic <;> tr_fill_from_hypothesis $hyponame <;>
            -- try simp
            try dsimp only [
                Param.right, Param.left, Param.R, Param.right_implies_R,
                Param.R_implies_right, Param.R_implies_left, Param.left_implies_R,
                Param.R_implies_leftK, Param.R_implies_rightK,
                Param.forget, coeMap, ]
            )
          )
        -- let mut result : TSyntax `tactic := `(tactic| tr_fill_from $x)
        -- for t in xs do
        --   result := `(tactic| $result <;> tr_fill_from $t)
        -- return result

    let tsepArray : Syntax.TSepArray `term "," := td

    let els := tsepArray.getElems

    let result : TSyntax `tactic ← unfoldList els.toList
    replaceMainGoal (<- evalTacticAt result (← getMainGoal))
