import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Trace
import Lean.Util
import Qq
open Qq Lean Elab Command Tactic Term Expr Meta

-- axiom functionRelationApplication
--   (p1 : Param10 (A -> B) (A' -> B'))
--   (p2 : Param10 A A')
--   (p3 : Param10 B B')
--   :
--   ∀ f f' (_ : p1.R f f'),
--   ∀ a a' (_ : p2.R a a'), p3.R (f a) (f' a')


-- builtin_initialize Lean.registerTraceClass `tr_split_application

-- #eval show IO Unit from do
--   Lean.registerTraceClass `tr_split_application

-- elab "tr_sometest" : tactic =>
--   withMainContext do

def forallApplication
  {α α' : Sort _}
  {β : α -> Sort _}
  {β' : α' -> Sort _}
  (p1 : Param00 α α')
  (a : α)
  (a' : α')
  (aR : p1.R a a')
  (p2 : ∀ a a' (_ : p1.R a a'), Param cov con (β a) (β' a'))
  :
  Param cov con (β a) (β' a') := (p2 a a' aR)

elab "tr_inspect_expr" td:term : tactic =>
  withMainContext do
    let expr ← Tactic.elabTerm td .none

    trace[tr.utils] s!"Type as expression is\n  {repr expr}"

    match expr with
    | .fvar _ =>
      --
      let ldecl ← getFVarLocalDecl expr
      trace[tr.utils] s!"Fvar value is\n  {repr ldecl.value}"

    | _ => return ()

structure SplitApplicationConfig where
  allowHead := true
declare_config_elab elabSplitAppConfigCore    SplitApplicationConfig

#check
  (let x := 3; Fin x)
  -- ((let x := 3; Fin x) : ((y : Nat) → Fin y : Type))

-- #check
--   ∀ x : Nat,
--   Fin x

#reduce (let x := 3; x + 5)


example : (let x := 3; Fin 7) := by
  let h := make_whnf (let x := 3; x + 5)


  tr_whnf

  -- simp at h


  sorry


#check Simp.SimprocsArray

#eval (fun x y => x + y) 4 3

-- elab "tr_split_application'" a:stx,*,? : tactic =>
-- elab "tr_split_application'" a:(Lean.Parser.Tactic.config)? : tactic =>
-- elab "tr_split_application'" ppSpace colGt a:("("Lean.Parser.Tactic.config ")")? : tactic =>

elab "tr_split_application'" ppSpace colGt !ident a:Lean.Parser.Tactic.optConfig : tactic =>
-- elab "tr_split_application'" : tactic =>

  -- TODO Is there a more elegant way to write the constant function?
  Lean.withTraceNode `tr.utils (fun _ => return "tr_split_application") do
    withMainContext do
      trace[tr.utils] s!"syntax is {repr a}"
      let config ← elabSplitAppConfigCore a

      let allowHead := config.allowHead

      trace[tr.utils] s!"Obtaining goal"
      let goal ← getMainGoal
      let goalType ← getMainTarget
      let tag ← goal.getTag

      -- trace[tr.utils] s!"Type is {goalType}"
      -- trace[tr.utils] s!"Type as expression is {repr goalType}"

      trace[tr.utils] s!"Performing pattern match"
      let levelU ← mkFreshLevelMVar
      let levelV ← mkFreshLevelMVar
      let levelW ← mkFreshLevelMVar

      let fromType : Q(Sort $levelU) ← mkFreshExprMVar .none (userName := `fromType)
      let toType : Q(Sort $levelV) ← mkFreshExprMVar .none (userName := `toType)

      let covMapType : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `covMapType)
      let conMapType : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `conMapType)

      let matcher : Q(Type (max levelU levelV levelW)) := q(Param.{levelW} $covMapType $conMapType $fromType $toType)

      trace[tr.utils] s!"Checking defEq"
      if !(← isExprDefEq matcher goalType) then
        trace[tr.utils] s!"Throwing 'goal should be of type Param'"
        throwTacticEx `tr_split_application goal ("goal should be of type Param")

      trace[tr.utils] s!"Checked defEq"
      let fromType : Q(Sort $levelU) ← instantiateMVars fromType
      let toType : Q(Sort $levelV) ← instantiateMVars toType
      let covMapType : Q(MapType) ← instantiateMVars covMapType
      let conMapType : Q(MapType) ← instantiateMVars conMapType

      trace[tr.utils] s!"fromType: {fromType}"
      trace[tr.utils] s!"toType: {toType}"
      trace[tr.utils] s!"covMap: {covMapType}"
      trace[tr.utils] s!"conMap: {conMapType}"

      /-
        Given two function applications, finds the last (most outer) argument
        where both function applications have a non-fvar. Returns a triple of
        the head, the targeted argument, and the trailing arguments.

        For example, for `findFirstNonFvars (f a b c d, []) (f' a' b' c' d', [])`
        where `b` and `b'` are expressions, and `c`, `c'`, `d`, `d'` are fvars,
        the result is `(f a, b, [c, d]), (f' a', b', [c', d'])`.
      -/

      let rec findFirstNonFvars
        (fromType toType : (Expr × List Expr))
        : MetaM ((Expr × Option Expr × List Expr) × (Expr × Option Expr × List Expr)) := do
        let (fromType, fromArgs) := fromType
        let (toType, toArgs) := toType

        let depth := fromArgs.length
        let pref := s!"({depth}) "

        match fromType, toType with
        | .app f a, .app g b =>
          match a, b with
          | .fvar _, .fvar _ =>
            trace[tr.utils] s!"{pref}Both final arguments are fvars"
            findFirstNonFvars
              (f, a :: fromArgs)
              (g, b :: toArgs)

          | _, _ =>
            match a, b with
            | .fvar _, _
            | _, .fvar _ =>
              trace[tr.utils] s!"{pref}One of the final arguments is not an fvar"
            | _, _ =>
              trace[tr.utils] s!"{pref}Final arguments are not fvar"

            -- trace[tr.utils] s!"{pref}a: {a}"
            -- trace[tr.utils] s!"{pref}b: {b}"

            -- let aDecl := LocalContext.findFVar? lctx a
            -- let bDecl := LocalContext.findFVar? lctx b

            -- trace[tr.utils] s!"{pref}aDecl: {aDecl.isSome}"
            -- trace[tr.utils] s!"{pref}bDecl: {bDecl.isSome}"

            let aType ← inferType a
            let bType ← inferType b

            -- match aDecl, bDecl with
            -- | .some aDecl, .some bDecl =>
            --   let aType := aDecl.type
            --   let bType := bDecl.type

            --   trace[tr.utils] s!"{pref}Type of a: {format aType}"
            --   trace[tr.utils] s!"{pref}Type of b: {format bType}"


            if Expr.isSort aType || Expr.isSort bType then
              trace[tr.utils] s!"{pref}One or both types are Sort type. Skipping to next"
              return (← findFirstNonFvars
                (f, a :: fromArgs)
                (g, b :: toArgs))

            -- | _, _ => pure ()


            return (
              (f, .some a, fromArgs),
              (g, .some b, toArgs),
            )
        | _, _ =>
          trace[tr.utils] s!"{pref}No application"
          return (
              (fromType, .none, fromArgs),
              (toType, .none, toArgs),
            )

      /-
        Wraps an expression `e` with loose bvars in `count` lambda expressions,
        to reseal the bvars. Takes a mandatory list `exampleValues` used to infer
        the binder types of the lambda's.
      -/
      let rec sealLambda
        (e : Expr) (count : Nat) (exampleValues : List Expr) : MetaM (Expr × List Expr) := do
        trace[tr.utils] s!"Doing sealLambda for count {count}, (exampleValues.length: {exampleValues.length})"
        -- FIXME Can this function be re-enabled safely?
        if count > 0 then
          throwError "Disabled sealLambda for testing"
        match count, exampleValues with
        | 0, _
        | _, [] => return (e, exampleValues)
        | n+1, a::as =>
            let (body, remaining) ← sealLambda e n as
            return (Expr.lam Name.anonymous (← inferType a) body BinderInfo.default, remaining)

      /-
        Moves fvar arguments to the outside of the a function application.

        For example, if `b` is a constant, and `a`, `c` and `d` are fvars, then
        `hoistFVarsToLambda' (f a b c d) (f' a' b' c' d') true`
        yields
        `(((fun x y z => f x b y z), [a, c, d]), ((fun x y z => f x b' y z), [a', c', d']))`

        and
        `hoistFVarsToLambda' (f a b c d) (f' a' b' c' d') false`
        yields
        `(((fun x => f x b), [a, c, d]), ((fun x => f x b'), [a', c', d']))`.

        Indeed, `needsSeal` can be false for a trailing part of the application
        where only fvars occur, eliminating excessive lambda wrapping. In
        invocation, set `needsSeal` to false, it is only needed in recursive
        calls.

      -/
      let rec hoistFVarsToLambda'
        (e1 e2 : Expr)
        -- (lambdaDepth : Nat)
        -- (isTrailing : Bool)
        (needsSeal : Bool)

        : MetaM ((Expr × List Expr) × (Expr × List Expr) × Nat) := do
        match e1, e2 with
        | .app f a, .app g b =>
          trace[tr.utils] s!"[hoistFVarsToLambda'] f: {repr f}"
          trace[tr.utils] s!"[hoistFVarsToLambda'] a: {repr a}"

          match a, b with
            | .fvar _, .fvar _ =>
              let ((f, fVars), (g, gVars), sealDepth) ← hoistFVarsToLambda' f g needsSeal
              return match needsSeal with
              | true =>  (
                  (.app f (.bvar sealDepth), a::fVars),
                  (.app g (.bvar sealDepth), b::gVars),
                  sealDepth + 1
                )
              | false => (
                  (f, a::fVars),
                  (g, b::gVars),
                  0
                )

            | _, _ =>
              let ((f, fVars), (g, gVars), sealDepth) ← hoistFVarsToLambda' f g true
              let (fSealed, _) ← sealLambda (.app f a) sealDepth fVars
              let (gSealed, _) ← sealLambda (.app g b) sealDepth gVars
              return ((fSealed, fVars), (gSealed, gVars), 0)
              -- match isTrailing with
              -- | true => ((f, fVars), (g, gVars))
              -- | false => ((.app f a, fVars), (.app g b, gVars))
        | _, _ =>
          return ((e1, []), (e2, []), 0)

      -- Can't proof easily because it uses the MetaM now
      -- have sealDepthIsZeroWhenNoSeal : ∀ e1 e2, (←hoistFVarsToLambda' e1 e2 false).3 == 0 := by

      /-
      Extracts the head of a function application to a lambda.

      For example, if `b` is a constant, and `a`, `c` and `d` are fvars, then
      `hoistFVarsToLambda (f a b c d) (f' a' b' c' d')`
      yields
      `((fun z => z a c d),    (fun x => f x b),`
      ` (fun z => z a' c' d'), (fun x => f x b'))`

      -/
      let hoistFVarsToLambda (e1 e2 : Expr) : MetaM ((Expr × Expr) × (Expr × Expr)) := do
        let ((a1, a1Vars), (a2, a2Vars), _) ← hoistFVarsToLambda' e1 e2 false

        -- let a1VarsTypes ← List.mapM inferType a1Vars
        -- let a2VarsTypes ← List.mapM inferType a2Vars

        -- let rec mkApplierFun (types : List Expr) : Expr :=

        -- let applierFun1 := a1VarsTypes.foldr
        --   (fun x y => Expr.lam .anonymous x y .default)
        --   (.bvar 0)

        trace[tr.utils] s!"[hoistFVarsToLambda] a1: {a1}"
        trace[tr.utils] s!"[hoistFVarsToLambda] a1 repr: {repr a1}"
        trace[tr.utils] s!"[hoistFVarsToLambda] a1Vars: {a1Vars}"

        let applierFun1 := Expr.lam .anonymous (← inferType a1) (mkAppN (.bvar 0) ⟨a1Vars.reverse⟩) .default
        -- let applierFun2 ← withLocalDeclD .anonymous (← inferType a2) (pure $ mkAppN . ⟨a2Vars⟩)
        let applierFun2 := Expr.lam .anonymous (← inferType a2) (mkAppN (.bvar 0) ⟨a2Vars.reverse⟩) .default

        trace[tr.utils] s!"[hoistFVarsToLambda] applierFun1 repr: {repr applierFun1}"
        trace[tr.utils] s!"[hoistFVarsToLambda] applierFun1: {applierFun1}"


        return ((applierFun1, a1), (applierFun2, a2))

      let rec getFunctionHead (e : Expr) : Expr :=
        match e with
        | .app f _ => getFunctionHead f
        | _ => e

      let shouldExtract (e1 e2 : Expr) :=
        match e1, e2 with
        | .fvar _, .fvar _ => false
        | .lam _ _ _ _, .lam _ _ _ _ => false
        | _, _ => true


      let mut ((body1, target1, args1), (body2, target2, args2))
        ← findFirstNonFvars (fromType, []) (toType, [])

      let (a, a') ← match target1, target2 with
      | .none, _
      | _, .none =>
        -- If no non-fvars in the arguments are found, then we will extract the
        -- head of the function application instead.

        if !allowHead then
          throwTacticEx `tr_split_applicaton' goal "No non-fvars found in body"

        if !shouldExtract (getFunctionHead fromType) (getFunctionHead toType) then
          throwTacticEx `tr_split_applicaton' goal "No non-fvars found in body, and head is fvar of lambda"

        let ((f1, a1), (f2, a2)) ← hoistFVarsToLambda fromType toType

        body1 ← instantiateMVars f1
        body2 ← instantiateMVars f2
        args1 := []
        args2 := []

        pure (← instantiateMVars a1, ← instantiateMVars a2)

        -- throwTacticEx `tr_split_application goal "Can't split application: not an application, or no non-fvar arguments"
      | some a, some a' => pure (a, a')


      -- if target1.isNone || target2.isNone then
      --   throwTacticEx `tr_split_application goal "Can't split application: not an application, or no non-fvar arguments"

      let levelX1 ← mkFreshLevelMVar
      let levelX2 ← mkFreshLevelMVar
      let levelY1 ← mkFreshLevelMVar
      let levelY2 ← mkFreshLevelMVar
      let levelZ ← mkFreshLevelMVar


      let α : Q(Sort $levelX1) ← inferType a
      let α' : Q(Sort $levelX2) ← inferType a'
      -- let α : Q(Sort $levelX1) ← mkFreshExprMVar (.some q(Sort $levelX1)) (userName := `α)
      -- let α' : Q(Sort $levelX2) ← mkFreshExprMVar (.some q(Sort $levelX2)) (userName := `α')

      -- let a : Q($α) := a
      -- let a' : Q($α') := a'


      -- let targetFVar1 ← mkFreshFVarId
      -- let targetFVar2 ← mkFreshFVarId

      -- let abc : LocalDecl := sorry
      -- let ghi := abc.toExpr

      -- trace[tr.utils] s!"Getting type of fvar1 and fvar2:"
      -- -- trace[tr.utils] s!"targetFVar1: {←targetFVar1.findDecl}"
      -- trace[tr.utils] s!"targetFVar2: {Option.map LocalDecl.toExpr (←targetFVar2.findDecl?)}"

      -- let lambda1pre := mkAppN body1 ⟨(.fvar targetFVar1)::args1⟩

      -- trace[tr.utils] s!"lambda1pre: {repr lambda1pre}"
      -- let lambda1pre <- instantiateMVars lambda1pre

      -- trace[tr.utils] s!"lambda1pre: {repr lambda1pre}"

      -- let lambda1 ←
      --   mkLambdaFVars #[.fvar targetFVar1]
      --   <| lambda1pre

      -- let lambda2 ← instantiateMVars <| (← mkLambdaFVars #[.fvar targetFVar2]
      --   <| mkAppN body2 ⟨(.fvar targetFVar2)::args2⟩)

      /-
      Lean.Expr.lam
      Lean.Name.anonymous
      (Lean.Expr.const `_inhabitedExprDummy [])
      (Lean.Expr.app

      -/

      -- let levelA1 ← mkFreshLevelMVar
      -- let levelA2 ← mkFreshLevelMVar


      if !(← isDefEq (← inferType α) q(Sort $levelX1)) then
        throwTacticEx `tr_split_application goal "Failed to infer universe level of target1Type"

      if !(← isDefEq (← inferType α') q(Sort $levelX2)) then
        throwTacticEx `tr_split_application goal "Failed to infer universe level of target2Type"



      let β
          -- : Q($target1Type → $fromType)
          : Q($α → Sort $levelY1)
          ← withLocalDeclD `trtarget α
          fun b => mkLambdaFVars #[b] <| mkAppN body1 ⟨b::args1⟩

      let β'
          -- : Q($target2Type → $toType)
          : Q($α' → Sort $levelY2)
          ← withLocalDeclD `trtarget α'
          fun b => mkLambdaFVars #[b] <| mkAppN body2 ⟨b::args2⟩

      -- trace[tr.utils] s!"lambda1 (a): {repr lambda1}"
      -- let lambda1 ← instantiateMVars lambda1
      -- trace[tr.utils] s!"lambda1 (b): {repr lambda1}"

      let result1 : Q(Sort $levelU) := .app β a
      let result2 : Q(Sort $levelV) := .app β' a'

      -- trace[tr.utils] s!"Got result {result}"
      let resultType : Q(Type (max levelU levelV levelW))
        := q(Param.{levelW} $covMapType $conMapType $result1 $result2)

      -- evalTactic (← `(tactic| show $resultType))

      if !(← isDefEq goalType resultType) then
        throwTypeMismatchError none goalType resultType (mkStrLit "dummy")

        throwTacticEx `tr_split_application goal "Failed to replace goal with new one"

      -- let lambda1 : Expr ← instantiateMVars lambda1
      -- let lambda2 : Expr ← instantiateMVars lambda2

      -- trace[tr.utils] s!"α: {repr α}"
      -- trace[tr.utils] s!"α': {repr α'}"
      -- trace[tr.utils] s!"a: {repr a}"
      -- trace[tr.utils] s!"lambda1: {repr β}"
      -- trace[tr.utils] s!"lambda2: {repr β'}"
      -- trace[tr.utils] s!"target1: {repr target1}"
      -- trace[tr.utils] s!"target2: {repr target2}"

      /-
      The following does not work, because following it with apply or refine undoes
      our works, eta reducing to the original goal:
      ```
      let newGoal ← goal.replaceTargetDefEq resultType
      replaceMainGoal [newGoal]
      ```
      -/

      -- let α : Q(Sort $levelU) ← mkFreshExprMVar (.some q(Sort)) (userName := `α)
      -- let α' : Q(Sort $levelV) ← mkFreshExprMVar (.some q(Sort)) (userName := `α')

      -- let α ← inferType target1
      -- let α' ← inferType target2

      -- let levelAA1 ← mkFreshLevelMVar
      -- let levelAA2 ← mkFreshLevelMVar

      -- let α : Q(Sort $levelX1) ← mkFreshExprMVar .none (userName := `α)
      -- let α' : Q(Sort $levelX2) ← mkFreshExprMVar .none (userName := `α')

      -- if !(← isExprDefEq α (←inferType target1)) then
      --   throwTacticEx `tr_split_application goal "Failed to match type of target1 with α"

      -- if !(← isExprDefEq α' (←inferType target2)) then
      --   throwTacticEx `tr_split_application goal "Failed to match type of target2 with α"

      let βType := q($α → Sort $levelY1)
      let βType' := q($α' → Sort $levelY2)

      if !(← isExprDefEq βType (←inferType β)) then
        throwTacticEx `tr_split_application goal "Failed to match type of lambda1 with type of β"
      if !(← isExprDefEq βType' (←inferType β')) then
        throwTacticEx `tr_split_application goal "Failed to match type of lambda2 with type of β'"

      -- let β : Q($α → Sort $levelY1) := lambda1
      -- let β' : Q($α' → Sort $levelY2) := lambda2

      -- let β : Q($α → Sort $levelY1) := sorry
      -- let β' : Q($α' → Sort $levelY2) := sorry

      /-
      stuck at solving universe constraint
        max
        (max (max (max (max levelX1 levelX2) (levelY1+1)) (levelY2+1)) ?u.20766)
        (?u.20772+1) =?= max (max levelU levelV) (levelW+1)
      while trying to unify
        Sort
          (max (max (max (max (max levelX1 levelX2) ?u.20766) (levelY2 + 1)) (levelY1 + 1))
              (?u.20772 +
                  1)) : Type (max (max (max (max (max levelX1 levelX2) ?u.20766) (levelY2 + 1)) (levelY1 + 1)) (?u.20772 + 1))
      with
        Sort (max levelU levelV (levelW + 1)) : Type (max levelU levelV (levelW + 1))
      -/

      -- This does not work
      -- let p1Type : Q(Type (max levelX1 levelX2)) := q(Param10 $α $α')
      -- let p1 : Q($p1Type) ← mkFreshExprMVar (.some p1Type) (userName := `p1)

      -- Cryptic errors like "unknown constant '_inhabitedExprDummy'"
      --   Solved now.  Was using an fresh FVar without `withLocalDec`

      -- This will be a goal
      let p1 : Q(Param00.{levelZ} $α $α') ←
        mkFreshExprMVar (.some q((Param00.{levelZ} $α $α'))) (userName := .str tag "p1")

      -- This will be inferred
      -- let a : Q($α) := target1
      -- let a' : Q($α') := target2
      -- let a : Q($α) ← mkFreshExprMVar (.some q($α)) (userName := `a)
      -- let a' : Q($α') ← mkFreshExprMVar (.some q($α')) (userName := `a')

      /-
      Sometimes it's a hunt for loose universe levels, and trying various things
      until something works.

      stuck at solving universe constraint
        max
        (max (max (max levelX1 levelX2) (levelY1+1)) (levelY2+1))
        (?u.20373+1) =?= max (max (max levelX1 levelX2) (levelY1+1)) (levelY2+1)
      while trying to unify
        Sort
          (max (max (max (max levelX1 levelX2) (levelY2 + 1)) (levelY1 + 1))
              (?u.20373 + 1)) : Type (max (max (max (max levelX1 levelX2) (levelY2 + 1)) (levelY1 + 1)) (?u.20373 + 1))
      with
        Sort (max levelX1 levelX2 (levelY2 + 1) (levelY1 + 1)) : Type (max levelX1 levelX2 (levelY2 + 1) (levelY1 + 1))

      -/
      /-
      stuck at solving universe constraint
        max
        (max (max (max (max levelX1 levelX2) (levelY1+1)) (levelY2+1)) levelZ)
        (?u.20294+1) =?= max (max (max (max levelX1 levelX2) (levelY1+1)) (levelY2+1)) levelZ
      while trying to unify
        Sort
          (max (max (max (max (max levelX1 levelX2) levelZ) (levelY2 + 1)) (levelY1 + 1))
              (?u.20294 +
                  1)) : Type (max (max (max (max (max levelX1 levelX2) levelZ) (levelY2 + 1)) (levelY1 + 1)) (?u.20294 + 1))
      with
        Sort
          (max levelX1 levelX2 levelZ (levelY2 + 1)
              (levelY1 + 1)) : Type (max levelX1 levelX2 levelZ (levelY2 + 1) (levelY1 + 1))
      -/
      -- let mytest
      -- --  : Q(Sort (max levelX1 levelX2 levelZ (levelY2+1) (levelY1+1) ))
      -- -- := q(Param10 ($β $a) ($β' $a') : Type (max (max levelX1 levelY1) (max levelX2 levelY2) levelZ))
      -- := q(Param10 ($β $a) ($β' $a') : Type (max levelY1 levelY2 levelZ))

      -- let p2Type
      -- : Q(Sort (max levelX1 levelX2 levelZ (levelY2+1) (levelY1+1) ))
      -- := q(∀ a a' (_ : ($p1).R a a'), (Param10 ($β a) ($β' a') : Type (max (max levelX1 levelY1) (max levelX2 levelY2) levelZ)))

      -- trace[tr.utils] s!"p2Type: {repr p2Type}"

      -- p2.mvarId!.ass

      -- trace[tr.utils] s!"p2: {repr p2}"

      let aVal := a
      let a : Q($α) ← mkFreshExprMVar α (userName := .mkSimple "a")
      a.mvarId!.assign aVal

      let aVal' := a'
      let a' : Q($α') ← mkFreshExprMVar α' (userName := .mkSimple "a'")
      a'.mvarId!.assign aVal'

      let aRtype := q(($p1).R $a $a')
      -- trace[tr.utils] s!"aRtype: {repr aRtype}"

      -- These will be goals
      let aR
        : Q(($p1).R $a $a')
        ← mkFreshExprMVar (.some q(($p1).R $a $a')) (userName := .str tag "aR")


      let p2base
        ← mkFreshExprMVarQ
          q(let a : $α := $a; let a' : $α' := $a';
            let aR: ($p1).R a a' := $aR;
            (Param.{levelZ} $covMapType $conMapType ($β a) ($β' a')))
          (userName := .str tag "p2")

      trace[tr.utils] s!"p2 base is {format p2base}"

      let (p2FvarIds, p2mvarId) ← p2base.mvarId!.introNP 3

      p2mvarId.withContext do

      let p2 : Q(Param.{levelZ} $covMapType $conMapType ($β $a) ($β' $a')) :=
        .mvar p2mvarId

      -- let p2 := p2base

      trace[tr.utils] s!"p2 is {format p2}"

      let sometest2 := q(4)

      -- -- (a : α)
      -- -- (a' : α')
      -- -- (aR : p1.R a a')
      -- -- (p2 : ∀ a a' (_ : p1.R a a'), Param10 (β a) (β' a'))

      -- /-
      --   {α α' : Sort _}
      --   {β : α -> Sort _}
      --   {β' : α' -> Sort _}
      --   (p1 : Param10 α α')
      --   (a : α)
      --   (a' : α')
      --   (aR : p1.R a a')
      --   (p2 : ∀ a a' (_ : p1.R a a'), Param10 (β a) (β' a'))
      --   :
      --   Param10 (β a) (β' a')
      -- -/


      -- let complete := q(forallApplication $p1 $a $a' $aR $p2)
      -- let complete := q(@forallApplication _ _ $β $β' $p1 $a $a' $aR $p2)
      -- let almostComplete := q(fun aR => @forallApplication $covMapType $conMapType _ _ $β $β' $p1 $a $a' aR $p2)
      -- let almostComplete := q(fun aR => @forallApplication $covMapType $conMapType _ _ $β $β' $p1 $a $a' aR $p2)
      -- let complete : Expr := .app almostComplete aR

      -- let completeResult : Simp.Result ← unfold complete ``forallApplication
      -- let complete := completeResult.expr

      -- The function `mkSimpContext`
      -- let (complete, _) ←
      --   dsimp p2
      --     (← Simp.mkContext)
      --     -- (simprocs := #[{}])
      --     -- (simprocs := #[←Simp.Simprocs.add {} ``forallApplication false])

      -- -- trace[tr.utils] s!"Complete is {repr complete}"
      -- -- trace[tr.utils] s!"Complete is {← ppTerm <| ← PrettyPrinter.delab complete}"
      -- let complete ← instantiateMVars complete

      let complete := ← instantiateMVars p2

      trace[tr.utils] s!"Goal type is {format goalType}"

      trace[tr.utils] s!"Complete type is {format (← inferType complete)}"

      if !(← isDefEq goalType (← inferType complete)) then
        throwTypeMismatchError
          "Could not unify goal type (1) with assembled type"
          goalType (← inferType complete) complete
          -- `tr_split_application

        throwTacticEx `tr_split_application goal "Could not unify goal type (1) with assembled type"

      trace[tr.utils] s!"Passed type unification test 1."

      if !(← isDefEq (← goal.getType) (← inferType complete)) then
        throwTacticEx `tr_split_application goal "Could not unify goal type (2) with assembled type"


      trace[tr.utils] s!"Complete is {format complete}"

      /-
      MVarId.assign recommends:
      ```
      Add mvarId := x to the metavariable assignment. This method does not check
      whether mvarId is already assigned, nor it checks whether a cycle is being
      introduced, or whether the expression has the right type. This is a
      low-level API, and it is safer to use isDefEq (mkMVar mvarId) x.
      ```

      While recommended by MVarId.assign, this throws, even though the above
      type check.
      ```
      if !(← isDefEq (mkMVar goal) complete) then
         throwTacticEx `tr_split_application goal "Could not unify goal with assembled value (but succeeded at type)"
      ```
      -/

      goal.assign p2base

      replaceMainGoal [p1.mvarId!, aR.mvarId!, p2.mvarId!]



      -- let somtest := q(4)
      -- let complete : Q(Nat) := q(4 : Nat)



      -- match fromType, toType with
      -- | .app f a, .app g b =>
      --   match a, b with
      --   | .fvar _, .fvar _ =>
      --     trace[tr.utils] s!"Both final arguments are fvars"
      --   | .fvar _, _
      --   | _, .fvar _ =>
      --     trace[tr.utils] s!"One of the final arguments is not an fvar"
      --   | _, _ =>
      --     trace[tr.utils] s!"Final arguments are not fvar"
      -- | _, _ =>
      --   trace[tr.utils] s!"No application"

      -- getForallArity


-- macro "tr_split_application'" : tactic => `(
--   tactic| (
--     tr_split_application'
--   )
-- )


-- TODO Make the derived macro's accept config options.
/-
  I was unable to pass around the config options through simple wrappers.
  Because in `Split.lean` working with builtin_tactic didn't work, I haven't
  tried that one yet.

  ```lean
  -- syntax (name := tr_split_application_basic) "tr_split_application" notFollowedBy(ident) ppSpace Lean.Parser.Tactic.optConfig : tactic

  -- elab_rules : tactic
  --   | `(tactic| tr_split_application) => do
  --     evalTactic (← `(tactic| tr_split_application' <;> try infer_instance))
  --   | `(tactic| tr_split_application $cfg) => do
  --     evalTactic (← `(tactic| tr_split_application' $cfg <;> try infer_instance))

  -- -- @[builtin_tactic tr_split_application_basic]


  -- macro "tr_split_application" notFollowedBy(ident) cfg:Lean.Parser.Tactic.optConfig : tactic => `(tactic|tr_split_application' $cfg <;> try infer_instance)
  ```
-/

macro "tr_split_application'" : tactic => `(tactic|(tr_split_application'))

macro "tr_split_application" : tactic => `(tactic|tr_split_application' <;> try infer_instance)

-- #check binderIdent

macro "tr_split_application'" ppSpace colGt a:binderIdent a':binderIdent aR:binderIdent : tactic => `(
  tactic| (
    (tr_split_application'); (
      try
        (
          (case' p2 => rename_last $a $a' $aR);rotate_left 1
        ); tr_whnf
      )
    )
  )

macro "tr_split_application" ppSpace colGt a:binderIdent a':binderIdent aR:binderIdent : tactic => `(
  tactic| (
    (tr_split_application); (
      try (
        (case' p2 => rename_last $a $a' $aR);rotate_left 1); tr_whnf
        -- tr_simp_R at aR
      )
    )
  )


-- FIXME: After the 'by' it doesn't show the subgoal in the Goals list until you start
-- typing... The syntax mirrors syntax of 'case', so how is it working for 'case'?
-- Is there some magic missing in this implementation?
macro "tr_split_application" ppSpace colGt a:binderIdent a':binderIdent aR:binderIdent " by " sub:tacticSeq : tactic => `(
  tactic| (
    (tr_split_application $a $a' $aR; case aR => $sub)
  ))
macro "tr_split_application'" ppSpace colGt a:binderIdent a':binderIdent aR:binderIdent " by " sub:tacticSeq : tactic => `(
  tactic| (
    (tr_split_application' $a $a' $aR; case aR => $sub)
  ))
macro "tr_split_application" ppSpace colGt a:binderIdent a':binderIdent aR:binderIdent " => " sub:tacticSeq : tactic => `(
  tactic| (
    (tr_split_application $a $a' $aR; case aR => $sub)
  ))
