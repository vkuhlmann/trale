import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

import TraleTest.Utils.Lemmas.SummableSequence

set_option trace.tr.utils true

def mytest1 : Param42b nnR xnnR := inferInstance

-- instance : Param2b4 xnnR nnR := (inferInstance : Param42b nnR xnnR).flip
-- instance : Param04 seq_xnnR summable := (inferInstance : Param40 summable seq_xnnR).flip

-- def mytest2 : Param nnR _ _ _ := inferInstance


open Qq Lean Elab Command Tactic Term Expr Meta in
def mytest2 (a b : nnR) : (a + b = b + a) := by
  run_tac
    let toType : Q(Sort 1) <- mkFreshExprMVar q(Sort 1) (kind := .natural) (userName := `toType)
    let mapCov : Q(MapType) <- mkFreshExprMVar q(MapType) (kind := .natural) (userName := `mapCov)
    let mapCon : Q(MapType) <- mkFreshExprMVar q(MapType) (kind := .natural) (userName := `mapCon)
    -- let myInstValue <- mkFreshExprMVar q(Param42b.{0} nnR xnnR : Sort max 2 2 0) (kind := .natural) (userName := `myInstValue)
    -- let myInstValue <- mkFreshExprMVar q(Param42b.{0} nnR $toType : Sort max 2 2 0) (kind := .natural) (userName := `myInstValue)
    let myInstValue <- mkFreshExprMVar q(Param.{0} nnR $toType $mapCov $mapCon : Sort max 2 2 0) (kind := .natural) (userName := `myInstValue)
    if !(←synthesizeInstMVarCore myInstValue.mvarId!) then
      trace[tr.utils] s!"Failed to initialize value"
      return

    let myInstValue ← instantiateMVars myInstValue
    trace[tr.utils] s!"Found value: {myInstValue}"

  sorry


open Qq Lean Elab Command Tactic Term Expr Meta in
def mytest3 (a b : nnR) : (a + b = b + a) := by
  revert a b
  run_tac
    let levelV ← mkFreshLevelMVar
    let fromType := q(nnR)

    if !(← isDefEq (← inferType fromType) q(Sort levelV)) then
      throwTacticEx `tr_right (← getMainGoal) "Failed to infer level from fromType"

    let levelV ← instantiateLevelMVars levelV

    let toType : Q(Sort levelV) <- mkFreshExprMVar q(Sort levelV) (kind := .natural) (userName := `toType)
    -- let mapCov : Q(MapType) <- mkFreshExprMVar q(MapType) (kind := .natural) (userName := `mapCov)
    -- let mapCon : Q(MapType) <- mkFreshExprMVar q(MapType) (kind := .natural) (userName := `mapCon)
    -- let myInstValue <- mkFreshExprMVar q(Param42b.{0} nnR xnnR : Sort max 2 2 0) (kind := .natural) (userName := `myInstValue)
    -- let myInstValue <- mkFreshExprMVar q(Param42b.{0} nnR $toType : Sort max 2 2 0) (kind := .natural) (userName := `myInstValue)
    let myInstValue <- mkFreshExprMVar q(TrTranslateRight nnR $toType) (kind := .natural) (userName := `myInstValue)
    if !(←synthesizeInstMVarCore myInstValue.mvarId!) then
      trace[tr.utils] s!"Failed to initialize value"
      return

    let myInstValue ← instantiateMVars myInstValue
    trace[tr.utils] s!"Found value: {myInstValue}"

    let toType : Q(Sort levelV) ← instantiateMVars toType

    let levelX ← mkFreshLevelMVar
    let levelY ← mkFreshLevelMVar

    let goal ← getMainGoal
    let goalType : Q(Sort levelY) ← getMainTarget

    trace[tr.utils] s!"From type: {repr fromType}"
    trace[tr.utils] s!"To type: {repr toType}"

    let (fromName, toName) ← match fromType, toType with
      | .const a aLevels, .const b bLevels => pure (a, b)
      | _, _ =>
        throwTacticEx `tr_right goal "Couldn't extract constant names from fromType and toType"

    -- evalTactic (← `(tactic| trale_add_transformed [$fromType -> $toType] h1 := ))
    let transformedType : Q(Sort levelX) ← Converter.Conversion.trale (αName := fromName) (βName := toName) (← getMainTarget)
    trace[tr.utils] s!"Transformed type: {transformedType}"


    -- let levelW ← mkFreshLevelMVar

    if !(← isDefEq (← inferType transformedType) q(Sort levelX)) then
      throwTacticEx `tr_right goal "Failed to infer universe level of transformedType"

    if !(← isDefEq (← inferType goalType) q(Sort levelY)) then
      throwTacticEx `tr_right goal "Failed to infer universe level of goalType"

    let newBase : Q($transformedType)
      ← mkFreshExprMVar transformedType (userName := `base)

    -- let mvarIdNew ← goal.define `base transformedType newBase
    -- let (_, mvarIdNew) ← mvarIdNew.intro1P

    -- let newGoals ← evalTacticAt (← `(tactic| tr_by `(ident| base); tr_sorry sorry)) mvarIdNew
    trace[tr.utils] s!"Performing tr_by..."
    -- let newGoals ← evalTacticAt (← `(tactic| tr_by `(ident| basee))) mvarIdNew
    let baseIdent := mkIdent `base

    -- let newGoals ← evalTacticAt (← `(tactic| tr_by $baseIdent)) mvarIdNew

    /-
    (cannot evaluate code because
    '_tmp._lam_0._@.TraleTest.Transfer.SummableSequence._hyg.1926'
    uses 'sorry' and/or contains errors)

    unquoteExpr: transformedType✝ : Expr
    -/
    -- mvarIdNew.apply q(fun x => Param.right.{levelY, levelX, levelW} x $newBase)

    -- The `apply` function uses an elabForApply. This extra trickery makes it
    -- perhaps more difficult to still perform an apply for an already existing
    -- expression. We can't really and don't want to bring the expression back
    -- to a syntax.

    -- trace[tr.utils] s!"MvarIdNew: {repr mvarIdNew}"
    trace[tr.utils] s!"Transformed type: {repr transformedType}"
    trace[tr.utils] s!"Goal type: {repr goalType}"

    -- This gives universe metavariable error
    -- let paramType ← mkFreshExprMVar none
    -- let paramType ← mkFreshExprMVar none

    -- This gives the unquote error (unquoteExpr: transformedType✝ : Expr)
    let paramType := q(Param10.{0} $transformedType $goalType)

    let paramType := mkAppN (.const ``Param10 [.zero, levelX, levelY]) #[
      transformedType,
      goalType,
    ]

    let newGoals ← goal.applyN (
      .lam .anonymous paramType (
        mkAppN
        (.const ``Param.right [levelX, levelY, .zero])
        #[
          transformedType,
          goalType,
          .bvar 0,
          newBase
        ]
      ) .default) 1

    -- let newGoals ← evalTacticAt (← `(apply fun x => Param.right x $a)) mvarIdNew

    trace[tr.utils] s!"New goals: {repr newGoals}"
    trace[tr.utils] s!"Performed tr_by. newGoals length: {newGoals.length}"
    -- newGoals length: 4



    -- let newGoals := [mvarIdNew]

    -- goal.assign (.mvar mvarIdNew)
    replaceMainGoal <| [newBase.mvarId!] ++ newGoals

    -- goal.add

    -- evalApply
    -- let newMainGoal := apply fun x => Param.right x $a

    -- replaceMainGoal [
    --   newBase
    -- ] ++ (evalTacticAt (← `(tactic| tr_by `(term|$newBase))) goal)


  case instAddNnR =>
    infer_instance

  case base =>
    show ∀ (a b : xnnR), a + b = b + a
    intro a b

    exact xnnR_comm a b

  tr_intro a a' aR
  tr_intro b b' bR

  tr_split_application c c' cR by
    show extend (b' + a') = b + a
    unfold extend
    have h := tr.R_implies_map a' a aR
    dsimp at h
    subst h

    have h := tr.R_implies_map b' b bR
    dsimp at h
    subst h

    show xnnR.fin (b' + a') = tr.map b' + tr.map a'
    congr

    -- Or continue a bit more:
    -- simp [instParam, paramNNR, truncate_extend, SplitInj.toParam]
    -- show xnnR.fin (b' + a') = extend b' + extend a'
    -- unfold extend
    -- show xnnR.fin (b' + a') = .fin b' + .fin a'
    -- congr

  tr_split_application d d' dR by
    show extend (a' + b') = a + b
    have h := tr.R_implies_map a' a aR
    dsimp at h
    subst h

    have h := tr.R_implies_map b' b bR
    dsimp at h
    subst h

    congr

  show Param10 (d = c) (d' = c')

  simp [inferInstance, instParam, paramNNR, SplitInj.toParam] at aR bR cR dR
  subst aR bR cR dR

  tr_from_map
  intro h

  rw [←truncate_extend d', ←truncate_extend c']
  congr




-- Code based on 'summable.v' example by Trocq Rocq plugin developers.

theorem sum_nnR_add : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_by sum_xnnR_add

  -- We use these Params
  let _ := param_summable_seq

  -- TODO: Make this work with infer_instance
  -- We need to use `propParam` instance for `Param Prop Prop`, not the
  -- instance defined by equality.
  let _ : Param00 Prop Prop := propParam.forget

  let eqParam : Param00 (xnnR → xnnR → Prop) (nnR → nnR → Prop) := by
    tr_split; tr_split

  -- Part 1: split the foralls
  tr_intro a a' aR
  tr_intro b b' bR

  -- Part 2: Relate rhs:  X  =  *X*
  --                            ___
  --
  tr_split_application c c' cR by
    unfold extend

    show .fin (Σ a' + Σ b') = Σ a + Σ b

    have aF : seq_extend a' = a := tr.R_implies_map a' a aR
    have bF : seq_extend b' = b := tr.R_implies_map b' b bR

    subst aF bF

    repeat rw [summationHomeo]
    rw [add_xnnR_homeo]

  -- Part 3: Relate lhs:  *X*  =  X
  --                      ___
  --
  tr_split_application d d' dR by
    show .fin (Σ (a' + b')) = Σ (a + b)

    -- If you change this to a 'let', the `subst` won't work because it will see
    -- it as a hypothesis instead of an equality.
    have aF : seq_extend a' = a := tr.R_implies_map a' a aR
    have bF : seq_extend b' = b := tr.R_implies_map b' b bR

    subst aF bF

    have h1 : seq_extend a'.seq + seq_extend b'.seq = seq_extend (a' + b').seq := by
      congr

    rw [h1]
    rw [summationHomeo]

  show Param10 (d = c) (d' = c')

  -- Part 4: Relate eq:  X  *=*  X
  --                        ___
  --
  tr_split_application e e' eR by
    dsimp [inferInstance, eqParam, Param_arrow.Map0_arrow, propParam]

    intro x x' xR
    intro y y' yR

    show x = y → x' = y'

    rw [←tr.R_implies_map x x' xR]
    rw [←tr.R_implies_map y y' yR]

    exact congrArg _

  -- Part 5: Use relations to make the relation trivial
  --
  show Param10 (e d c) (e' d' c')
  dsimp [inferInstance, eqParam, Param_arrow.Map0_arrow, propParam] at eR

  tr_from_map
  show e d c → e' d' c'

  exact eR d d' dR c c' cR
