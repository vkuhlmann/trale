import Trale.Core.Param
import Trale.Utils.ExpressionHelpers

namespace Trale.Utils

open Lean Elab Tactic Meta

def refoldParamExpr
  (x : Expr) : MetaM (Except String Expr) := do
  trace[debug] s!"[In refold_param?] Expression is {← whnf x}"
  let p ← getParamParts? (← whnf x)

  match p with
  | .error _ =>
    return .error "Expression is not a param"

  | .ok p =>

  let covMapType ← recoverMapTypeFromExpr? p.covMapType
  let conMapType ← recoverMapTypeFromExpr? p.conMapType

  match covMapType, conMapType with
  | .none, _
  | _, .none =>
    return .error "Map types are not concrete (e.g. unassigned metavariables)"

  | .some covMapType, .some conMapType =>

  let x1 := covMapType.getMapTypeIndicator
  let x2 := conMapType.getMapTypeIndicator
  let funcName := (`Trale).str s!"Param{x1}{x2}"

  let x' :=
    mkAppN (.const funcName [p.levelW, p.levelU, p.levelV])
    #[p.fromType, p.toType]
  if !(←isDefEq x x') then
    throwError "Produced non-defeq term in refolding param: {x} vs {x'}"

  return .ok x'

def refoldParamExprDeep
  (x : Expr) : MetaM Expr := do

  replaceExprM (refoldParamExpr · >>= (pure ·.toOption)) x


open Lean Elab Term Tactic Meta in
elab "refold_param_type?" a:term : term => do
  let x ← elabTermEnsuringType a .none
  return (← refoldParamExpr x).toOption.getD x

open Lean.Parser.Tactic in
syntax (name := tr_refold) "tr_refold " (location)? : tactic

open Lean Elab Tactic Meta Term

def elabRefold (e : Expr) (p : Expr) (mkDefeqError : Expr → Expr → MetaM MessageData := elabChangeDefaultError) :
    TacticM Expr := do
    withAssignableSyntheticOpaque do
    unless ← isDefEq p e do
      throwError MessageData.ofLazyM (es := #[p, e]) do
        let (p, tgt) ← addPPExplicitToExposeDiff p e
        mkDefeqError p tgt
    instantiateMVars p

elab_rules : tactic
  | `(tactic| tr_refold $[$loc:location]?) => do
    withLocation (expandOptLocation (Lean.mkOptionalNode loc))
      (atLocal := fun h => do
        let newType ← refoldParamExprDeep (← h.getType)
        let (hTy', mvars) ← withCollectingNewGoalsFrom (elabRefold (← h.getType) newType) (← getMainTag) `change
        liftMetaTactic fun mvarId => do
          return (← mvarId.changeLocalDecl h hTy') :: mvars)
      (atTarget := do
        let newType ← refoldParamExprDeep (← getMainTarget)
        let (tgt', mvars) ← withCollectingNewGoalsFrom (elabRefold (← getMainTarget) newType) (← getMainTag) `change
        liftMetaTactic fun mvarId => do
          return (← mvarId.replaceTargetDefEq tgt') :: mvars)
      (failed := fun _ => throwError "'tr_refold' tactic failed")
