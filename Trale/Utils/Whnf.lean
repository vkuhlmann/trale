import Lean

open Lean Expr Elab Tactic MVarId in
elab "tr_whnf'" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget
    -- trace[tr.utils] s!"Goal is {goalType}"

    let goal2 ← Lean.Meta.whnf goalType
    -- trace[tr.utils] s!"Goal2 is {goal2}"

    let newGoal ← goal.replaceTargetDefEq goal2
    replaceMainGoal [newGoal]

open Lean Expr Elab Term Tactic MVarId Meta in
elab "make_whnf" td:term : term => do
  let v ← Term.elabTerm td none

  trace[debug] s!"v is {repr v}"

  let v : Expr ← do
    match v with
    | .fvar f =>
      match (← f.getValue?) with
      | .none => pure v
      | .some a => pure a
    | e => pure e

  let simplified ← whnf v
  trace[debug] s!"after whnf: {repr simplified}"

  return (← whnf v)

  -- return <| whnf <| ←elabTerm e


open Lean Expr Elab Tactic MVarId Meta in
elab "tr_whnf'" "at" ppSpace colGt t:ident : tactic =>
  withMainContext do
    let goal ← getMainGoal

    let fvarId : FVarId ← getFVarId t
    let decl ← fvarId.findDecl?

    match decl with
    | none => throwTacticEx `tr_whnf goal "Could not find hypothesis to apply whnf at"
    | some decl =>

    let declType ← whnf decl.type

    trace[debug] s!"Decl type: {decl.type}"
    trace[debug] s!"Decl type simp: {declType}"

    liftMetaTactic fun mvarId => do
      -- let mvarIdNew ← mvarId.define n.getId origType origVal
      let mvarIdNew ← mvarId.define t.getId declType (.fvar fvarId)
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

    -- FIXME: This clearing is currently not working. Why?
    -- If found, but not cleared, this would because of a forward dependency.
    -- which does make sense since we're currently still referring to the original
    -- fvar. Should we open it, and refer to its value, if that is assigned?
    liftMetaTactic1 (·.tryClear fvarId)


-- syntax (name := tr_whnf) "tr_whnf'" : tactic
open Lean.Parser.Tactic in
syntax (name := tr_whnf) "tr_whnf " (location)? : tactic


open Lean Elab Tactic Meta Term

def elabWhnf (e : Expr) (p : Expr) (mkDefeqError : Expr → Expr → MetaM MessageData := elabChangeDefaultError) :
    TacticM Expr := do
    withAssignableSyntheticOpaque do
    unless ← isDefEq p e do
      throwError MessageData.ofLazyM (es := #[p, e]) do
        let (p, tgt) ← addPPExplicitToExposeDiff p e
        mkDefeqError p tgt
    instantiateMVars p

elab_rules : tactic
  -- | `(tactic| subst_last%$t) =>
-- macro_rules --@[builtin_tactic change] def evalChange : Tactic
  | `(tactic| tr_whnf $[$loc:location]?) => do
    withLocation (expandOptLocation (Lean.mkOptionalNode loc))
      (atLocal := fun h => do
        let newType ← whnf (← h.getType)
        let (hTy', mvars) ← withCollectingNewGoalsFrom (elabWhnf (← h.getType) newType) (← getMainTag) `change
        liftMetaTactic fun mvarId => do
          return (← mvarId.changeLocalDecl h hTy') :: mvars)
      (atTarget := do
        let newType ← whnf (← getMainTarget)
        let (tgt', mvars) ← withCollectingNewGoalsFrom (elabWhnf (← getMainTarget) newType) (← getMainTag) `change
        liftMetaTactic fun mvarId => do
          return (← mvarId.replaceTargetDefEq tgt') :: mvars)
      (failed := fun _ => throwError "'change' tactic failed")
