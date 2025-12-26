import Trale.Core.Param
import Trale.Utils.Whnf
import Lean

def Param.toBottom (p : Param cov con α β) : Param00 α β :=
  p.forget (h1 := map0bottom) (h2 := map0bottom)


namespace Trale.Utils

def flipR [p : Param cov con α β] (r : p.R a b)
  : (p.flip.R b a) := by
    exact r

def flipR' [p : Param cov con α β] (r : p.flip.R a b)
  : (p.R b a) := by
    exact r


def normalizeR [p : Param cov con α β] (r : p.R a b)
  : p.toBottom.R a b := by
    exact r

def denormalizeR [p : Param cov con α β] (r : p.toBottom.R a b)
  : p.R a b := by
    exact r

theorem R_eq_normalize_R [p : Param cov con α β]
  : p.R = p.toBottom.R := by rfl


theorem flipFlipCancels [p : Param cov con α β] : p.flip.flip = p := by
  congr

macro "tr_flip" : tactic => `(tactic|
  first |apply Param.flip |apply flipR |apply flipR'
  )

syntax (name := subst_last) "subst_last" : tactic

-- BEGIN Source: Based on `subst` tactic (evalSubst)
-- Modified
open Lean Elab Tactic Meta Term

elab_rules : tactic
  | `(tactic| subst_last%$t) =>
    withMainContext do
      let lctx ← getLCtx
      let mvarId ← getMainGoal

      let hs := lctx.getFVarIds
      let hsSize := hs.size

      let fvarId ←
        if h: hsSize > 0 then
          pure hs[hsSize - 1]
        else
          throwTacticEx `subst_last mvarId "No last hypothesis"

      -- let fvarId ← match hs.toList with
      --   | [] => throwTacticEx `subst_last mvarId "No last hypothesis"
      --   | a::_ => pure a

      trace[debug] s!"Last hypothesis: {←fvarId.getUserName}"

      -- forEachVar (hs) fun mvarId fvarId => do
      let newMVarId ← do
        let decl ← fvarId.getDecl
        if decl.isLet then
          -- Zeta delta reduce the let and eliminate it.
          let (_, mvarId) ← mvarId.withReverted #[fvarId] fun mvarId' fvars => mvarId'.withContext do
            let tgt ← mvarId'.getType
            assert! tgt.isLet
            let mvarId'' ← mvarId'.replaceTargetDefEq (tgt.letBody!.instantiate1 tgt.letValue!)
            -- Dropped the let fvar
            let aliasing := (fvars.extract 1).map some
            return ((), aliasing, mvarId'')
          pure mvarId
        else
          Meta.subst mvarId fvarId

      replaceMainGoal [newMVarId]
  -- | _                     => throwUnsupportedSyntax
-- END Source



syntax (name := rename_last) "rename_last" (ppSpace colGt binderIdent)+ : tactic

-- BEGIN Source: Based on `rename_i` tactic (`renameInaccessibles`)
-- Modified
open Lean Elab Tactic Meta Term

def renameLast (mvarId : MVarId) (hs : TSyntaxArray ``binderIdent) : TacticM MVarId := do
  if hs.isEmpty then
    return mvarId
  else
    let mvarDecl ← mvarId.getDecl
    let mut lctx  := mvarDecl.lctx
    let mut hs    := hs
    let mut info  := #[]
    let mut found : NameSet := {}
    let n := lctx.numIndices
    -- hypotheses are inaccessible if their scopes are different from the caller's (we assume that
    -- the scopes are the same for all the hypotheses in `hs`, which is reasonable to expect in
    -- practice and otherwise the expected semantics of `rename_i` really are not clear)
    let some callerScopes := hs.findSome? (fun
        | `(binderIdent| $h:ident) => some <| extractMacroScopes h.getId
        | _ => none)
      | return mvarId
    for i in *...n do
      let j := n - i - 1
      match lctx.getAt? j with
      | none => pure ()
      | some localDecl =>
        if localDecl.isImplementationDetail then
          continue
        if let `(binderIdent| $h:ident) := hs.back! then
          let newName := h.getId
          lctx := lctx.setUserName localDecl.fvarId newName
          info := info.push (localDecl.fvarId, h)
        hs := hs.pop
        if hs.isEmpty then
          break
        found := found.insert localDecl.userName
    unless hs.isEmpty do
      logError m!"too many variable names provided"
    let mvarNew ← mkFreshExprMVarAt lctx mvarDecl.localInstances mvarDecl.type MetavarKind.syntheticOpaque mvarDecl.userName
    withSaveInfoContext <| mvarNew.mvarId!.withContext do
      for (fvarId, stx) in info do
        Term.addLocalVarInfo stx (mkFVar fvarId)
    mvarId.assign mvarNew
    return mvarNew.mvarId!

elab_rules : tactic
  | `(tactic| rename_last $hs*) =>
    do replaceMainGoal [← renameLast (← getMainGoal) hs]
-- END Source
