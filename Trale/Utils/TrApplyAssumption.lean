import Lean
import Trale.Core.Param

open Lean Elab Tactic Term Trale

namespace Trale.Utils

syntax (name := tr_apply_assumption) "tr_apply_assumption" : tactic

open Lean Elab Tactic Meta Term

macro "tr_apply_assumption" : tactic => `(tactic|
  focus (
      apply Param.forget
      case' p =>
        apply_assumption
      case h1 => decide
      case h2 => decide
  ))

-- example : P -> P ∨ Q := by
--   apply_assumption
--   sorry

-- elab_rules : tactic
--   | `(tactic| tr_apply_assumption%$t) =>
--     liftMetaTactic fun mvarId => do
--       let lctx ← getLCtx
--       let hs := lctx.getFVarIds
--       let hsSize := hs.size

--       if h : hsSize > 0 then
--         let maxIndex := hsSize - 1

--         for h2 : i in maxIndex...0 do
--           let h4 : i < hs.size := by
--             apply PPRange
--             let h5 := h2.upper

--             sorry

--           IO.println s!"{i-1}: {←hs[i].getUserName}"

--       let fvarId ←
--         if h: hsSize > 0 then
--           pure hs[hsSize - 1]
--         else
--           throwTacticEx `subst_last mvarId "No last hypothesis"

--       -- let fvarId ← match hs.toList with
--       --   | [] => throwTacticEx `subst_last mvarId "No last hypothesis"
--       --   | a::_ => pure a

--       trace[debug] s!"Last hypothesis: {←fvarId.getUserName}"

--       return ←mvarId.apply (.fvar fvarId)
