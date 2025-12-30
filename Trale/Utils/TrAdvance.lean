import Mathlib

import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Normalize
import Trale.Utils.Attr
import Trale.Utils.TrApplyAssumption

import Trale.Theories.Forall
import Trale.Theories.Sorts

namespace Trale.Utils

macro "tr_step_rel" : tactic => do
  let o1 ← `(tactic|apply flipR')
  let o2 ← `(tactic|rw [←Trale.param44_ident_symm])
  --
  let main ← `(tactic|
    (apply denormalizeR;
    --  (first| apply arrow_02a_rel);
     apply_assumption;
     run_tac
      trace[tr.utils] "Did arrow splitting"
     assumption
    )
  )
  --
  `(tactic|
    first
    | $main;
    | $o2; $main;
    | $o1; $main;
    | $o1; $o2; $main;
  )

set_option trace.tr.utils true

-- example : Param40 Nat String := by
--   show Param .Map4 .Map0 Nat String

--   sorry



-- macro "tr_refold" : tactic => `(tactic|
--   focus (
--     show Param _ _ _ _

--   )
--   )

macro "tr_advance_1" : tactic => `(tactic|
  focus first
    | rfl
    | trivial
    | assumption
    | infer_instance
    | (first
      | tr_intro _ _ _
      | tr_flip; tr_intro _ _ _
      | tr_split
      | tr_flip; tr_split); try subst_last
    | apply Trale.R_eq'
    | exact (Param44_ident'' rfl).forget
    | (intro x x' xR; rw [xR])
    | (intro x x' xR; rw [←xR])
    | exact congrArg _
    -- | (
    --     let : Param.R _ _ _ _ := by assumption;
    --     rw [this]
    --   )
    | apply_assumption only [*])

macro "tr_advance_2" : tactic => `(tactic|
  focus first
    | (refine (Trale.instantiatePropR_bi ?_).forget;
       tr_step_rel)
    | (refine (instantiatePropR ?_).forget; tr_step_rel)
    | (tr_flip; refine (instantiatePropR ?_).forget; tr_step_rel)
  )


macro "tr_advance" : tactic => `(tactic|
  (
  --   (run_tac
  --   -- This will produce the 'No goals to be solved' error if we are done.
  --   Lean.Elab.Tactic.getMainGoal
  -- );
  focus
    first
    | tr_advance_1
    | tr_ident; (first|apply_assumption only [*] |(apply Eq.symm; apply_assumption only [*]));
    | tr_apply_assumption
    -- | (
    --     tr_split_application';
    --     -- case' p2 => intro _ _ _
    --     first
    --     | case p1 => infer_instance
    --       case' aR => tr_whnf
    --     | case' aR => tr_whnf
    --       case' p1 => skip -- Fix the ordering

    --     -- case' p1 => try infer_instance
    --     -- case' aR => tr_whnf
    --     -- case' p1 => skip -- Fix the ordering. But this causes error if p1 is
    --                         -- already closed.
    --     )
    -- | (
    --     tr_flip;
    --     tr_split_application';
    --     -- case' p2 => intro _ _ _
    --     first
    --     | case p1 => infer_instance
    --       case' aR => tr_whnf -- The tr_whnf will a.o. remove the inferInstance
    --     | case' aR => tr_whnf
    --       case' p1 => skip -- Fix the ordering
    --   )
    -- | tr_advance_2
    | fail "No step available"
    )
  )

#check Trale.instantiatePropR_bi
#check instantiatePropR
#check flipR'
#check Trale.param44_ident_symm


add_aesop_rules 90% (by assumption) (rule_sets := [trale])
add_aesop_rules 50% (by apply_assumption) (rule_sets := [trale])
-- add_aesop_rules 90% apply Trale.R_eq' (rule_sets := [trale])
add_aesop_rules 90% (by apply Trale.R_eq') (rule_sets := [trale])
add_aesop_rules 80% (by tr_intro _ _ _) (rule_sets := [trale])
-- add_aesop_rules 50% (by (
--         let : Param.R _ _ _ _ := by assumption;
--         rw [this]
--       )) (rule_sets := [trale])
-- -- add_aesop_rules 40% (by tr_advance) (rule_sets := [trale])
-- add_aesop_rules 40% (by tr_advance_1) (rule_sets := [trale])
add_aesop_rules 70% (by tr_ident; (first|apply_assumption only [*] |(apply Eq.symm; apply_assumption only [*]))) (rule_sets := [trale])
add_aesop_rules 80% (by tr_apply_assumption)
-- add_aesop_rules 40% (by tr_advance_1) (rule_sets := [trale])
add_aesop_rules 30% (by tr_advance_2) (rule_sets := [trale])
