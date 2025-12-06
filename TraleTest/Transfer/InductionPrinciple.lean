import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Theories.Sorts

open Trale.Utils

set_option trace.tr.utils true

variable (I : Type _) (I0 : I) (IS : I -> I)
variable (to_nat : I -> Nat) (of_nat : Nat -> I)

#check         Nat.strongRecOn
#check Nat.caseStrongRecOn
#check WellFounded.induction

def nat_rect2 : forall P : Nat -> Sort u, P 0 -> (forall n, P n -> P (n + 1)) -> forall n, P n := by
  intro P P0 Pstep
  intro n
  induction n with
  | zero =>
    exact P0
  | succ m Pm =>
    exact Pstep m Pm

def arrow_02a_rel
  {p1 p2}
  {f : α → β}
  {f' : α' → β'}
  (r2 : (Param_arrow.Map2a_arrow (p1 := p1) (p2 := p2)).flip.R f f')
  (r1 : p1.R a' a)
  :  (p2.flip.toBottom.R (f a) (f' a')) := by

  exact r2 _ _ r1

macro "tr_step_rel" : tactic => do
  let o1 ← `(tactic|apply flipR')
  let o2 ← `(tactic|rw [←Trale.param44_ident_symm])
  --
  let main ←  `(tactic|
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

macro "tr_advance" : tactic => `(tactic|
  (
  --   (run_tac
  --   -- This will produce the 'No goals to be solved' error if we are done.
  --   Lean.Elab.Tactic.getMainGoal
  -- );
  focus
    first
    | assumption
    | apply_assumption
    | tr_intro _ _ _
    | tr_flip; tr_intro _ _ _
    | tr_split
    | tr_flip; tr_split

    | (
        tr_split_application';
        -- case' p2 => intro _ _ _
        first
        | case p1 => infer_instance
          case' aR => tr_whnf
        | case' aR => tr_whnf
          case' p1 => skip -- Fix the ordering

        -- case' p1 => try infer_instance
        -- case' aR => tr_whnf
        -- case' p1 => skip -- Fix the ordering. But this causes error if p1 is
                            -- already closed.
        )
    | (
        tr_flip;
        tr_split_application';
        -- case' p2 => intro _ _ _
        first
        | case p1 => infer_instance
          case' aR => tr_whnf
        | case' aR => tr_whnf
          case' p1 => skip -- Fix the ordering
      )

    | (refine (Trale.instantiatePropR_bi ?_).forget;
       tr_step_rel)
    | fail "No step available"
    )
  )



set_option trace.debug true in
def I_Srec : forall P : I -> Sort 0, P I0 -> (forall i, P i -> P (IS i)) -> forall i, P i := by
  tr_by nat_rect2

  -- refine ?hello

  have RN : Param2a3.{0} I Nat := by sorry
  have RN0 : tr.R I0 0 := by sorry
  have RNS {m n} : tr.R m n → tr.R (IS m) (Nat.succ n) := by sorry

  repeat tr_advance


  -- -- tr_split_forall
  -- -- apply (Param_forall.Map4_forall _ _).forget



  -- -- tr_split_application'


  -- tr_advance

  -- -- tr_intro _ _ _


  -- -- tr_split'

  -- -- tr_flip
  -- -- tr_advance
  -- -- tr_split'

  -- -- apply (fun p1 p2 => Param_arrow.Map4_arrow (p1 := p1) (p2 := p2))




  -- -- apply (fun p1 p2 => Param_arrow.Map1_arrow (p1 := p1) (p2 := p2))
  -- -- apply (fun [p1 : Param01 _ _] p2 => Param_arrow.Map1_arrow (p1 := p1) (p2 := p2))
  -- -- apply @Param_arrow.Map1_arrow

  -- -- tr_split_application

  -- -- (first
  -- --   | assumption
  -- --   | apply_assumption
  -- --   | tr_intro _ _ _
  -- --   -- | tr_flip; tr_intro _ _ _
  -- --   -- | tr_split
  -- --   -- | tr_flip; tr_split

  -- --   -- | (
  -- --   --     tr_split_application';
  -- --   --     case' p2 => intro _ _ _
  -- --   --     first
  -- --   --     | case p1 => infer_instance
  -- --   --       case' aR => tr_whnf
  -- --   --     | case' aR => tr_whnf
  -- --   --       case' p1 => skip -- Fix the ordering

  -- --   --     -- case' p1 => try infer_instance
  -- --   --     -- case' aR => tr_whnf
  -- --   --     -- case' p1 => skip -- Fix the ordering. But this causes error if p1 is
  -- --   --                         -- already closed.
  -- --   --     )
  -- --   -- | (
  -- --   --     tr_flip;
  -- --   --     tr_split_application';
  -- --   --     case' p2 => intro _ _ _
  -- --   --     first
  -- --   --     | case p1 => infer_instance
  -- --   --       case' aR => tr_whnf
  -- --   --     | case' aR => tr_whnf
  -- --   --       case' p1 => skip -- Fix the ordering
  -- --   --   )

  -- --   -- | (refine (Trale.instantiatePropR_bi ?_).forget;
  -- --   --    tr_step_rel)
  -- --   -- | fail "No step available"
  -- --   )




  -- tr_advance

  -- -- focus
  -- --   tr_split_arrow

  -- --   case' p1 => skip

  -- --   tr_split

  -- --   apply Param_forall.Map1_forall
  -- --   rotate_left 1

  -- --   tr_advance

  -- tr_advance
  -- tr_advance
  -- focus
  --   tr_advance


  -- tr_advance
  -- tr_advance
  -- tr_advance
  -- tr_advance
  -- tr_advance


  -- -- ⊢ Param01 (a✝¹ 0) (a'✝ I0)
  -- tr_advance
  -- -- ⊢ Param02a (Nat → Prop) (I → Prop)
  -- tr_advance
  -- -- ⊢ RN.1 I0 0
  -- tr_advance
  -- -- ⊢ Param MapType.Map0 MapType.Map1 (a✝³ a✝¹) (a'✝¹ a'✝)
  -- -- done
  -- -- focus done


  -- -- tr_advance
  -- -- -- ⊢ Param.R MapType.Map0 MapType.Map2b a'✝ a✝¹
  -- -- -- tr_intro _ _ _

  -- -- -- tr_flip
  -- -- -- dbg_trace "test"
  -- -- -- focus
  -- -- -- tr_split
  -- -- -- intro _ _ _

  -- -- -- tr_intro _ _ _
  -- -- -- tr_flip
  -- -- -- tr_split
  -- -- tr_flip
  -- -- -- tr_split'

  -- -- tr_split'
  -- -- -- case p1 => sorry

  -- -- -- focus (tr_split; case' p1.p.p2 => intro _ _ _)
  -- -- focus (tr_split'; case' p2 => intro _ _ _)

  -- -- tr_intro _ _ _


  -- -- tr_advance




  -- tr_advance
  -- tr_advance
  -- -- tr_advance
  -- -- tr_advance
  -- -- tr_advance
  -- -- tr_advance
  -- -- tr_advance
  -- -- -- tr_advance
  -- -- -- tr_advance
  -- -- -- tr_advance
  -- -- -- tr_advance
