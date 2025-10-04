import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Theories.Sorts

set_option trace.tr.utils true

variable (I : Type _) (I0 : I) (IS : I -> I)
variable (to_nat : I -> Nat) (of_nat : Nat -> I)

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
  (r2 : (Param_arrow.Map2a_arrow p1 p2).flip.R f f')
  (r1 : p1.R a' a)
  :  (p2.flip.toBottom.R (f a) (f' a')) := by

  exact r2 _ _ r1

macro "tr_step_rel" : tactic => do
  let o1 ← `(tactic|apply flipR')
  let o2 ← `(tactic|rw [←Param_ident.param44_ident_symm])
  --
  let main ←  `(tactic|
    (apply denormalizeR;
     (first| apply arrow_02a_rel);
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
  first
  | assumption
  | apply_assumption
  | tr_intro _ _ _
  | tr_flip; tr_intro _ _ _
  | tr_split
  | tr_flip; tr_split

    | (
        tr_split_application';
        case' p2 => intro _ _ _
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
        case' p2 => intro _ _ _
        first
        | case p1 => infer_instance
          case' aR => tr_whnf
        | case' aR => tr_whnf
          case' p1 => skip -- Fix the ordering
      )

  | (refine (Param_ident.instantiatePropR_bi ?_).forget;
     tr_step_rel)
  | fail "No step available"
  )



def I_Srec : forall P : I -> Sort 0, P I0 -> (forall i, P i -> P (IS i)) -> forall i, P i := by
  tr_by nat_rect2

  have RN : Param2a3.{0} I Nat := by sorry
  have RN0 : tr.R I0 0 := by sorry
  have RNS {m n} : tr.R m n → tr.R (IS m) (Nat.succ n) := by sorry

  let pAux1 : Param02a (Nat → Prop) (I → Prop) := by
    tr_advance

  tr_advance
  tr_advance
  ·
    tr_advance
    tr_advance
    tr_advance
    tr_advance

  tr_advance
  ·
    tr_advance
    tr_advance

    tr_advance
    tr_advance

    tr_advance
    tr_advance
    tr_advance

    tr_advance
    tr_advance

  tr_advance
  tr_advance
  tr_advance
