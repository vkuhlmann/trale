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


instance [Param00 α β] [Param00 γ δ] : Param00 (α -> γ) (β -> δ) := by
  tr_split

macro "tr_advance" : tactic => `(tactic|
  first
  | assumption
  | tr_intro _ _ _
  | (tr_split_application; try (
        (case' p2 => intro _ _ _);rotate_left 1); tr_whnf)

  )



def I_Srec : forall P : I -> Sort 0, P I0 -> (forall i, P i -> P (IS i)) -> forall i, P i := by
  tr_by nat_rect2

  let _ : Param00 Prop Prop := propParam.forget

  have RN : Param2a3.{0} I Nat := by sorry
  -- have I0_maps_to_zero : RN.right I0 = 0 := by sorry

  have RN0 : tr.R I0 0 := by sorry
  -- have _ : Param01 (P 0) (P' I0) := by sorry
  have RNS m n : tr.R m n → tr.R (IS m) (Nat.succ n) := by sorry

  tr_split_application goal goal' goalR by
    intro h
    tr_by h
    clear h

    tr_intro P P' PR
    case p1 =>
      tr_flip
      tr_split -- Needs Param02b I Nat

    tr_split
    case p1 =>
      show Param01 (P 0) (P' I0)
      tr_flip

      -- rw [←I0_maps_to_zero]
      -- dsimp

      -- have h := tr.map_implies_R _ _ PR
      tr_split_application zero zero' zeroR by
        exact RN0

        -- show RN.R I0 (tr.map I0)
        -- show RN.R I0 (RN.right I0)
        -- tr_whnf

        -- refine' (RN.right_implies_R I0 (RN.right I0 : Nat) ?_) -- Needs Param2a0 I Nat
        -- dsimp

      have a := PR zero zero' zeroR
      tr_whnf at a
      -- a : P zero' = P' zero := a✝
      rw [a]
      tr_ident

    tr_split
    case p1 =>
      tr_flip

      tr_intro n n' nR -- needs Param02a I Nat

      tr_split

      case p1 =>
        show Param01 (P' n) (P n')
        have h1 := PR n n' nR
        tr_whnf at h1
        rw [h1]
        tr_ident


      have c := RNS n n' nR

      have h1 := PR _ _ c
      tr_whnf at h1

      /-
      h1 : P n'.succ = P' (IS n) := h1✝
      ⊢ Param10 (P' (IS n)) (P (n' + 1))
      -/

      rw [h1]
      tr_ident

    tr_intro n n' nR

    show Param10 (P n) (P' n')

    tr_ident
    exact PR _ _ nR

  let goalR := by assumption
  exact (instantiatePropR goalR).forget
