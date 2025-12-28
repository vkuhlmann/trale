import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import TraleTest.Lemmas.TrAdvance
import Trale.Theories.Sorts

open Trale.Utils Trale

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


set_option trace.debug true in
def I_Srec : ∀ P : I → Prop, P I0 → (∀ i, P i → P (IS i)) → ∀ i, P i := by
  tr_by nat_rect2

  -- refine ?hello

  have RN : Param2a3.{0} I Nat := by sorry
  have RN0 : tr.R I0 0 := by sorry
  have RNS {m n} : tr.R m n → tr.R (IS m) (Nat.succ n) := by sorry

  -- tr_solve
  tr_advance
  tr_advance

  tr_ident; (first|apply_assumption |(apply Eq.symm; apply_assumption))



  -- apply_assumption


  -- rename_last aR
  -- tr_whnf at aR
  -- specialize aR 0 I0 sorry
  -- tr_whnf at aR

  -- apply Eq.symm
  -- apply_assumption
  -- apply aR




  -- tr_apply_assumption


  apply_assumption


  tr_advance
  tr_advance

  tr_advance
  tr_ident; (first|apply_assumption |(apply Eq.symm; apply_assumption))
  assumption
  tr_flip
  rename_last x x' xR y y' yR

  -- tr_whnf at xR yR
  -- specialize xR sorry sorry sorry
  -- tr_whnf at xR
  tr_ident; (first|apply_assumption only [*] |(apply Eq.symm; apply_assumption only [*]))
  tr_advance
  tr_advance
  tr_advance

  rename_last x x' xR y y' yR
  tr_whnf at xR
  -- -- specialize xR y y' yR
  -- tr_whnf at xR

  tr_ident
  apply Eq.symm
  -- apply congrFun
  apply_assumption only [*]

  -- run_tac
  --   trace[debug] s!"{←Lean.Elab.Tactic.getMainTarget}"
  tr_advance
