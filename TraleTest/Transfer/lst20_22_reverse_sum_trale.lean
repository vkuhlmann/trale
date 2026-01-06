import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Attr
import Trale.Theories.Sorts
import TraleTest.Lemmas.Modulo
import TraleTest.Lemmas.Zmod5
import Trale.Utils.TrAdvance
import TraleTest.Research.translation_inspect

open TraleTest.Lemmas Trale

open Trale.Utils

theorem sum_eq_reverse_sum_Nat (a b c : Nat)
    : (a + b) + c = (c + b) + a := by
  omega


/-
# Listing 20a
-/
theorem sum_eq_reverse_sum_Zmod5_manual3 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  refine Param.right' ?_ sum_eq_reverse_sum_Nat

  apply Trale.Map1_forall; intro a a' aR
  case p1 => exact ModParam.flip.forget

  apply Trale.Map1_forall; intro b b' bR
  case p1 => exact ModParam.flip.forget

  apply Trale.Map1_forall; intro c c' cR
  case p1 => exact ModParam.flip.forget

  apply (R_eq _ _ _ _ _ _).forget

  · apply R_add_Zmod5
    · apply R_add_Zmod5
      · exact aR
      · exact bR
    · exact cR

  · apply R_add_Zmod5
    · apply R_add_Zmod5
      · exact cR
      · exact bR
    · exact aR


/-
# Listing 20c
-/
theorem sum_eq_reverse_sum_Zmod5_manual5 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  refine Param.right' ?_ sum_eq_reverse_sum_Nat

  repeat first
    | apply Trale.Map1_forall
      case' p2 => intro _ _ _
      case p1 => infer_instance
    | apply (R_eq _ _ _ _ _ _).forget
    | apply R_add_Zmod5
    | assumption


/-
# Listing 22a
-/
theorem sum_eq_reverse_sum_Zmod5'' (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_Nat

  repeat first
    | apply R_add_Zmod5
    | apply (R_eq _ _ _ _ _ _).forget
    | tr_advance


/-
# Listing 22b
-/
theorem sum_eq_reverse_sum_Zmod5 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_Nat

  change Param10.{0} _ _
  tr_solve


/-
# Listing 22c
-/

theorem sum_eq_reverse_sum_Zmod5''' (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_exact sum_eq_reverse_sum_Nat



/-
# Other
-/

theorem sum_eq_reverse_sum_Zmod5' (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_Nat

  repeat first
    | assumption
    | apply R_add_Zmod5
    | tr_intro _ _ _
    | apply (R_eq _ _ _ _ _ _).forget


theorem sum_eq_reverse_sum_Zmod5_manual (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_Nat

  let _ : Param00 Prop Prop := propParam.forget

  tr_intro a a' aR
  tr_intro b b' bR
  tr_intro c c' cR

  apply (R_eq _ _ _ _ _ _).forget
  apply R_add_Zmod5
  apply R_add_Zmod5
  tr_advance; tr_advance; tr_advance

  apply R_add_Zmod5
  apply R_add_Zmod5
  tr_advance; tr_advance; tr_advance


theorem sum_eq_reverse_sum_Zmod5_manual2 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_Nat

  let _ : Param00 Prop Prop := propParam.forget

  tr_advance
  tr_advance
  tr_advance
  apply (R_eq _ _ _ _ _ _).forget
  apply R_add_Zmod5
  apply R_add_Zmod5
  tr_advance
  tr_advance
  tr_advance


  -- tr_advance
  apply R_add_Zmod5
  apply R_add_Zmod5
  tr_advance
  tr_advance
  tr_advance

  -- tr_advance
  -- exact R_eq

  -- refine (instantiatePropR ?_).forget
  -- exact aR _ _ (by assumption) _ _ (by assumption)

theorem sum_eq_reverse_sum_Zmod5_manual4 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  refine Param.right' ?_ sum_eq_reverse_sum_Nat

  apply Trale.Map1_forall; intro _ _ _
  case p1 => infer_instance

  apply Trale.Map1_forall; intro _ _ _
  case p1 => infer_instance

  apply Trale.Map1_forall; intro _ _ _
  case p1 => infer_instance

  apply (R_eq _ _ _ _ _ _).forget

  · apply R_add_Zmod5
    · apply R_add_Zmod5
      · assumption
      · assumption
    · assumption

  · apply R_add_Zmod5
    · apply R_add_Zmod5
      · assumption
      · assumption
    · assumption


-- #check inferInstanceAs (AddSemigroup (Modulo 5))


-------------------------------------------------------
