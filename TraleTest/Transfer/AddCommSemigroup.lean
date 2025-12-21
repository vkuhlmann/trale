import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Utils.Attr
import Trale.Theories.Sorts
import TraleTest.Lemmas.Modulo
import TraleTest.Lemmas.Zmod5
import TraleTest.Lemmas.TrAdvance

open TraleTest.Lemmas Trale
-- set_option trace.tr.utils true

-------------------------------------------------------
namespace Approach0

theorem sum_eq_reverse_sum_Nat (a b c : Nat)
    : (a + b) + c = (c + b) + a := by
  omega

theorem sum_eq_reverse_sum_Modulo (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by
  -- Error: omega could not prove the goal: No usable constraints found
  -- omega
  sorry

end Approach0
-------------------------------------------------------



-------------------------------------------------------
namespace Approach1

theorem sum_eq_reverse_sum_Nat (a b c : Nat)
    : (a + b) + c = (c + b) + a := by

  rw [Nat.add_comm _ c]
  rw [Nat.add_comm a b]

  -- show c + (b + a) = (c + b) + a
  simp [Nat.add_assoc]


lemma Zmod5.add_comm (a b : Zmod5)
  : a + b = b + a := by
  show (⟨_ , _⟩ : Zmod5) = ⟨_, _⟩; simp
  show (↑a + ↑b : Nat) % 5 = (↑b + ↑a) % 5
  rw [Nat.add_comm]

lemma Zmod5.add_assoc (a b : Zmod5)
  : a + b + c = a + (b + c) := by
  show (⟨_, _⟩ : Zmod5) = ⟨_, _⟩; simp
  rw [Nat.add_assoc]

theorem sum_eq_reverse_sum_Zmod5 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by
  rw [Zmod5.add_comm _ c]
  rw [Zmod5.add_comm a b]

  -- show c + (b + a) = (c + b) + a
  simp [Zmod5.add_assoc]

end Approach1
-------------------------------------------------------






-------------------------------------------------------
namespace Approach2

  -- [AddCommSemiGroup G] = [AddCommMagma G] + [AddSemigroup G]
  theorem sum_eq_reverse_sum {G : Type*} [AddCommSemigroup G] (a b c : G)
      : (a + b) + c = (c + b) + a := by

    rw [AddCommMagma.add_comm _ c]
    rw [AddCommMagma.add_comm a b]

    -- show c + (b + a) = (c + b) + a
    simp [AddSemigroup.add_assoc]

  theorem sum_eq_reverse_sum_Nat (a b c : Nat)
      : (a + b) + c = (c + b) + a :=
    sum_eq_reverse_sum a b c


  scoped instance : AddCommMagma Zmod5 where
    add_comm a b := by
      show (⟨_ , _⟩ : Zmod5) = ⟨_, _⟩
      simp
      show (↑a + ↑b : Nat) % 5 = (↑b + ↑a) % 5
      rw [Nat.add_comm]

  scoped instance : AddSemigroup Zmod5 where
    add_assoc a b c := by
      show (⟨_, _⟩ : Zmod5) = ⟨_, _⟩
      simp
      rw [Nat.add_assoc]

  scoped instance : AddCommSemigroup Zmod5 := {}


  theorem sum_eq_reverse_sum_Zmod5 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a :=
    sum_eq_reverse_sum a b c

end Approach2
-------------------------------------------------------


namespace Approach3

open Trale.Utils

instance p : Param2b2a Nat Zmod5 :=
  ModParam
  -- (by tr_from_map repr5K : Param42a Nat Zmod5).forget

theorem sum_eq_reverse_sum_Nat (a b c : Nat)
    : (a + b) + c = (c + b) + a := by
  omega

-- def sum_preserves_Zmod5
--   (a b : Nat)
--   (a' b' : Zmod5)
--   (aR : tr.R a a')
--   (bR : tr.R b b')
--   : (tr.R (a + b) (a' + b')) := by

--   tr_whnf
--   subst aR bR

--   show (⟨(a + b) % 5, _⟩ : Zmod5) = Fin.add (⟨a % 5, mod5_le5⟩ : Fin 5) (⟨b % 5, mod5_le5⟩ : Fin 5)
--   unfold Fin.add
--   simp


#check Nat.add

theorem sum_eq_reverse_sum_Zmod5 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_Nat

  change Param10.{0} _ _

  -- aesop (rule_sets := [trale])
  tr_solve


theorem sum_eq_reverse_sum_Zmod5' (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_Nat

  repeat first
    | assumption
    | apply R_add_Zmod5
    | tr_intro _ _ _
    | apply R_eq'


theorem sum_eq_reverse_sum_Zmod5'' (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_Nat

  repeat first
    | apply R_add_Zmod5
    | tr_advance



theorem sum_eq_reverse_sum_Zmod5''' (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_exact sum_eq_reverse_sum_Nat


#check Eq

theorem sum_eq_reverse_sum_Zmod5_manual (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_Nat

  let _ : Param00 Prop Prop := propParam.forget

  tr_intro a a' aR
  tr_intro b b' bR
  tr_intro c c' cR

  tr_advance
  apply R_add_Zmod5
  apply R_add_Zmod5
  tr_advance; tr_advance; tr_advance

  -- tr_advance
  apply R_add_Zmod5
  apply R_add_Zmod5
  tr_advance; tr_advance; tr_advance



  -- tr_advance

  -- intro lhs lhs' lhsR
  -- intro rhs rhs' rhsR

  -- subst lhsR
  -- subst rhsR

  -- tr_whnf
  -- intro this
  -- subst this
  -- rfl
  -- -- exact congrArg _


  -- refine (instantiatePropR ?_).forget
  -- -- apply denormalizeR
  -- tr_whnf
  -- tr_whnf at aR
  -- apply_assumption
  -- assumption
  -- assumption


theorem sum_eq_reverse_sum_Zmod5_manual2 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_Nat

  let _ : Param00 Prop Prop := propParam.forget

  tr_advance
  tr_advance
  tr_advance
  tr_advance
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

theorem sum_eq_reverse_sum_Zmod5_manual3 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  refine Param.right' ?_ sum_eq_reverse_sum_Nat

  apply Trale.Map1_forall; intro a a' aR
  case p1 => exact ModParam.forget

  apply Trale.Map1_forall; intro b b' bR
  case p1 => exact ModParam.forget

  apply Trale.Map1_forall; intro c c' cR
  case p1 => exact ModParam.forget

  apply R_eq'

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

  apply R_eq'

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


theorem sum_eq_reverse_sum_Zmod5_manual5 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  refine Param.right' ?_ sum_eq_reverse_sum_Nat

  repeat first
    | apply Trale.Map1_forall
      case' p2 => intro _ _ _
      case p1 => infer_instance
    | apply R_eq'
    | apply R_add_Zmod5
    | assumption

end Approach3


-- #check inferInstanceAs (AddSemigroup (Modulo 5))


-------------------------------------------------------
