import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Theories.Sorts
import TraleTest.Lemmas.Modulo
import TraleTest.Lemmas.Zmod5
import TraleTest.Lemmas.TrAdvance

open TraleTest.Lemmas
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

instance p : Param42a Nat Zmod5 :=
  by tr_from_map repr5K

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


def sum_preserves_Zmod5
  (aR : p.R a a')
  (bR : p.R b b')
  : (p.R (a + b) (a' + b')) := by

  tr_whnf
  subst aR bR

  show (⟨(a + b) % 5, _⟩ : Zmod5) = Fin.add (⟨a % 5, mod5_le5⟩ : Fin 5) (⟨b % 5, mod5_le5⟩ : Fin 5)
  unfold Fin.add
  simp

#check Nat.add


theorem sum_eq_reverse_sum_Zmod5 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_Nat

  let _ : Param00 Prop Prop := propParam.forget

  repeat first
    | assumption
    | apply sum_preserves_Zmod5
    | tr_advance

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
  apply sum_preserves_Zmod5
  apply sum_preserves_Zmod5
  tr_advance; tr_advance; tr_advance

  tr_advance
  apply sum_preserves_Zmod5
  apply sum_preserves_Zmod5
  tr_advance; tr_advance; tr_advance



  tr_advance

  intro lhs lhs' lhsR
  intro rhs rhs' rhsR

  subst lhsR
  subst rhsR

  tr_whnf
  intro this
  subst this
  rfl
  -- exact congrArg _


  refine (instantiatePropR ?_).forget
  apply denormalizeR
  tr_whnf
  tr_whnf at aR
  apply_assumption
  assumption
  assumption


theorem sum_eq_reverse_sum_Zmod5_manual2 (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_Nat

  let _ : Param00 Prop Prop := propParam.forget

  tr_advance
  tr_advance
  tr_advance
  tr_advance
  apply sum_preserves_Zmod5
  apply sum_preserves_Zmod5
  tr_advance
  tr_advance
  tr_advance


  tr_advance
  apply sum_preserves_Zmod5
  apply sum_preserves_Zmod5
  tr_advance
  tr_advance
  tr_advance

  tr_advance
  exact R_eq
  tr_advance
  assumption

end Approach3


-- #check inferInstanceAs (AddSemigroup (Modulo 5))


-------------------------------------------------------
