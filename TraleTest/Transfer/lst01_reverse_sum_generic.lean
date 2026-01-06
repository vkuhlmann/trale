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

namespace Approach1

/-
# Listing 1a
-/

-- Proof on the naturals.
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

/-
# Listing 1b
-/
-------------------------------------------------------
namespace Approach2

-- Generic proof
-- [AddCommSemiGroup G] = [AddCommMagma G] + [AddSemigroup G]
theorem sum_eq_reverse_sum {G : Type*} [AddCommSemigroup G] (a b c : G)
    : (a + b) + c = (c + b) + a := by

  rw [AddCommMagma.add_comm _ c]
  rw [AddCommMagma.add_comm a b]

  -- show c + (b + a) = (c + b) + a
  simp [AddSemigroup.add_assoc]

-- Proof on the naturals.
theorem sum_eq_reverse_sum_Nat (a b c : Nat)
    : (a + b) + c = (c + b) + a :=
  sum_eq_reverse_sum a b c


-- Proof on Zmod5.
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


/-
# Other
-/

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
