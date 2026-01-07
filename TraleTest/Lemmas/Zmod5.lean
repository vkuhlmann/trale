import Mathlib
import Trale.Utils.Constructor
import Trale.Utils.Split
import Trale.Utils.Attr
import Trale.Utils.TrAdvance

namespace TraleTest.Lemmas
open Trale

lemma fin5_mod5 (a : Fin 5) : a.val % 5 = a.val := by
  simp

lemma mod5_le5 : n % 5 < 5 := by
  apply Nat.mod_lt
  simp

abbrev Zmod5 := Fin 5

def mod5 (n : Nat) : Zmod5 := ⟨n % 5, mod5_le5⟩
def repr5 (a : Zmod5) : Nat := a

instance : Add Zmod5 where
  add := Fin.add

lemma lt_mod_eq
  (h : a < 5)
 : (a % 5 = a) := by
  simp
  assumption

lemma repr5K : ∀ (a' : Zmod5), mod5 (repr5 a') = a' := by
  intro a
  dsimp [repr5, mod5]
  congr
  apply lt_mod_eq
  simp

instance ModParam : Param2a4 Zmod5 Nat := by tr_from_map repr5K

@[trale]
def R_add_Zmod5
  (a b : Zmod5) (a' b' : Nat)
  (aR : tr.R a a')
  (bR : tr.R b b')
  : (tr.R (a + b) (a' + b')) := by

  tr_whnf
  subst aR bR

  change (⟨(a' + b') % 5, _⟩ : Zmod5) = Fin.add (⟨a' % 5, mod5_le5⟩ : Fin 5) (⟨b' % 5, mod5_le5⟩ : Fin 5)
  unfold Fin.add
  simp only [Nat.add_mod_mod, Nat.mod_add_mod]

@[trale]
def R_mul_Zmod5
  (a b : Zmod5) (a' b' : Nat)
  (aR : tr.R a a')
  (bR : tr.R b b')
  : (tr.R (a * b) (a' * b')) := by

  tr_whnf
  subst aR bR

  change (⟨(a' * b') % 5, _⟩ : Zmod5) = Fin.mul (⟨a' % 5, mod5_le5⟩ : Fin 5) (⟨b' % 5, mod5_le5⟩ : Fin 5)
  unfold Fin.mul
  simp only [Nat.mul_mod_mod, Nat.mod_mul_mod]

instance zmod5OfNat : OfNat Zmod5 x := Fin.instOfNat


@[trale]
def R_ofNat_Fin
  (n : Nat)
  : tr.R (zmod5OfNat (x := n)) (instOfNatNat (n := n)) := by rfl

-- @[trale]
-- def R_ofNat_Zmod5
--   {n : Nat}
--   -- (x : Zmod5)
--   -- (x' : Nat)
--   -- (xR : tr.R x x')
--   : tr.R (@OfNat.ofNat Zmod5 n Fin.instOfNat) (@OfNat.ofNat Nat n (instOfNatNat _))
--   := by rfl
