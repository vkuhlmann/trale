import Mathlib
import Trale.Core.Param
import Trale.Utils.Constructor
import Trale.Utils.Split
-- import Mathlib.Data.Finset.Sum

-- example : (4 : Nat) = (4 : Int) := by simp
-- example : (4.3 : ℚ) = (4.3 : ℝ) := by simp

#eval (5 : ℕ) - 7
#eval (5 : ℤ) - 7

namespace TraleTest.Lemmas

structure Modulo (n : Nat) where
  base : Nat

def Modulo.repr (a : Modulo n) : Nat := a.base % n

instance : Add (Modulo n) where
  add a b := ⟨a.base + b.base⟩

lemma smallerThanModCore : ∀ m n, Nat.modCore n (m+1) < (m+1) := by
  intro m n
  unfold Nat.modCore
  simp

  suffices ∀ fuel : Nat, (hfuel : fuel > n) -> Nat.modCore.go (m + 1) _ fuel n hfuel < m + 1 by
    apply this (n+1)

  induction n using Nat.strong_induction_on with
  | h u h1 =>
    intro fuel hfuel

    unfold Nat.modCore.go
    split; tauto

    case _ =>
      split
      case isFalse h2 =>
        simp at h2
        assumption

      case isTrue h2 =>
        apply h1
        omega


lemma smallerThanMod : ∀ m n, n % (m+1) < (m + 1) := by
  intro m n

  unfold HMod.hMod
  unfold instHMod
  unfold Mod.mod
  unfold Nat.instMod
  unfold Nat.mod

  simp

  split
  case _ =>
    simp
  case _ m =>
    split
    case isFalse h =>
      omega
    case isTrue =>
      exact smallerThanModCore _ _


instance ParamModFin : Param2a0 (Modulo (n + 1)) (Fin (n + 1)) := by
  tr_constructor

  case R =>
    intro a a'
    exact a.repr = a'.val

  case right =>
    intro a
    constructor

    case val =>
      exact a.repr

    case isLt =>
      simp [Modulo.repr]

      exact smallerThanMod _ _

  case right_implies_R =>
    intro a a' m
    rw [← m]
