import Mathlib

import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent

import TraleTest.Lemmas.Modulo
open TraleTest.Lemmas Trale

theorem P1 : ∀ f : (a : Nat) → Fin (a+1),
             ∑ b ∈ {1, 2, 3}, (f b).val ≤ 6
  := by
  simp
  omega

theorem P1' : ∀ f : (a : Nat) → Modulo (a+1),
              ∑ b ∈ {1, 2, 3}, (f b).repr ≤ 6
  := by

  -- apply fun x => Param.right x P1
  -- apply fun x : Param10 _ _ => x.right P1

  tr_by P1


  /-

  ⊢ Param10
    (∀ (f : (a : ℕ) → Fin    (a + 1)), ∑ b ∈ {1, 2, 3}, ↑(f b)      ≤ 6)
    (∀ (f : (a : ℕ) → Modulo (a + 1)), ∑ b ∈ {1, 2, 3},  (f b).repr ≤ 6)

  -/
  tr_split

  /-
  case p1
  ⊢ Param02a
    ((a : ℕ) → Fin    (a + 1))
    ((a : ℕ) → Modulo (a + 1))

  case p2
  ⊢   (f  : (a : ℕ) → Fin    (a + 1))
    → (f' : (a : ℕ) → Modulo (a + 1))
    → (?p1).R f f'
    → Param10
      (∑ b ∈ {1, 2, 3}, ↑(f  b)      ≤ 6)
      (∑ b ∈ {1, 2, 3},  (f' b).repr ≤ 6)

  -/

  case p1 =>
    /-
        ⊢ Param02a ((a : ℕ) → Fin (a + 1)) ((a : ℕ) → Modulo (a + 1))
    -/
    tr_flip
    tr_split'

    case p1 =>
      /-
          ⊢ Param04 ℕ ℕ
      -/
      infer_instance

    case p2 =>
      intro a a' aR
      tr_simp_R at aR
      /-
          a a' : ℕ
          aR : a = a'    (:= p1.p1.R)
          ⊢ Param2a0 (Modulo (a + 1)) (Fin (a' + 1))
      -/

      rw [aR]
      infer_instance

  case p2 =>
    intro f f' fR
    tr_whnf at fR
    tr_simp_R at fR

    /-
      f  : (a : ℕ) → Fin    (a + 1)
      f' : (a : ℕ) → Modulo (a + 1)
      fR : ∀ (a a' : ℕ) (aR : a = a'), ParamModFin.R (f' a) (f a)
      ⊢ Param10
        (∑ a ∈ {1, 2, 3}, ↑(f a) ≤ 6)
        (∑ a ∈ {1, 2, 3}, (f' a).repr ≤ 6)
    -/

    let F1 := fun (x : Nat → Nat) => ∑ a ∈ {1, 2, 3}, x a ≤ 6

    let A : ℕ → ℕ := fun a => ↑(f a)
    let B : ℕ → ℕ := fun a => (f' a).repr
    show Param10 (F1 A) (F1 B)

    suffices F1 A = F1 B by
      rw [this]
      tr_ident

    congr
    funext a
    specialize fR a a rfl
    exact fR.symm


    /-
      f : (a : ℕ) → Fin (a + 1)
      f' : (a : ℕ) → Modulo (a + 1)
      fR : ∀ (a : ℕ), ParamModFin.R (f' a) (f a)
      F1 : (ℕ → ℕ) → Prop := fun x => ∑ a ∈ {1, 2, 3}, x a ≤ 6
      A : ℕ → ℕ := fun a => ↑(f a)
      B : ℕ → ℕ := fun a => (f' a).repr
      ⊢ Param10 (F1 A) (F1 B)
    -/
