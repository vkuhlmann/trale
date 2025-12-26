import Mathlib

import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent

import Trale.Theories.Forall

import TraleTest.Lemmas.Modulo
open TraleTest.Lemmas Trale

def forallApplicationOrig
  {α α' : Sort _}
  {β : α -> Sort _}
  {β' : α' -> Sort _}
  (p1 : Param10 α α')
  (a : α)
  (a' : α')
  (aR : p1.R a a')
  (p2 : ∀ a a' (_ : p1.R a a'), Param10 (β a) (β' a'))
  :
  Param10 (β a) (β' a') :=
    by
    tr_constructor

    case R =>
      exact (p2 a a' aR).R

    case right =>
      exact (p2 a a' aR).right


instance ParamModFin2 : Param40 (Modulo (n + 1)) (Fin (n + 1)) := by
  tr_from_map

  intro a
  constructor

  case val =>
    exact a.repr

  case isLt =>
    simp [Modulo.repr]

    exact smallerThanMod _ _


theorem P1 : ∀ f : (a : Nat) → Fin (a+1),
             ∑ b ∈ {1, 2, 3}, (f b).val ≤ 6
  := by
  simp; omega

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
    -- unfold inferInstance at fR
    -- tr_simp_R at fR

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

    apply forallApplicationOrig

    case p1 =>
      infer_instance

    case aR =>
      /- If you don't know the type yet, you get to see
         `Param.R MapType.Map1 MapType.Map0 A B', where hovering over Param.R
         shows
         ```
         @Param.R
          (ℕ → ℕ) (ℕ → ℕ)
          MapType.Map1 MapType.Map0
          inferInstance A B : Prop
         ```

         You then recursively unfold the definition which is blocking. This
         could be
         ```
         simp [inferInstance, instParamMap1OfMap2b, instParamMap2bOfMap3,
               instParamMap3OfMap4, ...]
         ```

         I've now added simp to the instParamMap1OfMap2b etc which helps
         somewhat. Still, we should search for a more elegant option.
      -/
      simp [inferInstance, instParam]

      suffices B = A by
        tr_whnf
        rw [this]
        simp

      show B = A
      subst A B
      funext x

      show (f' x).repr = ↑(f x)

      -- We need some corresponde between f and f', but we have
      -- `fR : Param2a0 .Map2a .Map0 f' f`

      unfold inferInstance at fR
      unfold ParamModFin at fR
      -- unfold Param_forall.Map2a_forall at fR

      dsimp at fR
      specialize fR x x rfl
      dsimp at fR

      /-

      fR : (f' x).repr = ↑(f x)

      -/

      exact fR

    intro a a' aR

    show Param10 (F1 a) (F1 a')

    have aF := tr.R_implies_map a a' aR
    simp at aF

    /-

    aF : a = a'

    -/

    subst aF
    tr_ident
    rfl
