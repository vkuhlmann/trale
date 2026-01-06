import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Lean.PrettyPrinter

import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Basic
import Trale.Utils.Normalize
import Trale.Utils.AddFlipped
import Trale.Theories.Flip
import Trale.Theories.Arrow
import Trale.Theories.Sorts

import Qq open Qq Lean

namespace Trale open Utils

/-!
# Parametricity for Dependent Function Types (Forall)

This module defines parametric relations for dependent function types `∀ a : α, β a`.
This is similar to Arrow but handles dependent types where the codomain depends
on the input.

## The Forall Relation

Given:
- A relation `R₁ : α → α' → Sort _` on the domain
- A family of relations `R₂ : ∀ a a', R₁ a a' → Param00 (β a) (β' a')` on codomains

We define when two dependent functions are related:
```
forallR R₁ R₂ f f' := ∀ a a' (aR : R₁ a a'), R₂ a a' aR (f a) (f' a')
```

This is the dependent version of the arrow relation.

## Map Instances

We provide Param instances for transferring dependent function types.
The constructions are similar to Arrow but must carefully handle the dependency.
-/

universe u u' v v' x w1 w2 w3

variable {α : Sort u} {α' : Sort u'} {β : α -> Sort v} {β' : α' -> Sort v'}


/-- The parametricity relation for dependent function types.
    Two dependent functions are related if they map related inputs to related outputs,
    where the output relation depends on the proof that the inputs are related. -/
def forallR
  (p1 : Param00 α α')
  (p2 : ∀ a a', p1.R a a' → Param00 (β a) (β' a'))
  : (∀ a, β a) → (∀ a', β' a') → Sort _
  := fun f f' =>
    forall a a' (aR: p1.R a a'), (p2 a a' aR).R (f a) (f' a')

/-- Flipping the forall relation. -/
def flipForallR
  (r : forallR p1 p2 f f')
  : forallR p1.flip (fun a a' aR => (p2 a' a aR).flip) f' f
  := fun a' a aR' => (r a a' (flipR aR'))

/-- The forall relation respects flipping as a Param44 equivalence. -/
instance forallR_rel
  -- The order of α', α, β', β needs to be specified for
  -- tr_add_flipped to produce the correct flipped definition.
  {α' : Sort u'} {α : Sort u}
  {β' : α' → Sort v'} {β : α → Sort v}
  (p1 : Param00 α α')
  (p2 : ∀ a a', p1.R a a' → Param00 (β a) (β' a'))
  {f f'}
  : Param44.{0} (forallR p1.flip (fun a a' aR => (p2 a' a aR).flip) f' f)
    (forallR p1 p2 f f') := by

  tr_from_involution flipForallR



/-- Base Param instance for dependent function types: just the relation. -/
def Map0_forall
  (p1 : Param00 α α')
  (p2 : ∀ (a : α) (a' : α'), p1.R a a' → Param00 (β a) (β' a'))
  : Param00 (∀ a, β a) (∀ a', β' a') := by

  tr_constructor

  exact forallR p1 p2


/-- Dependent function map.
    Maps `f : ∀ a, β a` to a function that:
    1. Takes input `x' : α'`
    2. Computes `x = p1.left x' : α`
    3. Applies `f x : β x`
    4. Maps to `β' x'` using `p2 x x'`
    
    Requires contravariant structure on α to go from α' to α. -/
def Map1_forall
  (p1 : Param02a α α')
  (p2 : ∀ (a : α) (a' : α'), p1.R a a' → Param10 (β a) (β' a'))
  : Param10 (∀ a, β a) (∀ a', β' a') := by

  tr_extend Map0_forall p1 (p2 . . .)

  intro f x'
  let x := p1.left x'
  let f' := (p2 x x' (p1.left_implies_R _ _ rfl)).right
  exact f' (f x)

/-- Alternative formulation using arrow relation for the dependent part. -/
def Map1_forall'
  {α α' : Sort u}
  {β : α → Sort v}
  {β' : α' → Sort v}
  (p1 : Param02a α α')
  (p2 : arrowR p1 (sortParam .Map1 .Map0).forget β β')
  := Map1_forall p1 p2


def Map2a_forall
  (p1 : Param04 α α')
  (p2 : forall (a : α) (a' : α'), p1.R a a' -> Param2a0 (β a) (β' a'))
  : Param2a0 (∀ a, β a) (∀ a', β' a')
  := by

  tr_extend Map1_forall p1 (p2 . . .)

  intro f f' fF
  intro a a' aR
  apply (p2 a a' aR).right_implies_R
  subst fF

  have := p1.R_implies_left a a' aR
  subst this
  congr

  repeat exact (p1.R_implies_leftK _ _ _).symm

def Map2a_forall_flipped
  {α : Sort u} {α' : Sort u'}
  {β : α → Sort v}
  {β' : α' → Sort v'}
  (p1 : Param40 α α')
  (p2 : forall (a : α) (a' : α'), p1.R a a' → Param02a (β a) (β' a'))
  : Param02a (∀ a, β a) (∀ a', β' a')
  -- :=
  -- flip2a (Map2a_forall p1.flip (fun a a' aR => (p2 a' a aR).flip))
  -- -- flip2a (Map2a_forall p1 p2)
  -- -- ((forallR_rel p1 p2))
  -- ((forallR_rel p1 p2).flip.forget (h1 := map4top) (h2 := map4top))

  := by
    let x := forallR p1.toBottom.flip (fun a a' aR => (p2 a' a aR).toBottom.flip)
    let y := forallR p1.toBottom (fun a a' aR => (p2 a a' aR).toBottom)

    apply flip2a (Map2a_forall p1.flip (fun a a' aR => (p2 a' a aR).flip))

    intro f f'
    dsimp [Map2a_forall]

    change Param10
      (forallR p1.toBottom.flip (fun a a' aR => (p2 a' a aR).toBottom.flip) f' f)
      _

    let h : Param44 (x f' f) (y f f') := (forallR_rel p1.toBottom (fun a a' aR => (p2 a a' aR).toBottom) (f' := f') (f := f))
    change Param10.{_,0,_} (x f' f) (y f f')

    exact h.forget


def Map2b_forall
  (p1 : Param02a α α')
  (p2 : forall (a : α) (a' : α'), p1.R a a' -> Param2b0 (β a) (β' a'))
  : Param2b0 (∀ a, β a) (∀ a', β' a')
  := by

  tr_extend Map1_forall p1 (p2 . . .)

  intro f f'
  intro R

  funext a'
  let a : α := p1.left a'
  let aR := p1.left_implies_R a a' rfl

  exact (p2 a a' aR).R_implies_right (f a) (f' a') (R a a' aR)


def Map3_forall
  (p1 : Param04 α α')
  (p2 : forall (a : α) (a' : α'), p1.R a a' → Param30 (β a) (β' a'))
  : Param30 (∀ a, β a) (∀ a', β' a')
  := by
  tr_extend_multiple [Map2a_forall p1 (p2 . . .), Map2b_forall p1 (p2 . . .)]


def Map4_forall
  (p1 : Param04 α α')
  (p2 : forall (a : α) (a' : α'), p1.R a a' → Param40 (β a) (β' a'))
  : Param40 (∀ a, β a) (∀ a', β' a')
  := by

  tr_extend Map3_forall p1 (p2 . . .)
  intro f f' fr
  funext a a' aR
  simp

  let Param_b := p2 a a' aR

  let b_mapK := Param_b.covariant.R_in_mapK (f a) (f' a') (fr a a' aR)
  apply Eq.symm
  apply Eq.trans b_mapK.symm

  rfl
