import Trale.Core.Param
import Trale.Utils.Constructor
import Trale.Utils.ParamIdent

namespace Trale.Utils

/-!
# Constructing Params from Functions

This module provides utilities for constructing Param instances from functions
and their properties. These are convenient helpers for the most common cases.

## Key Functions

- `Param_id`: Identity Param (full equivalence on same type)
- `paramFromMap`: Param40 from any function (graph relation)
- `paramFromSurjection`: Param42a from a split surjection
- `paramFromInjection`: Param42b from a split injection

These are commonly used as building blocks when setting up parametricity for
custom types.
-/

/-- Identity Param: relates a type to itself via equality.
    This is a Param44 (full equivalence). -/
def Param_id : Param44 α α := Param44_ident

/-- Identity Param with a type equality proof.
    Useful when types are definitionally equal but not syntactically the same. -/
def Param_id' {α α' : Sort u} (h : α = α') : Param44 α α' := by
  rw [h]
  exact Param_id

/-- Construct a Param40 from any function.
    The relation is the graph: `R a b := f a = b`.
    This gives full covariant structure with f as the map. -/
@[simp]
def paramFromMap
  (f : α → α')
: Param40 α α' := by
  tr_constructor

  -- R
  exact (f . = .) -- R

  -- 4
  exact f
  repeat simp

/-- Construct a Param42a from a split surjection.
    Given `sect : α → α'` and `retract : α' → α` with `retract ∘ sect = id`,
    we get:
    - In the covariant direction: Map4 structure using `retract`
    - In the contravariant direction: Map2a structure using `sect`
    
    This corresponds to a split surjection from α' onto α (retract is surjective
    with section sect), or equivalently, a split injection from α into α' in the
    contravariant direction. -/
def paramFromSurjection
  {sect : α → α'} {retract : α' → α}
  (sectK : ∀ a, retract (sect a) = a)
  : Param42a α' α := by
  tr_extend paramFromMap retract

  -- 2a
  · exact sect
  · intro _ _  aF; subst aF
    exact sectK _

/-- Construct a Param42b from a split injection.
    Given `sect : α → α'` and `retract : α' → α` with `retract ∘ sect = id`,
    we get:
    - In the covariant direction: Map4 structure using `sect`
    - In the contravariant direction: Map2b structure using `retract`
    
    This corresponds to a split injection from α into α' (sect is injective
    with retraction retract), or equivalently, a split surjection from α' onto α
    in the contravariant direction. -/
def paramFromInjection
  {sect : α → α'} {retract : α' → α}
  (sectK : ∀ a, retract (sect a) = a)
  : Param42b α α' := by
  tr_extend paramFromMap sect

  -- 2b
  · exact retract
  · intro _ _  aR; subst aR
    exact sectK _


theorem transportRoundtrip
  (p :  Param2a2b A B)
  (x : A)
  : p.left (p.right x) = x := by

  let x' := p.right x
  let xR : p.R x x' := p.right_implies_R x x' rfl

  exact p.R_implies_left x x' xR


def paramFromInvolution
  {flipR : α → β}
  {flipR' : β → α}
  (h : ∀ a, flipR' (flipR a) = a)
  (h' : ∀ b, flipR (flipR' b) = b := by exact h)

  : Param44 α β := by

  tr_constructor

   -- R
  exact (flipR · = ·)

  -- 4
  exact flipR
  simp
  simp
  simp

  -- 4
  exact flipR'
  simp

  apply h'
  · intro x x' xR
    subst xR
    apply  h
  simp

def paramFromEquiv
  {f : α → β}
  {g : β → α}
  (h1 : ∀ x, g (f x) = x)
  (h2 : ∀ x, f (g x) = x)
  : Param44 α β := by
  tr_extend paramFromMap f

  -- 4
  exact g
  · intro _ _ aF; subst aF; exact h2 _
  · intro _ _ aR; subst aR; exact h1 _
  · intro _ _ aR; rfl
