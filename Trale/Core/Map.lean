import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command

namespace Trale

/-!
# Map Types for Parametricity Relations

This module defines the hierarchy of map types that capture different properties
of relations between types. These map types form the foundation of the Trale
parametricity framework.

## Overview

A relation `R : α → β → Sort w` may have associated mapping functions between
`α` and `β`. The Map hierarchy captures increasingly strong properties:

- `Map0`: Just the relation itself, no functions
- `Map1`: Adds a map function `α → β`
- `Map2a`: The map captures the relation (covariant)
- `Map2b`: The relation implies equality via the map (contravariant)
- `Map3`: Both Map2a and Map2b properties
- `Map4`: Full equivalence with coherence

The hierarchy forms a partial order: `0 < 1 < 2a < 3 < 4` and `0 < 1 < 2b < 3 < 4`,
where `2a` and `2b` are incomparable.
-/

section Map
universe w u v

section RExplicit
variable {α: Sort u} {β : Sort v}
variable (R : α -> β -> Sort w)

/-- Flip a binary relation, swapping the argument order. -/
@[simp]
def flipRel : β -> α -> Sort w := fun a b => R b a

/-- `Map0`: A relation with no additional structure.
    This is the base of the hierarchy, containing only the relation itself. -/
structure Map0 (R : α -> β -> Sort w) : Type (max u v w)

/-- `Map1`: A relation with a mapping function from `α` to `β`.
    This adds directionality to the relation. -/
structure Map1 extends Map0 R where
  map : α -> β

/-- `Map2a`: The map captures the relation (covariant property).
    If `map a = b`, then `R a b` holds.
    This means the map function witnesses the relation. -/
structure Map2a extends Map1 R where
  map_in_R : forall (a : α) (b : β), map a = b -> R a b

/-- `Map2b`: The relation determines the map (contravariant property).
    If `R a b` holds, then `map a = b`.
    This means elements in the relation are uniquely determined by the map. -/
structure Map2b extends Map1 R where
  R_in_map : forall (a : α) (b : β), R a b -> map a = b

/-- `Map3`: Both Map2a and Map2b properties hold.
    The relation and equality via the map are equivalent: `R a b ↔ map a = b`. -/
structure Map3 extends Map2a R, Map2b R where

/-- `Map4`: Full equivalence with coherence.
    Extends Map3 with a proof that the round-trip `map_in_R ∘ R_in_map` is the identity.
    This ensures the relation behaves like a proper equivalence with no higher structure. -/
structure Map4 extends Map3 R where
  R_in_mapK : forall (a : α) (b : β) (r : R a b),
              (map_in_R a b (R_in_map a b r)) = r

end RExplicit

/-- Enumeration of the map types in the hierarchy.
    Used for metaprogramming and type-level computations. -/
inductive MapType where
  | Map0
  | Map1
  | Map2a
  | Map2b
  | Map3
  | Map4
deriving DecidableEq, Repr

instance : Inhabited MapType := ⟨.Map0⟩

instance : ToString MapType where
  toString
    | .Map0 => "Map0"
    | .Map1 => "Map1"
    | .Map2a => "Map2a"
    | .Map2b => "Map2b"
    | .Map3 => "Map3"
    | .Map4 => "Map4"

/-- Short indicator strings for map types, used in naming conventions. -/
def MapType.getMapTypeIndicator
  : MapType → String
  | .Map0 => "0"
  | .Map1 => "1"
  | .Map2a => "2a"
  | .Map2b => "2b"
  | .Map3 => "3"
  | .Map4 => "4"

/-- Interpret a MapType as the corresponding Map structure.
    This connects the type-level representation to the actual structures. -/
@[reducible, simp] def MapType.interp
  (mapType : MapType)
  (R : α -> β -> Sort w) :=
  match mapType with
  | .Map0 => Trale.Map0 R
  | .Map1 => Trale.Map1 R
  | .Map2a => Trale.Map2a R
  | .Map2b => Trale.Map2b R
  | .Map3 => Trale.Map3 R
  | .Map4 => Trale.Map4 R

/-- Partial order on map types.
    The hierarchy: 0 ≤ 1 ≤ {2a, 2b} ≤ 3 ≤ 4, where 2a and 2b are incomparable.
    This order represents "has at least as much structure as". -/
def leMapType (a b : MapType) : Bool :=
  match a, b with
    | .Map0, _
    | .Map1, .Map1
    | .Map1, .Map2a
    | .Map1, .Map2b
    | .Map1, .Map3
    | .Map1, .Map4
    | .Map2a, .Map2a
    | .Map2a, .Map3
    | .Map2a, .Map4
    | .Map2b, .Map2b
    | .Map2b, .Map3
    | .Map2b, .Map4
    | .Map3, .Map3
    | .Map3, .Map4
    | .Map4, .Map4 => true
    | _, _ => false

@[reducible]
instance : LE MapType where
  le a b : Bool := leMapType a b

instance : DecidableLE MapType :=
  fun s t => by
    simp [LE.le, leMapType]

    split
    rotate_right 1

    · -- The cases '_, _' from leMapType
      show Decidable (false = true)
      exact Decidable.isFalse (Bool.false_ne_true)

    -- The cases '.MapX, .MapY' from leMapType
    repeat (
      show Decidable (true = true)
      exact Decidable.isTrue rfl
    )

theorem map0bottom {X : MapType} : MapType.Map0 ≤ X := by
  cases X <;> decide

/-- Map4 is the top element: it has the most structure. -/
theorem map4top {X : MapType} : X ≤ MapType.Map4 := by
  cases X <;> decide

#eval instDecidableLEMapType .Map0 .Map0

theorem mapTypeTrans {a b c : MapType} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  simp [LE.le, leMapType]
  cases a <;> cases c <;> simp <;> cases b <;> contradiction

theorem mapTypeTrans' {a b c : MapType} (h1 : a ≥ b) (h2 : b ≥ c) : a ≥ c := by
  apply mapTypeTrans h2 h1

instance : Std.IsPreorder MapType where
  le_refl a := by cases a <;> rfl
  le_trans := @mapTypeTrans

instance : Std.IsPartialOrder MapType where
  le_antisymm a b h1 h2 := by
    cases a <;> cases b <;> first|rfl |contradiction


/-- Union of map types: takes the least upper bound in the hierarchy.
    Special case: Map2a ∪ Map2b = Map3 (they combine to give both properties). -/
instance : Union MapType where
  union
    | .Map2a, .Map2b => .Map3
    | .Map2b, .Map2a => .Map3
    | a, b =>
      if a ≤ b then b else a

theorem maptype_U_maptype_symm
  (a b : MapType)
  : a ∪ b = b ∪ a := by

  cases a <;> cases b <;> rfl

theorem maptype_U_maptype_geq_maptype
  (a b : MapType)
  : a ∪ b ≥ a := by

  cases a <;> cases b <;> decide

theorem maptype_U_maptype_monotone
  (a b c : MapType)
  (h : a ≥ c)
  : a ∪ b ≥ c ∪ b := by

  cases a <;>
    cases b <;>
      cases c <;> first
        | decide
        | contradiction


/-- Intersection of map types: takes the greatest lower bound in the hierarchy.
    Special case: Map2a ∩ Map2b = Map1 (their common structure is just the map). -/
instance : Inter MapType where
  inter
    | .Map2a, .Map2b => .Map1
    | .Map2b, .Map2a => .Map1
    | a, b =>
      if a ≤ b then
        a
      else
        b

theorem maptype_inter_symm
  (a b : MapType)
  : a ∩ b = b ∩ a := by

  cases a <;> cases b <;> rfl

theorem maptype_inter_leq_maptype
  (a b : MapType)
  : a ∩ b ≤ a := by

  cases a <;> cases b <;> rfl


theorem maptype_inter_monotone
  (a b c : MapType)
  (h : a ≥ c)
  : a ∩ b ≥ c ∩ b := by

  cases a <;>
    cases b <;>
      cases c <;> first
        | decide
        | contradiction


/-- Alternative interpretation of MapType using pattern matching.
    Functionally equivalent to `MapType.interp` but with different reduction behavior. -/
@[reducible] def MapType.interp' (mapType : MapType) (R : α -> β -> Sort w) : Type _ :=
  MapType.casesOn (motive := fun _ => Type _) mapType
  (Trale.Map0 R)
  (Trale.Map1 R)
  (Trale.Map2a R)
  (Trale.Map2b R)
  (Trale.Map3 R)
  (Trale.Map4 R)


/-- Coercion instances following the Map hierarchy.
    These allow automatic weakening of stronger map types to weaker ones. -/
instance : Coe (Map1 R) (Map0 R) where
  coe m := m.toMap0

instance : Coe (Map2a R) (Map1 R) where
  coe m := m.toMap1

instance : Coe (Map2b R) (Map1 R) where
  coe m := m.toMap1

instance : Coe (Map3 R) (Map2a R) where
  coe m := m.toMap2a

instance : Coe (Map3 R) (Map2b R) where
  coe m := m.toMap2b

instance : Coe (Map4 R) (Map3 R) where
  coe m := m.toMap3


/-- Coerce a map structure to a weaker one, given a proof that the target is
    weaker in the hierarchy. This is the general coercion function. -/
@[simp]
def coeMap {m1 m2 : MapType} {R : α -> β -> Sort w}
  (m : m1.interp R) (h : m2 ≤ m1) : m2.interp R := by

  match m1, m2 with
  | .Map4, .Map0 => constructor
  | .Map4, .Map1 => exact (m : Map1 R)
  | .Map4, .Map2a => exact (m : Map2a R)
  | .Map4, .Map2b => exact (m : Map2b R)
  | .Map4, .Map3 => exact (m : Map3 R)
  | .Map4, .Map4 => exact (m : Map4 R)
  | .Map3, .Map0 => constructor
  | .Map3, .Map1 => exact (m : Map1 R)
  | .Map3, .Map2a => exact (m : Map2a R)
  | .Map3, .Map2b => exact (m : Map2b R)
  | .Map3, .Map3 => exact (m : Map3 R)
  | .Map2a, .Map0 => constructor
  | .Map2a, .Map1 => exact (m : Map1 R)
  | .Map2a, .Map2a => exact (m : Map2a R)
  | .Map2b, .Map0 => constructor
  | .Map2b, .Map1 => exact (m : Map1 R)
  | .Map2b, .Map2b => exact (m : Map2b R)
  | .Map1, .Map0 => constructor
  | .Map1, .Map1 => exact (m : Map1 R)
  | .Map0, .Map0 => constructor


/-- Alternative implementation of `coeMap` with more detailed proof structure.
    Uses case analysis to systematically handle all valid coercions. -/
@[simp]
def coeMap' {m1 m2 : MapType} {R : α -> β -> Sort w}
  (m : m1.interp R) (h : m2 ≤ m1) : m2.interp R := by

  cases m1 <;> cases m2

  -- Aesthetic, removes the `MapType.interp` invocations.
  all_goals (
    dsimp only [MapType.interp] at m ⊢
  )

  -- Solves the 16 impossible goals. Eg, for Map2a <= Map0
  all_goals (try (
    -- Do not use exfalso directly, because if followed by a simp on the goal, the
    -- goal will not be backtracked after exiting try, causing it to stay False
    -- for possible cases.
    -- FIXME: Why is that happening?

    dsimp [LE.le, instLEMapType, leMapType] at h
    suffices false = true by
      exfalso
      simp at this

    exact h
  ))

  -- Solves the 20 possible goals. Eg. Map0 <= Map2a
  all_goals
  (
    -- Now that the bad cases are ruled out, the types should be coercable.
    -- We simply invoke class inference on CoeT to find the right coercion.
    -- If any case fails, it means:
    --    1. a coercion is missing, or,
    --    2. `LE MapType` is incorrectly true for m1 and m2
    --    3. the above filtering code is incorrect.
    exact CoeT.coe m
  )
