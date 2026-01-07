import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Map

import Qq open Qq Lean

namespace Trale

/-!
# Parametricity Relations (Param)

This module defines the core `Param` class that represents parametric relations
between types. A `Param` instance captures a relation `R : α → β → Sort w` along
with associated mapping functions and their properties.

## Overview

The `Param` class is indexed by two `MapType` values that specify what properties
the relation has in the covariant (α → β) and contravariant (β → α) directions.

For example:
- `Param44 α β`: Full equivalence in both directions
- `Param2a4 α β`: Covariant surjection with contravariant equivalence
- `Param10 α β`: Simple map from α to β with no contravariant structure

## Common Abbreviations

- `Param00`: Just the relation (no functions)
- `Param10`: Covariant map
- `Param2a0`: Covariant map with proof it captures R
- `Param2b0`: Covariant map with proof R implies equality
- `Param40`: Full covariant equivalence
- `Param44`: Full equivalence in both directions

The same pattern applies to the contravariant (second) index.
-/

section Params
universe w u v

variable (α: Sort u) (β : Sort v)

/--
The core parametricity class.

A `Param mapCov mapContra α β` represents a parametric relation between types
`α` and `β`, equipped with:
- A relation `R : α → β → Sort w`
- Covariant structure of type `mapCov` (operations from α to β)
- Contravariant structure of type `mapContra` (operations from β to α)

The map types determine what properties the relation has:
- `Map0`: Just the relation
- `Map1`: Plus a mapping function
- `Map2a`: Map captures the relation
- `Map2b`: Relation implies equality via map
- `Map3`: Both Map2a and Map2b
- `Map4`: Full equivalence with coherence
-/
class Param
    (mapCov : MapType)
    (mapContra : MapType)
    (α : Sort u) (β : Sort v)
  where

  R : α → β → Sort w
  covariant : mapCov.interp R
  contravariant : mapContra.interp (flipRel R)


-- ## Param abbreviations
--
-- We enumerate all 36 abbreviations manually (6×6 combinations of map types).
-- This could be slightly shorter with metaprogramming, but this is clearer and
-- more explicit.

abbrev Param00  :=  Param.{w} .Map0 .Map0
abbrev Param01  :=  Param.{w} .Map0 .Map1
abbrev Param02a :=  Param.{w} .Map0 .Map2a
abbrev Param02b :=  Param.{w} .Map0 .Map2b
abbrev Param03  :=  Param.{w} .Map0 .Map3
abbrev Param04  :=  Param.{w} .Map0 .Map4

abbrev Param10  :=  Param.{w} .Map1 .Map0
abbrev Param11  :=  Param.{w} .Map1 .Map1
abbrev Param12a :=  Param.{w} .Map1 .Map2a
abbrev Param12b :=  Param.{w} .Map1 .Map2b
abbrev Param13  :=  Param.{w} .Map1 .Map3
abbrev Param14  :=  Param.{w} .Map1 .Map4

abbrev Param2a0 :=  Param.{w} .Map2a .Map0
abbrev Param2a1 :=  Param.{w} .Map2a .Map1
abbrev Param2a2a := Param.{w} .Map2a .Map2a
abbrev Param2a2b := Param.{w} .Map2a .Map2b
abbrev Param2a3 :=  Param.{w} .Map2a .Map3
abbrev Param2a4 :=  Param.{w} .Map2a .Map4

abbrev Param2b0 :=  Param.{w} .Map2b .Map0
abbrev Param2b1 :=  Param.{w} .Map2b .Map1
abbrev Param2b2a := Param.{w} .Map2b .Map2a
abbrev Param2b2b := Param.{w} .Map2b .Map2b
abbrev Param2b3 :=  Param.{w} .Map2b .Map3
abbrev Param2b4 :=  Param.{w} .Map2b .Map4

abbrev Param30  :=  Param.{w} .Map3 .Map0
abbrev Param31  :=  Param.{w} .Map3 .Map1
abbrev Param32a :=  Param.{w} .Map3 .Map2a
abbrev Param32b :=  Param.{w} .Map3 .Map2b
abbrev Param33  :=  Param.{w} .Map3 .Map3
abbrev Param34  :=  Param.{w} .Map3 .Map4

abbrev Param40  :=  Param.{w} .Map4 .Map0
abbrev Param41  :=  Param.{w} .Map4 .Map1
abbrev Param42a :=  Param.{w} .Map4 .Map2a
abbrev Param42b :=  Param.{w} .Map4 .Map2b
abbrev Param43  :=  Param.{w} .Map4 .Map3
abbrev Param44  :=  Param.{w} .Map4 .Map4


-- FIXME The last expression has type `MapType.Map1.interp p.R`. Can we apply a simplification automatically
--     such that it becomes `Map1 p.R` instead?
#check
  let p : Param11 ?a ?b := ?p
  p.covariant

end Params

/-- Coerce a Param to one with weaker structure.
    Allows using instance inference to weaken Param types when needed. -/
instance
  CoeParam

  (p : Param.{w} X Y α β)
  [CoeTC (X.interp p.R) (X'.interp p.R)]
  [CoeTC (Y.interp (flipRel p.R)) (Y'.interp (flipRel p.R))]
  :
  CoeDep
  (Param.{w} X Y α β)
  p
  (Param.{w} X' Y' α β)
   where
   coe := {
    R := p.R,
    covariant := p.covariant,
    contravariant := p.contravariant,
   }


namespace Param

/-- Forget some structure of a Param by weakening the map types.
    Uses explicit coercion instances. -/
@[simp]
def forget'
  (Rp : Param.{w} X Y α β)
  [Coe (X.interp Rp.R) (X'.interp Rp.R)]
  [Coe (Y.interp (flipRel Rp.R)) (Y'.interp (flipRel Rp.R))]
: Param.{w} X' Y' α β
 := (CoeParam Rp).coe

/-- Forget some structure of a Param by weakening the map types.
    Uses decidable proofs that X' ≤ X and Y' ≤ Y. -/
@[simp]
def forget
  {X Y X' Y': MapType}

  (h1 : X' ≤ X := by decide)
  (h2 : Y' ≤ Y := by decide)
  (p : Param.{w} X Y α β)
  :
  (Param.{w} X' Y' α β)
  := {
    R := p.R,
    covariant := coeMap p.covariant h1,
    contravariant := coeMap p.contravariant h2,
  }

/-- Flip a Param, swapping the roles of α and β.
    Also swaps covariant and contravariant structure. -/
@[simp]
abbrev flip (p : Param α β m1 m2) : Param β α m2 m1 :=
  { R := flipRel p.R, covariant := p.contravariant, contravariant := p.covariant,
  }

/-- Extract the covariant map function from a Param10. -/
@[simp]
abbrev right' (p : Param10 α β) : α -> β :=
  p.covariant.map

/-- Extract the covariant map function from any Param with at least Map1 covariance. -/
@[simp]
abbrev right (p : Param cov con α β) (a : α) (h : .Map1 ≤ cov := by decide) : β :=
  (p.forget h map0bottom).covariant.map a


/-- Extract the contravariant map function from a Param01. -/
@[simp]
abbrev left' (p : Param01 α β) : β -> α :=
  p.contravariant.map

/-- Extract the contravariant map function from any Param with at least Map1 contravariance. -/
@[simp]
abbrev left (p : Param cov con α β) (b : β) (h : .Map1 ≤ con := by decide) : α :=
  (p.forget map0bottom h).contravariant.map b

/-- From a Param2a0, get that the covariant map captures the relation. -/
@[simp]
abbrev right_implies_R (p : Param2a0 α β)
  := p.covariant.map_in_R

/-- From a Param02a, get that the contravariant map captures the relation. -/
@[simp]
abbrev left_implies_R {β : Sort v} (p : Param02a α β)
  : ∀ (a : α) (b : β), p.left b = a → p.R a b :=
    fun a b h => p.contravariant.map_in_R b a h

-- We need to give an explicit level name to β, else it will get inferred as a
-- Type for some reason.
-- FIXME Why do we need to specify β?
/-- From a Param2b0, get that the relation implies equality via the covariant map. -/
@[simp]
abbrev R_implies_right {β : Sort v} (p : Param2b0 α β)
  : forall (a : α) (b : β), p.R a b -> p.right a = b := p.covariant.R_in_map

/-- From a Param40, get the coherence proof for the covariant direction. -/
@[simp]
abbrev R_implies_rightK (p : Param40 α β)
  := p.covariant.R_in_mapK

/-- From a Param02b, get that the relation implies equality via the contravariant map. -/
@[simp]
abbrev R_implies_left {β : Sort v} (p : Param02b α β)
  : forall (a : α) (b : β), p.R a b -> p.left b = a := by
    let h := p.contravariant.R_in_map
    simp
    simp [flipRel] at h
    intros a b h'
    let h2 := h b a
    exact h2 h'

/-- From a Param04, get the coherence proof for the contravariant direction. -/
@[simp]
abbrev R_implies_leftK (p : Param04 α β)
  := p.contravariant.R_in_mapK

end Param

/-! ## Namespace `tr`

Convenient abbreviations for accessing Param fields.
These are designed to be used with instance inference, e.g., `tr.R` will
find the appropriate Param instance and extract its relation.
-/
namespace tr

/-- Access the relation from a Param instance. -/
@[simp]
abbrev R [p : Param00 α β] := p.R


/-- Access the covariant map from a Param instance. -/
@[simp]
abbrev map [p : Param10 α β] : α -> β :=
  p.covariant.map

/-- Access the proof that R implies equality via map. -/
@[simp]
abbrev R_implies_map [p : Param2b0 α β]
  : forall (a : α) (b : β), (aR : p.R a b) -> p.right a = b := p.covariant.R_in_map

/-- Access the proof that equality via map implies R. -/
@[simp]
abbrev map_implies_R [p : Param2a0 α β]
  : (a : α) -> (b : β) -> p.right a = b -> p.R a b := p.covariant.map_in_R

/-- Access the coherence proof. -/
@[simp]
abbrev R_implies_mapK [p : Param40 α β]
  := p.covariant.R_in_mapK

end tr

/-- Automatic flipping: if we have `Param α β cov con`, we also have `Param β α con cov`. -/
instance (priority := 80) [p : Param α β cov con] : Param β α con cov := p.flip

-- Instances for weakening (coercing/forgetting) Param structures.
-- These allow automatic weakening when a weaker Param is expected.
@[simp] instance (priority := low) [p : Param .Map4 con α β] : Param .Map3 con α β := p
@[simp] instance (priority := low) [p : Param .Map3 con α β] : Param .Map2a con α β := p
@[simp] instance (priority := low) [p : Param .Map3 con α β] : Param .Map2b con α β := p
@[simp] instance (priority := low) [p : Param .Map2a con α β] : Param .Map1 con α β := p
@[simp] instance (priority := low) [p : Param .Map2b con α β] : Param .Map1 con α β := p
@[simp] instance (priority := low) [p : Param .Map1 con α β] : Param .Map0 con α β := p

@[simp] instance (priority := low) [p : Param cov .Map4 α β] : Param cov .Map3 α β := p
@[simp] instance (priority := low) [p : Param cov .Map3 α β] : Param cov .Map2a α β := p
@[simp] instance (priority := low) [p : Param cov .Map3 α β] : Param cov .Map2b α β := p
@[simp] instance (priority := low) [p : Param cov .Map2a α β] : Param cov .Map1 α β := p
@[simp] instance (priority := low) [p : Param cov .Map2b α β] : Param cov .Map1 α β:= p
@[simp] instance (priority := low) [p : Param cov .Map1 α β] : Param cov .Map0 α β := p
