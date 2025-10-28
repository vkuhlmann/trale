import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Map

import Qq open Qq Lean

section Params
universe w u v

variable (α: Sort u) (β : Sort v)

structure NormativeDirection where
  this_dir : Bool
  other_dir : Bool

namespace NormativeDirection
def both : NormativeDirection := ⟨true, true⟩
def this : NormativeDirection := ⟨true, false⟩
def other : NormativeDirection := ⟨false, true⟩
def none : NormativeDirection := ⟨false, false⟩

def opposite : NormativeDirection → NormativeDirection
  := (match . with | ⟨a, b⟩ => ⟨b, a⟩)
end NormativeDirection

class TrTranslateRight (α : Sort u) (β : outParam (Sort v)) where
  -- hypotheses : Array (((p : Prop), (proof : p)) : (p : Prop) ×' (_ : p))
  -- hypotheses : Σ' (p : Prop), (_ : p)
  -- or type like Simprocs? Do it by attributes?



class TrTranslateLeft (α : outParam (Sort u)) (β : Sort v)
-- class TrTranslateRight (α : Sort u) : Sort (max 1 u)
-- class TrTranslateLeft (α : outParam (Sort u)) (β : Sort v)

-- structure ParamRoot (α : Sort u) (β : Sort v)
--     (mapCov : MapType)
--     (mapContra : MapType)
--   -- : Sort ((max u v w) + 1)
--    where

--   R : α → β -> Sort w

-- FIXME Being a 'class' sometimes hurts readability, especially when
-- constructing new params based on previous ones. However, if manipulation of
-- Params can be done by this library, such that the user (almost) never needs
-- to do it, this issue is more limited.
class Param
    (mapCov : MapType)
    (mapContra : MapType)
    (α : Sort u) (β : Sort v)
  -- extends ParamRoot.{w, u, v} α β mapCov mapContra
  where

  R : α → β → Sort w
  covariant : mapCov.interp R
  contravariant : mapContra.interp (flipRel R)
  -- normativeDirection : NormativeDirection := .this


-- ## Param abbreviations
--
-- We're enumerating all the abbreviations manually.
--
-- It's not the most pure and
-- sophisticated way, but it gets the job done, and performing all the necessary
-- metaprogramming to automatically enumerate the cases would likely be more
-- lines of code, and confuse code editor tools like IntelliSense.
--
-- I looked into this in the past, and the cleanest entrance for an api was private,
-- meaning that for including it in a public library, I would need to replicate its
-- many private dependencies.

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


#check (_ : Param11 ?a ?b).covariant

#check (_ : Param11 ?a ?b).R

-- FIXME The last expression has type `MapType.Map1.interp p.R`. Can we apply a simplification automatically
--     such that it becomes `Map1 p.R` instead?
#check
  let p : Param11 ?a ?b := ?p
  p.covariant

end Params

set_option pp.all true in
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
    -- normativeDirection := Rp.normativeDirection
   }
  --  (@Param.mk α β X' Y' Rp.R Rp.covariant Rp.contravariant Rp.normativeDirection : Param.{w} α β X' Y')


namespace Param

@[simp]
def forget'
  (Rp : Param.{w} X Y α β)
  [Coe (X.interp Rp.R) (X'.interp Rp.R)]
  [Coe (Y.interp (flipRel Rp.R)) (Y'.interp (flipRel Rp.R))]
: Param.{w} X' Y' α β
 := (CoeParam Rp).coe

theorem map0bottom {X : MapType} : MapType.Map0 ≤ X := by
  cases X <;> decide

theorem map4top {X : MapType} : X ≤ MapType.Map4 := by
  cases X <;> decide

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

@[simp]
abbrev flip (p : Param α β m1 m2) : Param β α m2 m1 :=
  { R := flipRel p.R, covariant := p.contravariant, contravariant := p.covariant,
  -- normativeDirection := p.normativeDirection.opposite
  }

@[simp]
abbrev right' (p : Param10 α β) : α -> β :=
  p.covariant.map

@[simp]
abbrev right (p : Param cov con α β) (a : α) (h : .Map1 ≤ cov := by decide) : β :=
  (p.forget h map0bottom).covariant.map a


@[simp]
abbrev left' (p : Param01 α β) : β -> α :=
  p.contravariant.map

@[simp]
abbrev left (p : Param cov con α β) (b : β) (h : .Map1 ≤ con := by decide) : α :=
  (p.forget map0bottom h).contravariant.map b

@[simp]
abbrev right_implies_R (p : Param2a0 α β)
  := p.covariant.map_in_R
  -- : (a : α) -> (b : β) -> p.right a = b -> p.R a b := p.covariant.map_in_R

@[simp]
abbrev left_implies_R {β : Sort v} (p : Param02a α β)
  : forall (a : α) (b : β), p.left b = a -> p.R a b := by
    let h := p.contravariant.map_in_R
    simp
    simp [flipRel] at h
    intros a b h'
    let h2 := h b
    rw [h'] at h2
    apply h2
    trivial

-- We need to give an explicit level name to β, else it will get inferred as a
-- Type for some reason.
-- FIXME Why do we need to specify β?
@[simp]
abbrev R_implies_right {β : Sort v} (p : Param2b0 α β)
  : forall (a : α) (b : β), p.R a b -> p.right a = b := p.covariant.R_in_map

@[simp]
abbrev R_implies_rightK (p : Param40 α β)
  := p.covariant.R_in_mapK

@[simp]
abbrev R_implies_left {β : Sort v} (p : Param02b α β)
  : forall (a : α) (b : β), p.R a b -> p.left b = a := by
    let h := p.contravariant.R_in_map
    simp
    simp [flipRel] at h
    intros a b h'
    let h2 := h b a
    exact h2 h'

@[simp]
abbrev R_implies_leftK (p : Param04 α β)
  := p.contravariant.R_in_mapK

end Param

-- @[simp]
-- abbrev right [p : Param10 α β] : α -> β :=
--   p.covariant.map

namespace tr

@[simp]
abbrev R [p : Param00 α β] := p.R


@[simp]
abbrev map [p : Param10 α β] : α -> β :=
  p.covariant.map

-- @[simp]
-- abbrev R_implies_left [p : Param02b α β]
--   : forall (a : α) (b : β), p.R a b -> p.left b = a := by
--     let h := p.contravariant.R_in_map
--     simp
--     simp [flipRel] at h
--     intros a b h'
--     let h2 := h b a
--     exact h2 h'

@[simp]
abbrev R_implies_map [p : Param2b0 α β]
  : forall (a : α) (b : β), (aR : p.R a b) -> p.right a = b := p.covariant.R_in_map

@[simp]
abbrev map_implies_R [p : Param2a0 α β]
  : (a : α) -> (b : β) -> p.right a = b -> p.R a b := p.covariant.map_in_R

@[simp]
abbrev R_implies_mapK [p : Param40 α β]
  := p.covariant.R_in_mapK

end tr



-- instance [p : Param α β cov con] [c :Coe (Param α β cov con) (Param α β cov2 con2)]
--   : Param α β cov2 con2 := c.coe p

-- instance : Param42a.{0} String Nat := sorry

-- instance [p : Param40 α β] : Param10 α β := p
-- instance [p : Param α β cov con] [h : cov ≥ .Map1]
--   : Param10 α β := p.forget
-- instance [p : Param α β cov con] (h : cov ≥ .Map1 := by decide)
--   : Param10 α β := p.forget

-- instance [p : Param α β .Map4 con] : Param α β .Map1 con := p
-- instance [p : Param α β cov .Map2a] : Param α β cov .Map0 := p
-- instance : Param10.{0} String Nat := sorry
-- def abc : Nat := right "hoi"

instance (priority := 80) [p : Param α β cov con] : Param β α con cov := p.flip

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
