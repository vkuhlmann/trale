import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Map

import Qq open Qq Lean

section Params
universe w u v

variable (α: Sort u) (β : Sort v)

structure Param (α : Sort u) (β : Sort v)
    (mapCov : MapType)
    (mapContra : MapType)
  : Sort ((max u v w) + 1) where

  R : α → β -> Sort w
  covariant : mapCov.interp R
  contravariant : mapContra.interp (flipRel R)


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

abbrev Param00  :=  Param.{w} α β .Map0 .Map0
abbrev Param01  :=  Param.{w} α β .Map0 .Map1
abbrev Param02a :=  Param.{w} α β .Map0 .Map2a
abbrev Param02b :=  Param.{w} α β .Map0 .Map2b
abbrev Param03  :=  Param.{w} α β .Map0 .Map3
abbrev Param04  :=  Param.{w} α β .Map0 .Map4

abbrev Param10  :=  Param.{w} α β .Map1 .Map0
abbrev Param11  :=  Param.{w} α β .Map1 .Map1
abbrev Param12a :=  Param.{w} α β .Map1 .Map2a
abbrev Param12b :=  Param.{w} α β .Map1 .Map2b
abbrev Param13  :=  Param.{w} α β .Map1 .Map3
abbrev Param14  :=  Param.{w} α β .Map1 .Map4

abbrev Param2a0 :=  Param.{w} α β .Map2a .Map0
abbrev Param2a1 :=  Param.{w} α β .Map2a .Map1
abbrev Param2a2a := Param.{w} α β .Map2a .Map2a
abbrev Param2a2b := Param.{w} α β .Map2a .Map2b
abbrev Param2a3 :=  Param.{w} α β .Map2a .Map3
abbrev Param2a4 :=  Param.{w} α β .Map2a .Map4

abbrev Param2b0 :=  Param.{w} α β .Map2b .Map0
abbrev Param2b1 :=  Param.{w} α β .Map2b .Map1
abbrev Param2b2a := Param.{w} α β .Map2b .Map2a
abbrev Param2b2b := Param.{w} α β .Map2b .Map2b
abbrev Param2b3 :=  Param.{w} α β .Map2b .Map3
abbrev Param2b4 :=  Param.{w} α β .Map2b .Map4

abbrev Param30  :=  Param.{w} α β .Map3 .Map0
abbrev Param31  :=  Param.{w} α β .Map3 .Map1
abbrev Param32a :=  Param.{w} α β .Map3 .Map2a
abbrev Param32b :=  Param.{w} α β .Map3 .Map2b
abbrev Param33  :=  Param.{w} α β .Map3 .Map3
abbrev Param34  :=  Param.{w} α β .Map3 .Map4

abbrev Param40  :=  Param.{w} α β .Map4 .Map0
abbrev Param41  :=  Param.{w} α β .Map4 .Map1
abbrev Param42a :=  Param.{w} α β .Map4 .Map2a
abbrev Param42b :=  Param.{w} α β .Map4 .Map2b
abbrev Param43  :=  Param.{w} α β .Map4 .Map3
abbrev Param44  :=  Param.{w} α β .Map4 .Map4


#check (_ : Param11 ?a ?b).covariant

-- ASK The last expression has type `MapType.Map1.interp p.R`. Can we apply a simplification automatically
--     such that it becomes `Map1 p.R` instead?
#check
  let p : Param11 ?a ?b := ?p
  p.covariant

end Params

set_option pp.all true in
instance
  CoeParam

  (Rp : Param.{w} α β X Y)
  [CoeTC (X.interp Rp.R) (X'.interp Rp.R)]
  [CoeTC (Y.interp (flipRel Rp.R)) (Y'.interp (flipRel Rp.R))]
  :
  CoeDep
  (Param.{w} α β X Y)
  Rp
  (Param.{w} α β X' Y')
   where
   coe :=
   (@Param.mk α β X' Y' Rp.R Rp.covariant Rp.contravariant : Param.{w} α β X' Y')


namespace Param

@[simp]
def forget
  (Rp : Param.{w} α β X Y)
  [Coe (X.interp Rp.R) (X'.interp Rp.R)]
  [Coe (Y.interp (flipRel Rp.R)) (Y'.interp (flipRel Rp.R))]
: Param.{w} α β X' Y'
 := (CoeParam Rp).coe

theorem map0bottom {X : MapType} : MapType.Map0 ≤ X := by
  cases X <;> decide

theorem map4top {X : MapType} : X ≤ MapType.Map4 := by
  cases X <;> decide

@[simp]
def forget'
  {X Y X' Y': MapType}

  (h1 : X' ≤ X := by decide)
  (h2 : Y' ≤ Y := by decide)
  (Rp : Param.{w} α β X Y)
  :
  (Param.{w} α β X' Y')
  := by

    constructor
    case R => exact Rp.R
    case covariant => exact coeMap Rp.covariant h1
    case contravariant => exact coeMap Rp.contravariant h2


@[simp]
abbrev flip (p : Param α β m1 m2) : Param β α m2 m1 :=
  { R := flipRel p.R, covariant := p.contravariant, contravariant := p.covariant }

@[simp]
abbrev right (p : Param10 α β) : α -> β :=
  p.covariant.map

@[simp]
abbrev left (p : Param01 α β) : β -> α :=
  p.contravariant.map

@[simp]
abbrev right_implies_R (p : Param2a0 α β)
  : (a : α) -> (b : β) -> p.right a = b -> p.R a b := p.covariant.map_in_R

@[simp]
abbrev left_implies_R (p : Param02a α β)
  : forall (a : α) (b : β), p.left b = a -> p.R a b := by
    let h := p.contravariant.map_in_R
    simp
    simp [flipRel] at h
    intros a b h'
    let h2 := h b
    rw [h'] at h2
    apply h2
    trivial

@[simp]
abbrev R_implies_right (p : Param2b0 α β)
  : forall (a : α) (b : β), p.R a b -> p.right a = b := p.covariant.R_in_map

@[simp]
abbrev R_implies_rightK (p : Param40 α β)
  := p.covariant.R_in_mapK

@[simp]
abbrev R_implies_left (p : Param02b α β)
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
