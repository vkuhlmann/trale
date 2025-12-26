import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Map
import Trale.Core.Param
import Trale.Theories.Arrow

open Trale

variable {α: Sort u} {β : Sort v}
variable (R : α -> β -> Sort w)

structure Map3' (R : α -> β -> Sort w) where
  map : α -> β
  map_in_R : forall (a : α) (b : β), map a = b -> R a b
  R_in_map : forall (a : α) (b : β), R a b -> map a = b

-- #check ∀ (x : Nat), String
-- #check ∃ (x : Nat), String

#check
  let R : α -> β -> Sort 0 := _
  let m : Map3' R := _
  m.3

-- #eval ((id): Map1 (Eq))
#check ((id): (Nat → Nat))
#check (⟨id, fun a b => by simp⟩: (map : Nat → Nat) ×' (forall (a : Nat) (b : Nat), map a = b -> Eq a b))
#check (⟨id, fun a b => by simp, 6⟩: (map : Nat → Nat) ×' (forall (a : Nat) (b : Nat), map a = b -> Eq a b) ×' Nat)

#check (⟨id, fun a b => by simp, 6⟩: (map : Nat → Nat) ×' (forall (a : Nat) (b : Nat), map a = b -> Eq a b) ×' Nat).2.2

-- #check (⟨id, fun a b => by simp⟩: (map : Nat → Nat) ×' (forall (a : Nat) (b : Nat), map a = b -> Eq a b))

#check Map2b.R_in_map
#check
  let R : α -> β -> Sort 0 := ?R
  (m : Map1 R) ×' (forall (a : α) (b : β), m.map a = b -> R a b)

#check Param.R


#check Coe


#check
  let p1 : Param .Map4 .Map2b Nat String := ?p1
  let f := p1.covariant.map
  let x := 4
  let x' := f x
  let xR : p1.R x x' := p1.covariant.map_in_R x x' rfl

  let g := p1.contravariant.map
  let gx' := g x'

  by
    show gx' = x

    let gxR := p1.contravariant.R_in_map x' x ?xR

    case xR =>
      -- unfold flipRel
      exact xR

    exact gxR


-- instance (priority := 80) [p : Param α β cov con] : Param β α con cov :=
--   { R := flipRel p.R, covariant := p.contravariant, contravariant := p.covariant }

#check @Trale.Map0_arrow (p1 := ?_) (p2 := ?_)
-- have test1 : Param01 α α' := by infer_instance -- This fails



example : MapType.Map2a ≤ MapType.Map4 := by decide
example : ¬(MapType.Map4 ≤ MapType.Map2a) := by decide

#check
  let p : Map3 ?R := ?p
  p.toMap1

#check Array

#check default
example : ∀ a : α, @default _ (Inhabited.mk a) = a := by
  sorry


-- #check Trale.Map0_arrow (ParamModFin)
#check
  let p1 : Param03.{5} Nat String := ?p1
  let p2 : Param40.{1} Nat String := ?p2
  (Trale.Map4_arrow (p1 := p1) (p2 := p2)).R

#check cast_heq

  -- rename' a => c
  -- rename' a' => c'
  -- rename' aR => cR
