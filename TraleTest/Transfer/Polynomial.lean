import Mathlib

-- #check Nat.Mod
#check CommMonoid

open Polynomial

-- https://people.bath.ac.uk/masjhd/Slides/SYNASC2024-PolyLean.pdf

noncomputable
example : Nat := by
  let p : Nat[X] := monomial 4 2

  refine p.sum ?_
  let x := 3

  exact fun y z => z * (y ^ x)

-- #eval 4 + 3
-- #eval (monomial 4 2 : Nat[X]).coeff 1


namespace Polynomial.Test1
variable {R : Type*} [Semiring R]

-- noncomputable
-- example : R[X] := by
--   let p : R[X] := monomial 4 2

--   refine p.sum ?_
