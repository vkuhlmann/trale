import Trale.Core.Param
open Trale

/-
# Listing 6
-/

theorem injectiveFunctionInvert'
  (p :  Param42b A B)
  (x : A)
  : p.left (p.right x) = x := by

  let x' := p.forget.right' x
  let xR : p.R x x' := p.right_implies_R x x' rfl

  show p.left x' = x
  exact p.R_implies_left x x' xR

/-
# Original (anonymous) listing:
-/

theorem injectiveFunctionInvert
  (p :  Param .Map4 .Map2b A B)
  (x : A)
  : p.contravariant.map (p.covariant.map x) = x := by

  let x' := p.covariant.map x
  let xR : p.R x x' := p.covariant.map_in_R x x' rfl

  show p.contravariant.map x' = x
  exact p.contravariant.R_in_map x' x xR
