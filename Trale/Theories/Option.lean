import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Utils.Extend
import Qq open Qq Lean

namespace Trale

/-!
# Parametricity for Option Types

This module defines parametric relations for option types `Option α`.
Two options are related if they are both `none` or both `some` with related values.

## The Option Relation

We define an inductive relation:
```
inductive R_option : Option α → Option α' → Sort _ where
  | someR : R a a' → R_option (some a) (some a')
  | noneR : R_option none none
```

This ensures:
- `none` relates only to `none`
- `some a` relates only to `some a'` when `a` relates to `a'`

## Map Instances

The map function is straightforward:
- `none ↦ none`
- `some a ↦ some (map a)`
-/

universe u v x w w1 w2 w3

/-- Inductive relation for option types.
    Relates none to none, and some to some when values are related. -/
inductive R_option
  {α : Type u} {α' : Type u}
  (αR : α -> α' -> Sort w1)
   : (Option α) -> (Option α') -> Sort _ where

  | someR : (a : α) -> (a' : α') -> αR a a' -> R_option (α := α) (α' := α') αR (some a) (some a')
  | noneR : R_option αR none none

variable {α : Type u} {α' : Type u}

/-- Base Param instance for options using the inductive relation. -/
def Map0_option
  (p1 : Param00 α α')
  : Param00 (Option α) (Option α') := by
    tr_constructor

    exact R_option p1.R

/-- Map for options: map the value if present, preserve none. -/
def Map1_option
  (p1 : Param10 α α')
  : Param10 (Option α) (Option α') := by
    tr_extend Map0_option p1

    intro ma
    exact match ma with
    | some a => some (p1.right a)
    | none => none

-- def extend_to_2a
--   (p1 : Param2a0.{_,_,w1} α α')
--   (base_constr : Param10.{_,_,w1} α α' -> Param10 γ γ')
--   (map_in_R : forall a b, p1.right a = b -> p1.R a b)
--   : Param2a
--   := by


/-- Map2a for options: equality of mapped options implies the option relation. -/
def Map2a_option
  (p1 : Param2a0 α α')
  : Param2a0 (Option α) (Option α') := by
    tr_extend Map1_option p1

    intro ma ma'
    match ma with
    | some a =>
      simp
      intro h
      rw [← h]
      apply R_option.someR

      apply p1.right_implies_R
      dsimp

    | none =>
      simp
      intro h
      rw [← h]
      exact R_option.noneR

def Map2b_option
  (p1 : Param2b0 α α')
  : Param2b0 (Option α) (Option α') := by
    tr_extend Map1_option p1

    intro ma ma' maR
    match maR with
    | R_option.noneR => rfl
    | R_option.someR a a' aR =>
      let h := p1.R_implies_right a a' aR
      simp
      exact p1.R_implies_right a a' aR

def Map3_option
  (p1 : Param30 α α')
  : Param30 (Option α) (Option α') := by
    tr_extend_multiple [Map2a_option p1, Map2b_option p1]

def Map4_option
  (p1 : Param40 α α')
  : Param40 (Option α) (Option α') := by
    tr_extend Map3_option p1

    intro ma ma' maR

    match maR with
    | .noneR => rfl
    | (.someR a a' aR : R_option p1.R (some a) (some a')) =>

      have h3 := p1.R_implies_rightK a a' aR
      rw [←h3]

      have h := p1.R_implies_right a a' aR
      simp at h

      subst h

      dsimp only [id_eq]
      congr
