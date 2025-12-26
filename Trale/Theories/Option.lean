import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Core.Related
import Trale.Utils.Extend
import Qq open Qq Lean

namespace Trale

universe u v x w w1 w2 w3

inductive R_option
  {α : Type u} {α' : Type u}
  (αR : α -> α' -> Sort w1)
   : (Option α) -> (Option α') -> Sort _ where

  | someR : (a : α) -> (a' : α') -> αR a a' -> R_option (α := α) (α' := α') αR (some a) (some a')
  | noneR : R_option αR none none

variable {α : Type u} {α' : Type u}

def Map0_option
  (p1 : Param00 α α')
  : Param00 (Option α) (Option α') := by
    tr_constructor

    exact R_option p1.R

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


-- instance [inst : Related α β] : Related (Option α) (Option β) where
--   mapCov := inst.mapCov
--   mapCon := .Map0

--   param := by
--     let cov := inst.mapCov
--     let contra := inst.mapCon
--     have p : Param cov contra α β := inst.param

--     show Param cov .Map0 (Option α) (Option β)
--     match cov with
--     | .Map0 =>
--       apply Map0_option
--       apply p.forget (h2 := _)
--       cases contra <;> decide

--     | .Map1 =>
--       apply Map1_option
--       apply p.forget (h2 := _)
--       cases contra <;> decide

--     | .Map2a =>
--       apply Map2a_option
--       apply p.forget (h2 := _)
--       cases contra <;> decide

--     | .Map2b =>
--       apply Map2b_option
--       apply p.forget (h2 := _)
--       cases contra <;> decide

--     | .Map3 =>
--       apply Map3_option
--       apply p.forget (h2 := _)
--       cases contra <;> decide

--     | .Map4 =>
--       apply Map4_option
--       apply p.forget (h2 := _)
--       cases contra <;> decide
