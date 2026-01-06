import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Theories.Sorts
import TraleTest.Lemmas.Modulo
import TraleTest.Lemmas.Zmod5
import Trale.Utils.TrAdvance
import Mathlib

open Trale

/-
# Listing 30
-/

-- Based on `trocq_gen_rewrite.v` from Trocq plugin in Rocq
-- (https://github.com/rocq-community/trocq)

@[trale]
theorem add_morph
  {m m' : Nat} (mR : m ≤ m')
  {n n' : Nat} (nR : n ≤ n')
  : m + n ≤ m' + n' :=
  Nat.add_le_add mR nR

theorem le_morph
  {m m' : Nat} (mR : m ≤ m')
  {n n' : Nat} (nR : n' ≤ n)
  : (m' ≤ n') → (m ≤ n) :=
  fun h =>
    Nat.le_trans (Nat.le_trans mR h) nR

@[trale]
def le01
  {m m' : Nat} (mR : m ≤ m')
  {n n' : Nat} (nR : n' ≤ n)
  : Param01.{0} (m ≤ n) (m' ≤ n')
  := by

  tr_from_map le_morph mR nR

theorem ipi_i (i : Nat)
  : i + i + i ≤ i + i + i := Nat.le_refl _


theorem ipi_manual (i j : Nat) (jiR : j ≤ i) (iiR : i ≤ i)
  : j + i + j ≤ i + i + i := by

  tr_by (ipi_i i)

  tr_flip
  apply le01

  · apply add_morph
    · apply add_morph
      · exact jiR
      · exact iiR
    · exact jiR
  · apply add_morph
    · apply add_morph
      · exact iiR
      · exact iiR
    · exact iiR

theorem ipi_manual_2 (i j : Nat) (jiR : j ≤ i) (iiR : i ≤ i)
  : j + i + j ≤ i + i + i := by

  tr_by (ipi_i i)

  tr_flip
  repeat first
    | apply le01
    | apply add_morph
    | assumption


open Lean Elab Tactic in
def test1 :  TacticM Unit := do

  let target ← Lean.Elab.Tactic.getMainTarget
  trace[tr.utils] s!"Before apply le01: {target}"
  try
    Lean.Elab.Tactic.evalTactic (←`(tactic| apply @le01))
  catch e =>
    trace[tr.utils] s!"Failed to apply le01: {←e.toMessageData.format}"


theorem ipi (i j : Nat) (jiR : j ≤ i) (iiR : i ≤ i)
  : j + i + j ≤ i + i + i := by

  tr_by (ipi_i i)

  -- Since aesop will simplify `i + i + i` to `True`, aesop will fail when
  -- applied to this goal. Hence we need to do the first step manually.
  tr_flip; apply le01

  tr_solve
  tr_solve
