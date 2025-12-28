import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Theories.Sorts
import TraleTest.Lemmas.Modulo
import TraleTest.Lemmas.Zmod5
import Trale.Utils.TrAdvance
import Mathlib

open Trale

-- Based on `trocq_gen_rewrite.v` from Trocq plugin in Rocq
-- (https://github.com/rocq-community/trocq)

-- set_option pp.universes true

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


open Lean Elab Tactic in
macro "tr_test_1" : tactic => `(tactic|
  first
    -- | apply add_morph
    | ((run_tac
        test1

        -- let target ← Lean.Elab.Tactic.getMainTarget
        -- trace[tr.utils] s!"Before apply le01: ${target}"
        -- try
        --   Lean.Elab.Tactic.evalTactic (←`(tactic| apply le01))
        -- catch e =>
        --   trace[tr.utils] s!"Failed to apply le01: ${e}"

      ); fail "Message")
    | (
      apply le01;
      run_tac
        trace[tr.utils] s!"Successfully applied le01"
    )
    | (run_tac
        trace[tr.utils] s!"After failed apply le01"; fail "Message")
  )

-- add_aesop_rules 90% (by tr_test_1) (rule_sets := [trale])


set_option trace.debug true
set_option trace.tr.utils true

-- FIXME: Why is tr_solve not working?
theorem ipi (i j : Nat) (jiR : j ≤ i) (iiR : i ≤ i)
  : j + i + j ≤ i + i + i := by

  tr_by (ipi_i i)

  tr_flip
  -- tr_advance

  -- change Param01.{0} ((?m : Nat) ≤ ?n) ((?m' : Nat) ≤ ?n')
  -- set m := ?m
  -- set n := ?n
  -- set m' := ?m'
  -- set n' := ?n'

  -- tr_test_1
  apply le01
  tr_solve
  aesop? (rule_sets := [trale])
  -- tr_solve
  -- tr_solve
  -- sorry
