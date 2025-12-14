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
import TraleTest.Lemmas.TrAdvance

-- Based on `trocq_gen_rewrite.v` from Trocq plugin in Rocq
-- (https://github.com/rocq-community/trocq)

set_option pp.universes true

-- @[trale]
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

-- @[trale]
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

macro "tr_test_1" : tactic => `(tactic|
  first
    | apply le01
    | apply add_morph
  )

add_aesop_rules 90% (by tr_test_1) (rule_sets := [trale])


-- FIXME: Why is tr_solve not working?
theorem ipi (i j : Nat) (jiR : j ≤ i) (iiR : i ≤ i)
  : j + i + j ≤ i + i + i := by

  tr_by (ipi_i i)

  tr_flip

  change Param01.{0} ((?m : ℕ) ≤ ?n) ((?m' : ℕ) ≤ ?n')
  set m := ?m
  set n := ?n
  set m' := ?m'
  set n' := ?n'

  -- tr_test_1
  -- apply le01
  -- tr_solve
  -- tr_solve
  -- tr_solve
  sorry
