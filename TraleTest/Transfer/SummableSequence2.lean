import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.TrAdvance

import TraleTest.Lemmas.SummableSequence2

import Mathlib
import Mathlib.Topology.Algebra.InfiniteSum.Defs

set_option trace.tr.utils true

namespace TraleTest.Transfer.SummableSequence
open NNReal ENNReal
open TraleTest.Transfer.SummableSequence2
open Trale


#check tsum
#check ⊤


open Classical in
theorem sum_xnnR_add (u v : ℕ → ℝ≥0) :
  ∑'' i, (u + v) i = (∑'' i, u i) + (∑'' i, v i) := by

  repeat rw [tsum_extended_def]
  dsimp
  split <;> split <;> split

  rename_i h_fg h_f h_g

  all_goals sorry


  -- if h1 : Summable f then
  --   sorry
  -- else

  --   sorry

#check ENNReal

-- #check
--   let u : ℕ → ℝ≥0 := ?u
--   (∑'' i, u i : ℝ≥0∞)

-- #check (5 : ℝ≥0∞)

theorem sum_nnR_add
: ∀ (u v : summable),
  ∑' i, (u + v) i = (∑' i, u i) + (∑' i, v i) := by
  tr_exact sum_xnnR_add

  -- tr_by sum_xnnR_add

  -- -- let := propParam.toBottom

  -- tr_solve

  -- repeat first
  --   | apply R_add_ENNReal
  --   | apply R_summable
  --   | apply R_add_summable
  --   -- | apply R_eq
  --   | tr_advance
