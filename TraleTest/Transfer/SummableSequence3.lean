import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Utils.Attr

import TraleTest.Lemmas.TrAdvance
import TraleTest.Lemmas.SummableSequence2

set_option trace.tr.utils true

namespace TraleTest.Transfer.SummableSequence2
open TraleTest.Lemmas ENNReal NNReal Trale.Attr

#eval
  let p : ℕ := 4
  (p : ℝ)


example : Param2a0 (ℝ≥0∞ → ℝ≥0∞ → Prop) (ℝ≥0 → ℝ≥0 → Prop) := by
  -- refine ?subgoals


  focus
  ((first
  | apply (fun p1 p2 => Trale.Map0_arrow (p1 := p1) (p2 := p2))
  | apply (fun p1 p2 => Trale.Map1_arrow (p1 := p1) (p2 := p2))
  | apply (fun p1 p2 => Trale.Map2a_arrow (p1 := p1) (p2 := p2))
  | apply (fun p1 p2 => Trale.Map2b_arrow (p1 := p1) (p2 := p2))
  | apply (fun p1 p2 => Trale.Map3_arrow (p1 := p1) (p2 := p2))
  | apply (fun p1 p2 => Trale.Map4_arrow (p1 := p1) (p2 := p2))
  ); case' p1 => skip -- Fix goal ordering
  )

  -- tr_split_arrow
  infer_instance

  -- focus
  -- ((first
  -- | apply (fun p1 p2 => Trale.Map0_arrow (p1 := p1) (p2 := p2))
  -- | apply (fun p1 p2 => Trale.Map1_arrow (p1 := p1) (p2 := p2))
  -- | apply (fun p1 p2 => Trale.Map2a_arrow (p1 := p1) (p2 := p2))
  -- | apply (fun p1 p2 => Trale.Map2b_arrow (p1 := p1) (p2 := p2))
  -- | apply (fun p1 p2 => Trale.Map3_arrow (p1 := p1) (p2 := p2))
  -- | apply (fun p1 p2 => Trale.Map4_arrow (p1 := p1) (p2 := p2))
  -- ); case' p1 => skip -- Fix goal ordering
  -- )
  tr_split_arrow

  -- infer_instance

  -- tr_split_arrow
  -- infer_instance

  -- tr_split_arrow
  infer_instance

  exact (Trale.sortParam' .Map1 .Map0).forget


theorem sum_eq_reverse_sum_seq
  (a b c : ℕ → ℝ≥0)
  : a + b + c = c + b + a := by
  funext i
  change a i + b i + c i = c i + b i + a i

  rw [AddCommMagma.add_comm _ (c _)]
  rw [AddCommMagma.add_comm (a _) (b _)]
  simp [AddSemigroup.add_assoc]

#tr_add_translations_from_instances
#tr_translate ∀ (a b c : summable), (a + b + c = c + b + a)

#check summable
#check ℕ → ℝ≥0

set_option pp.all true in
theorem sum_eq_reverse_sum_summable
  (a b c : summable)
  : a + b + c = c + b + a := by

  revert a b c
  -- trale

  -- tr_sorry sorry
  -- sorry



  tr_by sum_eq_reverse_sum_seq

  let _ : Param00 Prop Prop := Trale.propParam.forget
  repeat first
    | apply R_eq_seq_summable
    | apply R_add_summable
    | tr_advance
