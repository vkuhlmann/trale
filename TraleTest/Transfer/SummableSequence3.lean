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
open TraleTest.Lemmas ENNReal NNReal Trale.Attr Trale

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

set_option pp.all true in
theorem sum_eq_reverse_sum_summable
  (a b c : summable)
  : a + b + c = c + b + a := by

  revert a b c
  tr_exact sum_eq_reverse_sum_seq
