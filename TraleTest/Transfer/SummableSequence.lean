import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Attr

import Trale.Utils.TrAdvance
import TraleTest.Lemmas.SummableSequence

set_option trace.tr.utils true

namespace TraleTest.Transfer.SummableSequence
open TraleTest.Lemmas Trale

theorem sum_nnR_add : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_exact sum_xnnR_add
