import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

import TraleTest.Utils.Lemmas.SummableSequence

set_option trace.tr.utils true

theorem sum_nnR_add : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_by sum_xnnR_add

  -- FIXME: Why can't we use `show` or coercion to upgrade the type for this?
  suffices Param40
    (∀ (f g : seq_xnnR), Σ (f + g) = Σ f + Σ g)
    (∀ (u v : summable), Σ (u + v) = Σ u + Σ v) by
    exact this.forget

  tr_sorry sorry

#check
  let p : Param11 ?a ?b := ?p
  p.forget.right
