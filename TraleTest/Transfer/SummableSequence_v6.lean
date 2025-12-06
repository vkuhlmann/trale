import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

import TraleTest.Lemmas.SummableSequence
open TraleTest.Lemmas Trale

-- Code based on 'summable.v' example by Trocq Rocq plugin developers.

theorem sum_nnR_add : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_by sum_xnnR_add

  -- Part 1: split the foralls
  tr_intro a a' aR
  tr_intro b b' bR

  apply instantiatePropR'
  apply R_eq'


  -- Part 2: Relate lhs:  *X*  =  X
  --                      ___
  --
  ·
    show tr.R (Σ (a + b)) (Σ (a' + b'))
    apply R_sum_xnnR

    -- FIXME: Why is it the swapped order by default?
    -- show tr.R (a + b) (a' + b')
    show tr.R (a' + b') (a + b)
    apply seq_nnR_add

    · exact aR
    · exact bR


  -- Part 3: Relate rhs:  X  =  *X*
  --                            ___
  --
  ·
    show tr.R (Σ a + Σ b) (Σ a' + Σ b')
    apply R_add_xnnR

    · show tr.R (Σ a') (Σ a)
      exact R_sum_xnnR a' a aR
    · show tr.R (Σ b') (Σ b)
      exact R_sum_xnnR b' b bR

-- Minimal
theorem sum_nnR_add_minimal : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_by sum_xnnR_add

  tr_intro _ _ aR
  tr_intro _ _ bR

  apply instantiatePropR'
  apply R_eq'

  · apply R_sum_xnnR
    apply seq_nnR_add
    · exact aR
    · exact bR

  · apply R_add_xnnR
    · exact R_sum_xnnR _ _ aR
    · exact R_sum_xnnR _ _ bR
