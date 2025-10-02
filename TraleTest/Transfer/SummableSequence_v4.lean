import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

import TraleTest.Utils.Lemmas.SummableSequence


-- Code based on 'summable.v' example by Trocq Rocq plugin developers.

theorem sum_nnR_add : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_by sum_xnnR_add

  -- We use these Params
  let _ := param_summable_seq

  -- TODO: Make this work with infer_instance
  -- We need to use `propParam` instance for `Param Prop Prop`, not the
  -- instance defined by equality.
  let _ : Param00 Prop Prop := propParam.forget

  let eqParam : Param00 (xnnR → xnnR → Prop) (nnR → nnR → Prop) := by
    tr_split; tr_split

  -- Part 1: split the foralls
  tr_intro a a' aR
  tr_intro b b' bR

  -- Part 2: Relate rhs:  X  =  *X*
  --                            ___
  --
  tr_split_application' c c' cR by
    show tr.R (Σ a + Σ b) (Σ a' + Σ b')
    apply R_add_xnnR

    · show tr.R (Σ a') (Σ a)
      exact R_sum_xnnR a' a aR
    · show tr.R (Σ b') (Σ b)
      exact R_sum_xnnR b' b bR

  -- Part 3: Relate lhs:  *X*  =  X
  --                      ___
  --
  tr_split_application' d d' dR by
    show tr.R (Σ (a + b)) (Σ (a' + b'))
    apply R_sum_xnnR

    -- FIXME: Why is it the swapped order by default?
    -- show tr.R (a + b) (a' + b')
    show tr.R (a' + b') (a + b)
    apply seq_nnR_add

    · exact aR
    · exact bR

  show Param10 (d = c) (d' = c')
  -- Part 4: Relate eq:  X  *=*  X
  --                        ___
  --
  tr_split_application e e' eR by
    exact R_eq

  -- Part 5: Use relations to make the relation trivial
  --
  dsimp
  show Param10 (e d c) (e' d' c')

  /-
  By the Param rules of lambda abstraction and application, we can get the goal
  relation as:
  -/
  have goalTypeR : tr.R (e d c) (e' d' c') := eR d d' dR c c' cR
  /-
  This is a relation for the 'propParam' Param. I.e. `Param Prop Prop`.
  We use `instantiatePropR` to convert it to the Param between those types.
  -/
  exact (instantiatePropR goalTypeR).forget
