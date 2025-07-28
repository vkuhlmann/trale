import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application

import TraleTest.Utils.Lemmas.SummableSequence

set_option trace.tr.utils true

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
  tr_split_application c c' cR by
    unfold extend

    show .fin (Σ a' + Σ b') = Σ a + Σ b

    have aF : seq_extend a' = a := tr.R_implies_map a' a aR
    have bF : seq_extend b' = b := tr.R_implies_map b' b bR

    subst aF bF

    repeat rw [summationHomeo]
    rw [add_xnnR_homeo]

  -- Part 3: Relate lhs:  *X*  =  X
  --                      ___
  --
  tr_split_application d d' dR by
    show .fin (Σ (a' + b')) = Σ (a + b)

    -- If you change this to a 'let', the `subst` won't work because it will see
    -- it as a hypothesis instead of an equality.
    have aF : seq_extend a' = a := tr.R_implies_map a' a aR
    have bF : seq_extend b' = b := tr.R_implies_map b' b bR

    subst aF bF

    have h1 : seq_extend a'.seq + seq_extend b'.seq = seq_extend (a' + b').seq := by
      congr

    rw [h1]
    rw [summationHomeo]

  show Param10 (d = c) (d' = c')

  -- Part 4: Relate eq:  X  *=*  X
  --                        ___
  --
  tr_split_application e e' eR by
    dsimp [inferInstance, eqParam, Param_arrow.Map0_arrow, propParam]

    intro x x' xR
    intro y y' yR

    show x = y → x' = y'

    rw [←tr.R_implies_map x x' xR]
    rw [←tr.R_implies_map y y' yR]

    exact congrArg _

  -- Part 5: Use relations to make the relation trivial
  --
  show Param10 (e d c) (e' d' c')
  dsimp [inferInstance, eqParam, Param_arrow.Map0_arrow, propParam] at eR

  tr_from_map
  show e d c → e' d' c'

  exact eR d d' dR c c' cR
