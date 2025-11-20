import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

import TraleTest.Lemmas.TrAdvance
import TraleTest.Lemmas.SummableSequence

set_option trace.tr.utils true

namespace TraleTest.Transfer.SummableSequence
open TraleTest.Lemmas

theorem sum_eq_reverse_sum_seq_xnnR
  (a b c : seq_xnnR)
  : a + b + c = c + b + a := by
  funext i

  change a i + b i + c i = c i + b i + a i
  dsimp [HAdd.hAdd, Add.add, add_seq_xnnR, add_xnnR]

  match a i with
  | .inf => cases b i; cases c i; rfl; rfl; simp
  | .fin a' =>

  match b i with
  | .inf => cases c i; rfl; rfl
  | .fin b' =>

  match c i with
  | .inf => rfl
  | .fin c' =>

  show xnnR.fin (a' + b' + c') = xnnR.fin (c' + b' + a')

  rw [AddCommMagma.add_comm _ c']
  rw [AddCommMagma.add_comm a' b']
  simp [AddSemigroup.add_assoc]


theorem sum_eq_reverse_sum_summable
  (a b c : summable)
  : a + b + c = c + b + a := by

  revert a b c
  tr_by sum_eq_reverse_sum_seq_xnnR

  let _ : Param00 Prop Prop := propParam.forget

  tr_intro a a' aR
  tr_intro b b' bR
  tr_intro c c' cR

  -- rewrite [Eq.symm (a := a + b + c) (b := c + b + a)]
  -- rewrite [Eq.symm (a := a' + b' + c') (b := c' + b' + a')]

  -- apply Param.flip


  -- (refine (instantiatePropR ?_).forget;
  -- --tr_step_rel
  -- )
  tr_advance


  -- rw [Eq.symm ]

  -- apply Trale.Utils.flipR'

  -- apply @R_eq _ _ param_summable_NNR_seq


  show tr.R (c + b + a) (c' + b' + a')
  · apply seq_nnR_add
    apply seq_nnR_add
    all_goals assumption

  rename _ => rhsR
  -- rw [←aR]
  -- dsimp

  -- subst aR

  tr_advance
  show tr.R (_ + b' + c') (_ + b + c)
  · apply seq_nnR_add
    apply seq_nnR_add
    all_goals assumption

  rename _ => lhsR
  -- tr_whnf at aR

  -- rw [←aR]
  -- clear aR

  -- rw [aR]
  -- simp


  -- subst aR

  tr_from_map
  -- rename _ => d

  intro h

  rw [h] at lhsR
  tr_whnf at lhsR rhsR
  dsimp at lhsR rhsR

  have h2 := Eq.trans lhsR rhsR.symm

  -- rw [←rhsR] at lhsR
  apply param_summable_seq_injective _ _ h2





  -- tr_advance


  -- let x := @R_eq _ _ param_summable_seq.forget
  -- intro d d' dR
  -- intro e e' eR
  -- intro h

  -- specialize x d' d dR e' e eR
  -- tr_whnf at x
  -- change

  -- tr_whnf




  -- tr_from_map
  -- intro h
  -- subst aR
  -- subst aR




  -- repeat first
  --   | apply R_add_xnnR
  --   | refine R_sum_xnnR _ _ ?_
  --   | exact R_eq
  --   | apply seq_nnR_add
  --   | tr_advance

  -- focus skip -- Assert goals to be done
  -- all_goals sorry
