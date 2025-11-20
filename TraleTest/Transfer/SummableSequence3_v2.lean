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

  tr_advance

  show tr.R (c + b + a) (c' + b' + a')
  · apply seq_nnR_add
    apply seq_nnR_add
    all_goals assumption

  tr_advance
  show tr.R (_ + b' + c') (_ + b + c)
  · apply seq_nnR_add
    apply seq_nnR_add
    all_goals assumption

  tr_advance
  · tr_advance; dsimp
    tr_advance; dsimp
    apply R_eq_seq_xnnR_summable
    tr_advance
    tr_advance

  tr_advance
  tr_advance

  -- let _ := param_summable_seq_injective
  -- (refine (instantiatePropR ?_).forget)

  -- apply R_eq_seq_xnnR_summable
  -- assumption
  -- assumption
