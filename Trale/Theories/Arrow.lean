import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Whnf
import Qq open Qq Lean

-- DNC, > 6 minutes

-- 8 seconds
-- 6 seconds
-- 2 seconds


-- set_option trace.profiler true
-- set_option trace.profiler.threshold 10
-- set_option trace.profiler.output.pp true

namespace Param_arrow

variable {α : Sort u} {α' : Sort u} {β : Sort v} {β' : Sort v}


instance Map0_arrow
  (p1 : Param00 α α')
  (p2 : Param00 β β')
: Param00 (α → β) (α' → β') := by
  tr_constructor

  exact fun f f' =>
    forall a a', p1.R a a' -> p2.R (f a) (f' a')


instance Map1_arrow
  (p1 : Param01 α α')
  (p2 : Param10 β β')
: Param10 (α → β) (α' → β') := by
  tr_extend Map0_arrow p1 p2

  exact fun f => p2.right ∘ f ∘ p1.left


-- def Map1_arrow'
--   (p1 : Param01 α α')
--   (p2 : Param10 β β')
-- : Param10 (α -> β) (α' -> β') :=
--   MapToParam p1 p2 _ <| by
--     constructor

--     case map =>
--       exact MapFun p1 p2


instance Map2a_arrow
  (p1 : Param02b α α')
  (p2 : Param2a0 β β')
: Param2a0 (α → β) (α' → β') := by
  tr_extend Map1_arrow p1 p2

  intro f f' mapF

  -- Goal: ∀ (a : α) (a' : α'), p1.R a a' → p2.R (f a) (f' a')
  intro x x' xR
  apply p2.right_implies_R
  subst mapF
  congr

  -- Goal: x = p1.left x'
  exact (p1.R_implies_left x x' xR).symm


  -- apply Eq.symm
  -- apply Eq.trans (congrFun mapF x').symm

  -- simp

  -- let mapAtoA' := (p1.R_implies_left x x') xR
  -- simp at mapAtoA'

  -- rw [mapAtoA']


-- (* (02a, 2b0) + funext -> 2b0 *)
instance Map2b_arrow
  (p1 : Param02a α α')
  (p2 : Param2b0 β β')
  : Param2b0 (α -> β) (α' -> β') := by

  tr_extend Map1_arrow p1 p2

  intro f f'
  intro relH
  apply funext
  intro a'

  apply p2.R_implies_right
  apply relH
  apply p1.left_implies_R
  simp

-- (* (03, 30) + funext -> 30 *)
instance Map3_arrow'
  (p1 : Param03 α α')
  (p2 : Param30 β β')
  : Param30 (α -> β) (α' -> β') :=
  by

  tr_add_param_base param_base2 := Map2b_arrow p1 p2
  tr_extend Map2a_arrow p1 p2 <;> tr_fill_from_hypothesis param_base2


-- (* (03, 30) + funext -> 30 *)
instance Map3_arrow
  (p1 : Param03 α α')
  (p2 : Param30 β β')
  : Param30 (α -> β) (α' -> β') :=
  by
  tr_extend_multiple [Map2a_arrow p1 p2, Map2b_arrow p1 p2]


-- (* (04(????), 40) + funext -> 40 *)
instance Map4_arrow
  (p1 : Param03 α α')
  (p2 : Param40 β β')
  : Param40 (α -> β) (α' -> β') := by
  tr_extend Map3_arrow p1 p2

  -- case R_implies_rightK =>
  intro f f'
  -- simp [MapR, Map2a_arrow, Map2b_arrow]
  intro
  funext a a' p1H
  simp
  apply p2.R_implies_rightK
