import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Whnf
import Trale.Utils.Basic
import Trale.Utils.AddFlipped
import Qq
import Trale.Theories.Flip

open Qq Lean Trale.Utils


-- set_option trace.profiler true
-- set_option trace.profiler.threshold 10
-- set_option trace.profiler.output.pp true

namespace Param_arrow

variable {α : Sort u} {α' : Sort u} {β : Sort v} {β' : Sort v}

def arrowR
  (p1 : Param00 α α')
  (p2 : Param00 β β')
  : (α → β) -> (α' → β') -> Sort _
  := fun f f' =>
    forall a a', p1.R a a' -> p2.R (f a) (f' a')

def flipArrowR
  (r : arrowR p1 p2 f f')
  : arrowR p1.flip p2.flip f' f
  := fun a' a aR' => r a a' (flipR aR')

instance arrowR_rel
  -- The order of α', α, β', β needs to be specified for
  -- tr_add_flipped to produce the correct flipped definition.
  {α' α : Sort u}
  {β' β : Sort v}
  [p1 : Param00 α α']
  [p2 : Param00 β β']
  {f f'}
  : Param44 (arrowR p1.flip p2.flip f' f) (arrowR p1 p2 f f') := by

  tr_from_involution flipArrowR



instance Map0_arrow
  [p1 : Param00 α α']
  [p2 : Param00 β β']
: Param00 (α → β) (α' → β') := by
  tr_constructor
  exact arrowR p1 p2

  -- exact fun f f' =>
  --   forall a a', p1.R a a' -> p2.R (f a) (f' a')

@[tr_add_flipped Param_arrow.arrowR_rel]
instance Map1_arrow
  [p1 : Param01 α α']
  [p2 : Param10 β β']
: Param10 (α → β) (α' → β') := by
  tr_extend Map0_arrow (p1 := p1) (p2 := p2)

  exact fun f => p2.right ∘ f ∘ p1.left


-- def Map1_arrow'
--   (p1 : Param01 α α')
--   (p2 : Param10 β β')
-- : Param10 (α -> β) (α' -> β') :=
--   MapToParam p1 p2 _ <| by
--     constructor

--     case map =>
--       exact MapFun p1 p2

@[tr_add_flipped Param_arrow.arrowR_rel]
instance Map2a_arrow
  [p1 : Param02b α α']
  [p2 : Param2a0 β β']
: Param2a0 (α → β) (α' → β') := by
  -- We cannot use instance inference, because the types (α, α', ..) are
  -- metavariables at this piont.
  tr_extend Map1_arrow (p1 := p1) (p2 := p2)

  intro f f' mapF -- f maps to f'
  intro x x' xR -- x and x' are related
  -- Goal: p2.R (f x) (f x')
  apply p2.right_implies_R
  subst mapF -- substitute f' away

  congr -- find the parts in the equality that still need to match up

  -- Goal: x = p1.left x'
  exact (p1.R_implies_left x x' xR).symm


  -- apply Eq.symm
  -- apply Eq.trans (congrFun mapF x').symm

  -- simp

  -- let mapAtoA' := (p1.R_implies_left x x') xR
  -- simp at mapAtoA'

  -- rw [mapAtoA']

-- (* (02a, 2b0) + funext -> 2b0 *)
@[tr_add_flipped Param_arrow.arrowR_rel]
instance Map2b_arrow
  [p1 : Param02a α α']
  [p2 : Param2b0 β β']
  : Param2b0 (α -> β) (α' -> β') := by

  tr_extend Map1_arrow (p1 := p1) (p2 := p2)

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

  tr_add_param_base param_base2 := Map2b_arrow (p1 := p1) (p2 := p2)
  tr_extend Map2a_arrow (p1 := p1) (p2 := p2) <;> tr_fill_from_hypothesis param_base2


-- (* (03, 30) + funext -> 30 *)
@[tr_add_flipped Param_arrow.arrowR_rel]
instance Map3_arrow
  [p1 : Param03 α α']
  [p2 : Param30 β β']
  : Param30 (α -> β) (α' -> β') :=
  by
  tr_extend_multiple [
    Map2a_arrow (p1 := p1) (p2 := p2),
    Map2b_arrow (p1 := p1) (p2 := p2)
  ]

-- (* (04(????), 40) + funext -> 40 *)
@[tr_add_flipped Param_arrow.arrowR_rel]
instance Map4_arrow
  [p1 : Param03 α α']
  [p2 : Param40 β β']
  : Param40 (α → β) (α' → β') := by
  tr_extend Map3_arrow (p1 := p1) (p2 := p2)

  /- Alternatively:

  ```lean
  have _ : Param30 β β' := p2
  tr_extend (inferInstance : Param30 (α -> β) (α' -> β'))
  ```

  But this gives problems because the inferInstance is not properly unfolded.
  -/

  -- case R_implies_rightK =>
  intro f f' fR
  funext a a' aR
  simp
  -- FIXME: Want to do this, but getting type mismatch:
  -- show p1.right_implies_R _ _ (p1.R_implies_right _ _ _) = fR a a' aR
  apply p2.R_implies_rightK
