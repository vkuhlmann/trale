import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Whnf
import Trale.Utils.Normalize
import Trale.Utils.Glueing
import Trale.Utils.ParamFromFunction
import Qq open Qq Lean

namespace Trale

open Trale.Utils

def flip0
  {α : Sort u} {β : Sort v}
  (base : Param00.{w} β α)
  {R : α → β → Sort w}
  (_ : ∀ {a b}, Param00.{x} (base.R b a) (R a b))
  : Param00.{w} α β := by

  tr_constructor
  exact R

def flip1
  {α : Sort u} {β : Sort v}
  (base : Param10.{w} β α)
  {R : α → β → Sort w}
  (_ : ∀ {a b}, Param10.{x} (base.R b a) (R a b))
  : Param01.{w} α β := by

  tr_constructor
  exact R
  exact base.right

def flip2a
  -- Alpha needs to have an explicit universe level, else it
  -- will become a Type.
  -- FIXME: Why does it become a Type without?
  {α : Sort u} {β : Sort v}
  (base : Param2a0.{w} β α)
  {R : α → β → Sort w}
  (conv : ∀ {a b}, Param10.{x} (base.R b a) (R a b))
  : Param02a.{w} α β := by
  tr_extend flip1 base conv

  exact (conv.right $ base.right_implies_R . . .)

def flip2b
  {α : Sort u} {β : Sort v}
  (base : Param2b0.{w} β α)
  {R : α → β → Sort w}
  (conv : ∀ {a b}, Param11.{x} (base.R b a) (R a b))
  : Param02b.{w} α β := by

  tr_extend flip1 base conv.forget

  exact (base.R_implies_right . . $ conv.left .)

def flip3
  {α : Sort u} {β : Sort v}
  (base : Param30.{w} β α)
  {R : α → β → Sort w}
  (conv : ∀ {a b}, Param11.{x} (base.R b a) (R a b))
  : Param03.{w} α β := by

  tr_extend_multiple [flip2a base conv.forget, flip2b base conv.forget]

def flip4
  {α : Sort u} {β : Sort v}
  (base : Param40.{w} β α)
  {R : α → β → Sort w}
  (conv : ∀ {a b}, Param2b2a.{x} (base.R b a) (R a b))
  : Param04.{w} α β := by

  tr_extend flip3 base conv.forget

  intro a a' aR
  let aR' := conv.left aR
  let aRR := conv.forget.left_implies_R aR' aR rfl

  let unique_aR' := base.R_implies_rightK a a' aR'

  have : conv.right aR' = aR :=
    conv.forget.R_implies_right _ _ aRR

  rw [←this, ←unique_aR']
  rfl
