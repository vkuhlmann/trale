import Trale.Theories.Flip
import Trale.Utils.Split
import TraleTest.Lemmas.TrAdvance

open Trale.Utils

def prop2a (p : Param10 α β) := ∀ (a : α) (b : β), p.right a = b → p.R a b

def prop2a_R
  {α : Type u} {β : Type v}
  (base : Param2a0.{w} β α)
  {R : α → β → Sort w}
  (conv : ∀ {a b}, Param10.{x} (base.R b a) (R a b))
  : Param10 (prop2a base.forget) (prop2a (flip1 base.forget conv).flip) := by

  repeat tr_advance
  -- tr_solve

def flip2a'
  {α : Type u} {β : Type v}
  (base : Param2a0.{w} β α)
  {R : α → β → Sort w}
  (conv : ∀ {a b}, Param10.{x} (base.R b a) (R a b))
  : Param02a.{w} α β := by
  tr_extend flip1 base conv

  let := prop2a_R base conv
  exact this.right base.right_implies_R

def prop2a_R_1
  (base : Param2a0.{w} β α)
  {R : α → β → Sort w}
  (conv : ∀ {a b}, Param10.{x} (base.R b a) (R a b))
  : Param10 (prop2a base.forget) (prop2a (flip1 base.forget conv).flip) := by

  -- dsimp [prop2a, flipRel]
  tr_intro b b' bR
  subst bR

  tr_intro a a' aR
  subst aR

  tr_intro h h' hR
  case p2 =>
    exact conv

  simp
  tr_from_map
  intro h
  exact h

-- def flip_Map2a

set_option trace.debug true
