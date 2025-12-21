import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Lean.PrettyPrinter

import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Basic
import Trale.Utils.Normalize
import Trale.Utils.AddFlipped
import Trale.Theories.Flip
import Trale.Theories.Arrow
import Trale.Theories.Sorts

import Qq open Qq Lean
open Trale.Utils

namespace Trale

universe u u' v v' x w1 w2 w3

variable {α : Sort u} {α' : Sort u'} {β : α -> Sort v} {β' : α' -> Sort v'}

@[simp]
abbrev P1
  (P1_R_type : Sort u -> Sort u -> Sort w1)
  (α : Sort u) (α' : Sort u)
  := P1_R_type α α'

@[simp]
abbrev P2
  (P2_R_type : Sort v -> Sort v -> Sort w2)
  (β : α -> Sort v) (β' : α' -> Sort v)
  (p1_R : α -> α' -> Sort _)
  := forall (a : α) (a' : α'), p1_R a a' -> P2_R_type (β a) (β' a')

@[simp]
abbrev P3
  (P3_R_type : Sort _ -> Sort _ -> Sort w3)
  (β : α -> Sort v) (β' : α' -> Sort v')
  := P3_R_type (forall a, β a) (forall a', β' a')



def forallR
  (p1 : Param00 α α')
  (p2 : ∀ a a', p1.R a a' → Param00 (β a) (β' a'))
  : (∀ a, β a) -> (∀ a', β' a') -> Sort _
  := fun f f' =>
    forall a a' (aR: p1.R a a'), (p2 a a' aR).R (f a) (f' a')

def flipForallR
  (r : forallR p1 p2 f f')
  : forallR p1.flip (fun a a' aR => (p2 a' a aR).flip) f' f
  := fun a' a aR' => r a a' (flipR aR')

instance forallR_rel
  -- The order of α', α, β', β needs to be specified for
  -- tr_add_flipped to produce the correct flipped definition.
  {α' : Sort u'} {α : Sort u}
  {β' : α' → Sort v'} {β : α → Sort v}
  (p1 : Param00 α α')
  (p2 : ∀ a a', p1.R a a' → Param00 (β a) (β' a'))
  {f f'}
  : Param44 (forallR p1.flip (fun a a' aR => (p2 a' a aR).flip) f' f)
    (forallR p1 p2 f f') := by

  tr_from_involution flipForallR



def Map0_forall
  (p1 : Param00 α α')
  (p2 : ∀ (a : α) (a' : α'), p1.R a a' → Param00 (β a) (β' a'))
  : P3 Param00 β β' := by

  tr_constructor

  exact forallR p1 p2
  -- exact fun f f' =>
  --   forall a a' (aR: p1.R a a'), (p2 a a' aR).R (f a) (f' a')


def Map1_forall
  (p1 : Param02a α α')
  (p2 : ∀ (a : α) (a' : α'), p1.R a a' → Param10 (β a) (β' a'))
  : Param10 (∀ a, β a) (∀ a', β' a') := by

  tr_extend Map0_forall p1 (p2 . . .)

  intro f x'
  let x := p1.left x'
  let f' := (p2 x x' (p1.left_implies_R _ _ rfl)).right
  exact f' (f x)

def Map1_forall'
  {α α' : Sort u}
  {β : α → Sort v}
  {β' : α' → Sort v}
  (p1 : Param02a α α')
  (p2 : arrowR p1 (sortParam .Map1 .Map0).forget β β')
  := Map1_forall p1 p2


def Map2a_forall
  (p1 : Param04 α α')
  (p2 : forall (a : α) (a' : α'), p1.R a a' -> Param2a0 (β a) (β' a'))
  : Param2a0 (∀ a, β a) (∀ a', β' a')
  := by

  tr_extend Map1_forall p1 (p2 . . .)

  intro f f' mapFF'
  intro a a' aR

  apply (p2 a a' aR).right_implies_R

  dsimp at mapFF'
  subst mapFF'
  dsimp

  have := p1.R_implies_left a a' aR
  subst this
  congr
  -- show_term

  repeat exact (p1.R_implies_leftK _ _ _).symm

  -- congr

  -- have h := congrFun mapFF' a'

  -- have m : p1.contravariant.map a' = a := by
  --     exact p1.R_implies_left a a' aR

  -- have h2 := p1.contravariant.R_in_mapK
  -- specialize h2 a' a aR
  -- subst m
  -- have h3 : (p1.contravariant.map_in_R a' (p1.contravariant.map a')
  --           (Eq.refl (p1.contravariant.map a'))) = aR := by

  --   exact h2

  -- subst h3
  -- exact h

def Map2a_forall_flipped
  {α : Sort u} {α' : Sort u'}
  {β : α → Sort v}
  {β' : α' → Sort v'}
  (p1 : Param40 α α')
  (p2 : forall (a : α) (a' : α'), p1.R a a' -> Param02a (β a) (β' a'))
  : Param02a (∀ a, β a) (∀ a', β' a')
  -- := flip2a (Map2a_forall p1.flip (fun a a' aR => (p2 a' a aR).flip))
  := by
    apply flip2a

    intro f f'
    tr_sorry sorry
    sorry
    sorry

  -- flip2a (Map2a_forall sorry sorry)
  --   (R := forallR.{u,u',v,v'} p1 (p2 · · ·))
  --   sorry
  -- -- (by
  -- --       -- fun {f f'} => (forallR_rel sorry sorry).forget

  -- --       intro f f'
  -- --       let h := forallR_rel (f := f) (f' := f') (p1 := p1) (p2 := (p2 · · ·))
  -- --       dsimp at h

  -- --       exact (h.forget : Param10 _ _)
  -- --       -- sorry
  -- --     )

-- #check
--   let a := Map2a_forall ?p1 ?p2
--   by
--   unfold P3 at a
--   exact a


def Map2b_forall
  (p1 : Param02a α α')
  (p2 : forall (a : α) (a' : α'), p1.R a a' -> Param2b0 (β a) (β' a'))
  : P3 Param2b0 β β'
  := by

  tr_extend Map1_forall p1 (p2 . . .)

  intro f f'
  intro R

  funext a'
  let a : α := p1.left a'
  let aR := p1.left_implies_R a a' rfl

  exact (p2 a a' aR).R_implies_right (f a) (f' a') (R a a' aR)


def Map3_forall
  (p1 : Param04 α α')
  (p2 : forall (a : α) (a' : α'), p1.R a a' -> Param30 (β a) (β' a'))
  : Param30 (∀ a, β a) (∀ a', β' a')
  := by
  tr_extend_multiple [Map2a_forall p1 (p2 . . .), Map2b_forall p1 (p2 . . .)]


def Map4_forall
  (p1 : Param04 α α')
  (p2 : forall (a : α) (a' : α'), p1.R a a' -> Param40 (β a) (β' a'))
  : P3 Param40 β β'
  := by

  tr_extend Map3_forall p1 (p2 . . .)
  intro f f' fr
  funext a a' aR
  simp

  let Param_b := p2 a a' aR

  let b_mapK := Param_b.covariant.R_in_mapK (f a) (f' a') (fr a a' aR)
  apply Eq.symm
  apply Eq.trans b_mapK.symm

  rfl
