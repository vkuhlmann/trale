import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command

import Trale.Core.Param
import Trale.Utils.Extend

import Qq open Qq Lean

namespace Param_prod

universe u v x w w1 w2 w3

variable {α : Type u} {α' : Type u} {β : Type v} {β' : Type v}
variable {αR : α -> α' -> Sort w1}
variable {βR : β -> β' -> Sort w2}

structure R_prod
  (αR : α -> α' -> Sort w1)
  (βR : β -> β' -> Sort w2)
  (r1 : α × β) (r2 : α' × β') : Sort (max (u+1) (v+1) w1 w2) where
  aR : αR r1.fst r2.fst
  bR : βR r1.snd r2.snd

def tuple_eq_split_1
  {a a' : α}
  {b b' : β}
  (h : (a, b) = (a', b'))
  : a = a' := by
    simp at h
    exact h.1

def tuple_eq_split_2
  {a a' : α}
  {b b' : β}
  (h : (a, b) = (a', b'))
  : b = b' := by
    simp at h
    exact h.2


theorem R_prod_eq
  {αR : α -> α' -> Sort w1}
  {βR : β -> β' -> Sort w2}
  {r1 : α × β} {r2 : α' × β'}
  (v1 : R_prod αR βR r1 r2)
  (v2 : R_prod αR βR r1 r2)

  (h1 : v1.aR = v2.aR)
  (h2 : v1.bR = v2.bR)

  : v1 = v2 := by
    cases v1
    cases v2
    simp
    constructor
    · exact h1
    · exact h2

theorem R_prod_eq_helper
  (αR : α -> α' -> Sort w1)
  (βR : β -> β' -> Sort w2)
  (a : α) (b : β) (a' : α') (b' : β')

  (r1 : R_prod αR βR (a, b) (a', b'))
  (r2 : R_prod αR βR (a, b) (a', b'))
  :
  (r1.aR = r2.aR) -> (r1.bR = r2.bR) -> r1 = r2 := by
    intro e1 e2
    match r1, r2 with
    | ⟨aR1, bR1⟩, ⟨aR2, bR2⟩ =>
      simp
      exact ⟨e1, e2⟩


def Map0_prod
  (p1 : Param00 α α')
  (p2 : Param00 β β')
  : Param00 (α × β) (α' × β') := by
  tr_constructor

  case R =>
    exact R_prod (αR := p1.R) (βR := p2.R)


def Map1_prod
  (p1 : Param10.{w1} α α')
  (p2 : Param10.{w2} β β')
  : Param10 (α × β) (α' × β') := by
  tr_extend Map0_prod p1 p2

  intro (a, b)
  exact (p1.right a, p2.right b)


def Map2a_prod
  (p1 : Param2a0 α α')
  (p2 : Param2a0 β β')
  : Param2a0 (α × β) (α' × β') := by

  tr_extend Map1_prod p1 p2

  simp
  intro x x' h

  constructor
  · exact p1.right_implies_R x.fst x'.fst (tuple_eq_split_1 h)
  . exact p2.right_implies_R x.snd x'.snd (tuple_eq_split_2 h)


def Map2b_prod
  (p1 : Param2b0 α α')
  (p2 : Param2b0 β β')
  : Param2b0 (α × β) (α' × β') := by

  tr_extend Map1_prod p1 p2

  intro (a, b) (a', b')
  intro R
  simp

  constructor
  · exact p1.R_implies_right a a' R.aR
  . exact p2.R_implies_right b b' R.bR

def Map3_prod
  (p1 : Param30 α α')
  (p2 : Param30 β β')
  : Param30 (α × β) (α' × β') := by

  tr_extend_multiple [
    Map2a_prod p1 p2,
    Map2b_prod p1 p2,
  ]


def Map4_prod
  (p1 : Param40 α α')
  (p2 : Param40 β β')
  : Param40 (α × β) (α' × β') := by

  tr_extend Map3_prod p1 p2

  intro (a, b) (a', b') r
  simp

  apply R_prod_eq
  case h1 =>
    exact p1.covariant.R_in_mapK a a' r.aR

  case h2 =>
    exact p2.covariant.R_in_mapK b b' r.bR
