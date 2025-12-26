import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

import TraleTest.Lemmas.SummableSequence

open Trale

open TraleTest.Lemmas

-- set_option trace.tr.utils true

def someProjection (b : Bool) : xnnR := match b with
  | true => .fin 5
  | false => .fin 1


def someProjection2 (b : Bool) : nnR := match b with
  | true => 5
  | false => 1

def someTest (b : Bool) : nnR := by
  revert b
  tr_by someProjection

  tr_split

  -- tr_intro b b' bR
  -- sorry

def someNumber := someProjection2 true

def typeYielder : Bool → Type := (if . then String else List Nat)
def typeYielder2 (b : Bool) (n : Nat) : Type := if b then String else Fin n
def typeYielder3 (n : Nat) : Type := (if n > 0 then (String × String) else List Nat)

def someFunc : Bool → Nat → String := (
  match ., . with
  | false, n => s!"{n}"
  | true, n => s!"<{n}>"
  )

def basedOn (b : xnnR) : (typeYielder true) := "abc" -- s!"{repr b}"

set_option pp.universes true in
def someNumber2 (a : nnR) : (typeYielder3 4) := by
  revert a

  let _ : Param02a Bool Nat := by
    tr_constructor

    intro b n
    exact b = (n > 0)

    -- 0


    -- 1
    · exact (· > 0)
    · simp

  let _ : Param00 (Bool -> Type) (Nat -> Type) := by
    tr_split


  tr_by basedOn
  tr_split'

  case p1 =>
    infer_instance

  show Param10.{1, 1, 1} (typeYielder true) (typeYielder3 4)
  tr_split_application

  sorry
  sorry
  sorry



  -- case aR =>
  --   tr_whnf

  --   decide

  -- intro a a' aR

  -- tr_split_application

  -- case p1 =>

  --   tr_split'
  --   infer_instance

  --   exact sortParam



  -- case aR =>
  --   tr_whnf
  --   intro b b' bR
  --   tr_whnf
  --   show typeYielder b = typeYielder3 b'

  --   have bR : b = (b' > 0) := bR

  --   unfold typeYielder typeYielder3

  --   cases b

  --   case false =>
  --     simp
  --     intro h
  --     exfalso

  --     have h2 := (Eq.mpr bR) h
  --     simp at h2

  --   case true =>
  --     simp
  --     simp at bR
  --     omega

  -- intro b b' bR
  -- dsimp



  --   if b then
  --     sorry













  -- case p1 =>


  -- sorry
  -- a a' aR by

  --   tr_whnf
  --   rfl









  -- tr_split'
  -- case p2 =>
  --   -- exact sortParam
  --   exact indent

  -- tr_intro a a' aR
