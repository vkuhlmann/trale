import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Whnf
import Trale.Utils.Basic
import Trale.Utils.Normalize
import Trale.Utils.AddFlipped
import Qq

open Qq Lean Trale.Utils

namespace Trale

/-
In Trocq plugin:

```coq
Definition R_trans {A B C : Type} (R1 : A -> B -> Type) (R2 : B -> C -> Type) : A -> C -> Type :=
  fun a c => {b : B & R1 a b * R2 b c}.
```
-/

def transR
  {β : Sort u}
  {α : Sort v}
  {γ : Sort w}
  (p1 : Param00 α β)
  (p2 : Param00 β γ)
  : α → γ → Sort _
  :=
  fun a c => Σ' b, p1.R a b ×' p2.R b c

def flipTransR
  {p1 : Param00 α β}
  {p2 : Param00 β γ}
  (r : transR p1 p2 a c)
  : transR p2.flip p1.flip c a
  := match r with
    | ⟨b, abR, bcR⟩ =>
      ⟨b, flipR bcR, flipR abR⟩

instance R_flip_trans
  {β α γ}
  [p1 : Param00 α β]
  [p2 : Param00 β γ]
  {a c}
  : Param44 (transR p2.flip p1.flip c a) (transR p1 p2 a c) := by

  tr_from_involution flipTransR


def Map0_trans
  (p1 : Param00 α β)
  (p2 : Param00 β γ)
  : Param00 α γ := by
  tr_constructor

  exact transR p1 p2

  -- intro a c
  -- exact Σ' b, p1.R a b ×' p2.R b c

def Map1_trans
  (p1 : Param10 α β)
  (p2 : Param10 β γ)
  : Param10 α γ := by
  tr_extend Map0_trans p1 p2.forget

  exact p2.right ∘ p1.right

def Param01_trans
  (p1 : Param01 α β)
  (p2 : Param01 β γ)
  : Param01 α γ := by

  apply flip1 (Map1_trans p2.flip p1.flip)

  intro a c
  exact
    (
      R_flip_trans (a := a) (c := c) (p1 := p1.forget) (p2 := p2.forget)
    ).forget


def Map2a_trans
  (p1 : Param2a0 α β)
  (p2 : Param2a0 β γ)
  : Param2a0 α γ := by
  tr_extend Map1_trans p1 p2.forget

  dsimp
  intro a c acF

  let b := p1.right a
  let abR := p1.right_implies_R a b (by rfl)
  let bcR := p2.right_implies_R b c (by congr)

  /-
  Type mismatch
    (b, abR, bcR)
  has type
    β × Param.R MapType.Map2a MapType.Map0 a b × Param.R MapType.Map2a MapType.Map0 b c
  but is expected to have type
    (b : β) ×' p1.1 a b ×' Param.R MapType.Map2a MapType.Map0 b c

  -- exact (b, abR, bcR)
  -/

  exact ⟨b, abR, bcR⟩

def Param02a_trans
  (p1 : Param02a α β)
  (p2 : Param02a β γ)
  : Param02a α γ := by

  apply flip2a (Map2a_trans p2.flip p1.flip)

  intro a c
  exact
    (
      R_flip_trans (a := a) (c := c) (p1 := p1.forget) (p2 := p2.forget)
    ).forget

def Map2b_trans
  (p1 : Param2b0 α β)
  (p2 : Param2b0 β γ)
  : Param2b0 α γ := by
  tr_extend Map1_trans p1 p2.forget

  dsimp
  intro a c acR
  have ⟨b, abR, bcR⟩ := acR

  show tr.map (tr.map a) = c

  have abF := tr.R_implies_map _ _ abR
  have bcF := tr.R_implies_map _ _ bcR

  subst bcF
  subst abF
  rfl

def Map3_trans
  (p1 : Param30 α β)
  (p2 : Param30 β γ)
  : Param30 α γ := by
  tr_extend_multiple [Map2a_trans p1 p2.forget, Map2b_trans p1 p2.forget]

theorem Map2b_prop1
  (p1 : Param2b0 α α')
  (aR : p1.R a a')
  : p1.right a = a' := by

  exact p1.R_implies_right _ _ aR

theorem Map2b_prop2
  (p1 : Param2b0 α β)
  (ab1R : p1.R a b1)
  (ab2R : p1.R a b2)
  : b1 = b2 := by

  have ab1F := tr.R_implies_map _ _ ab1R
  have ab2F := tr.R_implies_map _ _ ab2R

  subst ab1F ab2F
  rfl

-- set_option diagnostics true

-- @[tr_add_flipped Trale.R_flip_trans]
def Map4_trans
  [p1 : Param40 α β]
  [p2 : Param40 β γ]
  : Param40 α γ := by

  tr_extend Map3_trans p1 p2.forget

  intro a c ⟨b, abR, bcR⟩

  tr_subst a b abR
  apply PSigma.eta rfl
  apply PProd.ext <;> dsimp

  exact p1.forget.R_implies_rightK _ _ abR
  exact p2.forget.R_implies_rightK _ _ bcR


def Param04_trans
  [p1 : Param04 α β]
  [p2 : Param04 β γ]
  : Param04 α γ := by

  apply flip4 (Map4_trans (β := β))

  intro a c
  exact
    (
      R_flip_trans (a := a) (c := c) (p1 := p1.forget) (p2 := p2.forget)
    ).forget


  -- apply PSigma.ext; dsimp


  -- simp?


  -- constructor

  -- change ?lhs = ?rhs
  -- let h := ?lhs
  -- tr_whnf at h

  -- exact p1.forget.R_implies_rightK _ _ abR
  -- exact p2.forget.R_implies_rightK _ _ bcR



  --  _ _ abR


  -- let b : β := tr.map a
  -- tr_subst b c bcR





  -- congr




  -- sorry
