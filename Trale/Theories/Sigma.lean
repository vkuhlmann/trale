import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Utils.Extend
import Qq open Qq Lean

namespace Param_sigma

universe u v x w1 w2 w3

variable {α : Sort u} {α' : Sort u} {β : α -> Sort v} {β' : α' -> Sort v}

def Map0_sigma
  (p1 : Param00 α α')
  (p2 : ∀ a a', p1.R a a' -> Param00 (β a) (β' a'))
  : Param00 (Σ' a, β a) (Σ' a', β' a') := by

  tr_constructor

  intro x@⟨a, ba⟩ x'@⟨a', ba'⟩

  exact ∃ (aR : p1.R a a'),
          (p2 a a' aR).R ba ba'


def Map1_sigma
  (p1 : Param2a0 α α')
  (p2 : ∀ a a', p1.R a a' -> Param10 (β a) (β' a'))
  : Param10 (Σ' a, β a) (Σ' a', β' a') := by

  tr_extend Map0_sigma p1 (p2 . . .)

  intro ⟨a, ba⟩

  let a' : α' := p1.right a
  exists a'

  let aR      := p1.right_implies_R a a' rfl

  -- exact ⟨a', (p2 a a' aR).right ba⟩
  exact (p2 a a' aR).right ba


def Map2a_sigma
  (p1 : Param2a0 α α')
  (p2 : ∀ a a', p1.R a a' -> Param2a0 (β a) (β' a'))
  : Param2a0 (Σ' a, β a) (Σ' a', β' a') := by

  tr_extend Map1_sigma p1 (p2 . . .)

  -- intro x@⟨a0, ba0⟩ x'@⟨a'0, ba'0⟩ (fX : ?right x = x')
  -- intro x@⟨a, ba⟩ x'@⟨a', ba'⟩ (fX : ?right ⟨a, ba⟩ = ⟨a', ba'⟩)
  intro ⟨a, ba⟩ ⟨a', ba'⟩ (fX : ?right ⟨a, ba⟩ = ⟨a', ba'⟩)

  dsimp at fX

  have h1 : p1.right a = a' := by
    match fX with
    | rfl => rfl

  let aR := p1.right_implies_R a a' h1

  have h2 : (p2 a a' aR).right ba = ba' := by
    subst h1
    simp at fX
    exact fX

  exists aR
  exact (p2 a a' aR).right_implies_R ba ba' h2


def Map2b_sigma
  (p1 : Param40 α α')
  (p2 : ∀ a a', p1.R a a' -> Param2b0 (β a) (β' a'))
  : Param2b0 (Σ' a, β a) (Σ' a', β' a') := by

  tr_extend Map1_sigma p1 (p2 . . .)

  intro ⟨a, ba⟩ ⟨a', ba'⟩ ⟨aR, baR⟩

  dsimp at ⊢ aR baR

  -- Need to prove:
  -- 1. p1.right a = a'
  -- 2. (p2 a a' aR2).right ba = ba'
  --
  -- where aR2 is the canonical relation for the mapping a ↦ a'
  -- and   aR  is _any_ supplied relation between a and a', as provided by [?R]

  have h1 : p1.right a = a' := by
    exact p1.R_implies_right a a' aR

  let aR2 := p1.right_implies_R a a' h1

  have h2 : (p2 a a' aR2).right ba = ba' := by
    have h3 : aR2 = aR := p1.R_implies_rightK a a' aR
    rw [h3]

    exact (p2 a a' aR).R_implies_right ba ba' baR

  -- have h2 := (p2 a a' aR).R_implies_right ba ba' baR

  subst h1
  simp
  exact h2


def Map3_sigma
  (p1 : Param40 α α')
  (p2 : ∀ a a', p1.R a a' -> Param30 (β a) (β' a'))
  : Param30 (Σ' a, β a) (Σ' a', β' a') := by

  tr_extend_multiple [
    Map2a_sigma p1 (p2 . . .),
    Map2b_sigma p1 (p2 . . .)
  ]


def Map4_sigma
  (p1 : Param40 α α')
  (p2 : ∀ a a', p1.R a a' -> Param30 (β a) (β' a'))
  : Param40 (Σ' a, β a) (Σ' a', β' a') := by

  tr_extend Map3_sigma p1 (p2 . . .)

  intro ⟨a, ba⟩ ⟨a', ba'⟩ ⟨aR, baR⟩
  simp
