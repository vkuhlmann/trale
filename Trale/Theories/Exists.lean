import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Theories.Sigma
import Qq open Qq Lean

namespace Trale

variable {α : Sort u} {α' : Sort u} {β : α -> Prop} {β' : α' -> Prop}

def Map0_exists
  (p1 : Param00 α α')
  (p2 : ∀ a a', p1.R a a' → Param00.{0} (β a) (β' a'))
  : Param00.{0} (∃ a, β a) (∃ a', β' a') := by

  tr_constructor

  -- intro _ _
  -- exact ∃ (a : α) (a' : α') (aR : p1.R a a')
  --         (ba : β a) (ba' : β' a'),
  --          (p2 a a' aR).R ba ba'

  intro x x'

  exact ∃ (p1R : p1.R x.choose x'.choose),
          (p2 x.choose x'.choose p1R).R x.choose_spec x'.choose_spec


def Map1_exists
  (p1 : Param2a0 α α')
  (p2 : ∀ a a', p1.R a a' → Param10 (β a) (β' a'))
  : Param10 (∃ a, β a) (∃ a', β' a') := by

  tr_extend Map0_exists p1 (p2 . . .)

  intro ⟨a, ba⟩

  let a' : α' := p1.right a
  exists a'

  let aR      := p1.right_implies_R a a' rfl

  -- exact ⟨a', (p2 a a' aR).right ba⟩
  exact (p2 a a' aR).right ba

/-

We may attempt to construct Map2a_exists. From Map1_exists we have an arrow
`(∃ a, β a) → (∃ a', β' a')`, e.g. a mapping `⟨a, ba⟩ ↦ ⟨a', ba'⟩`, for some
`a`, `a'`, `ba`, `ba'`. However, by proof-irrelevance, for any other
`⟨a'', ba''⟩ : (∃ a', β' a')`, there is `⟨a', ba'⟩ = ⟨a'', ba''⟩`, and hence
also `⟨a, ba⟩ ↦ ⟨a'', ba''⟩` from Map1_exists.

Hence Map2a_exists would need to show some `aR : p1.R a a''` and
`(p2 a a'' aR).R ba ba''`. We can only make this work if every `a : α` is
related to any other `a' : α'`, and similar for `(β a)`, `(β' a')`. I.e.
that both types are practically subsingletons. We see the proof-irrelevance
gets pushed out to the framework. Hence we can obtain 2a only without erasure
of information, i.e. via sigma types, like Map2a_sigma.
-/

def Map2b_exists
  (p1 : Param2a0 α α')
  (p2 : ∀ a a', p1.R a a' → Param10 (β a) (β' a'))
  : Param2b0 (∃ a, β a) (∃ a', β' a') := by
  tr_extend Map1_exists p1 (p2 · · ·)

  intro ⟨a, ba⟩ ⟨a', ba'⟩ aR
  rfl
