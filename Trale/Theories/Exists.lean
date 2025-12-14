import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Theories.Sigma
import Qq open Qq Lean

namespace Param_exists

open Param_sigma

variable {α : Sort u} {α' : Sort u} {β : α -> Prop} {β' : α' -> Prop}

noncomputable def toSigma (h : ∃ a, β a) : (Σ' a, β a) := by
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

def toExists (h : Σ' a, β a) : ∃ a, β a := by
  exact ⟨h.1, h.2⟩



def Map0_exists
  (p1 : Param00 α α')
  (p2 : ∀ a a', p1.R a a' → Param00.{0} (β a) (β' a'))
  : Param00.{0} (∃ a, β a) (∃ a', β' a') := by

  tr_constructor

  intro _ _
  -- obtain ⟨a, ha⟩ := x


  exact ∃ (a : α) (a' : α') (aR : p1.R a a')
          (ba : β a) (ba' : β' a'),
           (p2 a a' aR).R ba ba'
            -- (Map0_sigma p1 p2).R (toSigma x) (toSigma x')

  -- intro x x'
  -- exact ∃ (p1R : p1.R x.choose x'.choose),
  --         (p2 x.choose x'.choose p1R).R x.choose_spec x'.choose_spec


def Map1_exists
  (p1 : Param2a0 α α')
  (p2 : ∀ a a', p1.R a a' -> Param10 (β a) (β' a'))
  : Param10 (∃ a, β a) (∃ a', β' a') := by

  tr_extend Map0_exists p1 (p2 . . .)

  intro ⟨a, ba⟩

  let a' : α' := p1.right a
  exists a'

  let aR      := p1.right_implies_R a a' rfl

  -- exact ⟨a', (p2 a a' aR).right ba⟩
  exact (p2 a a' aR).right ba

-- def Map2a_exists
--   (p1 : Param2a0 α α')
--   (p2 : ∀ a a', p1.R a a' -> Param2a0 (β a) (β' a'))
--   : Param2a0 (∃ a, β a) (∃ a', β' a') := by
--   tr_extend Map1_exists p1 (p2 · · ·)

--   intro ⟨a, ba⟩ ⟨a', ba'⟩ aF

--   exists a
--   exists a'








-- def Map0_exists
--   (p1 : Param00 α α')
--   (p2 : ∀ a a', p1.R a a' -> Param00 (β a) (β' a'))
--   : Param00 (∃ a, β a) (∃ a', β' a') := by

--   tr_constructor

--   intro x x'
--   exact ∃ (p1R : p1.R x.choose x'.choose),
--           (p2 x.choose x'.choose p1R).R x.choose_spec x'.choose_spec


-- def Map1_exists
--   (p1 : Param2a0 α α')
--   (p2 : ∀ a a', p1.R a a' -> Param10 (β a) (β' a'))
--   : Param10 (∃ a, β a) (∃ a', β' a') := by

--   tr_extend Map0_exists p1 (p2 . . .)

--   show (∃ a, β a) → ∃ a', β' a'

--   intro x

--   -- show ∀ (x : α), β x → ∃ a', β' a'
--   -- intro a ba

--   let ba      := x.choose_spec

--   let a : α   := x.choose
--   let a' : α' := p1.right a
--   let aR      := p1.right_implies_R a a' rfl

--   exists a'
--   exact (p2 a a' aR).right ba

-- def Map2a_exists
--   (p1 : Param2a0 α α')
--   (p2 : ∀ a a', p1.R a a' -> Param2a0 (β a) (β' a'))
--   : Param2a0 (∃ a, β a) (∃ a', β' a') := by

--   tr_extend Map1_exists p1 (p2 . . .)

--   -- case right =>
--   --   -- Why is this necessary?
--   --   sorry

--   case right_implies_R =>
--     sorry
