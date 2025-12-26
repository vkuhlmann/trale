import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Glueing
import Qq open Qq Lean

namespace Trale

universe u v x w1 w2 w3

variable {α : Sort u} {α' : Sort u} {β : α -> Sort v} {β' : α' -> Sort v}

instance Map0_sigma
  (p1 : Param00 α α')
  (p2 : ∀ a a', p1.R a a' → Param00 (β a) (β' a'))
  : Param00 (Σ' a, β a) (Σ' a', β' a') := by

  tr_constructor

  intro x@⟨a, ba⟩ x'@⟨a', ba'⟩

  exact Σ' (aR : p1.R a a'),
           (p2 a a' aR).R ba ba'


def Map1_sigma
  (p1 : Param2a0 α α')
  (p2 : ∀ a a', p1.R a a' → Param10 (β a) (β' a'))
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
  (p2 : ∀ a a', p1.R a a' → Param2a0 (β a) (β' a'))
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

-- example
--   {α α' : Prop}
--   {β : α -> Prop}
--   {β' : α' -> Prop}
--   [p1 : Param2a2a α α']
--   (p2 : ∀ a a', p1.R a a' -> Param2a2a (β a) (β' a'))
--   : Param2a1 (Σ' a, β a) (Σ' a', β' a') := by
--   apply Trale.Utils.glued (Map2a_sigma p1 (p2 . . .))
--     (Map1_sigma p1.flip (∀ a a', fun aR => (p2 a a' aR).flip)).flip

--   funext (a, b) (a', b')

--   show ((p1.R a a') × (p2.R b b'))
--         =
--        ((p1.flip.R a' a) × (p2.flip.R b' b))

--   show ((p1.R a a') × (p2.R b b'))
--         =
--        ((p1.R a a') × (p2.R b b'))

--   rfl


def Map2b_sigma
  (p1 : Param40 α α')
  (p2 : ∀ a a', p1.R a a' → Param2b0 (β a) (β' a'))
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
  (p2 : ∀ a a', p1.R a a' → Param30 (β a) (β' a'))
  : Param30 (Σ' a, β a) (Σ' a', β' a') := by

  tr_extend_multiple [
    Map2a_sigma p1 (p2 . . .),
    Map2b_sigma p1 (p2 . . .)
  ]


-- FIXME: Proof uses sorry
def Map4_sigma
  (p1 : Param40 α α')
  (p2 : ∀ a a', p1.R a a' → Param40 (β a) (β' a'))
  : Param40 (Σ' a, β a) (Σ' a', β' a') := by

  tr_extend Map3_sigma p1 (p2 . . .)

  intro ⟨a, ba⟩ ⟨a', ba'⟩ ⟨aR, baR⟩
  dsimp


  have h2 := p1.R_implies_rightK a a' aR
  dsimp at baR
  dsimp at aR

  have h := (p2 a a' aR).R_implies_rightK ba ba' baR

  -- have h3 : ∀ (aR1 aR2 : ?R), aR2 = aR2 := by
  --   sorry
  -- match aR with
  -- | _ =>
  rw [← h]
  apply PSigma.eta

  rotate_right 1
  assumption
  simp
  congr


  sorry
  -- subst h2


  -- dsimp



  -- assumption


  -- -- show (⟨?aR', ?baR'⟩ : ?_ ×' ?_) = _
  -- show ?lhs = ?rhs
  -- let lhs := ?lhs
  -- show lhs = _

  -- let aR' := lhs.fst
  -- have h3 : aR' = aR := by
  --   congr

  -- have h4 : lhs = ⟨aR, ?secondPart⟩ := by
  --   -- apply lhs.ext
  --   have : ⟨lhs.fst, lhs.snd⟩ = lhs := by congr



  --   rw [←h3]

  --   sorry

  -- -- (⟨aR, baR⟩ : ?_ ×' ?_)






  -- rw [←h]

  -- -- rw [←h2] at h

  -- -- subst h2
  -- rw [←h2]





  -- -- have a :
  -- --   Param.R MapType.Map4 MapType.Map0 ba ba' = (p2 ⟨a, ba⟩.fst ⟨a', ba'⟩.fst aR).1 ⟨a, ba⟩.snd ⟨a', ba'⟩.snd
  -- --   := by sorry


  -- simp
  -- apply And.intro
  -- · exact p1.R_implies_rightK _ _ _
  -- ·
  --   congr
  --   repeat exact p1.R_implies_rightK _ _ _

  --   dsimp




  --   -- exact (p2 a a' aR).R_implies_rightK ba ba' baR
