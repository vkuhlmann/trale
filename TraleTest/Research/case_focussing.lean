import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Mathlib

import TraleTest.Lemmas.SummableSequence
import TraleTest.Lemmas.Modulo
open TraleTest.Lemmas Trale

set_option trace.tr.utils false

namespace TraleTest.Research.CaseFocussing

example : Param00 (xnnR → xnnR → Prop) (nnR → nnR → Prop) := by
  refine ?subgoals

  tr_split_arrow
  infer_instance

  tr_split_arrow
  infer_instance

  exact (sortParam .Map1 .Map0).forget

/-
example : Param00 (xnnR → xnnR → Prop) (nnR → nnR → Prop) := by
    -- refine ?subgoals

    tr_split'

    case p1 => infer_instance

    tr_split'

    case p1 => infer_instance

    -- TODO: Make this work with infer_instance
    exact propParam.forget

example  : Param00 ((∀ (n : Nat), Fin n) → Prop) ((nnR → nnR) → Prop) := by
  refine ?subgoals
  tr_split'

  case p1 =>
    tr_split'


  case p2 =>

    tr_split'

    case p1 => infer_instance

    -- TODO: Make this work with infer_instance
    exact propParam.forget
-/

/-
theorem P1 : ∀ f : (a : Nat) → Fin (a+1),
             ∑ b ∈ {1, 2, 3}, (f b).val ≤ 6
  := by
  simp
  omega

theorem P1' : ∀ f : (a : Nat) → Modulo (a+1),
              ∑ b ∈ {1, 2, 3}, (f b).repr ≤ 6
  := by

  -- apply fun x => Param.right x P1
  -- apply fun x : Param10 _ _ => x.right P1

  refine ?subgoals

  tr_by P1


  /-

  ⊢ Param10
    (∀ (f : (a : ℕ) → Fin    (a + 1)), ∑ b ∈ {1, 2, 3}, ↑(f b)      ≤ 6)
    (∀ (f : (a : ℕ) → Modulo (a + 1)), ∑ b ∈ {1, 2, 3},  (f b).repr ≤ 6)

  -/
  -- tr_split
  apply Trale.Map1_forall; case' p1 => skip

  /-
  case p1
  ⊢ Param02a
    ((a : ℕ) → Fin    (a + 1))
    ((a : ℕ) → Modulo (a + 1))

  case p2
  ⊢   (f  : (a : ℕ) → Fin    (a + 1))
    → (f' : (a : ℕ) → Modulo (a + 1))
    → (?p1).R f f'
    → Param10
      (∑ b ∈ {1, 2, 3}, ↑(f  b)      ≤ 6)
      (∑ b ∈ {1, 2, 3},  (f' b).repr ≤ 6)

  -/

  -- case p1 =>
  -- ·
  /-
      ⊢ Param02a ((a : ℕ) → Fin (a + 1)) ((a : ℕ) → Modulo (a + 1))
  -/

  -- focus
  apply Trale.Map2a_forall_flipped
  (case' p2 => intro _ _ _)
  case' p1 => infer_instance
  subst_last -- (custom tactic)
  infer_instance

  -- case' p1 => skip

  -- case p1 =>
  focus

    -- tr_flip
    -- tr_split'

    -- Error: Case tag `p1` not found.
    case p1 =>
      sorry
-/
