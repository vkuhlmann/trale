import Mathlib
import TraleTest.Lemmas.Zmod5 open TraleTest.Lemmas

theorem sum_eq_reverse_sum_Nat (a b c : ℕ)
    : (a + b) + c = (c + b) + a := by
  omega

theorem sum_eq_reverse_sum_Zmod5 : ∀ (a b c : Zmod5),
  (a + b) + c = (c + b) + a := by
  tr_exact sum_eq_reverse_sum_Nat




-- Note: #tr_add_translations_from_instances is now optional!
-- The trale tactic automatically registers instances as needed.
#tr_add_translations_from_instances

set_option pp.all true in
theorem sum_eq_reverse_sum_Zmod5' : ∀ (a b c : Zmod5),
  (a + b) + c = (c + b) + a := by
  trale
  omega












--

/-
rw [Nat.add_comm _ c]
  rw [Nat.add_comm a _]
  simp [Nat.add_assoc]
  -/
