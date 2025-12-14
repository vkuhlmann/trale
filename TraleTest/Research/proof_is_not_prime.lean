import Mathlib

def isNotPrime (n : ℕ) := (n = 0 ∨ n = 1) ∨
    (∃ p q, p * q = n ∧ p ≥ 2 ∧ q ≥ 2)

theorem ge_add {p : ℕ} (q : ℕ)
  : p + q ≥ p := by simp

example : isNotPrime 167719 :=
  Or.inr (Exists.intro 367 (Exists.intro 457 (And.intro rfl    (And.intro (ge_add 365) (ge_add 455)))))














-- by
--   right
--   use 367
--   use 457
--   split_ands
--   · rfl
--   · simp
--   · simp


















--
