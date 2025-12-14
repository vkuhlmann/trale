import Mathlib
import TraleTest.Lemmas.Zmod5 open TraleTest.Lemmas

theorem sum_eq_reverse_sum_Nat (a b c d e : ℕ)
    : a + (b + c * e) * d = d * b + c * d * e + a * 1 := by
  rw [add_mul, mul_comm b d, mul_assoc c e d,
      mul_assoc c d e, mul_comm e d]
  omega

theorem sum_eq_reverse_sum_Zmod5 : ∀ (a b c d e : Zmod5),
  a + (b + c * e) * d = d * b + c * d * e + a * 1 := by
  tr_exact sum_eq_reverse_sum_Nat
