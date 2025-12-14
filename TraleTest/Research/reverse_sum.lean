import Mathlib open Real

-- AddCommSemigroup = AddSemigroup + AddCommMagma
variable {G : Type*} [AddCommSemigroup G]
theorem sum_eq_reverse_sum (a b c : G)
    : (a + b) + c = (c + b) + a := by
  rw [AddCommMagma.add_comm _ c]
  rw [AddCommMagma.add_comm a _]
  simp [AddSemigroup.add_assoc]

theorem sum_eq_reverse_sum_Nat (a b c : ℕ)
    : (a + b) + c = (c + b) + a :=
    sum_eq_reverse_sum a b c

theorem sum_eq_reverse_sum_Rat (a b c : ℚ)
    : (a + b) + c = (c + b) + a :=
    sum_eq_reverse_sum a b c

#check
  sum_eq_reverse_sum (G := ℝ) 8 π 3.5
#check
  sum_eq_reverse_sum (G := ZMod 5) 8 2 3

-- ZMod 5
#check mul_comm
#check mul_assoc
#check mul_add
#check List Nat
#check mul_one














theorem sum_eq_reverse_sum_Rat' (a b c : ℚ)
    : (a + b) + c = (c + b) + a := by
  rw [Rat.add_comm _ c]
  rw [Rat.add_comm a _]
  simp [Rat.add_assoc]
  -- rw [Nat.add_comm _ c]
  -- rw [Nat.add_comm a _]
  -- simp [Nat.add_assoc]




























-----
