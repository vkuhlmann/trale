import Mathlib.Data.ZMod.Basic
import Trale.Utils.Normalize

def test1 : ZMod 6 := 3

#eval (7 : ZMod 6)

abbrev N := ZMod 6

abbrev is_square (n : N) := (m : N) ×' (n = m*m)
abbrev leq (n m : N) := (q : N) ×' (m = n + q)
abbrev is_divisable (n : N) := (a : N) × (b : N) ×' (a ≠ 1) ×' (b ≠ 1) ×' (n = a*b)

-- abbrev square_num := (n : Int) × (m : Int) ×' (n = m^2)
abbrev Square_num := (n : N) × is_square n
abbrev Divis_num := (n : N) × is_divisable n

def lemma1 : (n : Square_num) → n.1 ≠ 1 → n.2.1 ≠ 1 :=
  fun n h1 => (fun h2 => h1 (by have g := n.2.2; rw [h2] at g; exact g))

-- def lemma1' : (n : Square_num) → n.1 ≠ 1 → n.2.1 ≠ 1 :=
--   fun n h1 => (fun h2 => h1 (Eq.trans h2 n.2.2))

-- def lemma1' : (n : Square_num) → n.1 ≠ 1 → n.2.1 ≠ 1 :=
--   fun n h1 => (fun h2 => h1 (mul_one  (congrArg (fun x => x * x) h2).symm))

def square_to_divisable : (n : Square_num) → (n.1 ≠ 1) → (a : Divis_num) ×' (a.1 = n.1) :=
  fun n h1 => ⟨⟨n.1, ⟨n.2.1, n.2.1, lemma1 n h1, lemma1 n h1, n.2.2⟩⟩, rfl⟩


-- Nat only

namespace NatOnly

#check rfl
#check refl
#eval (7 : ZMod 6)

abbrev N := Nat

abbrev is_square (n : N) := (m : N) ×' (n = m*m)
abbrev leq (n m : N) := (q : N) ×' (m = n + q)
abbrev is_divisable (n : N) := (a : N) × (b : N) × (leq 2 a) × (leq 2 b) ×' (n = a*b)

-- abbrev square_num := (n : Int) × (m : Int) ×' (n = m^2)
abbrev Square_num := (n : N) × is_square n
abbrev Divis_num := (n : N) × is_divisable n

def lemma3 : (leq a b) × (leq b a) → a = b :=
  by
  unfold leq
  intro (h1, h2)
  sorry

def exclusion : ((leq a b) → False) → leq (b+1) a := sorry
def exclusion' : (leq (b+1) a × (leq a b)) → False := sorry

def lemma1_Nat : (n : Square_num) → leq 4 n.1 → leq 2 n.2.1 :=
  fun n h1 => exclusion (fun h2 => match h2 with
    | ⟨0, h3⟩ => by
      rw [n.2.2] at h1
      simp at h3
      rw [←h3] at h1
      exact exclusion' (⟨2, rfl⟩, h1)

    | ⟨1, h3⟩ => by
      rw [n.2.2] at h1
      simp at h3
      rw [h3] at h1
      exact exclusion' (⟨3, rfl⟩, h1)
    )


def square_to_divisable_Nat : (n : Square_num) → (leq 4 n.1) → (a : Divis_num) ×' (a.1 = n.1) :=
  fun n h1 => ⟨⟨n.1, ⟨n.2.1, n.2.1, lemma1_Nat n h1, lemma1_Nat n h1, n.2.2⟩⟩, rfl⟩

end NatOnly

-----

-- def isNotPrime (n : Nat) := (n = 1) ∨ (∃ (p : Nat), ∃ (q : Nat), (p * q = n) ∧ ((p ≥ 2) ∨ (q ≥ 2)))
def isNotPrime (n : Nat) := ((n = 0) ∨ (n = 1)) ∨ (∃ (p : Nat), ∃ (q : Nat), (p * q = n) ∧ (p ≥ 2) ∧ (q ≥ 2))

#check 2-8

example : 5 ≥ 3 := by
  constructor
  sorry

#check Nat.le
-- #check le_add_lef

theorem le_add (p q : Nat)
  : p ≤ p + q := by simp

theorem ge_add {p : Nat} (q : Nat)
  : p + q ≥ p := by simp

def is_ge (p q : Nat) := ∃ x, p = q + x

example : ∀ (p : Nat), is_ge p 20 → is_ge p 2 :=
  fun p ⟨m, hm⟩ => ⟨m+18, by omega⟩



#eval 6 + 3

#reduce delta% zeta% beta%
  by
    show ∃ x, 20 + x = 30
    let ⟨y, hy⟩ : is_ge 30 20 := ⟨10, rfl⟩
    -- have h : y = 10 := by
    exact ⟨y, hy.symm⟩

def h2 :=
  by
    show ∃ x, 20 + x = 30
    let ⟨y, hy⟩ : is_ge 30 20 := ⟨10, rfl⟩
    -- have h : y = 10 := by
    exact ⟨y, hy.symm⟩

#reduce by
  let x := h2
  show 4 = 3 + 1
  unfold h2 at x
  -- dsimp[h2] at x
  sorry


#check (n : Nat) -> (n = n)
#check ∀ (n : Nat), (n = n)

#check (n : Nat) ×' (n = n)
#check Σ' (n : Nat), (n = n)
#check ∃ (n : Nat), (n = n)


example : isNotPrime 0 := Or.inl (Or.inl rfl)
example : isNotPrime 1 := Or.inl (Or.inr rfl)
example : isNotPrime 4 := Or.inr ⟨2, 2, rfl, ge_add 0, ge_add 0⟩
example : isNotPrime 75 := Or.inr ⟨3, 25, rfl, ge_add 1, ge_add 23⟩
example : isNotPrime 167719 := Or.inr ⟨367, 457, rfl, ge_add 365, ge_add 455⟩

example : isNotPrime 167719 := by
  refine Or.inr ?rhs
  refine ⟨?p, ?q, ?h⟩
  case p => exact 367
  case q => exact 457
  case h =>
    refine ⟨?h2, ?h3, ?h4⟩
    case h2 => exact rfl
    case h3 => exact ge_add 365
    case h4 => exact ge_add 455

example : isNotPrime 167719 := by
  right
  use 367
  use 457
  split_ands
  · rfl
  · exact ge_add 365
  · exact ge_add 455

#check Equiv
-- #check ≣
#check Nat.mul

#reduce
  let _ : ((4+3)*0 + ?x) = 0 + ?x := refl ((0 * 2) + ?x)
  ()

#check Nat.rec

#check funext
#check propext

#reduce (refl ((0 * 2) + ?x) : ((4+3)*0 + ?x) = 0 + ?x)
-- #reduce (refl ((0 * 2) + ?x) : ((4+3)*0 + ?x) = 0)

#reduce (refl (?x + (0 * 2)) : (?x + (4+3)*0) = ?x + 0)
-- #reduce (refl (?x + (0 * 2)) : (?x + (4+3)*0) = ?x)
#reduce (refl ?x : ?x = ?x)
-- #reduce (refl ?x : ?y = ?x)
#reduce (refl 4 : 4 + 0 = 4)

-- #reduce (refl ?x : ?x + 0 = ?x)
#reduce (refl 0 : ?x*0 = 0)
-- #reduce (refl 0 : 0*?x = 0)

-- #reduce (refl ?x + 0 : ?x = ?x)



theorem evensNotPrime'
  (n : Nat) : isNotPrime (n*2) ∨ n*2=2 :=
    match n with
      | 0 => .inl (.inl (.inl rfl))
      | 1 => .inr rfl
      | m+2 => .inl $ .inr $ by
          use 2
          use (2+m)
          split_ands
          omega
          rfl
          exact ge_add m

theorem mul_monotonicity
  (n p q : Nat) (h : p * q = n) (h2 : n ≠ 0)
  : (p ≤ n) := by

  match q with
  | 0 => exact False.elim (h2 h.symm)
  | 1 =>
    subst h
    simp

  | m + 2 =>
    have : p ≠ 0 := by
      intro h3
      subst h3
      subst h
      simp at h2

    subst h
    rw [mul_add]
    omega

    -- unfold 2
    -- rw [mul_add_one p 1]
    -- show p ≤ p * m + p + p
    -- apply Nat.le_add_left

  -- induction n

  -- case zero =>
  --   exact False.elim (h2 h.symm)

  -- case succ m hm =>

  --   sorry



  -- exact Nat.mul_ge

  --  sorry

-- lemma : ¬(∃ m, 1 = m * 2)

theorem evensNotPrime
  (n : Nat) (h : ∃ k, n = k * 2) : isNotPrime n ∨ n=2 :=
    match n with
      | 0 => .inl (.inl (.inl rfl))
      | 1 => False.elim $ by omega
      --  False.elim $ match h with
      --   | ⟨k, hk⟩ =>
      --       by omega

      --       -- let h2 := (mul_monotonicity 1 _ h.choose _ _)
      --       -- Nat.not_le_of_gt (by simp) h2
      --     -- Nat.not_le_of_gt _ (mul_monotonicity _ _ h.choose _ _)
      | 2 => .inr rfl
      | m+3 => .inl $ .inr $ by
          use 2
          use h.choose
          exact ⟨by omega, by rfl, by omega⟩

-- Or.inr ⟨367, 457, rfl, ge_add 365, ge_add 455⟩



namespace Other1
abbrev is_square (n : Nat) := ∃ m, n*n = m
abbrev leq (n m : Nat) := ∃ q, m = n + q

abbrev DivisableNumber := Σ' n, (∃ a b, a ≥ 2 ∧ b ≥ 2 ∧ a*b = n)
abbrev DivisableNumber.toNat (n : DivisableNumber) := n.fst
def is_prime (n : Nat) := ∀ p q, p ≤ q → p * q = n → p = 1
def square_is_divisable : (n : Nat) → (is_square n ∧ n ≥ 4) → (Σ' a : DivisableNumber, a.toNat = n) :=
  fun n h => ⟨⟨n, ⟨h.1.choose, ⟨h.1.choose, sorry⟩⟩⟩, sorry⟩

end Other1

namespace Other2
abbrev is_square' (n : Nat) := (m : Nat) ×' n*n = m
abbrev leq' (n m : Nat) := (q : Nat) ×' (m = n + q)
def DivisableNumber' := (n : Nat) × (a : Nat) × (b : Nat) × (leq' 2 a) × (leq' 2 b) ×' (a*b = n)
def DivisableNumber.toNat (a : DivisableNumber') : Nat := a.1
end Other2

#check Quot
#check Quot.sound


namespace IsPrime

def isPrime (n : Nat) := (n ≥ 2) ∧ (∀ p, (∃ q, p * q = n) → (p = 1 ∨ p = n))

theorem isPrime_iff_not_isNotPrime
  : isPrime n ↔ ¬(isNotPrime n) := by

constructor
· intro hp hnp
  show False

  match hnp, hp with
  -- Case n=0. Then 0 ≥ 2 -> False
  | .inl (.inl h1), ⟨nge2, _⟩ =>  subst h1; tauto

  -- Case n=1. Then 1 ≥ 2 -> False
  | .inl (.inr h1), ⟨nge2, _⟩ =>  subst h1; tauto

  -- Case n≥2.
  | .inr ⟨p, q, h1, h2⟩, ⟨nge2, h3⟩ =>
    subst h1
    specialize h3 p ⟨q, rfl⟩

    match h3 with
    | .inl h4 => -- Case p=1. Then (h2 : 1 ≥ 2 ∧ q ≥ 2) -> False
      subst h4; tauto

    | .inr h4 => -- Case p=n (p=p*q).
      rw [Nat.mul_comm] at h4
      let h5 : p ≥ q * p := by omega
      grewrite [h2.right] at h5
      -- Using (p ≥ 2 * p) ∧ (p ≥ 2) -> False
      omega


· intro hnnp
  show isPrime n
  unfold isNotPrime at hnnp
  -- push_neg at hnnp

  split_ands
  · show n ≥ 2
    apply le_of_not_gt
    intro h1
    apply hnnp
    /-
        h1 : n < 2
        ⊢ (n = 0 ∨ n = 1) ∨ ∃ p q, p * q = n ∧ p ≥ 2 ∧ q ≥ 2
    -/

    match n with
    | 0 => exact .inl (.inl rfl)
    | 1 => exact .inl (.inr rfl)
    | (x+2) => tauto

  · intro p h1
    choose q h2 using h1
    push_neg at hnnp
    let h3 := hnnp.2 p q h2

    match h4 : p with
    | 0 => subst h2; simp
    | 1 => left; rfl
    | x+2 =>
      specialize h3 (by omega)
      --  h3 : q < 2

      match q with
      | 0 => omega
      | 1 => omega
      | y+2 => omega


-- def decide

-- def f : (p : Nat) → (∃ q, p*q = 7) → (p=1 ∨ p=7)
--   | 1, _ => .inl rfl
--   | 7, _ => .inr rfl
--   | p, ⟨q, h⟩ =>
--     by
--     -- omega

--     exfalso

--     -- if h1 : p=1 then
--     --   return exact .inl rfl

--     have h1 : p ≠ 1 := by sorry
--     have h2 : p ≠ 7 := by sorry

--     -- suffices ¬(p * q = 7) by
--     --   exfalso
--     --   exact this h

--     -- induction p

--     cases p <;> cases q
--     tauto
--     simp at h
--     simp at h


--     tauto

--     decide
--     decide

--     tauto


--     -- induction (p, q)




-- example : isPrime 7 := ⟨ge_add 5, match
--   | 1 => sorry
--   ⟩


end IsPrime
