import Lean

theorem sum_eq_reverse_sum_Nat (a b c : Nat)
    : (a + b) + c = (c + b) + a := by
  omega

def mod5_R (a : Nat) (b : Nat) : Prop :=
  ∃ n m : Nat, a + 5 * n = b + 5 * m

abbrev Zmod5 := Quot mod5_R
abbrev Zmod5.ofNat : Nat → Zmod5 := Quot.mk _
abbrev Zmod5.lift
  (f : Nat → β)
  (h : ∀ {a a'}, (aR : mod5_R a a') → f a = f a')
  : Zmod5 → β

  := Quot.lift f @h

theorem Zmod5_ident : mod5_R a a := ⟨0, 0, rfl⟩

def R (a : Nat) (b : Zmod5) := .ofNat a = b

def Zmod5.lift2
  {f : Nat → Nat → β}
  (h : ∀ {a a'}, (aR : mod5_R a a') →
       ∀ {b b'}, (bR : mod5_R b b') →
       f a b = f a' b'
  )
  : Zmod5 → Zmod5 → β

  := Zmod5.lift
    (fun a => Zmod5.lift (fun b => f a b) (h Zmod5_ident ·))
    (fun aR => by
      dsimp only
      congr
      funext b
      exact h aR Zmod5_ident
    )

def add_preserves_mod5_R
  {a a' : Nat} (aR : mod5_R a a')
  {b b' : Nat} (bR : mod5_R b b')
  : mod5_R (a + b) (a' + b')
  := by
  obtain ⟨n1, m1, _⟩ := aR
  obtain ⟨n2, m2, _⟩ := bR

  exists (n1 + n2)
  exists (m1 + m2)
  omega

instance : Add Zmod5 where
  add := Zmod5.lift2 (f := (Zmod5.ofNat $ · + ·)) (fun aR => fun bR => Quot.sound (add_preserves_mod5_R aR bR))

def R_add
  {a a'} (aR : R a a')
  {b b'} (bR : R b b')
  : R (a + b) (a' + b')
  := by
  subst aR bR
  exact Quot.sound ⟨0, 0, rfl⟩

def intro_mod5
  {β : Nat → Sort _}
  {β' : Zmod5 → Sort _}
  (h : ∀ a a', R a a' → (β a → β' a'))
  : (∀ a, β a) → (∀ a', β' a') := by

  intro x a'
  apply Quot.ind
  intro a
  exact h a (.ofNat a) rfl (x a)

def R_eq
  {a a'} (aR : R a a')
  {b b'} (bR : R b b')
  : (a = b) → (a' = b') := by
  intro h; subst aR bR; exact congrArg _ h

theorem sum_eq_reverse_sum_Modulo :
    ∀ (a b c : Zmod5), (a + b) + c = (c + b) + a :=
    (
    intro_mod5 fun _ _ aR =>
    intro_mod5 fun _ _ bR =>
    intro_mod5 fun _ _ cR =>

    R_eq
      (R_add (R_add aR bR) cR)
      (R_add (R_add cR bR) aR)
    ) sum_eq_reverse_sum_Nat


theorem sum_eq_reverse_sum_Modulo' (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c

  refine (?_ : _ → _) sum_eq_reverse_sum_Nat

  apply intro_mod5; intro a a' aR
  apply intro_mod5; intro b b' bR
  apply intro_mod5; intro c c' cR

  let lhsR : R (a + b + c) (a' + b' + c') :=
    R_add (R_add aR bR) cR

  let rhsR : R (c + b + a) (c' + b' + a') :=
    R_add (R_add cR bR) aR

  exact R_eq lhsR rhsR
