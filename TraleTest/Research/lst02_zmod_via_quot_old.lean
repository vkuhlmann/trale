import Lean
-- import TraleTest.Utils.Lemmas.Zmod5
import Mathlib

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

#check Subrelation
#check flip
#check Iff

def Zmod5.lift2'
  {R : β → β → Sort _}
  {f : Nat → Nat → β}
  (h : ∀ {a a'}, (aR : mod5_R a a') →
       ∀ {b b'}, (bR : mod5_R b b') →
       R (f a b) (f a' b')
  )
  : Zmod5 → Zmod5 → (c : β) × (c' : β) × (R c c')
  := sorry




def one_zmod5 : Zmod5 := Zmod5.ofNat 1
def four_zmod5 : Zmod5 := Zmod5.ofNat 4
def six_zmod5 : Zmod5 := Zmod5.ofNat 6

example : one_zmod5 = six_zmod5 := by
  apply Quot.sound
  exists 1, 0

def add_R_nat
  {a a' : Nat} (aR : a = a')
  {b b' : Nat} (bR : b = b')
  : (a + b) = (a' + b')
  := by rw [aR, bR]


def add_R
  {a a' : Nat} (aR : mod5_R a a')
  {b b' : Nat} (bR : mod5_R b b')
  : mod5_R (a + b) (a' + b')
  := by
  obtain ⟨n1, m1, _⟩ := aR
  obtain ⟨n2, m2, _⟩ := bR

  exists (n1 + n2)
  exists (m1 + m2)
  omega


def add_R'
  {a a' : Nat} (aR : mod5_R a a')
  {b b' : Nat} (bR : mod5_R b b')
  : Zmod5.ofNat (a + b) = Zmod5.ofNat (a' + b')
  := Quot.sound (add_R aR bR)


-- def add_Zmod5_1 : Zmod5 -> Zmod5 -> Zmod5 :=
--   .lift
--   (fun a => .lift (.fromNat $ a + ·) (add_R' Zmod5_ident ·))
--   (fun aR => by
--     dsimp only
--     congr
--     funext b
--     apply add_R' aR Zmod5_ident
--   )

instance : Add Zmod5 where
  -- add := Zmod5.lift2 add_R'
  add := Zmod5.lift2 (f := (Zmod5.ofNat $ · + ·)) (fun aR => fun bR => Quot.sound (add_R aR bR))

#check Quot
#check Quot.mk
#check Quot.lift
#check Quot.ind
#check Quot.rec
#check Quot.sound

theorem sum_eq_reverse_sum_Modulo' (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  refine Quot.ind (β := fun a => (a + _) + _ = (_ + _) + a) ?_ _
  intro a'

  refine Quot.ind (β := fun b => (_ + b) + _ = (_ + b) + _) ?_ _
  intro b'

  refine Quot.ind (β := fun c => (_ + _) + c = (c + _) + _) ?_ _
  intro c'

  show (Zmod5.ofNat a' + Zmod5.ofNat b' + Zmod5.ofNat c' : Zmod5)
       =
       (Zmod5.ofNat c' + Zmod5.ofNat b' + Zmod5.ofNat a')

  apply Quot.sound
  show mod5_R (a' + b' + c') (c' + b' + a')

  rw [sum_eq_reverse_sum_Nat]
  exact Zmod5_ident



theorem sum_eq_reverse_sum_Modulo (a b c : Zmod5)
    : (a + b) + c = (c + b) + a := by

  revert a b c

  apply Quot.ind; intro a'
  apply Quot.ind; intro b'
  apply Quot.ind; intro c'

  show (.ofNat a' + .ofNat b' + .ofNat c' : Zmod5)
       =
       (.ofNat c' + .ofNat b' + .ofNat a')

  apply Quot.sound
  show mod5_R (a' + b' + c') (c' + b' + a')

  rw [sum_eq_reverse_sum_Nat]
  exact Zmod5_ident

  -- apply add_R

  -- refine Quot.ind (β := fun x => x = _) ?_ _
  -- have h1 : (Zmod5.fromNat $ a' + b' + c') = (.fromNat a') + (.fromNat b') + (.fromNat c') := sorry
  -- have h2 : (Zmod5.fromNat $ c' + b' + a') = (.fromNat c') + (.fromNat b') + (.fromNat a') := sorry



  -- apply add_R'


  -- apply Quot.ind
  -- intro rhsNat
  -- let rhs := Zmod5.fromNat rhsNat

  -- show (fun x => x = rhs) _
  -- apply Quot.ind (β := fun r => r = rhs)
  -- intro lhsNat
  -- let lhs := Zmod5.fromNat lhsNat

  -- show lhs = rhs





  -- -- apply Quot.sound

  -- sorry
