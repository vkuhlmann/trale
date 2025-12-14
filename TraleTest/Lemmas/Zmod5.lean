import Mathlib
import Trale.Utils.Constructor
import Trale.Utils.Split
import Trale.Utils.Attr
import TraleTest.Lemmas.TrAdvance

namespace TraleTest.Lemmas

lemma fin5_mod5 (a : Fin 5) : a.val % 5 = a.val := by
  simp

lemma mod5_le5 : n % 5 < 5 := by
  apply Nat.mod_lt
  simp

-- structure Zmod5 where
--   repr : Fin 5

abbrev Zmod5 := Fin 5

def mod5 (n : Nat) : Zmod5 := ⟨n % 5, mod5_le5⟩
def repr5 (a : Zmod5) : Nat := a

def addMod5 (a b : Zmod5) : Zmod5 := a + b

instance : Add Zmod5 where
  add := addMod5

lemma lt_mod_eq
  (h : a < 5)
 : (a % 5 = a) := by
  simp
  assumption

lemma repr5K : ∀ (a' : Zmod5), mod5 (repr5 a') = a' := by
  intro a
  dsimp [repr5, mod5]
  congr
  apply lt_mod_eq
  simp

#print instLEFin

-- lemma fin5_mod5 (a : Fin 5) : a.val % 5 = a.val := by
--   -- unfold HMod.hMod
--   -- unfold instHMod
--   -- unfold Mod.mod
--   -- unfold Nat.instMod
--   -- unfold Nat.mod
--   simp
--   -- have h1 := a.isLt

--   -- split
--   -- case _ h2 =>
--   --   exact h2.symm

--   -- case _ b c h2 =>
--   --   split
--   --   case _ h3 =>
--   --     omega

--   --   case _ h4 =>
--   --     exact h2.symm

-- lemma fin5_mod5' (a : Fin 5) : a % 5 = a := by
--   unfold HMod.hMod
--   unfold instHMod
--   unfold Mod.mod
--   unfold Fin.instMod
--   unfold Fin.mod
--   unfold HMod.hMod
--   unfold instHMod
--   unfold Nat.instMod
--   unfold Nat.mod

--   simp
--   have h1 := a.isLt

--   congr

--   split
--   case _ h2 =>
--     exact h2.symm

--   case _ b c h2 =>
--     split
--     case _ h3 =>

--       -- simp at h3
--       let abc := h3.eq
--       tauto


--       rw [← h2] at h3
--       simp at h3

--       suffices 5 < a.val by
--         omega


--       simp only [Fin.val] at h1
--       unfold LE.le at h3
--       unfold instLEFin at h3
--       reduce at h3
--       exact h3

--       exact h3.reduce


--       simp at h3





--       let abc := h3.


--       simp at h1
--       omega

--     case _ h4 =>
--       exact h2.symm

/-
@[simp]
def ModParam : Param42a Nat Zmod5 := by
  tr_constructor

  case R =>
    exact fun n m => (mod5 n) = m

  case right =>
    exact mod5

  case right_implies_R =>
    tauto

  case R_implies_right =>
    tauto

  case R_implies_rightK =>
    tauto

  case left =>
    exact repr5

  case left_implies_R =>
    intro a b h

    simp [mod5]

    congr
    rw [← h]

    apply lt_mod_eq
    exact a.isLt

  -- case R_in_map =>
  --   simp
  --   intro a a' aR
  --   rw [← aR]
  --   simp [mod5, repr5]


  --   sorry
-/


instance ModParam : Param42a Nat Zmod5 := by tr_from_map repr5K

-- @[aesop 90% apply (rule_sets := [trale])]
@[trale]
def R_add_Zmod5
  (aR : tr.R a a')
  (bR : tr.R b b')
  : (ModParam.R (a + b) (a' + b')) := by

  tr_whnf
  subst aR bR

  change (⟨(a + b) % 5, _⟩ : Zmod5) = Fin.add (⟨a % 5, mod5_le5⟩ : Fin 5) (⟨b % 5, mod5_le5⟩ : Fin 5)
  -- change _ = Fin.add (⟨a % 5, mod5_le5⟩ : Fin 5) (⟨b % 5, mod5_le5⟩ : Fin 5)
  unfold Fin.add
  simp

@[trale]
def R_mul_Zmod5
  (aR : tr.R a a')
  (bR : tr.R b b')
  : (ModParam.R (a * b) (a' * b')) := by

  tr_whnf
  subst aR bR

  change (⟨(a * b) % 5, _⟩ : Zmod5) = Fin.mul (⟨a % 5, mod5_le5⟩ : Fin 5) (⟨b % 5, mod5_le5⟩ : Fin 5)
  -- change _ = Fin.add (⟨a % 5, mod5_le5⟩ : Fin 5) (⟨b % 5, mod5_le5⟩ : Fin 5)
  unfold Fin.mul
  simp
