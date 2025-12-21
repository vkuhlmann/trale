import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Attr
import Trale.Theories.Sorts
import Aesop

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic

-- Code based on 'summable.v' example by Trocq Rocq plugin developers.

-- declare_aesop_rule_sets [trale, abcd] (default := true)

namespace TraleTest.Lemmas

-- axiom nnR : Type
-- axiom zero_nnR : nnR
-- axiom one_nnR : nnR

#check NNReal
#check ENNReal
def nnR := NNRat deriving Repr, AddCommMagma, AddSemigroup, AddCommSemigroup,
  Zero, AddZeroClass, Add
-- def nnR := NNReal deriving Repr

#eval 4.8 + 4.2

-- #eval ((7 : NNReal) + (2 : NNReal)).toReal

instance : OfNat nnR n where
  ofNat := (n : NNRat)
-- instance : Zero nnR where
--   zero := 0
-- instance : AddCommMagma nnR := inferInstanceAs (AddCommMagma NNReal)
-- instance : AddSemigroup nnR := inferInstanceAs (AddSemigroup NNReal)
-- instance : AddCommSemigroup nnR := inferInstanceAs (AddCommSemigroup NNReal)
-- instance : Zero nnR := inferInstanceAs (Zero NNReal)
-- instance : AddZeroClass nnR := inferInstanceAs (AddZeroClass NNReal)


def zero_nnR : nnR := 0

-- instance : Add nnR where
--   -- add := Nat.add
--   add (a : NNRat) (b : NNReal) := a + b

inductive xnnR where
  | fin : nnR -> xnnR
  | inf : xnnR
-- deriving Repr

def add_xnnR (a b : xnnR) : xnnR :=
  match a, b with
  | .fin a', .fin b' => .fin (a' + b')
  | _, _ => .inf

instance : Add xnnR where
  add := add_xnnR

theorem add_xnnR_homeo
  (a b : nnR)
  : (xnnR.fin (a + b) = xnnR.fin a + xnnR.fin b) := by
  show xnnR.fin (a + b) = add_xnnR (xnnR.fin a) (xnnR.fin b)

  unfold add_xnnR
  dsimp only

@[aesop 70%]
theorem nnR_comm (a b : nnR) : a + b = b + a := by
  unfold nnR at *
  -- exact Nat.add_comm a b
  exact AddCommMagma.add_comm a b


theorem xnnR_comm (a b : xnnR) : a + b = b + a := by
  show add_xnnR a b = add_xnnR b a
  unfold add_xnnR

  match a, b with
  | .fin a, .fin b =>
    show (xnnR.fin a) + (.fin b) = (.fin b) + (.fin a)
    repeat rw [←add_xnnR_homeo]
    apply congrArg
    exact nnR_comm a b

  | .inf, .inf
  | .fin a, .inf
  | .inf, .fin b => dsimp

instance : AddCommMagma xnnR where
  add_comm := xnnR_comm
instance : AddSemigroup xnnR where
  add_assoc a b := sorry
instance : AddCommSemigroup xnnR := {}
instance : AddCommMonoid xnnR where
  zero := .fin 0
  zero_add := by intro a; match a with
    |.fin x =>
      change xnnR.fin (0 + x) = xnnR.fin x; congr;

      -- change @OfNat.ofNat nnR 0 Zero.toOfNat0 + x = x with x
      -- exact AddZeroClass.zero_add x
      sorry
    |.inf => rfl
  add_zero := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry

def seq_nnR := Nat → nnR
def seq_xnnR := Nat → xnnR --ENNReal

noncomputable
def add_seq_xnnR (f g : seq_xnnR) : seq_xnnR :=
  fun n => (f n) + (g n)

noncomputable
instance : Add (seq_xnnR) where
  add := add_seq_xnnR

axiom sum_xnnR : seq_xnnR -> xnnR

axiom abc : seq_xnnR

-- class SequenceSummation (seq : Type _) where
--   sumT : Type _
--   sum : seq → sumT

class SequenceSummation (seq : Type _) (sumT : outParam (Type _)) where
  sum : seq → sumT

noncomputable
instance : SequenceSummation seq_xnnR xnnR  where
  sum := sum_xnnR

noncomputable
instance : SequenceSummation (Nat → xnnR) xnnR  where
  sum := sum_xnnR

notation "Σ " a:68 => SequenceSummation.sum a

axiom sum_xnnR_add :
  ∀ (f g : seq_xnnR), Σ (f + g) = (Σ f + Σ g)

def isFin (x : xnnR) : Bool :=
  match x with
  | .fin _ => True
  | .inf => False

def isSummable (f : seq_nnR) : Prop :=
  isFin (Σ (.fin ∘ f : seq_xnnR))

def extend : nnR → xnnR := .fin

def truncate : xnnR → nnR := (
  match . with
  | .inf => zero_nnR
  | .fin r => r
  )

def truncate_extend (r : nnR) : truncate (extend r) = r := by
  simp only [truncate, extend]

structure summable where
  seq : seq_nnR
  is_summable : isSummable seq

instance : Coe summable (seq_nnR) where
  coe s := s.seq

instance : CoeFun summable (fun _ => (Nat → nnR)) where
  coe s := s.seq

def seq_extend : seq_nnR → seq_xnnR := (extend ∘ .)

axiom summable_add :
  ∀ u v : summable, isSummable (fun n => u n + v n)

instance : Add summable where
  add a b := ⟨_, summable_add a b⟩

noncomputable
instance instSummationSummable : SequenceSummation summable nnR where
  sum a := truncate (Σ (xnnR.fin ∘ a))

-- theorem summableSummationDoesNotTruncate
--   (a : summable)
--   : truncate (Σ (xnnR.fin ∘ a)) = .isFin

theorem summationHomeo (a : summable) : Σ seq_extend a.seq = .fin (Σ a) := by
  let h1 := a.is_summable
  unfold isSummable at h1

  let extended := Σ xnnR.fin ∘ a.seq

  show extended = xnnR.fin (truncate extended)

  replace h1 : isFin extended = true := h1

  match extended with
  | .fin b =>
    dsimp only [truncate]

  | .inf =>
    dsimp only [isFin] at h1
    contradiction


instance paramNNR : Param42b nnR xnnR
  := by tr_from_map truncate_extend
instance : TrTranslateRight nnR xnnR := by constructor
instance : TrTranslateLeft nnR xnnR := by constructor

instance param_NNR_seq : Param40 seq_nnR seq_xnnR
  := by tr_from_map seq_extend

instance param_summable_NNR_seq : Param40 summable seq_nnR
  := by tr_from_map summable.seq

-- def summableSeqK (a : summable)
--   :  (summable.seq a)

-- instance param_summable_NNR_seq' : Param40 summable seq_nnR := by
--     tr_from_map


instance param_summable_seq : Param40 summable seq_xnnR
  :=
  by tr_from_map (tr.map (α := seq_nnR) $ tr.map .)
  -- := by tr_from_map (param_NNR_seq.right ∘ param_summable_NNR_seq.right)

theorem param_summable_seq_injective
  (a b : summable)
  (h : param_summable_seq.right a = param_summable_seq.right b)
  : a = b := by
  change seq_extend (summable.seq _) = seq_extend (summable.seq _) at h

  -- match a with
  -- | ⟨a_seq, a_sum⟩ =>
  obtain ⟨a_seq, a_sum⟩ := a
  obtain ⟨b_seq, b_sum⟩ := b

  dsimp [seq_extend, extend] at h

  have : a_seq = b_seq := by
    funext x
    apply congrFun at h
    specialize h x
    exact (xnnR.fin.injEq _ _).mp h

  subst this

  rfl


instance : TrTranslateRight summable seq_xnnR := by constructor
instance : TrTranslateLeft summable seq_xnnR := by constructor
-- For propParam, see Trale/Theories/Sorts.lean


@[trale]
theorem R_sum_xnnR
  (u : summable) (u' : seq_xnnR) (uR : tr.R u u')
  : tr.R (Σ u) (Σ u') := by

  tr_whnf at uR
  tr_whnf
  rw [←uR]

  dsimp [extend, param_NNR_seq, seq_nnR, param_summable_NNR_seq]
  exact (summationHomeo u).symm

-- TODO Add trale attribute
-- @[trale]

-- @[aesop 90% apply (rule_sets := [trale])]



@[aesop safe,trale]
theorem R_add_xnnR
  (a : nnR) (a' : xnnR) (aR : tr.R a a')
  (b : nnR) (b' : xnnR) (bR : tr.R b b')
  : tr.R (a + b) (a' + b') := by

  tr_whnf
  show extend (a + b) = a' + b'

  tr_subst a a' aR
  tr_subst b b' bR

  exact add_xnnR_homeo a b


@[trale]
theorem seq_nnR_add
  -- (a : summable) (a' : seq_xnnR) (aR : tr.R a a')
  -- (b : summable) (b' : seq_xnnR) (bR : tr.R b b')
  (a : seq_xnnR) (a' : summable) (aR : tr.R a a')
  (b : seq_xnnR) (b' : summable) (bR : tr.R b b')
  : tr.R (a' + b') (a + b) := by

  tr_whnf; simp

  tr_subst a' a aR

  -- let bR : tr.R (α := seq_xnnR) (β := summable) (p := param_summable_seq.flip) _ _ := bR
  -- unfold tr.R at bR
  -- let bR : (_ : Param _ _ seq_xnnR summable).R _ _ := bR
  -- have aF := tr.R_implies_map _ _ bR;
  -- simp at aF;
  -- subst aF

  tr_subst b' b bR

  congr

theorem R_eq_seq_xnnR_summable'
  -- [Param2b0 α α']
  (a : seq_xnnR) (a' : summable) (aR : tr.R a a')
  (b : seq_xnnR) (b' : summable) (bR : tr.R b b')
  -- : propParam.R (a = b) (a' = b') := by
  : (a = b) -> (a' = b') := by

  -- tr_whnf
  -- show a = b → a' = b'

  intro h

  -- tr_whnf at aR bR
  -- dsimp at aR bR

  have h2 := Eq.trans (.trans aR h) bR.symm
  exact param_summable_seq_injective _ _ h2

theorem R_eq_seq_xnnR_summable
  (a : seq_xnnR) (a' : summable) (aR : tr.R a a')
  (b : seq_xnnR) (b' : summable) (bR : tr.R b b')
  : (a = b) -> (a' = b') :=
  fun h => param_summable_seq_injective _ _ (Eq.trans (.trans aR h) bR.symm)
