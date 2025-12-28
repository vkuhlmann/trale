import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

import Mathlib
import Mathlib.Topology.Algebra.InfiniteSum.Defs


import Trale.Utils.TrAdvance
-- import TraleTest.Lemmas.SummableSequence

set_option trace.tr.utils true

namespace TraleTest.Transfer.SummableSequence
open NNReal ENNReal Trale

#check Summable

-- #check ((fun (x : Nat) => x) + (fun (x : Int) => 6))
#eval (((fun x => x) + (fun (x : Nat) => 6)) : Nat -> Nat) 4

#check Summable.tsum_add
#check Summable.tsum_add_tsum_compl

#check Summable.tsum_eq_add_tsum_ite
#check Summable.tsum_eq_add_tsum_ite'

def extend : NNReal → ENNReal := .some

def truncate : ℝ≥0∞ → ℝ≥0
  | .some r => r
  | .none => 0

def truncate_extend (r : NNReal) : truncate (extend r) = r := by
  simp only [truncate, extend]

structure summable where
  seq : Nat -> NNReal
  is_summable : Summable seq

instance : CoeFun summable (fun _ => Nat -> NNReal) where
  coe s := s.seq

-- instance : HAdd summable summable (Nat -> NNReal) where
--   hAdd x y := x.seq + y.seq

instance : Add summable where
  add x y := ⟨x.seq + y.seq, x.is_summable.add y.is_summable⟩

instance paramNNR : Param42b ℝ≥0 ℝ≥0∞
  := by tr_from_map truncate_extend

instance : Param42b ℝ≥0 (WithTop ℝ≥0) := paramNNR

#check tsum

open scoped Classical in
@[to_additive /-- `∑' i, f i` is the sum of `f` if it exists and is unconditionally convergent,
or 0 otherwise. -/]
noncomputable irreducible_def tprod_extended [CommMonoid α] [TopologicalSpace α] {β} (f : β → α) : WithTop α :=
  if h : Multipliable f then
  /- Note that the product might not be uniquely defined if the topology is not separated.
  When the multiplicative support of `f` is finite, we make the most reasonable choice to use the
  product over the multiplicative support. Otherwise, we choose arbitrarily an `a` satisfying
  `HasProd f a`. -/
    if (Function.mulSupport f).Finite then .some (finprod f)
    else h.choose
  else .none

notation3 "∑'' "(...)", "r:67:(scoped f => tsum_extended f) => r

theorem summable_matches_tsum (u : summable)
  : ∑' i, u i = ∑'' i, u i := by

  rw [tsum_extended_def, tsum_def]

  split
  · split
    rfl
    rfl
  · exfalso
    rename_i h
    apply h
    exact u.is_summable

-- instance param_NNR_seq : Param40 seq_nnR seq_xnnR
--   := by tr_from_map seq_extend

-- instance param_summable_NNR_seq : Param40 summable seq_nnR
--   := by tr_from_map summable.seq

instance param_summable_seqExtended : Param40 summable (ℕ → ℝ≥0∞)
  := by tr_from_map fun x n => extend (x.seq n)

instance param_summable_seq : Param40 summable (ℕ → ℝ≥0)
  := by tr_from_map fun x n => x.seq n


theorem summable_rel (u : summable) (u' : ℕ → ℝ≥0)
  (uR : tr.R u u')
  : tr.R (∑' i, u i) (∑'' i, u' i) := by

  -- rw [tsum_extended_def, tsum_def]
  subst uR
  rw [←summable_matches_tsum u]
  rfl

theorem summable_rel' (u : summable)
  (u'' : ℕ → ℝ≥0)
  (uR' : tr.R u u'')
  (u' : ℕ → ℝ≥0)
  (uR : tr.R u u')
  : tr.R (∑' i, u'' i) (∑'' i, u' i) := by

  subst uR'
  exact summable_rel _ _ uR

theorem summable_rel'' (u : summable)
  (u' : ℕ → ℝ≥0)
  (uR : tr.R u u')
  : tr.R (∑' i, u' i) (∑'' i, u' i) := by

  subst uR
  exact summable_rel _ _ rfl


-- This definition does not work right, since ∑' will be zero if not convergent,
-- even for the ENNReal case.
-- theorem R_sum_xnnR
--   (u : summable) (u' : ℕ → ℝ≥0∞) (uR : tr.R u u')
--   : tr.R (α := ℝ≥0) (β := ℝ≥0∞) (∑' i, u i) (∑' i, u' i) := by

--   sorry
  -- tr_whnf at uR
  -- tr_whnf
  -- rw [←uR]

  -- dsimp [extend, param_NNR_seq, seq_nnR, param_summable_NNR_seq]
  -- exact (summationHomeo u).symm

theorem R_add_xnnR
  (a : ℝ≥0) (a' : ℝ≥0∞) (aR : tr.R a a')
  (b : ℝ≥0) (b' : ℝ≥0∞) (bR : tr.R b b')
  : tr.R (a + b) (a' + b') := by

  tr_whnf
  show extend (a + b) = a' + b'

  tr_subst a a' aR
  tr_subst b b' bR
  rfl

theorem seq_nnR_add
  (a : ℕ → ℝ≥0) (a' : summable) (aR : tr.R a a')
  (b : ℕ → ℝ≥0) (b' : summable) (bR : tr.R b b')
  : tr.R (a' + b') (a + b) := by
  sorry




axiom sum_xnnR_add :
  ∀ (f g : ℕ -> ℝ≥0), ∑'' i, (f + g) i = (∑'' i, f i) + (∑'' i, g i)

example : ((∞ : ℝ≥0∞) + 4) = ∞ := by rfl

theorem sum_nnR_add
  -- {α : Type*}
  -- [AddCommMonoid α]
  -- [TopologicalSpace α]
  [Param2a0 NNReal ENNReal]
--  : ∀ (u v : Nat → NNReal) (hu : Summable u) (hv : Summable v),
: ∀ (u v : summable),
  ((∑' i, (u + v) i) = ((∑' i, u i)) + ((∑' i, v i))) := by
  tr_by sum_xnnR_add

  let _ : Param00 Prop Prop := propParam.forget

  tr_advance
  tr_advance

  simp

  tr_advance
  apply summable_rel
  apply seq_nnR_add
  tr_advance
  tr_advance

  change paramNNR.R _ _
  -- apply Trale.Utils.denormalizeR

  apply R_add_xnnR
  apply summable_rel
  rfl
  apply summable_rel
  rfl

  -- tr_advance

  -- apply summable_rel
  -- apply seq_nnR_add
  -- -- tr_whnf
  -- -- tr_whnf at aR
  -- rfl
  -- rfl

  -- -- tr_whnf at aR
  -- tr_advance
  -- tr_advance
  -- -- subst_last
  -- tr_advance
  -- -- subst_last
  -- tr_advance
  -- apply R_eq

  -- apply_assumption
  -- apply_assumption

  -- tr_advance
  -- tr_advance


  -- rename_last this
  -- tr_whnf at this
  -- rw[←this]
  -- tr_whnf

  -- exact R_eq



  -- funext a
  -- rfl



  -- tr_advance




  -- -- change param_summable_seq.R ((_ : summable) + (_ : summable)) _

  -- apply R_add_xnnR


  -- tr_whnf





  -- tr_advance
  -- tr_advance
  -- tr_advance


  -- repeat tr_advance


  -- all_goals sorry
