
import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application

import Mathlib
import Mathlib.Topology.Algebra.InfiniteSum.Defs


import Trale.Utils.TrAdvance
set_option trace.tr.utils true

namespace TraleTest.Transfer.SummableSequence4
open NNReal ENNReal Trale

def extend : ℝ≥0 → ℝ≥0∞ := .some

def truncate : ℝ≥0∞ → ℝ≥0
  | .some r => r
  | .none => 0

def truncate_extend (r : ℝ≥0) : truncate (extend r) = r := by
  simp only [truncate, extend]

structure summable where
  seq : Nat → ℝ≥0
  is_summable : Summable seq

instance : CoeFun summable (fun _ => Nat → ℝ≥0) := ⟨(·.seq)⟩
  -- coe s := s.seq

instance : Add summable := ⟨fun x y => ⟨x.seq + y.seq, x.is_summable.add y.is_summable⟩⟩
  -- add x y := ⟨x.seq + y.seq, x.is_summable.add y.is_summable⟩

instance paramNNR : Param42b ℝ≥0 ℝ≥0∞
  := by tr_from_map truncate_extend

instance : Param42b ℝ≥0 (WithTop ℝ≥0) := paramNNR

#check tsum

-- BEGIN Source: mathlib's tprod+tsum
-- Modified

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

-- END Source

#print tsum_extended_def

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


-- instance param_summable_seqExtended : Param40 summable (ℕ → ℝ≥0∞)
--   := by tr_from_map fun x n => extend (x.seq n)

-- instance param_summable_seq : Param40 summable (ℕ → ℝ≥0)
--   := by tr_from_map fun x => x.seq


def zeroSum : summable := by
  refine ⟨fun n => 0, ⟨0, ?_⟩⟩
  simp only [HasSum, Finset.sum_const_zero, tendsto_const_nhds_iff]

/-
# Listing 26
-/
open Classical in
noncomputable
def to_summable
  (seq : ℕ → ℝ≥0) : summable :=
  if h : Summable seq then ⟨seq, h⟩ else zeroSum

/-
# Other
-/

def truncate_extend_sequence (r) : to_summable (summable.seq r) = r := by
  unfold to_summable
  split
  · rfl
  · exfalso
    apply_assumption
    exact r.is_summable


-- noncomputable
-- instance param_summable_seq_extended : Param42b summable (ℕ → ℝ≥0)
--   := by tr_from_map truncate_extend_sequence

noncomputable
instance param_summable_seq_extended : Param2a4 summable (ℕ → ℝ≥0)
  := by tr_from_map truncate_extend_sequence


#check ⊤

theorem R_summable (u : summable) (u' : ℕ → ℝ≥0)
  (uR : tr.R u u')
  : tr.R (∑' i, u i) (∑'' i, u' i) :=
  sorry
  -- by

  -- -- rw [←uR]
  -- let x := summable_matches_tsum u
  -- tr_whnf
  -- simp [extend]
  -- rw [x]


  -- rw []
  -- rfl

-- example (u : ℕ → ℝ≥0)
--   : truncate (∑'' i, u i) = (∑' i, u i) := by
--   apply Eq.symm

--   apply R_summable

-- #check (⊔ a : _, _)

theorem R_add_ENNReal
  (a : ℝ≥0) (a' : ℝ≥0∞) (aR : tr.R a a')
  (b : ℝ≥0) (b' : ℝ≥0∞) (bR : tr.R b b')
  : tr.R (a + b) (a' + b') := by
  -- sorry

  tr_whnf
  show extend (a + b) = a' + b'

  tr_subst a a' aR
  tr_subst b b' bR
  rfl

-- theorem R_add_summable
--   (a : summable) (a' : ℕ → ℝ≥0) (aR : tr.R a a')
--   (b : summable) (b' : ℕ → ℝ≥0) (bR : tr.R b b')
--   : tr.R (a + b) (a' + b') := by
--   sorry
  -- tr_whnf
  -- tr_subst a a' aR
  -- tr_subst b b' bR
  -- congr

#check HasSum

theorem sum_nnR_add' (u v : summable)
: ∑' i, (u i + v i) = (∑' i, u i) + (∑' i, v i) :=
  Summable.tsum_add u.is_summable v.is_summable

/-
theorem sum_xnnR_add' (u v : ℕ → ℝ≥0) :
  ∑'' i, (u + v) i = (∑'' i, u i) + (∑'' i, v i) := by

  revert u v
  tr_by sum_nnR_add'



  tr_advance
  tr_advance
  tr_advance



  apply R_add_ENNReal
  apply R_summable
  -- rw [truncate_sequence]
  rfl
  apply R_summable
  rfl

  tr_advance
  repeat rw [to_summable]
  -- simp
  rw [tsum_extended_def]
  split
  rename_i h1

  dsimp
  split
  rename_i h2





  first
    | try_this apply R_add_ENNReal
    | apply R_summable
    | apply R_add_summable
    | apply R_eq
    | tr_advance


  tr_advance
  tr_advance
  tr_advance
  tr_advance


  -- repeat first
  --   | apply R_add_ENNReal
  --   | apply R_summable
  --   | apply R_add_summable
  --   | apply R_eq
  --   | tr_advance




  tr_sorry sorry
-/
