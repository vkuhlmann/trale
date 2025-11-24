import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

import Mathlib
import Mathlib.Topology.Algebra.InfiniteSum.Defs


import TraleTest.Lemmas.TrAdvance
-- import TraleTest.Lemmas.SummableSequence

set_option trace.tr.utils true

namespace TraleTest.Transfer.SummableSequence
open TraleTest.Lemmas NNReal ENNReal

def extend : ℝ≥0 → ℝ≥0∞ := .some

def truncate : ℝ≥0∞ → ℝ≥0
  | .some r => r
  | .none => 0

def truncate_extend (r : ℝ≥0) : truncate (extend r) = r := by
  simp only [truncate, extend]

structure summable where
  seq : Nat → ℝ≥0
  is_summable : Summable seq

instance : CoeFun summable (fun _ => Nat → ℝ≥0) where
  coe s := s.seq

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


instance param_summable_seqExtended : Param40 summable (ℕ → ℝ≥0∞)
  := by tr_from_map fun x n => extend (x.seq n)

instance param_summable_seq : Param40 summable (ℕ → ℝ≥0)
  := by tr_from_map fun x n => x.seq n


theorem summable_rel (u : summable) (u' : ℕ → ℝ≥0)
  (uR : tr.R u u')
  : tr.R (∑' i, u i) (∑'' i, u' i) := by

  subst uR
  rw [←summable_matches_tsum u]
  rfl

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
  tr_whnf; simp
  tr_subst a' a aR
  tr_subst b' b bR
  congr


axiom sum_xnnR_add :
  ∀ (f g : ℕ → ℝ≥0), ∑'' i, (f + g) i = (∑'' i, f i) + (∑'' i, g i)

theorem sum_nnR_add
  [Param2a0 ℝ≥0 ℝ≥0∞]
: ∀ (u v : summable),
  ((∑' i, (u + v) i) = ((∑' i, u i)) + ((∑' i, v i))) := by
  tr_by sum_xnnR_add

  let _ : Param00 Prop Prop := propParam.forget

  repeat first
    | rfl
    | assumption
    | apply R_add_xnnR
    | apply summable_rel
    | apply seq_nnR_add
    | apply R_eq
    | tr_advance
