import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Attr
import Trale.Utils.TrAdvance
import Trale.Utils.ParamFromFunction

import Mathlib
import Mathlib.Topology.Algebra.InfiniteSum.Defs

namespace TraleTest.Transfer.SummableSequence2

open NNReal ENNReal Trale

section R_ENNReal

def extend : ℝ≥0 → ℝ≥0∞ := .some

def truncate : ℝ≥0∞ → ℝ≥0
  | .some r => r
  | .none => 0

def truncate_extend (r : ℝ≥0) : truncate (extend r) = r := by
  simp only [truncate, extend]

instance paramNNR : Param42b ℝ≥0 ℝ≥0∞
  := by tr_from_map truncate_extend

instance : Param42b ℝ≥0 (WithTop ℝ≥0) := paramNNR

end R_ENNReal


section summable

structure summable where
  seq : Nat → ℝ≥0
  is_summable : Summable seq

instance : CoeFun summable (fun _ => Nat → ℝ≥0) := ⟨(·.seq)⟩
  -- coe s := s.seq

instance : Add summable := ⟨fun x y => ⟨x.seq + y.seq, x.is_summable.add y.is_summable⟩⟩
  -- add x y := ⟨x.seq + y.seq, x.is_summable.add y.is_summable⟩


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

#check Summable.tsum_add

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

end summable

section R_summable

instance param_summable_seqExtended : Param40 summable (ℕ → ℝ≥0∞)
  := by tr_from_map fun x n => extend (x.seq n)

instance param_summable_seq : Param40 summable (ℕ → ℝ≥0)
  := by tr_from_map fun x => x.seq

@[trale]
theorem R_summable (u : summable) (u' : ℕ → ℝ≥0)
  (uR : tr.R u u')
  : tr.R (∑' i, u i) (∑'' i, u' i) :=
  -- sorry
  by

  subst uR
  rw [←summable_matches_tsum u]
  rfl

-- example (u : ℕ → ℝ≥0)
--   : truncate (∑'' i, u i) = (∑' i, u i) := by
--   apply Eq.symm

--   apply R_summable

-- #check (⊔ a : _, _)

@[trale]
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
#check ∑ _, _

@[trale]
theorem R_add_summable
  (a : summable) (a' : ℕ → ℝ≥0) (aR : tr.R a a')
  (b : summable) (b' : ℕ → ℝ≥0) (bR : tr.R b b')
  : tr.R (a + b) (a' + b') := by
  tr_whnf; simp
  tr_subst a a' aR
  tr_subst b b' bR
  congr


theorem param_summable_seq_injective
  {a b : summable}
  (h : param_summable_seq.right a = param_summable_seq.right b)
  : a = b := by
  change (summable.seq _) = (summable.seq _) at h

  obtain ⟨a_seq, a_sum⟩ := a
  obtain ⟨b_seq, b_sum⟩ := b

  dsimp [extend] at h

  have : a_seq = b_seq := by
    funext x
    apply congrFun at h
    exact h x

  subst this
  rfl



@[trale]
def R_eq_seq_summable'
  (a :  ℕ → ℝ≥0) (a' : summable) (aR : tr.R a a')
  (b :  ℕ → ℝ≥0) (b' : summable) (bR : tr.R b b')
  : Param40 (a = b) (a' = b') := by
  tr_from_map
    fun h => param_summable_seq_injective (Eq.trans (.trans aR h) bR.symm)


end R_summable
