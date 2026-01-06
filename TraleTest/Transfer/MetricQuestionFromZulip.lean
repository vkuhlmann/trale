import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Theories.Sorts
import Trale.Theories.Trans
import Trale.Utils.Glueing

import Trale.Utils.TrAdvance

import TraleTest.Research.equiv


-- import Mathlib
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine

open Module Complex
open scoped Affine EuclideanGeometry Real RealInnerProductSpace ComplexConjugate
open AffineSubspace EuclideanGeometry
open Trale


/-
https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/transport.20tactic/near/542850827

Jovan Gerbscheid
2:28 AM
Yes, I absolutely agree that actually integrating such a tool into to_additive would be a lot of extra work. But it could be interesting to see if it the tool also works in this context. There is indeed this issue in to_additive that we need a heuristic to figure out what to translate and what not, which is implemented in the additiveTest function that tells whether the type should be translated or not.

I look forward to seeing what is possible with this kind of framework!

One more example I have in mind, for which I also don't know if this is in scope, is in Euclidean geometry. The typical setup is

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)]
But proving things in this setup is equivalent to proving things with V = P = ℝ × ℝ, so it would be neat if you could replace V and P with ℝ × ℝ (using some equivalence
like the one given by finDimVectorspaceEquiv)
-/

section InReals
-- #check Nat.prime

variable
  [NormedAddCommGroup (ℝ × ℝ)]

instance : SeminormedAddCommGroup (ℝ × ℝ) := NormedAddCommGroup.toSeminormedAddCommGroup
instance : PseudoMetricSpace (ℝ × ℝ) := MetricSpace.toPseudoMetricSpace

-- abbrev x : NormedAddTorsor (ℝ × ℝ) (ℝ × ℝ) := sorry

variable
  [InnerProductSpace ℝ (ℝ × ℝ)]

-- #eval (inferInstanceAs (InnerProductSpace ℝ (ℝ × ℝ)))

variable
  [MetricSpace (ℝ × ℝ)] [NormedAddTorsor (ℝ × ℝ) (ℝ × ℝ)] [hd2 : Fact (Module.finrank ℝ (ℝ × ℝ) = 2)]
  [Module.Oriented ℝ (ℝ × ℝ) (Fin 2)]
  [Oriented ℝ (ℝ × ℝ) (Fin 2)]

#check finDimVectorspaceEquiv
#check AddCommMonoid
#check LinearEquiv
#check Module.finrank

-- https://loogle.lean-lang.org/?q=MetricSpace%2C+NormedAddTorsor%2C+Module.finrank
#check EuclideanGeometry.oangle
#check EuclideanGeometry.oangle_self_left
#check AffineSubspace.SOppSide.oangle_sign_eq_neg

#check Prod.seminormedAddCommGroup

def oangle_real
  [NormedAddCommGroup (ℝ × ℝ)]
  [InnerProductSpace ℝ (ℝ × ℝ)]
  [MetricSpace (ℝ × ℝ)]
  [NormedAddTorsor (ℝ × ℝ) (ℝ × ℝ)]
  [hd2 : Fact (Module.finrank ℝ (ℝ × ℝ) = 2)]
  [Module.Oriented ℝ (ℝ × ℝ) (Fin 2)]
  (p₁ p₂ p₃ : ℝ × ℝ) : Real.Angle
  := sorry

-- BEGIN Source: mathlib (Mathlib/Geometry/Euclidean/Angle/Oriented/Affine.lean)
-- Modified

-- set_option pp.universes true in
-- abbrev V := (ℝ × ℝ)
-- def oangle_sign_eq_neg'
--     -- [z : NormedAddCommGroup V]
--     -- let seminorm : SeminormedAddCommGroup V := z.toSeminormedAddCommGroup in
--     -- (_ : PseudoMetricSpace (ℝ × ℝ) := MetricSpace.toPseudoMetricSpace)
--     -- [InnerProductSpace ℝ (ℝ × ℝ)]
--     [x : @InnerProductSpace.{0, 0} Real V _ NormedAddCommGroup.toSeminormedAddCommGroup.{0}]
--     [y : @NormedAddTorsor.{0, 0} V V NormedAddCommGroup.toSeminormedAddCommGroup MetricSpace.toPseudoMetricSpace]
--     [hd2 : Fact (finrank ℝ V = 2)]
--     {s : AffineSubspace ℝ V} {p₁ p₂ p₃ p₄ : V}
--     (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃p₄ : s.SOppSide p₃ p₄) :
--     -- let x := inferInstanceAs (InnerProductSpace ℝ (ℝ × ℝ))
--     -- EuclideanGeometry.oangle (V := (ℝ×ℝ)) (p₁ -ᵥ p₄) (p₂ -ᵥ p₄)
--     @EuclideanGeometry.oangle V _ _ x _ y _ _ (p₁ -ᵥ p₄) (p₂ -ᵥ p₄)
--     -- (∡ p₁ p₄ p₂).sign = -(∡ p₁ p₃ p₂).sign
--      :=
--     sorry

-- set_option pp.universes true in
-- /-- Given two points in an affine subspace, the angles between those two points at two other
-- points on opposite sides of that subspace have opposite signs. -/
-- def oangle_sign_eq_neg
--     [NormedAddCommGroup (ℝ × ℝ)]
--     -- [InnerProductSpace ℝ (ℝ × ℝ)]
--     [x : @InnerProductSpace.{0, 0} Real (Prod.{0, 0} Real Real) _ NormedAddCommGroup.toSeminormedAddCommGroup.{0}]
--     [y : NormedAddTorsor.{0, 0} (Prod.{0, 0} Real Real) (Prod.{0, 0} Real Real)]
--     {s : AffineSubspace ℝ (ℝ × ℝ)} {p₁ p₂ p₃ p₄ : (ℝ × ℝ)}
--     (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃p₄ : s.SOppSide p₃ p₄) :
--     -- let x := inferInstanceAs (InnerProductSpace ℝ (ℝ × ℝ))
--     -- EuclideanGeometry.oangle (V := (ℝ×ℝ)) (p₁ -ᵥ p₄) (p₂ -ᵥ p₄)
--     @EuclideanGeometry.oangle (ℝ×ℝ) _ _ x _ y _ _ (p₁ -ᵥ p₄) (p₂ -ᵥ p₄)
--     -- (∡ p₁ p₄ p₂).sign = -(∡ p₁ p₃ p₂).sign
--      :=
--     sorry

  --   by
  -- have hp₁p₃ : p₁ ≠ p₃ := by rintro rfl; exact hp₃p₄.left_notMem hp₁
  -- rw [← (hp₃p₄.symm.trans (AffineSubspace.sOppSide_pointReflection hp₁ hp₃p₄.left_notMem)).oangle_sign_eq hp₁ hp₂,
  --   ← oangle_rotate_sign p₁, ← oangle_rotate_sign p₁, oangle_swap₁₃_sign,
  --   (sbtw_pointReflection_of_ne ℝ hp₁p₃).symm.oangle_sign_eq _]

-- END Source


end InReals

variable {V : Type*} {P : Type*}

noncomputable
instance
  -- [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [AddCommMonoid V]
  [Module ℝ V] [Free ℝ V]
  [hd2 : Fact (Module.rank ℝ V = 2)]
  : Param44 V (Fin 2 → ℝ) :=
  paramFromEquiv (finDimVectorspaceEquiv 2 hd2.out).toEquiv



instance
  : Param44 (Fin 2 → ℝ) (ℝ×ℝ)
  := by

  let cov (a : Fin 2 → ℝ) : (ℝ×ℝ) := (a 0, a 1)
  let con (a : ℝ×ℝ) : (Fin 2 → ℝ) := (match · with | 0 => a.1 | 1 => a.2)

  let cov_con_K (a) : cov (con a) = a := rfl
  let con_cov_K (a) : con (cov a) = a := by funext b; match b with | 0 => rfl | 1 => rfl

  tr_constructor

  -- R
  exact (cov · = ·)

  -- 4
  · exact cov
  · intro _ _; exact id
  · intro _ _; exact id
  · intro _ _ _; rfl

  -- 4
  · exact con
  · intro _ _ aF; subst aF; apply cov_con_K
  · intro _ _ aR; subst aR; apply con_cov_K
  · intro _ _ _; dsimp only [flipRel]

noncomputable
instance
  [AddCommMonoid V]
  [Module ℝ V] [Free ℝ V]
  [hd2 : Fact (Module.rank ℝ V = 2)]
  : Param44 V (ℝ×ℝ) :=
    Trale.Utils.glued
      (Map4_trans (β := Fin 2 → ℝ))
      (Map4_trans_flipped)
      rfl


  -- apply Trale.Utils.glued

  -- case p1 =>
  --   tr_from_map
  --   intro x
  --   exact (x 0, x 1)

  -- case p2 =>
  --   sorry
  --   -- tr_from_map
  --   -- intro (x, y) z
  --   -- match z with
  --   -- | 0 => exact x
  --   -- | 1 => exact y

  -- -- rw [Trale.Utils.R_eq_normalize_R]

  -- -- change (∀ (_ : _) (_ : _), _ = _) = _
  -- funext x y

  -- rw [@Trale.Utils.R_eq_normalize_R _]
  -- apply Eq.symm
  -- rw [@Trale.Utils.R_eq_normalize_R _]
  -- apply Eq.symm

  -- -- congr

  -- change ?lhs = ?rhs
  -- set lhs := ?lhs
  -- set rhs := ?rhs

  -- -- tr_whnf at rhs
  -- -- match h : lhs with
  -- -- | (_ -> _ -> (_ = _)) => sorry


  -- -- dsimp at lhs
  -- -- unfold Trale.Utils.paramFromMap at lhs


  -- tr_whnf

noncomputable
def
  R_dist
  -- [NormedAddCommGroup V]
  -- [InnerProductSpace ℝ V]
  [AddCommMonoid V]
  [Module ℝ V]
  [Free ℝ V]
  [pseudo : PseudoMetricSpace V]

  [Fact (Module.rank ℝ V = 2)]
  (a : V) (a' : Fin 2 → ℝ) (aR : tr.R a a')
  (b : V) (b' : Fin 2 → ℝ) (bR : tr.R b b')
  : (dist a b) = (dist a' b') := by

  unfold dist
  tr_subst a a' aR
  tr_subst b b' bR

  sorry

def
  R_dist_zero
  [AddCommMonoid V]
  [Module ℝ V]
  [Free ℝ V]
  [pseudo : PseudoMetricSpace V]

  [Fact (Module.rank ℝ V = 2)]
  (a : V) (a' : Fin 2 → ℝ) (aR : tr.R a a')
  (b : V) (b' : Fin 2 → ℝ) (bR : tr.R b b')
  : Param44 ((dist a b) = 0) ((dist a' b') = 0) := by

  unfold dist
  tr_subst a a' aR
  tr_subst b b' bR

  sorry


#check dist
#check pseudoMetricSpacePi.dist
#check NormedAddCommGroup

set_option trace.tr.utils true

instance
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [hd2 : Fact (Module.rank ℝ V = 2)]
  : Param40 (MetricSpace V) (MetricSpace (Fin 2 → ℝ)) := by

  let p := inferInstanceAs <| Param44 V (Fin 2 → ℝ)

  tr_from_map
  intro v
  let h2 := v.1
  let h1 := @v.eq_of_dist_eq_zero

  constructor
  change (∀ x y, _)
  apply fun x => Param.right' x @h1

  tr_intro x x' xR
  tr_intro y y' yR
  tr_intro h h' hR

  case p1 =>
    change Param.{0} _ _ _ _
    apply (R_dist_zero _ _ _ _ _ _).forget

    -- apply R_eq

    -- case bR => rfl

    -- apply Utils.flipR'
    -- apply R_dist (V := V)
    assumption
    assumption

  case p2 =>
    apply (R_eq _ _ _ _ _ _).forget
    assumption
    assumption



noncomputable
def metricEquiv'
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [hd2 : Fact (Module.rank ℝ V = 2)]
  -- (h : )
  : Param40 (MetricSpace V) (MetricSpace (Fin 2 → ℝ)) := by

  let p := inferInstanceAs <| Param44 V (Fin 2 → ℝ)

  tr_from_map
  intro v
  let h2 := v.1
  let h1 := @v.eq_of_dist_eq_zero

  -- let h1 := v.toPseudoMetricSpace
  -- obtain ⟨h1⟩ := v

  constructor

  -- Make parameters explicit
  change (∀ x y, _)
  -- refine ((?_ : _ → _) @h1)
  apply fun x => Param.right' x @h1

  -- have pseudoMetricEq : NormedAddCommGroup.toSeminormedAddCommGroup.toPseudoMetricSpace = h2 := by
  --   -- rfl
  --   sorry
  -- rw [pseudoMetricEq]

  -- tr_by h1

  tr_intro x x' xR
  -- tr_advance
  tr_intro y y' yR
  -- tr_advance
  tr_intro h h' hR
  -- tr_advance
  case p1 =>
    -- have : dist x' y' = 0 → dist x y = 0 := by
    --   unfold dist
    --   dsimp [pseudoMetricSpacePi]
    --   intro h
    --   tr_subst x' x xR
    --   tr_subst y' y yR

    --   let equiv := finDimVectorspaceEquiv 2 hd2.out
    --   let h3 := equiv.mul



    --   sorry

    tr_flip
    apply (R_eq _ _ _ _ _ _).forget

    show tr.R 0 0; exact rfl

    apply Utils.flipR'
    tr_whnf

    -- rw [←pseudoMetricEq]
    let h := R_dist (V := V)
    -- rw [pseudoMetricEq] at h
    apply h

    assumption
    assumption

  case p2 =>
    -- tr_subst x x' xR
    apply (R_eq _ _ _ _ _ _).forget
    assumption
    assumption



  -- intro x y h2

  -- replace h1 := @h1 (p.left x) (p.left y)

  -- specialize h1 h2
  -- #check dist



example : NormedAddCommGroup (ℝ × ℝ) := by tauto

noncomputable
example : InnerProductSpace ℝ (ℝ × ℝ) := by
  apply InnerProductSpace.ofNorm
  -- apply InnerProductSpace.complexToReal
  intro x y
  sorry



example : MetricSpace (ℝ × ℝ) := by infer_instance
example : NormedAddTorsor (ℝ × ℝ) (ℝ × ℝ) := by tauto
example : Fact (Module.finrank ℝ (ℝ × ℝ) = 2) := by constructor; simp
example : Module.Oriented ℝ (ℝ × ℝ) (Fin 2) := by
  constructor
  -- aesop
  sorry


variable
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [hd2 : Fact (Module.finrank ℝ V = 2)]
  [Module.Oriented ℝ V (Fin 2)]

#check Std.PRange.Bound
#check Orientation

def oangle_v_p
  {V : Type u_1} {P : Type u_2}
  [a1 : NormedAddCommGroup V]
  [a2 : InnerProductSpace ℝ V]
  [a3 : MetricSpace P]
  [a4 : NormedAddTorsor V P]
  [hd2 : Fact (Module.rank ℝ V = 2)]
  [a5 : Module.Oriented ℝ V (Fin 2)]
  (p₁ p₂ p₃ : P) : Real.Angle
  := by

  let a := finDimVectorspaceEquiv 2 hd2.out

  let b := a.toEquiv
  let c := paramFromEquiv b

  -- let c := oangle_real (a. p₁) p₂ p₃


  let : Param10 (Module.Oriented ℝ V (Fin 2)) (Module.Oriented ℝ (ℝ × ℝ) (Fin 2)) := by
    tr_from_map
    intro h

    constructor


    apply Module.Basis.orientation
    sorry

    -- constructor


    -- exact v
    -- sorry

  #check LinearEquiv

  -- revert V ... P

  -- hd2

  revert a1 a2 a3 a4 hd2 a5 p₁ p₂ p₃

  tr_by @oangle_real
  show Param10 (∀ (_ : NormedAddCommGroup (ℝ × ℝ)), (_ : Sort 1)) (∀ (_ : NormedAddCommGroup V), (_ : Sort _))

  -- apply Param_forall.Map1_forall

  tr_intro a a' aR




  tr_sorry sorry
  tr_sorry sorry


/-
EuclideanGeometry.oangle.{u_1, u_2} {V : Type u_1} {P : Type u_2} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [hd2 : Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]
  (p₁ p₂ p₃ : P) : Real.Angle

-/
