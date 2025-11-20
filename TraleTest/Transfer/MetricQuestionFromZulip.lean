import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Theories.Sorts

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

import Mathlib

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [hd2 : Fact (Module.finrank ℝ V = 2)]

-- #check Nat.prime

#check finDimVectorspaceEquiv
#check AddCommMonoid
#check LinearEquiv
#check Module.finrank

-- https://loogle.lean-lang.org/?q=MetricSpace%2C+NormedAddTorsor%2C+Module.finrank
#check EuclideanGeometry.oangle
#check EuclideanGeometry.oangle_self_left

def oangle_real
  [NormedAddCommGroup (ℝ × ℝ)]
  [InnerProductSpace ℝ (ℝ × ℝ)]
  [MetricSpace (ℝ × ℝ)]
  [NormedAddTorsor (ℝ × ℝ) (ℝ × ℝ)]
  [hd2 : Fact (Module.finrank ℝ (ℝ × ℝ) = 2)]
  [Module.Oriented ℝ (ℝ × ℝ) (Fin 2)]
  (p₁ p₂ p₃ : ℝ × ℝ) : Real.Angle
  := sorry

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
