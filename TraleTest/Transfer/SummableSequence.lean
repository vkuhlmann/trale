import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

import TraleTest.Utils.Lemmas.SummableSequence

set_option trace.tr.utils true

/-

⊢ Param (b a) (b' a')

tr_split_application'

[p1] ⊢ Param A A'
[aR] ⊢ ?p1.R a a'
[p2]   (a a' aR) -- values erased by generalisation
     ⊢ Param (b a) (b' a')

Solve:
exact p2

--------------

⊢ Param (b a) (b' a')

tr_split_app

[p1] ⊢ Param A A'

[aR] ⊢ ?p1.R a a'

[p2]   (a a' aR) -- values erased by generalisation
     ⊢ Param (B a) (B' a')

[bR]   (a a' aR)
     ⊢ ?p2.R (b a) (b' a')

[instantiate] ⊢ ?p2.R x x' -> Param x x'

Solve:
exact instantiate (bR a a' aR)



For example:
A : Type := nnR
A' : Type := xnnR
a : A := 4
a' : A' := .fin 4

let B : nnR → Type := fun (_ :  nnR) ↦ Prop
let B': xnnR → Type := fun (_ : xnnR) ↦ Prop
let b (a : nnR)  : B a  := (a  = a)
let b (a' : nnR) : B a' := (a'  = a')


⊢ Param (4 = 4) (.fin 4 = .fin 4)
⊢ Param (b a) (b' a')

tr_split_app

[p1] ⊢ Param A A'
     ⊢ Param nnR xnnR

[aR] ⊢ ?p1.R a a'
     ⊢ ?p1.R 4 (.fin 4)

[p2]   (a a' aR) -- values erased by generalisation
     ⊢ Param (B a) (B' a')
     ⊢ Param Prop Prop

[bR]   (a a' aR) -- values erased by generalisation
     ⊢ ?p2.R (b a) (b' a')
     ⊢ ?p2.R (a = a) (a' = a')

[instantiate] ⊢ ?p2.R (b a) (b a') -> Param (b a) (b' a')
              ⊢ ?p2.R (4 = 4) (.fin 4 = .fin 4) -> Param (4 = 4) (.fin 4 = .fin 4)

[instantiate] ⊢ ?p2.R x x' -> Param x x'

Solve:
exact instantiate (bR a a' aR)

-/


-- Code based on 'summable.v' example by Trocq Rocq plugin developers.

theorem sum_nnR_add : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_by sum_xnnR_add

  -- TODO: Make this work with infer_instance
  -- We need to use `propParam` instance for `Param Prop Prop`, not the
  -- instance defined by equality.
  let _ : Param00 Prop Prop := propParam.forget

  let eqParam : Param00 (xnnR → xnnR → Prop) (nnR → nnR → Prop) := by
    tr_split; tr_split

  -- Part 1: split the foralls
  tr_intro a a' aR
  tr_intro b b' bR

  -- Part 2: Relate rhs:  X  =  *X*
  --                            ___
  --
  tr_split_application' c c' cR by
    show tr.R (Σ a + Σ b) (Σ a' + Σ b')
    apply R_add_xnnR

    · show tr.R (Σ a') (Σ a)
      exact R_sum_xnnR a' a aR
    · show tr.R (Σ b') (Σ b)
      exact R_sum_xnnR b' b bR

  -- Part 3: Relate lhs:  *X*  =  X
  --                      ___
  --
  tr_split_application' d d' dR by
    show tr.R (Σ (a + b)) (Σ (a' + b'))
    apply R_sum_xnnR

    -- FIXME: Why is it the swapped order by default?
    -- show tr.R (a + b) (a' + b')
    show tr.R (a' + b') (a + b)
    apply seq_nnR_add

    · exact aR
    · exact bR

  show Param10 (d = c) (d' = c')
  -- Part 4: Relate eq:  X  *=*  X
  --                        ___
  --
  tr_split_application e e' eR by
    exact R_eq

  -- Part 5: Use relations to make the relation trivial
  --
  dsimp
  show Param10 (e d c) (e' d' c')

  /-
  By the Param rules of lambda abstraction and application, we can get the goal
  relation as:
  -/
  have goalTypeR : Param.R _ _ (e d c) (e' d' c') := eR d d' dR c c' cR
  /-
  This is a relation for the 'propParam' Param. I.e. `Param Prop Prop`.
  We use `instantiatePropR` to convert it to the Param between those types.
  -/
  exact (instantiatePropR goalTypeR).forget


-- Minimal
theorem sum_nnR_add_minimal : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_by sum_xnnR_add

  let _ : Param00 Prop Prop := propParam.forget
  let eqParam : Param00 (xnnR → xnnR → Prop) (nnR → nnR → Prop) := by
    repeat tr_split

  tr_intro _ _ aR
  tr_intro _ _ bR
  tr_split_application c c' cR by
    apply R_add_xnnR
    · exact R_sum_xnnR _ _ aR
    · exact R_sum_xnnR _ _ bR

  tr_split_application d d' dR by
    apply R_sum_xnnR
    apply seq_nnR_add
    · exact aR
    · exact bR

  tr_split_application e e' eR by
    exact R_eq

  exact (instantiatePropR (eR d d' dR c c' cR)).forget
