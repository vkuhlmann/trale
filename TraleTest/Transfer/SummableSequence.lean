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

instance [Param00 α β] [Param00 γ δ] : Param00 (α -> γ) (β -> δ) := by
  tr_split

macro "tr_advance" : tactic => `(tactic|
  first
  | assumption
  | tr_intro _ _ _
  | (tr_split_application; try (
        (case' p2 => intro _ _ _);rotate_left 1); tr_whnf)

  | apply R_add_xnnR
  | refine R_sum_xnnR _ _ ?_
  | exact R_eq
  | apply seq_nnR_add
  )

theorem sum_nnR_add : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_by sum_xnnR_add

  let _ : Param00 Prop Prop := propParam.forget

  tr_advance
  tr_advance
  tr_advance
  tr_advance
  tr_advance
  tr_advance
  tr_advance
  tr_advance
  tr_advance
  tr_advance
  tr_advance
  tr_advance
  tr_advance
  tr_advance
  tr_advance

  let eR := by assumption
  refine' (instantiatePropR (eR _ _ _ _ _ _)).forget

  assumption
  assumption
