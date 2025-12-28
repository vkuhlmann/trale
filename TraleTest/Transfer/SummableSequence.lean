import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Utils.Attr

import Trale.Utils.TrAdvance
import TraleTest.Lemmas.SummableSequence

set_option trace.tr.utils true

namespace TraleTest.Transfer.SummableSequence
open TraleTest.Lemmas Trale

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

#check (6 : Nat)
#check (Nat : Type)
--#check (Nat : Type 1)
#check ((Nat, Type) : Type × Type 1)
#check (((a : Nat) → Fin a) : Type)
#check (((a : Nat) → Fin a) : Type)

inductive MyTest where
   | mk (n : Nat) (a : Fin n) (b : Type)

#check MyTest.mk 4 9 Nat
#check MyTest


instance [Param00 α β] [Param00 γ δ] : Param00 (α -> γ) (β -> δ) := by
  tr_split

-- macro "tr_advance" : tactic => `(tactic|
--   first
--   | assumption
--   | tr_intro _ _ _
--   | (tr_split_application; try (
--         (case' p2 => intro _ _ _);rotate_left 1))

-- --   | aesop (rule_sets := [default, builtin, trale])
--   | apply R_add_xnnR
--   | refine R_sum_xnnR _ _ ?_
--   | exact R_eq
--   | apply seq_nnR_add
--   | fail "No step available"
--   )

#check Aesop.runRuleTac

example (a : nnR) (a' : xnnR)
     (b : nnR) (b' : xnnR)
     : Param.R .Map0 .Map0 (a + b) (a' + b') := by

     refine' _
     -- choose a using xxx

     -- aesop (rule_sets := [trale])

     sorry

-- example (a b c : nnR)
--      : (a + b) + c = c + (b + a) := by

--      -- rw [nnR_comm]
--      aesop


--      sorry

-- #check instParam
#printTraleInstances
#printTraleImpliedTranslations
#check Trale.arrowR_rel

#tr_add_translations_from_instances

set_option trace.debug true in
#tr_translate (∀ u : Nat, (Fin u) × summable)
#tr_translate ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v)

theorem sum_nnR_add : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_exact sum_xnnR_add

--   tr_solve

-- --   let _ : Param00 Prop Prop := propParam.forget

-- --   let _ := R_add_xnnR
-- --   let _ := R_sum_xnnR
-- --   let _ := R_eq

--   repeat first
--      | apply R_add_xnnR
--      | refine R_sum_xnnR _ _ ?_
--      | exact R_eq
--      | apply seq_nnR_add -- This one is optional
--      | tr_advance


--   tr_advance
--   tr_advance
--   tr_advance

--   show Param.R MapType.Map0 MapType.Map0 (Σ _ + Σ _) (Σ _ + Σ _)
-- --   show tr.R _ _
-- --   show tr.R (_ + _) (_ + _)
-- --   tr_flip
-- --   aesop (rule_sets := [trale])
-- --   apply R_add_xnnR




--   tr_advance
--   tr_advance
--   tr_advance
--   tr_advance
--   tr_advance
--   tr_advance
--   tr_advance
--   tr_advance
--   tr_advance
--   tr_advance
--   tr_advance
--   tr_advance

--   tr_advance
--   tr_advance


--   let eR := by assumption
--   refine' (instantiatePropR (eR _ _ _ _ _ _)).forget

--   assumption
--   assumption


#print sum_nnR_add
