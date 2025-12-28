import Mathlib

import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent

import Trale.Theories.Forall

import TraleTest.Lemmas.Modulo
import Trale.Utils.TrAdvance

open TraleTest.Lemmas Trale

instance : Param40 (Modulo (n + 1)) (Fin (n + 1)) := by
  tr_from_map

  intro a
  constructor

  case val =>
    exact a.repr

  case isLt =>
    simp [Modulo.repr]

    exact smallerThanMod _ _

-- def sum_R
--   [AddCommMonoid γ]
--   [AddCommMonoid γ']
--   {f : ∀ _ : ℕ, γ}
--   {f' : ∀ _ : ℕ, γ'}
--   {g : ∀ _ : γ, Sort _}
--   {g' : ∀ _ : γ', Sort _}
--   (p : ∀ b b', Param10 (f b) (f' b'))

--   : Param10 (g $ ∑ b ∈ {1, 2, 3}, f b) (g' $ ∑ b ∈ {1, 2, 3}, f' b)
--   := by

-- def sum_R
--   [AddCommMonoid γ]
--   [AddCommMonoid γ']
--   {f : ∀ _ : ℕ, γ}
--   {f' : ∀ _ : ℕ, γ'}
--   {g : ∀ _ : γ, Sort _}
--   {g' : ∀ _ : γ', Sort _}
--   (p : ∀ b b', Param10 (f b) (f' b'))

--   : Param10 (g $ f) (g $ f')
--   := by

-- def congr_fun
--   Param40
--   : Param40 (f a) (f a')


theorem P1 : ∀ f : (a : Nat) → Fin (a+1),
             ∑ b ∈ {1, 2, 3}, (f b).val ≤ 6
  := by
  simp
  omega


-- theorem P1'_auto : ∀ f : (a : Nat) → Modulo (a+1),
--               ∑ b ∈ {1, 2, 3}, (f b).repr ≤ 6 := by
--   tr_by P1
--   repeat tr_advance
--   funext b
--   specialize

open Lean Elab Tactic Meta in
elab "apply_assumption_specialised_3" a:term "," a':term "," aR:term : tactic => withMainContext do
  for h in ← getLCtx do
    -- if (h.userName == `fR) then
    try
      withoutRecover <|
        evalTactic (← `(tactic|apply ($(mkIdent h.userName) $a $a' $aR)))
    catch _ =>
      -- trace[debug] s!"Got error {←e.toMessageData.toString}"
      continue

    -- We found an assumption, successfully exit.
    return

  throwTacticEx `apply_assumption_specialised (←getMainGoal)
    "Failed to find assumption"
    -- (return ←evalTactic (← `(tactic|apply ($(mkIdent h.userName) $a $as*))))
    -- <|> pure ()


set_option trace.debug true

theorem P1' : ∀ f : (a : Nat) → Modulo (a+1),
              ∑ b ∈ {1, 2, 3}, (f b).repr ≤ 6
  := by

  tr_by P1

  tr_intro f f' fR
  tr_advance
  tr_advance

  tr_ident
  repeat1 (apply congr <;> try rfl)

  funext b
  apply Eq.symm
  apply_assumption_specialised_3 b, b, rfl
