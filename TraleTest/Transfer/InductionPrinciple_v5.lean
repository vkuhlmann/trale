import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Utils.TrApplyAssumption
import Trale.Theories.Sorts

open Trale.Utils Trale

set_option trace.tr.utils true

variable (I : Type _) (I0 : I) (IS : I -> I)
variable (to_nat : I -> Nat) (of_nat : Nat -> I)

def nat_rect2 : forall P : Nat -> Sort u, P 0 -> (forall n, P n -> P (n + 1)) -> forall n, P n := by
  intro P P0 Pstep
  intro n
  induction n with
  | zero =>
    exact P0
  | succ m Pm =>
    exact Pstep m Pm

def arrow_02a_rel
  {p1 p2}
  {f : α → β}
  {f' : α' → β'}
  (r2 : (Trale.Map2a_arrow (p1 := p1) (p2 := p2)).flip.R f f')
  (r1 : p1.R a' a)
  :  (p2.flip.toBottom.R (f a) (f' a')) := by

  exact r2 _ _ r1

macro "tr_step_rel" : tactic => do
  let o1 ← `(tactic|apply flipR')
  let o2 ← `(tactic|rw [←Trale.param44_ident_symm])
  --
  let main ←  `(tactic|
    (apply denormalizeR;
     (first| apply arrow_02a_rel);
     assumption
    )
  )
  --
  `(tactic|
    first
    | $main;
    | $o2; $main;
    | $o1; $main;
    | $o1; $o2; $main;
  )

macro "tr_advance" : tactic => `(tactic|
  first
  | assumption
  | apply_assumption
  | tr_intro _ _ _
  | tr_flip; tr_intro _ _ _
  | tr_split
  | tr_flip; tr_split


  | exact RN0
  | (
      have nR := by assumption;
      tr_ident;
      exact PR _ _ nR
    )

  | (tr_split_application; try (
        (case' p2 => intro _ _ _);rotate_left 1); tr_whnf)
  | (tr_flip; tr_split_application; try (
        (case' p2 => intro _ _ _);rotate_left 1); tr_whnf)

  | (refine (Trale.instantiatePropR_bi ?_).forget;
     tr_step_rel)
  | fail "No step available"
  )

def I_Srec : forall P : I -> Sort 0, P I0 -> (forall i, P i -> P (IS i)) -> forall i, P i := by
  tr_by nat_rect2

  have RN : Param2a3.{0} I Nat := by sorry
  have RN0 : tr.R I0 0 := by sorry
  have RNS {m n} : tr.R m n → tr.R (IS m) (Nat.succ n) := by sorry

  let pAux1 : Param02a (Nat → Prop) (I → Prop) := by
    apply Trale.Map2a_arrow_flipped (p2 := Trale.sortParam .Map4 .Map4)
    -- tr_advance

  tr_advance
  -- rename_last P P' PR
  -- tr_whnf at PR
  -- dsimp [inferInstance, instParam] at PR

  tr_advance
  ·
    tr_advance
    tr_advance

    -- change ∀ _ _ _, Param.R (self := Trale.sortParam .Map4 .Map4) _ _ _ _ at PR

    -- let abc :
    --   Param.R MapType.Map0 MapType.Map0 (P a) (P' a')

    -- change ∀ _ _ _, Param2a2a _ _ at PR
    -- change ∀ _ _ _, Param.R (self := Trale.sortParam .Map4 .Map4) _ _ (P a) (P' a') at PR
    -- change ∀ _ _ _, Param.R (self := Trale.sortParam .Map4 .Map4) (P a) (P' a') at PR

    -- change Param ?cov ?con _ _
    -- let pForget := fun {α β X Y} h1 h2 (p : Param X Y α β) => Param.forget (X' := .Map0) (Y' := .Map1) h1 h2 p

    -- apply_assumption [Param.forget (X' := ?cov) (Y' := ?con)]

    -- apply_assumption [Param.forget (X' := .Map0) (Y' := .Map1)]

    tr_apply_assumption
    exact aR

  tr_advance
  ·
    tr_advance
    rename_last i' i iR
    tr_advance
    tr_flip

    tr_apply_assumption
    -- apply (PR _ _ _).forget
    exact iR

    tr_flip
    tr_advance

    -- exact RNS iR
    apply_assumption
    assumption

    -- rename_last j j' jR

    tr_apply_assumption
    tr_advance
    -- exact (PR _ _ jR).forget

  tr_advance
  -- rename_last j j' jR
  tr_apply_assumption
  tr_advance
  -- exact (PR _ _ jR).forget
