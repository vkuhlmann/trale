import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Theories.Sorts

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


-- instance toArrow [Param α β cov con] [Param γ δ cov2 con2] : Param00 (α -> γ) (β -> δ) := by
--   tr_split

-- TODO Idea: split Param.R into own instance?

instance toArrow [Param00 α β] [Param00 γ δ] : Param00 (α -> γ) (β -> δ) := by
  tr_split

def applyR [p1 : Param00 α α'] [p2 : Param00 β β']
  (r3 : toArrow.R f f') (r1 : p1.R a a')
  : (p2.R (f a) (f' a')) := by

  exact r3 _ _ r1


-- macro "tr_advance" ppSpace colGt a:term a':term aR:term : tactic => `(tactic|
--   first
--   | assumption
--   | tr_intro a a' aR
--   | (tr_split_application; try (
--         (case' p2 => intro a a' aR);rotate_left 1); tr_whnf)

--   )

macro "close_PR_nR" : tactic => `(tactic|
  (
      have nR := by assumption;
      have PR : Param.R _ _ (_ : _ -> _) (_ : _ -> _) := by assumption
      tr_ident;
      exact PR _ _ nR
    )
  )

macro "tr_advance" : tactic => `(tactic|
  first
  | assumption
  | tr_intro _ _ _
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
  )


def I_Srec : forall P : I -> Sort 0, P I0 -> (forall i, P i -> P (IS i)) -> forall i, P i := by
  tr_by nat_rect2

  let _ : Param00 Prop Prop := propParam.forget

  have RN : Param2a3.{0} I Nat := by sorry
  have RN0 : tr.R I0 0 := by sorry
  have RNS m n : tr.R m n → tr.R (IS m) (Nat.succ n) := by sorry

  have _ : Param02a (Nat → Prop) (I → Prop) := by
    tr_advance

  tr_intro P P' PR
  -- case p1 =>
  --   tr_advance -- Needs Param02a I Nat

  tr_split
  case p1 =>
    show Param01 (P 0) (P' I0)
    tr_advance
    tr_advance

    tr_flip
    tr_from_map

    /-

    ```lean
    have nR := by assumption
    replace nR : Param.R .Map0 .Map0 ?a ?a' := nR
    ```

    ```plaintext
    Type mismatch
      nR
    has type
      Param.R MapType.Map0 MapType.Map0 a✝¹ a'✝
    but is expected to have type
      Param.R MapType.Map0 MapType.Map0 ?a ?a'

    ```
    -/

    have nR := by assumption
    replace nR : Param.R .Map0 .Map0 ?a ?a' := nR


    have PR : Param.R _ _ (_ : _ -> _) (_ : _ -> _) := by assumption



    -- We give them a name, else the tr.R fails
    show ?e1 → ?e2
    show tr.R ?e1 ?e2


    apply applyR

    tr_flip
    show Param.R .Map0 .Map0 ?f ?f'

    /-
    ```lean
    apply normalizeR
    ```

    Tactic `apply` failed: could not unify the conclusion of `@normalizeR`
      {a : ?α} → {b : ?β} → [p : Param ?α ?β ?cov ?con] → Param.R ?cov ?con a b → Param.R MapType.Map0 MapType.Map0 a b
    with the goal
      Param.R MapType.Map0 MapType.Map0 P' P

    Note: The full type of `@normalizeR` is
      {α : Sort ?u.339074} →
        {β : Sort ?u.339073} →
          {cov con : MapType} →
            {a : α} → {b : β} → [p : Param α β cov con] → Param.R cov con a b → Param.R MapType.Map0 MapType.Map0 a b
    -/


    exact PR.forget

    assumption


    -- have a : Param.R _ _ ?f ?f' := by assumption




    assumption

    ; assumption
    assumption





    tr_ident
    show P _ = P' _

    apply applyR


    have PR : Param.R _ _ _ _ := PR
    have PR : Param.R _ _ (_ : _ -> _) (_ : _ -> _) := by assumption


    close_PR_nR
    tr_advance



    have zeroR := by assumption
    tr_ident
    exact PR _ _ zeroR

  tr_split
  case p1 =>
    tr_flip

    tr_intro n n' nR -- needs Param02a I Nat

    tr_split

    case p1 =>
      show Param01 (P' n) (P n')
      have h1 := PR n n' nR
      tr_whnf at h1
      rw [h1]
      tr_ident


    have c := RNS n n' nR

    have h1 := PR _ _ c
    tr_whnf at h1

    /-
    h1 : P n'.succ = P' (IS n) := h1✝
    ⊢ Param10 (P' (IS n)) (P (n' + 1))
    -/

    rw [h1]
    tr_ident

  tr_intro n n' nR

  show Param10 (P n) (P' n')

  tr_ident
  exact PR _ _ nR
