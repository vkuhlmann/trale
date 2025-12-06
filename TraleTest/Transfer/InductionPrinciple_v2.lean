import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Theories.Sorts

open Trale.Utils

set_option trace.tr.utils true

variable (I : Type _) (I0 : I) (IS : I -> I)
variable (to_nat : I -> Nat) (of_nat : Nat -> I)

#check
  let p : Param44 Nat String := ?p
  (p : Param .Map0 .Map1 Nat String)


-- #check
--   let p1 : Param03.{5} Nat String := ?p1
--   let p2 : Param40.{1} Nat String := ?p2
--   (Param_arrow.Map4_arrow p1 p2).R


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
  -- [toArrow : Param00 (α → β) (α' → β')]
  (r3 : toArrow.R f f') (r1 : p1.R a a')
  : (p2.R (f a) (f' a')) := by

  exact r3 _ _ r1
#check Lean.Meta.whnfD

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
  )


def I_Srec : forall P : I -> Sort 0, P I0 -> (forall i, P i -> P (IS i)) -> forall i, P i := by
  tr_by nat_rect2

  -- let propParam00 : Param00 Prop Prop := propParam.forget
  -- let propParam10 : Param10 Prop Prop := propParam.forget
  -- let propParam2a0 : Param2a0 Prop Prop := propParam.forget

  have RN : Param2a3.{0} I Nat := by sorry
  have RN0 : tr.R I0 0 := by sorry
  have RNS m n : tr.R m n → tr.R (IS m) (Nat.succ n) := by sorry

  let pAux1 : Param02a (Nat → Prop) (I → Prop) := by
    tr_advance

  tr_intro P P' PR
  -- case p1 =>
  --   tr_advance -- Needs Param02a I Nat
  -- unfold inferInstance at PR

  unfold inferInstance at PR

  tr_split
  case p1 =>
    show Param01 (P 0) (P' I0)
    tr_advance
    tr_advance

    refine (Trale.instantiatePropR_bi ?_).forget
    apply flipR'
    rw [←Trale.param44_ident_symm]
    refine PR _ _ ?_
    assumption

    -- tr_whnf
    -- apply Eq.symm
    -- unfold inferInstance
    -- exact PR (by assumption) (by assumption) (by assumption)




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

    -- have nR := by assumption
    -- replace nR : Param.R .Map0 .Map0 _ _ := nR
    -- -- replace nR : Param.R .Map0 .Map0 ?a ?a' := nR


    -- -- have PR : Param.R _ _ (_ : _ -> _) (_ : _ -> _) := by assumption



    -- -- We give them a name, else the tr.R fails
    -- show ?e1 → ?e2
    -- show tr.R ?e1 ?e2

    -- refine applyR (p1 := RN.toBottom) (p2 := propParam00) (r1 := ?r1) (r3 := ?r3)

    -- -- apply applyR (p1 := RN.toBottom) (p2 := propParam00)

    -- case r1 => assumption

    -- tr_flip
    -- show Param.R .Map0 .Map0 ?f ?f'

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


    /-
    ```lean
    exact flipR (normalizeR PR)
    ```

    synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
      toArrow
    inferred
      Param.toBottom inferInstance
    -/
    -- exact flipR (normalizeR PR)

    -- unfold inferInstance at PR
    -- unfold

    -- have h := @normalizeR _ _ _ _ _ _ toArrow (flipR PR)

    -- have type1 := @Param.R MapType.Map0 MapType.Map0 (I → Prop) (Nat → Prop) (Param.flip inferInstance).toBottom P' P
    -- have type2 := @Param.R MapType.Map0 MapType.Map0 (I → Prop) (Nat → Prop) toArrow P' P

    -- have h := normalizeR (flipR PR)

    -- have eq : (Param.flip pAux1).toBottom = toArrow := by
    --   unfold pAux1
    --   unfold toArrow
    --   unfold inferInstance
    --   unfold Param.flip
    --   unfold flipRel
    --   unfold Param.toBottom
    --   unfold Param_arrow.Map0_arrow
    --   unfold Param.forget
    --   dsimp [coeMap]

    --   /-
    --   ⊢ { R := fun a b => Param.R MapType.Map2a MapType.Map0 a b, covariant := { }, contravariant := { } } =
    --     {
    --       R := fun f f' =>
    --         ∀ (a : I) (a' : Nat), Param.R MapType.Map2a MapType.Map3 a a' → Param.R MapType.Map0 MapType.Map0 (f a) (f' a'),
    --       covariant := { }, contravariant := { } }
    --   -/

    --   dsimp [Param_arrow.Map2a_arrow]
    --   /-

    --   ⊢ { R := fun a b => ∀ (a_1 : I) (a' : Nat), Param.R MapType.Map2a MapType.Map3 a_1 a' → propParam2a0.1 (a a_1) (b a'),
    --     covariant := { }, contravariant := { } } =
    --   {
    --     R := fun f f' =>
    --       ∀ (a : I) (a' : Nat), Param.R MapType.Map2a MapType.Map3 a a' → Param.R MapType.Map0 MapType.Map0 (f a) (f' a'),
    --     covariant := { }, contravariant := { } }

    --   Oud:
    --   ⊢ {
    --       R := fun a b =>
    --         ∀ (a_1 : I) (a' : Nat),
    --           Param.R MapType.Map2a MapType.Map3 a_1 a' → Param.R MapType.Map4 MapType.Map4 (a a_1) (b a'),
    --       covariant := { }, contravariant := { } } =
    --     {
    --       R := fun f f' =>
    --         ∀ (a : I) (a' : Nat), Param.R MapType.Map2a MapType.Map3 a a' → Param.R MapType.Map0 MapType.Map0 (f a) (f' a'),
    --       covariant := { }, contravariant := { } }
    --   -/
    --   congr


    -- rw[eq] at h
    -- exact h


    -- have a : Param.R _ _ ?f ?f' := by assumption




    -- assumption

    -- ; assumption
    -- assumption





    -- tr_ident
    -- show P _ = P' _

    -- apply applyR


    -- have PR : Param.R _ _ _ _ := PR
    -- have PR : Param.R _ _ (_ : _ -> _) (_ : _ -> _) := by assumption


    -- close_PR_nR
    -- tr_advance



    -- have zeroR := by assumption
    -- tr_ident
    -- exact PR _ _ zeroR

  tr_split
  case p1 =>
    tr_advance
    tr_advance

    case p1 =>
      show Param01 (P' _) (P _)

      -- tr_ident
      -- apply Eq.symm
      -- exact PR _ _ (by assumption)

      refine (Trale.instantiatePropR_bi ?_).forget
      refine PR _ _ ?_
      assumption

    -- tr_ident
    -- apply Eq.symm
    -- have := RNS (by assumption) (by assumption) (by assumption)
    -- exact PR _ _ (by assumption)

    -- have := RNS _ _ (by assumption)

    -- refine (Trale.instantiatePropR_bi ?_).forget
    -- exact PR _ _ (by assumption)

    refine (Trale.instantiatePropR_bi ?_).forget
    refine PR _ _ ?_
    refine RNS _ _ ?_
    assumption

  tr_intro n n' nR

  refine (Trale.instantiatePropR_bi ?_).forget
  apply flipR'
  rw [←Trale.param44_ident_symm]
  refine PR _ _ ?_
  assumption
