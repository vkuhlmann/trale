import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
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

  #check
    let tsepArray : Lean.Syntax.TSepArray `term "," := ?td
    let els := tsepArray.getElems
    sorry

def I_Srec : forall P : I -> Sort 0, P I0 -> (forall i, P i -> P (IS i)) -> forall i, P i := by
  tr_by nat_rect2

  have RN : Param2a3.{0} I Nat := by sorry
  have RN0 : tr.R I0 0 := by sorry
  have RNS {m n} : tr.R m n → tr.R (IS m) (Nat.succ n) := by sorry

  -- let _ : Param00 Prop Prop := propParam.forget

  let pAux1 : Param02a (Nat → Prop) (I → Prop) := by
    tr_advance

  tr_advance
  rename_last P P' PR
  tr_advance
  ·
    tr_advance
    tr_advance

    -- tr_flip
    tr_whnf at PR
    -- apply denormalizeR

    tr_flip
    -- (refine (instantiatePropR ?_).forget; apply aR)
    refine (Trale.instantiatePropR_bi ?_).forget
    apply PR
    exact aR


    -- (refine (Trale.instantiatePropR_bi ?_).forget;
    --  tr_step_rel)


    -- apply PR

    -- tr_flip
    -- tr_split_application

    -- tr_advance
    -- tr_advance

  tr_advance
  ·
    tr_advance
    rename_last i' i iR
    tr_advance
    -- tr_flip
    refine (Trale.instantiatePropR_bi ?_).forget
    exact PR _ _ iR

    tr_flip
    tr_advance

    exact RNS iR
    -- apply_assumption
    rename_last j j' jR

    -- apply flipR'
    refine (Trale.instantiatePropR_bi ?_).forget
    apply flipR'
    rw [←Trale.param44_ident_symm]
    -- apply denormalizeR

    -- apply_assumption
    exact PR _ _ jR

    -- apply arrow_02a_rel

    -- assumption

    -- tr_step_rel

    -- tr_advance

  tr_advance
  tr_advance
  tr_advance
