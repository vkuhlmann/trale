import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Theories.Sorts
-- import Mathlib

-- #eval Set.empty
open Trale.Utils Trale

set_option trace.tr.utils true

variable (I : Type _) (I0 : I) (IS : I -> I)
variable (to_nat : I -> Nat) (of_nat : Nat -> I)

#check
  let p : Param44 Nat String := ?p
  (p : Param .Map0 .Map1 Nat String)


-- #check
--   let p1 : Param03.{5} Nat String := ?p1
--   let p2 : Param40.{1} Nat String := ?p2
--   (Trale.Map4_arrow p1 p2).R


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

def arrow_02a_rel
  {p1 p2}
  {f : α → β}
  {f' : α' → β'}
  (r2 : (Trale.Map2a_arrow (p1 := p1) (p2 := p2)).flip.R f f')
  (r1 : p1.R a' a)
  :  (p2.flip.toBottom.R (f a) (f' a')) := by

  exact r2 _ _ r1

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
    -- | $main;
    -- | $o2; $main;
    -- -- | $o1; (first | $main; | $o2; $main;) -- this works but is less readable
    -- | $o1; $main;
    -- | $o1; $o2; $main;
    | $main;
    | $o2; $main;
    | $o1; $main;
    | $o1; $o2; $main;
  )

macro "tr_advance" : tactic => `(tactic|
  first
  -- | run_tac
  --     trace[tr.utils] s!"Doing tr_advance"
  --     -- Lean.Meta.throwTacticEx `debug "aaa"
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

  -- | run_tac
  --     trace[tr.utils] s!"Trying split_application"
  --     Lean.Meta.throwTacticEx `debug "aaa"

  | (tr_split_application; try (
        (case' p2 => intro _ _ _);rotate_left 1); tr_whnf)
  | (tr_flip; tr_split_application; try (
        (case' p2 => intro _ _ _);rotate_left 1); tr_whnf)

  | (refine (Trale.instantiatePropR_bi ?_).forget;
     tr_step_rel
    --  repeat apply_assumption
    )
  )





def I_Srec : forall P : I -> Sort 0, P I0 -> (forall i, P i -> P (IS i)) -> forall i, P i := by
  tr_by nat_rect2

  -- let propParam00 : Param00 Prop Prop := propParam.forget
  -- let propParam10 : Param10 Prop Prop := propParam.forget
  -- let propParam2a0 : Param2a0 Prop Prop := propParam.forget

  have RN : Param2a3.{0} I Nat := by sorry
  have RN0 : tr.R I0 0 := by sorry
  have RNS {m n} : tr.R m n → tr.R (IS m) (Nat.succ n) := by sorry

  let pAux1 : Param02a (Nat → Prop) (I → Prop) := by
    tr_advance

  tr_intro P P' PR
  dsimp

  unfold inferInstance at PR

  tr_split
  case p1 =>
    show Param01 (P 0) (P' I0)
    tr_advance
    -- tr_advance
    tr_advance
    tr_advance
    -- try tr_split_application' [(allowHead:= false)]
    -- sorry
    -- tr_split_application
    -- (case' p2 => intro _ _ _; rotate_left 1)
    -- case aR =>
    --   tr_whnf
    --   sorry

    -- case aR => sorry
    -- intro _ _ _


    -- tr_advance
    -- tr_advance


    -- refine (Trale.instantiatePropR_bi ?_).forget
    -- tr_step_rel
    assumption

  tr_split
  case p1 =>
    tr_advance
    tr_advance

    case p1 =>
      show Param01 (P' _) (P _)

      tr_advance
      -- tr_step_rel
      tr_advance

    -- refine (Trale.instantiatePropR_bi ?_).forget
    tr_advance
    tr_advance
    tr_advance

    tr_advance
    -- tr_step_rel
    tr_advance

  tr_intro n n' nR

  tr_advance
  -- tr_step_rel
  tr_advance
