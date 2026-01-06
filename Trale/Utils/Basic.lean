import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Lean.Elab

import Trale.Core.Param
import Trale.Utils.ParamFromFunction
import Qq
import Aesop

open Qq Lean Meta Elab Tactic Trale Trale.Utils

macro "tr_by" a:term:10 : tactic => `(tactic|
  apply fun x => Param.right' x $a
)

macro "tr_from_map" ppSpace colGt a:term:10 : tactic => `(tactic|
  first
  | refine (Trale.Utils.paramFromMap $a).forget
  | apply Trale.Utils.paramFromInjection $a
  | apply Trale.Utils.paramFromSurjection $a
  | refine (Trale.Utils.paramFromMap $a).forget.flip
  | apply (Trale.Utils.paramFromInjection $a).flip
  | apply (Trale.Utils.paramFromSurjection $a).flip
  | fail "No suitable constructing function found"
)

macro "tr_from_involution" ppSpace colGt a:term:10 : tactic => `(tactic|
    (first
     | (apply Trale.Utils.paramFromInvolution;
        apply $a;
        apply $a; done)
      | (apply Trale.Utils.paramFromInvolution;
         case flipR => exact $a
         case flipR' => exact $a
         case _ => intro _; rfl
         case _ => intro _; rfl
        )
    )
  )

macro "tr_from_equivalence" ppSpace colGt to_from:term:10 "," ppSpace colGt from_to:term:10 : tactic => `(tactic|
  exact Trale.Utils.paramFromEquiv $to_from $from_to
)

#check paramFromMap
#check Trale.Utils.paramFromInjection
#check Trale.Utils.paramFromSurjection


macro "tr_from_map" : tactic => `(tactic|
  tr_from_map ?_
  -- first
  -- | refine (Param_from_map ?_).forget
  -- | apply Trale.Utils.createInjection
)

macro "tr_ident" : tactic => `(tactic|
  (refine (Param44_ident'' ?_).forget (h1 := map4top) (h2 := map4top); try first |dsimp |decide)
)

macro "tr_subst" ppSpace colGt a:ident a':ident aR:term:10 : tactic => `(tactic|
  (
    have aF := tr.R_implies_map $a $a' $aR;
    simp at aF;
    subst aF
  )
)

macro "tr_sorry" a:term:10 : tactic => `(tactic|
  (show Param.{0} _ _ _ _; sorry)
  )

macro "tr_solve" : tactic => `(tactic|
     aesop (rule_sets := [trale])
  )

macro "tr_exact" a:term:10 : tactic => `(tactic|
     (
      tr_by $a
      change Param.{0} _ _ _ _
      tr_solve
     )
  )
