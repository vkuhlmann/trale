import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Theories.Forall
import Trale.Theories.Arrow
import Trale.Theories.Option
import Trale.Theories.Sigma
import Trale.Theories.Exists
import Qq open Qq Lean

macro "tr_by" a:term:10 : tactic => `(tactic|
  apply fun x => Param.right x $a
)

macro "tr_split_forall" : tactic => `(tactic|
  first
  | apply Param_forall.Map1_forall; rotate_left 1
  | apply Param_forall.Map2a_forall; rotate_left 1
  | apply Param_forall.Map2b_forall; rotate_left 1
  | apply Param_forall.Map3_forall; rotate_left 1
  | apply Param_forall.Map4_forall; rotate_left 1
  )

macro "tr_split_arrow" : tactic => `(tactic|
  first
  | apply Param_arrow.Map1_arrow; rotate_left 1
  | apply Param_arrow.Map2a_arrow; rotate_left 1
  | apply Param_arrow.Map2b_arrow; rotate_left 1
  | apply Param_arrow.Map3_arrow; rotate_left 1
  | apply Param_arrow.Map4_arrow; rotate_left 1
  )

macro "tr_split_exists" : tactic => `(tactic|
  first
  | apply Param_exists.Map1_exists; rotate_left 1
  )

macro "tr_split" : tactic => `(tactic|
  first
  | tr_split_arrow
  | tr_split_forall
  | tr_split_exists
  | fail "tr_split: no matching tactic found"
)

macro "tr_flip" : tactic => `(tactic|
  apply Param.flip
  )

macro "tr_sorry" a:term:10 : tactic => `(tactic|
  (show Param.{0} _ _ _ _; sorry)
  )
