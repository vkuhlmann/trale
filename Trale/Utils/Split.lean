import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Lean.Elab

import Trale.Core.Param
import Trale.Theories.Forall
import Trale.Theories.Arrow
import Trale.Theories.Option
import Trale.Theories.Sigma
import Trale.Theories.Exists
import Trale.Utils.ParamFromFunction
import Qq open Qq Lean Meta Elab Tactic

macro "tr_by" a:term:10 : tactic => `(tactic|
  apply fun x => Param.right x $a
)

macro "tr_from_map" : tactic => `(tactic|
  refine (Param_from_map ?_).forget
)

macro "tr_ident" : tactic => `(tactic|
  (refine (Param44_ident'' ?_).forget; try first |dsimp |decide)
)

macro "tr_split_forall" : tactic => `(tactic|
  first
  | apply Param_forall.Map0_forall; rotate_left 1
  | apply Param_forall.Map1_forall; rotate_left 1
  | apply Param_forall.Map2a_forall; rotate_left 1
  | apply Param_forall.Map2b_forall; rotate_left 1
  | apply Param_forall.Map3_forall; rotate_left 1
  | apply Param_forall.Map4_forall; rotate_left 1
  )

macro "tr_split_arrow" : tactic => `(tactic|
  first
  | apply Param_arrow.Map0_arrow
  | apply Param_arrow.Map1_arrow
  | apply Param_arrow.Map2a_arrow
  | apply Param_arrow.Map2b_arrow
  | apply Param_arrow.Map3_arrow
  | apply Param_arrow.Map4_arrow
  )

macro "tr_split_exists" : tactic => `(tactic|
  first
  | apply Param_exists.Map1_exists; rotate_left 1
  )

macro "tr_split'" : tactic => `(tactic|
  first
  | tr_split_arrow
  | tr_split_forall
  | tr_split_exists
  | fail "tr_split: no matching tactic found"
)

macro "tr_split" : tactic => `(tactic|
  (tr_split' <;> try infer_instance)
)


-- Some code based on syntax + definition of Lean 'intro' tactic

syntax (name := tr_intro_syntax_not_working) "tr_intro_not_working" notFollowedBy("|") (ppSpace colGt term:max)* : tactic

@[builtin_tactic tr_intro_syntax_not_working] def evalTrIntro : Lean.Elab.Tactic.Tactic := fun stx : Syntax => do
  evalTactic (← `(tactic| tr_split))
  let stx := match stx with
    | .node a `tr_intro b => .node a ``Lean.Parser.Tactic.intro b
    | _ => stx

  evalIntro stx

syntax (name := tr_intro_syntax) "tr_intro" notFollowedBy("|") (ppSpace colGt term:max)* : tactic


-- elab "tr_intro" notFollowedBy("|") (ppSpace colGt term:max)* : tactic =>
elab_rules : tactic
  -- | `(tactic| tr_intro) notFollowedBy("|") (ppSpace colGt term:max)* : tactic =>
  | `(tactic| tr_intro)                     =>  do
        evalTactic (← `(tactic| tr_split; (case' p2 => intro)))

  | `(tactic| tr_intro $h:ident)            => do
        evalTactic (← `(tactic| tr_split; (case' p2 => intro $h:ident)))

  | `(tactic| tr_intro $h:term $hs:term*)   =>  do
        evalTactic (← `(tactic| tr_split; (case' p2 => intro $h:term $hs:term*)))

  -- evalTactic (← `(tactic| intro $h:term; intro $hs:term*))

  -- `(tr_split)
  -- | `(tactic| intro $h:ident)          => introStep h h.getId
  -- | `(tactic| intro _%$tk)             => introStep tk `_
  -- /- Type ascription -/
  -- | `(tactic| intro ($h:ident : $type:term)) => introStep h h.getId type
  -- /- We use `@h` at the match-discriminant to disable the implicit lambda feature -/
  -- | `(tactic| intro $pat:term)         => evalTactic (← `(tactic| intro h; match @h with | $pat:term => ?_; try clear h))
  -- | `(tactic| intro $h:term $hs:term*) => evalTactic (← `(tactic| intro $h:term; intro $hs:term*))




#eval show MetaM Unit from do
  let stx : Syntax ← `(tactic| intro)

  IO.println s!"Value: {repr stx}"


  -- let stx := match stx with
  --   | .node a `tr_intro b => .node a ``Lean.Parser.Tactic.intro b
  --   | _ => stx

  -- evalIntro stx

  -- match stx with
  -- | `(tactic| intro)                   => introStep none `_
  -- | `(tactic| intro $h:ident)          => introStep h h.getId
  -- | `(tactic| intro _%$tk)             => introStep tk `_
  -- /- Type ascription -/
  -- | `(tactic| intro ($h:ident : $type:term)) => introStep h h.getId type
  -- /- We use `@h` at the match-discriminant to disable the implicit lambda feature -/
  -- | `(tactic| intro $pat:term)         => evalTactic (← `(tactic| intro h; match @h with | $pat:term => ?_; try clear h))
  -- | `(tactic| intro $h:term $hs:term*) => evalTactic (← `(tactic| intro $h:term; intro $hs:term*))
  -- | _ => throwUnsupportedSyntax


macro "tr_flip" : tactic => `(tactic|
  apply Param.flip
  )

macro "tr_sorry" a:term:10 : tactic => `(tactic|
  (show Param.{0} _ _ _ _; sorry)
  )
