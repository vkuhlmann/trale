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
import Trale.Utils.Application
import Qq open Qq Lean Meta Elab Tactic

open Trale.Utils

macro "tr_by" a:term:10 : tactic => `(tactic|
  apply fun x => Param.right' x $a
)

macro "tr_from_map" ppSpace colGt a:term:10 : tactic => `(tactic|
  first
  | refine (paramFromMap $a).forget
  | apply Trale.Utils.paramFromInjection $a
  | apply Trale.Utils.paramFromSurjection $a
  | refine (paramFromMap $a).forget.flip
  | apply (Trale.Utils.paramFromInjection $a).flip
  | apply (Trale.Utils.paramFromSurjection $a).flip
  | fail "No suitable constructing function found"
)


macro "tr_from_map" : tactic => `(tactic|
  tr_from_map ?_
  -- first
  -- | refine (Param_from_map ?_).forget
  -- | apply Trale.Utils.createInjection
)

macro "tr_ident" : tactic => `(tactic|
  (refine (Param44_ident'' ?_).forget; try first |dsimp |decide)
)

macro "tr_subst" ppSpace colGt a:ident a':ident aR:term:10 : tactic => `(tactic|
  (
    have aF := tr.R_implies_map $a $a' $aR;
    simp at aF;
    subst aF
  )
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

/-
There are three special things happening in the following code:

1. The combination of `focus`+`case'` is used to fix the order of goals.

2. We set explicit arguments (`(p1 := ..) `) because they are typeclass
   arguments, but may not be obtained through other steps, rather than
   typeclass synthesis.

3. We use the construction `apply (fun ... => ...)` instead of `refine`, because
   the latter will result in goal tags which are not prefix with the current
   goal tag. This will mess with our ability to use `case'`; normally, when
   using `case' p2`, this will match tags ending on `p2`, e.g. `p1.p1.p2`.
   However, if there is a goal whose full tag is `p2`, then it will be targeted,
   even when outside the focus scope.

   Without a focus, this would cause wrong ordering of goals, within a focus,
   this will cause an error of the goal not being found.

-/
macro "tr_split_arrow" : tactic => `(tactic|
  focus
  ((first
  | apply (fun p1 p2 => Param_arrow.Map0_arrow (p1 := p1) (p2 := p2))
  | apply (fun p1 p2 => Param_arrow.Map1_arrow (p1 := p1) (p2 := p2))
  | apply (fun p1 p2 => Param_arrow.Map2a_arrow (p1 := p1) (p2 := p2))
  | apply (fun p1 p2 => Param_arrow.Map2b_arrow (p1 := p1) (p2 := p2))
  | apply (fun p1 p2 => Param_arrow.Map3_arrow (p1 := p1) (p2 := p2))
  | apply (fun p1 p2 => Param_arrow.Map4_arrow (p1 := p1) (p2 := p2))
  ); case' p1 => skip -- Fix goal ordering
  )
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


macro "tr_step" ppSpace colGt a:ident a':ident aR:ident : tactic => `(
    tactic| (
      first
      | infer_instance
      | (tr_intro $a $a' $aR)
      | (tr_split_application $a $a' $aR)
      | decide

    )
  )



-- elab "tr_intro" notFollowedBy("|") (ppSpace colGt term:max)* : tactic =>
elab_rules : tactic
  -- | `(tactic| tr_intro) notFollowedBy("|") (ppSpace colGt term:max)* : tactic =>
  | `(tactic| tr_intro)                     =>  do
        evalTactic (← `(tactic| tr_split <;> try (case' p2 => intro)))

  | `(tactic| tr_intro $h:ident)            => do
        evalTactic (← `(tactic| tr_split <;> try (case' p2 => intro $h:ident)))

  | `(tactic| tr_intro $h:term $hs:term*)   =>  do
        evalTactic (← `(tactic| tr_split <;> try (case' p2 => intro $h:term $hs:term*)))

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

macro "tr_sorry" a:term:10 : tactic => `(tactic|
  (show Param.{0} _ _ _ _; sorry)
  )
