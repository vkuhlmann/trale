import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Whnf
import Trale.Utils.Basic
import Trale.Utils.AddFlipped
import Qq
import Trale.Theories.Flip

open Qq Lean Trale.Utils

namespace Trale

/-!
# Parametricity for Function Types (Arrow)

This module defines parametric relations for function types `α → β`.
Two functions are related if they map related inputs to related outputs.

## The Arrow Relation

Given relations `R₁ : α → α' → Sort _` and `R₂ : β → β' → Sort _`,
we define when two functions `f : α → β` and `f' : α' → β'` are related:

```
arrowR R₁ R₂ f f' := ∀ a a', R₁ a a' → R₂ (f a) (f' a')
```

This is the standard logical relation for function types.

## Map Instances

We provide Param instances showing how to transfer function types:
- `Map0_arrow`: Just the relation
- `Map1_arrow`: Adds function composition as the map
- `Map2a_arrow`: Proves the map captures the relation
- `Map2b_arrow`: Proves the relation implies equality (with funext)
-/

variable {α : Sort u} {α' : Sort u} {β : Sort v} {β' : Sort v}

/-- The parametricity relation for function types.
    Two functions are related if they map related inputs to related outputs. -/
def arrowR
  (p1 : Param00 α α')
  (p2 : Param00 β β')
  : (α → β) → (α' → β') → Sort _
  := fun f f' =>
    forall a a', p1.R a a' → p2.R (f a) (f' a')

/-- Flipping the arrow relation.
    If f and f' are related in one direction, they're related in the flipped direction.
    This reverses both domain and codomain relations: `R₁ a a'` becomes `R₁ a' a` 
    and `R₂ b b'` becomes `R₂ b' b`. -/
def flipArrowR
  : arrowR p1 p2 f f' → arrowR p1.flip p2.flip f' f
  := fun r a' a aR' => r a a' (flipR aR')

/-- The arrow relation respects flipping as a Param44 equivalence. -/
instance arrowR_rel
  -- The order of α', α, β', β needs to be specified for
  -- tr_add_flipped to produce the correct flipped definition.
  {α' α : Sort u}
  {β' β : Sort v}
  [p1 : Param00 α α']
  [p2 : Param00 β β']
  {f f'}
  : Param44 (arrowR p1.flip p2.flip f' f) (arrowR p1 p2 f f') := by

  tr_from_involution flipArrowR

/-- Base Param instance for function types: just the relation. -/
instance Map0_arrow
  [p1 : Param00 α α']
  [p2 : Param00 β β']
: Param00 (α → β) (α' → β') := by
  tr_constructor
  exact arrowR p1 p2


/-- Function map via composition.
    Maps `f : α → β` to `p2.right ∘ f ∘ p1.left : α' → β'`.
    Requires contravariant structure on α (to go from α' to α)
    and covariant structure on β (to go from β to β'). -/
@[tr_add_flipped Trale.arrowR_rel]
instance Map1_arrow
  [p1 : Param01 α α']
  [p2 : Param10 β β']
: Param10 (α → β) (α' → β') := by
  tr_extend Map0_arrow (p1 := p1) (p2 := p2)

  exact fun f => p2.right ∘ f ∘ p1.left


/-- The function map captures the arrow relation (Map2a).
    If `map f = f'`, then f and f' are related by arrowR. -/
@[tr_add_flipped Trale.arrowR_rel]
instance Map2a_arrow
  [p1 : Param02b α α']
  [p2 : Param2a0 β β']
: Param2a0 (α → β) (α' → β') := by
  -- We cannot use instance inference, because the types (α, α', ..) are
  -- metavariables at this point.
  tr_extend Map1_arrow (p1 := p1) (p2 := p2)

  intro f f' mapF -- f maps to f'
  intro x x' xR -- x and x' are related
  -- Goal: p2.R (f x) (f x')
  apply p2.right_implies_R
  subst mapF -- substitute f' away

  congr -- find the parts in the equality that still need to match up

  -- Goal: x = p1.left x'
  exact (p1.R_implies_left x x' xR).symm


-- (* (02a, 2b0) + funext -> 2b0 *)
/-- The arrow relation implies equality via the map (Map2b).
    If f and f' are related by arrowR, then `map f = f'` (using funext).
    This requires function extensionality. -/
@[tr_add_flipped Trale.arrowR_rel]
instance Map2b_arrow
  [p1 : Param02a α α']
  [p2 : Param2b0 β β']
  : Param2b0 (α → β) (α' → β') := by

  tr_extend Map1_arrow (p1 := p1) (p2 := p2)

  intro f f'
  intro relH
  apply funext
  intro a'

  apply p2.R_implies_right
  apply relH
  apply p1.left_implies_R
  simp


-- (* (03, 30) + funext -> 30 *)
@[tr_add_flipped Trale.arrowR_rel]
instance Map3_arrow
  [p1 : Param03 α α']
  [p2 : Param30 β β']
  : Param30 (α → β) (α' → β') := by
  tr_extend_multiple [
    Map2a_arrow (p1 := p1) (p2 := p2),
    Map2b_arrow (p1 := p1) (p2 := p2)
  ]


-- (* (04(????), 40) + funext -> 40 *)
@[tr_add_flipped Trale.arrowR_rel]
instance Map4_arrow
  [p1 : Param03 α α']
  [p2 : Param40 β β']
  : Param40 (α → β) (α' → β') := by
  tr_extend Map3_arrow (p1 := p1) (p2 := p2)
  intros; funext _ _ _; apply p2.R_implies_rightK


  /- Alternatively:

  ```lean
  have _ : Param30 β β' := p2
  tr_extend (inferInstance : Param30 (α -> β) (α' -> β'))
  ```

  But this gives problems because the inferInstance is not properly unfolded.
  -/

  -- case R_implies_rightK =>
  -- intro f f' fR
  -- funext a a' aR
  -- -- simp
  -- -- FIXME: Want to do this, but getting type mismatch:
  -- -- show p1.right_implies_R _ _ (p1.R_implies_right _ _ _) = fR a a' aR
  -- apply p2.R_implies_rightK
