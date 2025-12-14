import Trale.Core.Param
import Trale.Utils.Extend
-- import Trale.Utils.Split
import Trale.Utils.Basic
import Trale.Utils.Whnf
import Trale.Utils.ParamIdent
import Trale.Utils.ParamFromFunction
import Trale.Theories.Ident

open Trale.Utils
namespace Trale

instance (priority := low) sortParam''.{w} : Param00 (Sort u) (Sort u) := by
  tr_constructor

  -- R
  · intro x y
    /-
    This should technically be
    ```lean4
    exact show x → y → Sort u from @Param.R x y .Map0 .Map0 inferInstance
    ```
    but the inferInstance doesn't work for arbitrary types.
    -/
    exact x → y → Sort w


/-
Not possible because it relies on univalence:

example : Param44 (Sort u) (Sort u) := by
  tr_constructor

  -- R
  · exact Param44

  -- 4
  · exact id
  · intro _ _; exact Param44_ident''
  · intro a a' aR
    dsimp
    show a = a'
    sorry

  all_goals sorry
-/

#check Fin

def sortParam (cov con : MapType) : Param2a2a (Sort u) (Sort u) := by
  tr_constructor

  -- R
  · exact Param.{0,u,u} cov con

  -- 2a
  · exact id
  · intro a a' aF
    subst aF
    exact Param44_ident.forget (h1 := map4top) (h2 := map4top)

  -- 2a
  · exact id
  · intro a' a aF
    subst aF
    exact Param44_ident.forget (h1 := map4top) (h2 := map4top)


def sortParam'.{w} (cov con : MapType)
: Param11 (Sort u) (Sort u) := by
  tr_constructor
  · exact Param.{w,u,u} cov con
  · exact id
  · exact id




-- prop1 and prop2 are related if prop1 implies prop2.
instance (priority := high) propParam : Param2a2a Prop Prop := by
  tr_constructor

  -- R
  · intro x y
    exact x → y

  -- 2a
  · exact id
  · intro a a' aR
    subst aR
    exact id

  -- 2a
  · exact id
  · intro a a' aR
    subst aR
    exact id

-- FIXME: How to use `tr.R a b`? Currently that would infer the Eq instance instead.
def instantiatePropR
  {a b : Prop}
  (r : propParam.R a b)
  : Param40 a b :=
  by
  tr_from_map r

def instantiatePropR'
  {a b : Prop}
  (r : (sortParam cov con).R a b)
  : Param cov con a b := r

def instantiateSortDuality
  : (sortParam cov con).R a b = Param.{0} cov con a b := by rfl

def prop_equiv_implies_eq
  (α β : Prop)
  : Param11 α β → (α = β) := by
  intro h
  apply propext

  exact ⟨h.right, h.left⟩

def prop_eq_implies_equiv
  (α β : Prop)
  : (α = β) → Param44 α β := by
  intro h
  tr_ident
  exact h

def instantiatePropR_r
  {a b : Prop}
  (r : propParam.R b a)
  : Param04 a b := by
  tr_from_map r

theorem R_eq
  [Param2b0 α α']
  (a : α) (a' : α') (aR : tr.R a a')
  (b : α) (b' : α') (bR : tr.R b b')
  : propParam.R (a = b) (a' = b') := by

  tr_whnf
  show a = b → a' = b'

  tr_subst a a' aR
  tr_subst b b' bR

  exact congrArg _


def R_eq'
  [Param2b0 α α']
  (a : α) (a' : α') (aR : tr.R a a')
  (b : α) (b' : α') (bR : tr.R b b')
  : (sortParam .Map1 .Map0).R (a = b) (a' = b') := by

  tr_from_map

  show a = b → a' = b'

  tr_subst a a' aR
  tr_subst b b' bR

  exact congrArg _

/-
TODO: Make a Prop relation which translates types it comes across. That would
prevent needing to show equivalence of the propositions, where in some cases
only an implication is needed or possible.

```
let eqParam2 : Param10 (xnnR → xnnR → Prop) (nnR → nnR → Prop) := by
  tr_split
  case p1 => infer_instance

  tr_split
  case p1 => infer_instance

  infer_instance
```
-/
