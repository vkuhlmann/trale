import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent

instance (priority := low) sortParam.{w} : Param00 (Sort u) (Sort u) := by
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
  : Param40 a b := by

  tr_from_map
  exact r


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
