import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

import TraleTest.Lemmas.SummableSequence
open TraleTest.Lemmas Trale

-- set_option trace.tr.utils true


-- This fails
-- #check
--   let p : Param11 ?a ?b := ?p
--   p.right

-- But this works
#check
  let p : Param10 ?a ?b := ?p
  p.right'

#check
  let p : Param40 ?a ?b := ?p
  let x : ?a := ?x
  (p.right : ?a → ?b) x


theorem sum_nnR_add : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_by sum_xnnR_add

  -- FIXME: Why can't we use `show` or coercion to upgrade the type for this?
  suffices Param40
    (∀ (f g : seq_xnnR), Σ (f + g) = Σ f + Σ g)
    (∀ (u v : summable), Σ (u + v) = Σ u + Σ v) by
    exact this.forget

  tr_sorry sorry

#check
  let p : Param11 ?a ?b := ?p
  p.forget.right'

/-

The following code gives an error:
``lean4
#check
  let p : Param11 ?a ?b := ?p
  p.right
```

```plaintext
Application type mismatch: In the application
  Param.right p
the argument
  p
has type
  Param11 ?a ?b : Type (max ?u.209 ?u.208 ?u.210)
but is expected to have type
  Param10 ?m.253 ?m.254 : Type (max ?u.217 ?u.216 ?u.215)
```

-/
