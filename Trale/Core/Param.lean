import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Map

import Qq open Qq Lean

section Params
universe w u v

variable (α: Sort u) (β : Sort v)

class Param (α : Sort u) (β : Sort v)
    (mapCov : MapType)
    (mapContra : MapType)
  : Sort ((max u v w) + 1) where

  R : α → β -> Sort w
  covariant : mapCov.interp R
  contravariant : mapContra.interp (flipRel R)



#check Param.R

-- ## Param abbreviations
--
-- We're enumerating all the abbreviations manually.
--
-- It's not the most pure and
-- sophisticated way, but it gets the job done, and performing all the necessary
-- metaprogramming to automatically enumerate the cases would likely be more
-- lines of code, and confuse code editor tools like IntelliSense.
--
-- I looked into this in the past, and the cleanest entrance for an api was private,
-- meaning that for including it in a public library, I would need to replicate its
-- many private dependencies.

abbrev Param00  :=  Param.{w} α β .Map0 .Map0
abbrev Param01  :=  Param.{w} α β .Map0 .Map1
abbrev Param02a :=  Param.{w} α β .Map0 .Map2a
abbrev Param02b :=  Param.{w} α β .Map0 .Map2b
abbrev Param03  :=  Param.{w} α β .Map0 .Map3
abbrev Param04  :=  Param.{w} α β .Map0 .Map4

abbrev Param10  :=  Param.{w} α β .Map1 .Map0
abbrev Param11  :=  Param.{w} α β .Map1 .Map1
abbrev Param12a :=  Param.{w} α β .Map1 .Map2a
abbrev Param12b :=  Param.{w} α β .Map1 .Map2b
abbrev Param13  :=  Param.{w} α β .Map1 .Map3
abbrev Param14  :=  Param.{w} α β .Map1 .Map4

abbrev Param2a0 :=  Param.{w} α β .Map2a .Map0
abbrev Param2a1 :=  Param.{w} α β .Map2a .Map1
abbrev Param2a2a := Param.{w} α β .Map2a .Map2a
abbrev Param2a2b := Param.{w} α β .Map2a .Map2b
abbrev Param2a3 :=  Param.{w} α β .Map2a .Map3
abbrev Param2a4 :=  Param.{w} α β .Map2a .Map4

abbrev Param2b0 :=  Param.{w} α β .Map2b .Map0
abbrev Param2b1 :=  Param.{w} α β .Map2b .Map1
abbrev Param2b2a := Param.{w} α β .Map2b .Map2a
abbrev Param2b2b := Param.{w} α β .Map2b .Map2b
abbrev Param2b3 :=  Param.{w} α β .Map2b .Map3
abbrev Param2b4 :=  Param.{w} α β .Map2b .Map4

abbrev Param30  :=  Param.{w} α β .Map3 .Map0
abbrev Param31  :=  Param.{w} α β .Map3 .Map1
abbrev Param32a :=  Param.{w} α β .Map3 .Map2a
abbrev Param32b :=  Param.{w} α β .Map3 .Map2b
abbrev Param33  :=  Param.{w} α β .Map3 .Map3
abbrev Param34  :=  Param.{w} α β .Map3 .Map4

abbrev Param40  :=  Param.{w} α β .Map4 .Map0
abbrev Param41  :=  Param.{w} α β .Map4 .Map1
abbrev Param42a :=  Param.{w} α β .Map4 .Map2a
abbrev Param42b :=  Param.{w} α β .Map4 .Map2b
abbrev Param43  :=  Param.{w} α β .Map4 .Map3
abbrev Param44  :=  Param.{w} α β .Map4 .Map4


#check (_ : Param11 ?a ?b).covariant

#check (_ : Param11 ?a ?b).R

-- FIXME The last expression has type `MapType.Map1.interp p.R`. Can we apply a simplification automatically
--     such that it becomes `Map1 p.R` instead?
#check
  let p : Param11 ?a ?b := ?p
  p.covariant

end Params

set_option pp.all true in
instance
  CoeParam

  (Rp : Param.{w} α β X Y)
  [CoeTC (X.interp Rp.R) (X'.interp Rp.R)]
  [CoeTC (Y.interp (flipRel Rp.R)) (Y'.interp (flipRel Rp.R))]
  :
  CoeDep
  (Param.{w} α β X Y)
  Rp
  (Param.{w} α β X' Y')
   where
   coe :=
   (@Param.mk α β X' Y' Rp.R Rp.covariant Rp.contravariant : Param.{w} α β X' Y')

-- instance
--   CoeParam2

--   (Rp : Param.{w} α β X Y)
--   [CoeTC (X.interp Rp.R) (X'.interp Rp.R)]
--   [CoeTC (Y.interp (flipRel Rp.R)) (Y'.interp (flipRel Rp.R))]
--   :
--   CoeDep
--   (Param.{w} α β X Y)
--   Rp
--   (Param.{w} α β X' Y')
--    where
--    coe :=
--    (@Param.mk α β X' Y' Rp.R Rp.covariant Rp.contravariant : Param.{w} α β X' Y')




namespace Param

@[simp]
def forget'
  (Rp : Param.{w} α β X Y)
  [Coe (X.interp Rp.R) (X'.interp Rp.R)]
  [Coe (Y.interp (flipRel Rp.R)) (Y'.interp (flipRel Rp.R))]
: Param.{w} α β X' Y'
 := (CoeParam Rp).coe

theorem map0bottom {X : MapType} : MapType.Map0 ≤ X := by
  cases X <;> decide

theorem map4top {X : MapType} : X ≤ MapType.Map4 := by
  cases X <;> decide

@[simp]
def forget
  {X Y X' Y': MapType}

  (h1 : X' ≤ X := by first|decide |assumption |exact Param.map0bottom)
  (h2 : Y' ≤ Y := by first|decide |assumption |exact Param.map0bottom)
  (Rp : Param.{w} α β X Y)
  :
  (Param.{w} α β X' Y')
  := by

    constructor
    case R => exact Rp.R
    case covariant => exact coeMap Rp.covariant h1
    case contravariant => exact coeMap Rp.contravariant h2

@[simp]
abbrev flip (p : Param α β m1 m2) : Param β α m2 m1 :=
  { R := flipRel p.R, covariant := p.contravariant, contravariant := p.covariant }

/-!Test

With the original implementation of `Param.right_implies_R`, we need the
`forget` in
```
#check fun {α β} (p1 : Param2a3 α β) => (p1.forget.right_implies_R
        : ∀ a b, (p1.right a) = b → p1.R a b)
```

This is because `right_implies_R` was based on coercion:
```
abbrev Param.right_implies_R (p : Param2a0 α β)
  : (a : α) → (b : β) → p.right a = b → p.R a b := p.covariant.map_in_R
```

The issue is that we can't tell coercion to infer the implicit arguments α and
β from the coercion. Here is a minimal example of this issue:

```
---- Part 1: This works ----

axiom Foo1 : Type
axiom Bar1 : Type

def func1
  (p: Bar1) : Nat := 0

instance : Coe Foo1 Bar1 where
  coe p := sorry

axiom val1 : Foo1

#check func1 val1
-- Works


---- Part 2: This fails ----

axiom Foo2 : Type -> Type
axiom Bar2 : Type -> Type

def func2
  (p: Bar2 α) : Nat := 0

instance : Coe (Foo2 α) (Bar2 α) where
  coe p := sorry

axiom val2 : Foo2 Nat

#check func2 val2
-- Fails:
-- Application type mismatch: In the application
--   func2 val2
-- the argument
--   val2
-- has type
--   Foo2 Nat : Type
-- but is expected to have type
--   Bar2 ?m.361 : Type

#check @func2 Nat val2
-- Works
```

A solution would be to use
```
abbrev R_implies_right (p : Param α β m1 m2)
  (h1 : m1 ≥ .Map2b := by ...)
  : forall (a : α) (b : β), p.R a b → p.right a = b := by
    tr_cases_maptype m1 eliminate h1
    all_goals exact (p.forget (h1 := h1)).covariant.R_in_map
```
where `h1` is an autoParam.

Indeed then the following check works:
```
#check fun {α β} (p1 : Param2a3 α β) => p1.right_implies_R
```

In this case, we let Lean infer an ingredient for the coercion, and then
do the coercion ourselves, ultimately bypassing the limitation. We used
autoParams to infer this ingredient, being a condition of the MapType, that it
is high enough that the corresponding Param can be coerced to the Param we
actually need.


## Issue 1
There is one issue however with this use of autoParams.
Consider this:
```
abbrev right_implies_R
  (p : Param α β m1 m2)
  (h1 : m1 ≥ .Map2a := by ...)
  : ∀ a b, p.right a = b → p.R a b
```

Now this application does not work:
```
#check fun {α β} (p : Param2a0 α β) (a : α) =>
  p.right_implies_R a
-- Fails:
-- Application type mismatch: In the application
--   right_implies_R p a
-- the argument
--   a
-- has type
--   α : Sort ?u.61866
-- but is expected to have type
--   autoParam (MapType.Map0 ≥ MapType.Map2a) _auto✝ : Prop
```

Indeed, because the autoParam is a mandatory argument, it expects to get it
instead. We can't really move the autoParam
to the end of the parameter list, because `p.right` in the type definition
already depends on `h1`. What is even worse, is that we can't pass a placeholder
`_` to encourage autoParam to use its default value. We would need to pass a
value manually, or repeat the default value explicitly.

The best workaround is to use type ascription to force the autoparam from
being filled in, after which we can continue applying our arguments:
```
#check fun {α β} (p : Param2a0 α β) (a : α) =>
  (p.right_implies_R : ∀ _ _, _ → _) a
```


## Issue 2

We are now relying on autoParam inferring proofs to conditions like
`m1 ≥ .Map2a`, where the right-hand side can be any MapType. If the user uses
concrete MapTypes, i.e. they are a fixed known value, the `decide` tactic can
infer the proof.

But now in the definition of `right_implies_R`, we also need to use `right`.
We get a proof `m1 ≥ .Map2a`, but for `right` we need `m1 ≥ .Map1`. This is of
course easily addressed by a transitivity theorem:
```
theorem mapTypeTrans' {a b c : MapType} (h1 : a ≥ b) (h2 : b ≥ c) : a ≥ c
```
For us this means `(m1 ≥ .Map2a) → (.Map2a ≥ .Map1) → (m1 ≥ .Map1)`.

With this, we can make our autoParam be defined as
```
(h1 : m1 ≥ .Map1 := by first|decide |exact mapTypeTrans' (by assumption) (by decide))
```

While this works mostly, it is still quite limited. For one, if the user doesn't
provide a concrete MapType, they need to do cases on the MapType, to get
concrete MapTypes. Only then can you invoke these methods.

Secondly, in some scenarios, the `by assumption` may get tricked into using the
wrong assumption:
```
-- This works
example (h: a ≥ .Map2a) : (a ≥ .Map1) := by
  refine mapTypeTrans' (by assumption) (by decide)

-- This fails
-- example (h: a ≥ .Map2a) (h2 : a ≥ .Map0) : (a ≥ .Map1) := by
--   refine mapTypeTrans' (by assumption) (by decide)
```

Indeed, when an assumption is matched, but the subsequent `by decide` fails,
Lean doesn't backtrack to try a different matching assumption. This probably
can be solved by defining a tactic which does a more sophisticated search
through assumptions. Unfortunately, a neat implementation turned out to be
nontrivial, and it is currently not done. When it becomes blocking for
something, I can return to it.

This would be such a tactic:
```
-- So we want a tactic that can solve such cases
-- example (h: a ≥ .Map2a) (h2 : a ≥ .Map0) : (a ≥ .Map1) := by
--   decide_maptype_using_assump
```

Ideally, we would `omega` to help us, like it does for Nat:
```
-- It would be nice if somehow we can equip omega to handle such transitivity
-- for MapType as well.
example (h: a ≥ 4) (g : b ≥ a) : (b ≥ 4) := by
  omega
```
Despite efforts, I wasn't able to figure out if `omega` can help us with our
custom MapType.

-/

-- Code based on
-- https://github.com/leanprover-community/lean4-metaprogramming-book/blob/master/lean/main/09_tactics.lean
elab "decide_maptype_using_assump" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let lctx ← Lean.MonadLCtx.getLCtx


    for ldecl in lctx.decls do
      if ldecl.isNone then
        continue
      let ldecl := ldecl.get!

      let declType : Q(Type) := ldecl.type
      let declExpr : Q($declType) := ldecl.toExpr
      let declType ← Lean.Meta.inferType declExpr

      -- if (← Lean.Meta.isExprDefEq declType goalType) then
      --   Lean.Elab.Tactic.closeMainGoal `decide_maptype_using_assump declExpr
      --   return

      IO.println s!"Doing hypothesis of type {declType}"

      let fvarId := ldecl.fvarId
      let name := ldecl.userName

      -- let attempt := (Elab.Tactic.evalTactic (← `(tactic| try (let h : $declType := $declExpr; refine mapTypeTrans' (by assumption) (by decide)))))
      -- let attempt := (Elab.Tactic.evalTactic (← `(tactic| try refine mapTypeTrans' `(term|$declExpr) (by decide))))
      -- let attempt := (Elab.Tactic.evalTactic (← `(tactic| try refine mapTypeTrans' `(term|$fvarId) (by decide))))
      -- let success <- Elab.Tactic.tryTactic attempt

      -- if success && (←goal.isAssigned) then
      --   return

      -- try
      --   Elab.Tactic.evalTactic (← `(tactic| refine mapTypeTrans' (by assumption.) (by decide)))
      --   return
      -- catch _ =>
      --   continue


    -- let option_matching_expr ← lctx.findDeclM? fun ldecl: Lean.LocalDecl => do
    --   let declExpr := ldecl.toExpr
    --   let declType ← Lean.Meta.inferType declExpr

    --   if (← Lean.Meta.isExprDefEq declType goalType) then
    --     return some declExpr

    --   Elab.Tactic.evalTactic (← `(tactic| refine mapTypeTrans' (by assumption) (by decide)))

    --   -- Elab.Tactic.evalTactic
    --   -- mapTypeTrans'


    --   return none
    -- dbg_trace f!"matching_expr: {option_matching_expr}"
    -- match option_matching_expr with
    --   | some e => Lean.Elab.Tactic.closeMainGoal `custom_assump_2 e
    --   | none =>
    --     Lean.Meta.throwTacticEx `custom_assump_2 goal
    --       (m!"unable to find matching hypothesis of type ({goalType})")

    Lean.Meta.throwTacticEx `decide_maptype_using_assump goal
          (m!"unable to solve goal ({goalType})")


-- It would be nice if somehow we can equip omega to handle such transitivity
-- for MapType as well.
example (h: a ≥ 4) (g : b ≥ a) : (b ≥ 4) := by
  omega

variable {a : MapType}


-- This works
example (h: a ≥ .Map2a) : (a ≥ .Map1) := by
  refine mapTypeTrans' (by assumption) (by decide)

-- This fails
-- example (h: a ≥ .Map2a) (h2 : a ≥ .Map0) : (a ≥ .Map1) := by
--   refine mapTypeTrans' (by assumption) (by decide)

-- So we want a tactic that can solve such cases
-- example (h: a ≥ .Map2a) (h2 : a ≥ .Map0) : (a ≥ .Map1) := by
--   decide_maptype_using_assump


example (h: a ≥ .Map2a) : (a ≥ .Map1) := by
  refine mapTypeTrans' h ?_
  decide


-- Idea: Can we have a tactic which takes a parametric tactic as argument, then
--       runs this argument for each assumption as its parameter.
elab "for_each_assumption" td:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let subtactic ← Elab.Tactic.elabTermEnsuringType td q(Syntax)

    let lctx ← Lean.MonadLCtx.getLCtx

    for ldecl in lctx.decls do
      if ldecl.isNone then
        continue
      let ldecl := ldecl.get!

      let declExpr := ldecl.toExpr
      let declType := ldecl.type

      -- Elab.Tactic.evalTactic

macro "tr_exfalso_maptype" td:term : tactic => `(tactic|
    (let _tr_exfalso_maptype_h := $td
    ; dsimp [LE.le, instLEMapType, leMapType] at _tr_exfalso_maptype_h
    ; (suffices false = true by (exfalso; simp at this))
    ; exact _tr_exfalso_maptype_h
    )
  )

-- macro "tr_cases_with_maptype" m1:Lean.Parser.Tactic.elimTarget h:term : tactic => `(tactic|
--   (
--     cases $m1
--     -- <;> (all_goals try (tr_exfalso_maptype $h))
--   )
-- )

macro "tr_cases_maptype" m1:Lean.Parser.Tactic.elimTarget " eliminate " h:term:10 : tactic => `(tactic|
    cases $m1
    <;> (all_goals try (tr_exfalso_maptype $h))
)


@[simp]
abbrev right (p : Param α β m1 m2)
  (a : α)
  (h1 : m1 ≥ .Map1 := by first|decide |exact mapTypeTrans' (by assumption) (by decide))
: β :=
  p.forget (h1 := h1).covariant.map a

@[simp]
abbrev left (p : Param01 α β) : β -> α :=
  p.contravariant.map

@[simp]
abbrev right_implies_R (p : Param α β m1 m2)
  (h1 : m1 ≥ .Map2a := by first|decide |exact mapTypeTrans' (by assumption) (by decide))
  : ∀ a b, p.right a = b → p.R a b := by
    tr_cases_maptype m1 eliminate h1
    all_goals exact
      (p.forget (h1 := h1)).covariant.map_in_R

@[simp]
abbrev left_implies_R (p : Param02a α β)
  : forall (a : α) (b : β), p.left b = a -> p.R a b := by
    let h := p.contravariant.map_in_R
    simp
    simp [flipRel] at h
    intros a b h'
    let h2 := h b
    rw [h'] at h2
    apply h2
    trivial

@[simp]
abbrev R_implies_right (p : Param α β m1 m2)
  (h1 : m1 ≥ .Map2b := by first|decide |exact mapTypeTrans' (by assumption) (by decide))
  : forall (a : α) (b : β), p.R a b -> p.right a = b := by
    tr_cases_maptype m1 eliminate h1
    all_goals exact (p.forget (h1 := h1)).covariant.R_in_map

-- Because autoparams are mandatory arguments, they become awkward if we need to
-- pass in further arguments. We can either explicitly give the same value as
-- the autoparam, or we use type annotation to force Lean to fill the autoparam
-- for us.

-- #check forall {α β} (p : Param02b α β) a a' (aR : p.R a a'),
--   p.right_implies_R a a' aR

-- #check fun {α β} (p : Param2a0 α β) (a : α) =>
--   p.right_implies_R a
-- Fails:
-- Application type mismatch: In the application
--   right_implies_R p a
-- the argument
--   a
-- has type
--   α : Sort ?u.61866
-- but is expected to have type
--   autoParam (MapType.Map0 ≥ MapType.Map2a) _auto✝ : Prop

-- #check fun {α β} (p : Param2a0 α β) (a : α) =>
--   (p.right_implies_R : forall _ _, _ → _) a

-- #check fun {α β} (p : Param2a0 α β) (a : α) =>
--   p.right_implies_R (by ...) a

  -- (p.right_implies_R : forall (a : α) (b : β), p.R a b -> p.right a = b) a b h



@[simp]
abbrev R_implies_rightK (p : Param α β m1 m2)
  (h1 : m1 ≥ .Map4 := by decide)
  : forall a a' (aR : p.R a a'),
    -- p.right_implies_R (by exact mapTypeTrans' (by assumption) (by decide)) a a' (p.R_implies_right (by exact mapTypeTrans' (by assumption) (by decide)) a a' aR) = aR
    (p.right_implies_R : (_: _) -> (_: _) -> _ -> _)
      a a'
    ((p.R_implies_right : (_: _) -> (_: _) -> _ -> _) a a' aR) = aR
  := by
    tr_cases_maptype m1 eliminate h1
    all_goals exact
      p.covariant.R_in_mapK

@[simp]
abbrev R_implies_left (p : Param02b α β)
  : forall (a : α) (b : β), p.R a b -> p.left b = a := by
    let h := p.contravariant.R_in_map
    simp
    simp [flipRel] at h
    intros a b h'
    let h2 := h b a
    exact h2 h'

@[simp]
abbrev R_implies_leftK (p : Param04 α β)
  := p.contravariant.R_in_mapK

end Param
