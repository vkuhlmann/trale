import Qq
open Qq Lean Elab Command Tactic Term Expr Meta
/-
 This file researches when the 'unquoteExpr' error and similar other errors from
 Qq occur
-/

#eval show MetaM Unit from do
  pure ()

class TrTranslateRight (α : Sort u) (β : outParam (Sort v))

class Foo.{w} (α : Sort u) (β : Sort v) where
  R : α → β -> Sort w

def nnR := Nat

def unquoteDemo (a b : Nat) : a + b = b + a := by
  revert a b
  run_tac
    withMainContext do
      let goalType : Q(Sort) ← getMainTarget

      let equivalentType : Q(Sort) := goalType.replace (match . with
        | .const ``Nat ls => .some <| .const ``nnR ls
        | _ => none
      )

      let newGoal : Q($equivalentType)
        ← mkFreshExprMVar equivalentType

      (← getMainGoal).assign newGoal

      /-
        Error:
        ```plaintext
        unquoteExpr: replaceImpl
        (fun x =>
          match x with
          | const `Nat ls => some (const `nnR ls)
          | x => none)
        goalType : Expr
        ```

        When uncommenting one of the following lines:
      -/
      -- let mytest := q(4)
      -- let mytest : Q(Nat) := q(4 : Nat)

      replaceMainGoal [newGoal.mvarId!]

  exact Nat.add_comm


set_option trace.debug true in
def unquoteDemo2 (α : Type) (β: α → Sort 0) : ∀ a, β a → ∃ c, β c := by
  intro a ba

  run_tac
    -- If we omit the withMainContext, we don't have access to `a` and `ba`
    withMainContext do
      let ctx ← getLCtx
      let fvarUserNames ← ctx.getFVarIds.mapM (·.getUserName)
      trace[debug] s!"fvarUserNames: {fvarUserNames}"

      let αExpr : Q(Type) ← getFVarFromUserName `α
      let βExpr : Q($αExpr → Sort 0) ← getFVarFromUserName `β
      let aExpr : Q($αExpr) ← getFVarFromUserName `a

      let baType : Q(Sort 0) := q($βExpr $aExpr)
      let baExpr : Q($baType) ← getFVarFromUserName `ba

      let mytest := q(4)
      -- This _does_ work

      -- let aExpr : Q($α) := a
      pure

  exact ⟨a, ba⟩


set_option trace.debug true in
def unquoteDemo3_Success1 (a : α) (a' : α') : Sort _ := by
  run_tac
    withMainContext do
    let ctx ← getLCtx
      let uLevel ← mkFreshLevelMVar
      let vLevel ← mkFreshLevelMVar

      let α : Q(Sort uLevel) ← getFVarFromUserName `α
      let α' : Q(Sort vLevel) ← getFVarFromUserName `α'

      let aOld ← getFVarFromUserName `a
      let a' : Q($α') ← getFVarFromUserName `a'

      let a : Q($α) := aOld

      let p1 : Q(Foo.{0} $α $α') ←
        mkFreshExprMVar (.some q((Foo.{0} $α $α'))) (userName := `p1)

      let aRtype := q(($p1).R $a $a')

      let aR
        : Q(($p1).R $a $a')
        ← mkFreshExprMVar (.some q(($p1).R $a $a')) (userName := `aR)

      -- Error:
      -- unquoteExpr: aOld : Expr
      -- let sometest2 := q(4)
  sorry


set_option trace.debug true in
def unquoteDemo3 (a : α) (a' : α') : Sort _ := by
  run_tac
    withMainContext do
    let ctx ← getLCtx
      let uLevel ← mkFreshLevelMVar
      let vLevel ← mkFreshLevelMVar

      let aOld ← getFVarFromUserName `a
      let aOld' ← getFVarFromUserName `a'

      -- let α : Q(Sort $uLevel) ← inferType a
      -- let α' : Q(Sort $vLevel) ← inferType a'
      let α : Q(Sort uLevel) ← getFVarFromUserName `α
      let α' : Q(Sort vLevel) ← getFVarFromUserName `α'

      let a : Q($α) := aOld
      let a' : Q($α') := aOld'

      let p1 : Q(Foo.{0} $α $α') ←
        mkFreshExprMVar (.some q((Foo.{0} $α $α'))) (userName := `p1)

      let aRtype := q(($p1).R $a $a')

      let aR
        : Q(($p1).R $a $a')
        ← mkFreshExprMVar (.some q(($p1).R $a $a')) (userName := `aR)

      -- Error:
      -- unquoteExpr: aOld : Expr
      -- let sometest2 := q(4)

  sorry




set_option trace.debug true in
def unquoteDemo3_2 (a : α) (a' : α') : Sort _ := by
  run_tac
    withMainContext do
    let ctx ← getLCtx
      let uLevel ← mkFreshLevelMVar
      let vLevel ← mkFreshLevelMVar

      let αPlaceholder : Q(Sort $uLevel) ← mkFreshExprMVar q(Sort $uLevel)
      let αPlaceholder'  : Q(Sort $vLevel) ← mkFreshExprMVar q(Sort $vLevel)

      let aOld : Q($αPlaceholder) ← getFVarFromUserName `a
      let aOld' : Q($αPlaceholder') ← getFVarFromUserName `a'

      let α : Q(Sort $uLevel) ← inferType aOld
      let α' : Q(Sort $vLevel) ← inferType aOld'

      let a : Q($α) := aOld
      let a' : Q($α') := aOld'

      let p1 : Q(Foo.{0} $α $α') ←
        mkFreshExprMVar (.some q((Foo.{0} $α $α'))) (userName := `p1)

      let aRtype := q(($p1).R $a $a')

      let aR
        : Q(($p1).R $a $a')
        ← mkFreshExprMVar (.some q(($p1).R $a $a')) (userName := `aR)

      let sometest2 := q(4)

  sorry
