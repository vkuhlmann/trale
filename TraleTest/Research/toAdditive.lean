import Lean
import Mathlib
import Mathlib.Tactic.ToAdditive.Frontend

namespace TraleTest.Research.Attr.Eqns
-- BEGIN Source: Mathlib
def transpose {m n} (A : m → n → ℕ) : n → m → ℕ
  | i, j => A j i

theorem transpose_apply {m n} (A : m → n → ℕ) (i j) :
    transpose A i j = A j i := rfl

attribute [eqns transpose_apply] transpose

theorem transpose_const {m n} (c : ℕ) :
    transpose (fun (i : m) (j : n) => c) = fun j i => c := by
  funext i j -- the rw below does not work without this line
  rw [transpose]
-- END Source
end TraleTest.Research.Attr.Eqns

-- /-- Maps multiplicative names to their additive counterparts. -/

open Lean Meta Elab Command Std in
initialize tr_test1 : Lean.NameMapExtension Name ← Lean.registerNameMapExtension _


#check Lean.registerSimplePersistentEnvExtension

@[aesop safe apply, simp]
def sometest : Nat = Nat := sorry


@[seval]
def sometest2 : Nat = Nat := sorry


@[to_additive]
def mytest_mul : Nat := sorry

@[to_additive]
theorem mul_commTest' {α} [CommSemigroup α] (x y : α) : x * y = y * x := mul_comm x y

#check add_commTest'

#check mytest_add
