import Mathlib
import Trale.Utils.Constructor
import Trale.Utils.Split

structure Bogus where
  val : Nat
deriving Repr

def BogusParam : Param2a2a Nat Bogus := by
  tr_constructor

  case R =>
    intros
    exact Unit

  case right =>
    intro n
    exact { val := n + 1 }

  case right_implies_R =>
    tauto

  case left =>
    intro n
    exact (n.val + 1)

  case left_implies_R =>
    tauto


def f_nat : Nat -> Nat := id

def f_bogus : Bogus -> Bogus := by
  apply fun x => Param.right.{1,1,_} x f_nat

  /-
  ⊢ Param10 (ℕ → ℕ) (Bogus → Bogus)
  -/

  tr_split

  case p1 =>
    /-
    ⊢ Param01 ℕ Bogus
    -/

    exact BogusParam.forget

  case p2 =>
    /-
    ⊢ Param10 ℕ Bogus
    -/

    exact BogusParam.forget

#eval f_bogus { val := 0 }
#eval f_bogus { val := 1 }
#eval f_bogus { val := 2 }
#eval f_bogus { val := 10 }


theorem id_exists_nat
  : ∃ (f : Nat -> Nat), ∀ (x : Nat), f x = x := by
    exists id
    simp

theorem id_exists_bogus
  : ∃ (f : Bogus -> Bogus), ∀ (x : Bogus), f x = x := by

  tr_by id_exists_nat

  /-
      ⊢ Param10 (∃ f, ∀ (x : ℕ), f x = x) (∃ f, ∀ (x : Bogus), f x = x)
  -/

  tr_split
  case p1 =>
    --   ⊢ Param2a0 (ℕ → ℕ) (Bogus → Bogus)

    tr_split
    case p1 =>
      /-
      ⊢ Param02b ℕ Bogus
      -/

      /-
      type mismatch
        BogusParam
      has type
        Param2a2a ℕ Bogus : Type 2
      but is expected to have type
        Param02b ℕ Bogus : Type (max 1 ?u.2478 2 (?u.2478 + 1))
      -/


      apply BogusParam.forget (h2 := _)

      show MapType.Map2b ≤ MapType.Map2a

      /-
      tactic 'decide' proved that the proposition
        MapType.Map2b ≤ MapType.Map2a
      is false
      -/
      first
      | decide
      | sorry

    tr_sorry sorry

  case p2 =>
    intro f f' fR

    tr_sorry sorry
