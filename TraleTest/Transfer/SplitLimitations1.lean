import Mathlib
import Trale.Utils.Simp
import Trale.Utils.Split
import Trale.Utils.ParamFromFunction

import TraleTest.Lemmas.Zmod5
open TraleTest.Lemmas

/-

In this file, we show a case where can't use `tr_split` to break down the
problem.

The reason is that the existential quantification
```
∃ (f : Zmod5 → Zmod5),  ∀ (x : Zmod5), f x = x
```

then is broken into its quantifier (head) and predicate (body),
```
∃ (f : Zmod5 → Zmod5),                          -- head
                        ∀ (x : Zmod5), f x = x  -- body
```

The split would ask us to provide a transfer function for the head,
i.e. `(Nat → Nat) → (Zmod5 → Zmod5)` satisfying some properties. However, to
provide a sensible transfer function (`Param`) for the head, we need to use the
knowledge of the body. I.e. that our `(f : Nat → Nat)` satisfies
`∀ (x : Nat), f x = x`.

To still use split, we would incorporate this requirement in the relation of the
head part.

which satisfies necessary properties without knowing that



-/

/-
## Goal
We want to get

```
∃ (f : Zmod5 → Zmod5), ∀ (x : Zmod5), f x = x
```

from the below theorem:
-/

theorem id_exists_nat
  : ∃ (f : Nat → Nat), ∀ (x : Nat), f x = x := by
    exists id
    simp


/-

## Without split

-/

def f_nat : Nat → Nat := id

set_option pp.all true in

def f_mod5 : Zmod5 → Zmod5 := by
  tr_by f_nat

  /-
     ⊢ Param10 (ℕ → ℕ) (Zmod5 → Zmod5)
  -/

  tr_split_arrow

  case p1 =>
    --   ⊢ Param01 ℕ Zmod5
    exact ModParam.forget

  case p2 =>
    --   ⊢ Param10 ℕ Zmod5
    exact ModParam.forget

theorem id_exists_mod5_2
  : ∃ (f : Zmod5 → Zmod5), ∀ (x : Zmod5), f x = x := by

  exists f_mod5

/-

## With split

When using split, we can't

-/

theorem id_exists_mod5_1
  : ∃ (f : Zmod5 → Zmod5), ∀ (x : Zmod5), f x = x := by

  tr_by id_exists_nat

  /-
      ⊢ Param10 (∃ f, ∀ (x : ℕ), f x = x) (∃ f, ∀ (x : Zmod5), f x = x)
  -/

  tr_split

  case p1 =>
    /-
         ⊢ Param2a0 (ℕ → ℕ) (Zmod5 → Zmod5)
    -/

    tr_split

    case p1 =>
      /-
          ⊢ Param02b ℕ Zmod5
      -/

      /-
      type mismatch
        ModParam
      has type
        Param42a ℕ Zmod5 : Type 2
      but is expected to have type
        Param02b ℕ Zmod5 : Type (max 1 ?u.4256 2 (?u.4256 + 1))
      -/
      -- exact ModParam

      apply ModParam.forget (h2 := _)
      /-
      tactic 'decide' proved that the proposition
        MapType.Map2b ≤ MapType.Map2a
      is false
      -/
      try decide
      sorry


    case p2 =>
      -- show Param2a0.{_,_,0} ℕ Zmod5

      tr_sorry sorry

  case p2 =>
    intro f f' fR

    -- show Param10.{_,_,0} _ _

    tr_sorry sorry

theorem id_exists_mod5_3
  : ∃ (f : Zmod5 -> Zmod5), ∀ (x : Zmod5), f x = x := by

  tr_by id_exists_nat

  let _ := ModParam

  /-
      ⊢ Param10 (∃ f, ∀ (x : ℕ), f x = x) (∃ f, ∀ (x : Zmod5), f x = x)
  -/

  tr_split

  case p1 =>
    /-
         ⊢ Param2a0 (ℕ → ℕ) (Zmod5 → Zmod5)
    -/

    -- We will fail: we can't make it work for arbitrary functions ℕ → ℕ
    -- We can make a weak Param here, but then we fail in p2.

    tr_constructor

    case R =>
      intro f f'
      exact ∀ (n : Nat) (n' : Zmod5) (nR : tr.R n n'), n < 5 → tr.R (f n) (f' n')

    case right =>
      intro f a'
      exact ModParam.right (f (ModParam.left a'))

    case right_implies_R =>
      intro f f' mapF
      intro n n' nR (h : n < 5)

      rw [← mapF, ← nR]
      congr
      show n = repr5 (mod5 n)
      show n = n % 5

      omega

  case p2 =>
    intro f f' fR
    simp at fR

    tr_split

    case p2 =>
      intro a a' aR
      show Param10 (f a = a) (f' a' = a')

      tr_from_map
      intro P

      tr_simp_R at aR
      simp only at *

      /-
      f : ℕ → ℕ
      f' : Zmod5 → Zmod5
      a : ℕ
      a' : Zmod5
      aR : mod5 a = a'
      P : f a = a
      fR : ∀ n < 5, mod5 (f n) = f' (mod5 n)
      ⊢ f' a' = a'  -/

      rw [← aR, ← fR, P]

      show a < 5

      sorry
      sorry



theorem id_exists_mod5_4
  : ∃ (f : Zmod5 -> Zmod5), ∀ (x : Zmod5), f x = x := by

  tr_by id_exists_nat

  let _ := ModParam

  /-
      ⊢ Param10 (∃ f, ∀ (x : ℕ), f x = x) (∃ f, ∀ (x : Zmod5), f x = x)
  -/

  tr_split

  case p1 =>
    /-
         ⊢ Param2a0 (ℕ → ℕ) (Zmod5 → Zmod5)
    -/

    /-

    We are shifting all the burden to p2...

    We can't do better, because we also insensible functions of ℕ → ℕ need to
    be mapped to something, and that those two have to be related.

    Insensible functions: If we get a function ℕ → ℕ which does this:
    - 2 ↦ 3
    - 7 ↦ 4

    Then for our `Zmod5 → Zmod5` function, we have a conflict:
    - 2 ↦ 3?
    - 2 ↦ 4?

    Note we also can't split, since to avoid such conflicts, `tr_split` requires
    us to proof
    ```
    ⊢ Param02b ℕ Zmod5
    ```
    which we can't.
    -/

    tr_from_map

    intro f
    exact (tr.map <| f <| ModParam.left .)

  case p2 =>
    -- Note we're not splitting the forall!

    intro f f' fR
    simp at fR
    replace fR := congr_fun fR

    tr_from_map
    intro h

    /-

    f : ℕ → ℕ
    f' : Zmod5 → Zmod5
    fR : ∀ (a : Zmod5), mod5 (f (repr5 a)) = f' a
    h : ∀ (x : ℕ), f x = x
    ⊢ ∀ (x : Zmod5), f' x = x

    -/

    intro a'
    rw [← fR]

    -- If we had done the split, we would have `h : f a = a`, but
    -- we need `h : f (repr5 (mod5 a)) = (repr5 (mod5 a))` instead. We do have
    -- it now, since `h` was kept as a forall.
    rw [h]

    show mod5 (repr5 a') = a'
    apply repr5K

    -- intro h

    -- tr_split
    -- case p1 =>
    --   exact ModParam.forget

    -- case p2 =>
    --   intro a a' aR
    --   show Param10 (f a = a) (f' a' = a')

    --   apply (Param_from_map _).forget
    --   intro P

    --   -- tr_simp_R at aR
    --   simp [ModParam] at *
    --   dsimp [Param_from_map] at fR

    --   have fR := congr_fun fR a'
    --   rw [← fR]

    --   show mod5 (f (repr5 a')) = a'
    --   rw [← aR]

    --   congr

    --   /-

    --   P : f a = a
    --   ⊢ f (repr5 (mod5 a)) = a

    --   -/

    --   rw (occs := [2]) [← P]
    --   congr

    --   show repr5 (mod5 (a)) = a

    --   -- We're now stuck, because `repr5 (mod5 a) = a` does not hold for all
    --   -- a : ℕ.

    --   -- This problem was created because our mapping
    --   -- `(ℕ → ℕ) → (Zmod5 → Zmod5)` can't make good sense of function

    --   sorry
