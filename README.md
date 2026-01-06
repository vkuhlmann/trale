# Trale

With Trale we can transport results across types, e.g.
we can show an expression on some custom type Zmod5 by proving it on Nat,
provided we define appropriate transport theorems between Zmod5 and Nat.
Example:

```lean4
import Mathlib
import TraleTest.Lemmas.Zmod5 open TraleTest.Lemmas

theorem sum_eq_reverse_sum_Zmod5 : ∀ (a b c : Zmod5),
  (a + b) + c = (c + b) + a := by
  trale
  omega

example : ∀ (a b c d e : Zmod5),
  a + (b + c * e) * d = d * b + c * d * e + a * 1 := by

  trale
  intro a b c d e
  rw [add_mul, mul_comm b d, mul_assoc c e d,
      mul_assoc c d e, mul_comm e d]
  omega

```

This takes prerequisites (`TraleTest.Lemmas.Zmod5`):
```lean4
import ...

namespace TraleTest.Lemmas
abbrev Zmod5 := Fin 5
instance : Add Zmod5 := ...

lemma repr5K : ∀ (a : Zmod5), mod5 (repr5 a) = a := ...

instance : Param2a4 Zmod5 Nat := by tr_from_map repr5K

@[trale]
def R_add_Zmod5
  (a b : Zmod5) (a' b' : Nat)
  (aR : tr.R a a')
  (bR : tr.R b b')
  : (tr.R (a + b) (a' + b')) := ...

@[trale]
def R_mul_Zmod5
  (a b : Zmod5) (a' b' : Nat)
  (aR : tr.R a a')
  (bR : tr.R b b')
  : (tr.R (a * b) (a' * b'))

instance
  : Param10 (OfNat Zmod5 x) (OfNat Nat x)
  := by tr_from_map (fun _ => ⟨x⟩)

instance zmod5OfNat : OfNat Zmod5 x := Fin.instOfNat

@[trale]
def R_ofNat_Zmod5
  (n : Nat)
  : tr.R (zmod5OfNat (x := n)) (instOfNatNat (n := n)) := by rfl


#tr_add_translations_from_instances

```

Note we need to define a relation on ofNat instances, because of the occurrence
of the literal `1` in the expression.
