import Mathlib
import TraleTest.Lemmas.Zmod5 
open TraleTest.Lemmas

/-!
# Test automatic Param instance registration

This file tests that the `trale` tactic automatically registers Param instances
without needing the `#tr_add_translations_from_instances` command.
-/

-- Test theorem using trale without manual registration
-- This should work now that trale automatically registers instances
theorem auto_registration_test : ∀ (a b c : Zmod5),
  (a + b) + c = (c + b) + a := by
  trale
  omega

-- Test with a more complex example
theorem auto_registration_test2 : ∀ (a b c d e : Zmod5),
  a + (b + c * e) * d = d * b + c * d * e + a * 1 := by
  trale
  intro a b c d e
  rw [add_mul, mul_comm b d, mul_assoc c e d,
      mul_assoc c d e, mul_comm e d]
  omega

-- Test that manual registration still works (backward compatibility)
#tr_add_translations_from_instances

theorem manual_registration_test : ∀ (a b : Zmod5),
  a * b = b * a := by
  trale
  intro a b
  omega
