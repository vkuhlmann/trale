import Mathlib
import TraleTest.Lemmas.Zmod5
open TraleTest.Lemmas

/-!
# Test automatic Param instance registration

This file tests that the `trale` tactic automatically registers Param instances
without needing the `#tr_add_translations_from_instances` command.
-/

set_option trace.tr.utils true

-- Test 1: Basic automatic registration
-- This should work now that trale automatically registers instances
theorem auto_registration_test : ∀ (a b c : Zmod5),
  (a + b) + c = (c + b) + a := by
  trale
  omega

-- Test 2: Multiple theorems in sequence
-- Each invocation re-registers instances due to asyncMode := .local
theorem auto_registration_test2 : ∀ (a b c d e : Zmod5),
  a + (b + c * e) * d = d * b + c * d * e + a * 1 := by
  trale
  intro a b c d e
  rw [add_mul, mul_comm b d, mul_assoc c e d,
      mul_assoc c d e, mul_comm e d]
  omega

-- Test 3: Another theorem to verify each trale call works independently
theorem auto_registration_test3 : ∀ (a b : Zmod5),
  a + b = b + a := by
  trale
  omega

-- Test 4: Backward compatibility - manual registration still works
#tr_add_translations_from_instances

theorem manual_registration_test : ∀ (a b : Zmod5),
  a * b = b * a := by
  trale
  intro a b
  rw [mul_comm]

-- Test 5: After manual registration, subsequent theorems also work
theorem post_manual_test : ∀ (x y z : Zmod5),
  (x * y) * z = x * (y * z) := by
  trale
  intro x y z
  rw [mul_assoc]

-- Note: Due to asyncMode := .local in addTrTranslation, each trale
-- invocation re-scans for instances. The manual #tr_add_translations_from_instances
-- command persists across the file, but automatic registrations during
-- tactic execution do not.
