import Lean
import TraleTest.Research.env_test_extension

/-!
# Minimal test for environment modification in tactics

This file tests whether `modifyEnv` changes are visible immediately
after calling `getEnv` in various monad contexts.
-/

open Lean Meta Elab Tactic

-- Helper to add a value to the extension
def addToTestExtension (n : Nat) : CoreM Unit :=
  modifyEnv fun env => testExtension.addEntry env n

-- Test 1: Direct modifyEnv + getEnv in MetaM
def testMetaM : MetaM Nat := do
  let before := testExtension.getState (←getEnv)
  IO.println s!"Before: counter = {before.counter}"

  modifyEnv fun env => testExtension.addEntry env 1

  let after := testExtension.getState (←getEnv)
  IO.println s!"After: counter = {after.counter}"


  modifyEnv fun env => testExtension.addEntry env 1

  let after := testExtension.getState (←getEnv)
  IO.println s!"After: counter = {after.counter}"

  return after.counter

#eval discard <| MetaM.run testMetaM
-- Expected: Before: 0, After: 1

-- Test 2: MetaM inside TacticM with liftMetaTactic
elab "test_tactic_1" : tactic => do
  liftMetaTactic fun g => do
    let before := testExtension.getState (←getEnv)
    IO.println s!"[tactic1] Before: counter = {before.counter}"

    modifyEnv fun env => testExtension.addEntry env 10

    let after := testExtension.getState (←getEnv)
    IO.println s!"[tactic1] After in MetaM: counter = {after.counter}"

    return [g]

  -- Check if change persists in TacticM
  let afterTactic := testExtension.getState (←getEnv)
  IO.println s!"[tactic1] After in TacticM: counter = {afterTactic.counter}"

example : True := by
  test_tactic_1
  trivial

-- Test 3: Using liftMetaMAtMain and setEnv
elab "test_tactic_2" : tactic => do
  let (result, newEnv) ← liftMetaMAtMain fun _ => do
    let before := testExtension.getState (←getEnv)
    IO.println s!"[tactic2] Before: counter = {before.counter}"

    modifyEnv fun env => testExtension.addEntry env 100

    let after := testExtension.getState (←getEnv)
    IO.println s!"[tactic2] After in MetaM: counter = {after.counter}"

    return (after.counter, ←getEnv)

  setEnv newEnv

  -- Check if change persists after setEnv
  let afterSetEnv := testExtension.getState (←getEnv)
  IO.println s!"[tactic2] After setEnv in TacticM: counter = {afterSetEnv.counter}"

example : True := by
  test_tactic_2
  trivial

-- Test 4: Simple CoreM context
def testCoreM : CoreM Nat := do
  let before := testExtension.getState (←getEnv)
  IO.println s!"[CoreM] Before: counter = {before.counter}"

  modifyEnv fun env => testExtension.addEntry env 1000

  let after := testExtension.getState (←getEnv)
  IO.println s!"[CoreM] After: counter = {after.counter}"

  return after.counter

#eval testCoreM

-- Test 5: Check persistence across multiple calls
elab "test_tactic_3" : tactic => do
  let check := fun msg => do
    let state := testExtension.getState (←getEnv)
    IO.println s!"[tactic3] {msg}: counter = {state.counter}"

  check "Start"

  let (_, env1) ← liftMetaMAtMain fun _ => do
    modifyEnv fun env => testExtension.addEntry env 1
    return ((), ←getEnv)
  setEnv env1

  check "After first modification"

  let (_, env2) ← liftMetaMAtMain fun _ => do
    modifyEnv fun env => testExtension.addEntry env 1
    return ((), ←getEnv)
  setEnv env2

  check "After second modification"

example : True := by
  test_tactic_3
  trivial

-- Test 6: SimpleScopedEnvExtension (like trTranslationExtension)

elab "test_scoped_1" : tactic => do
  liftMetaTactic fun g => do
    let before := scopedTestExtension.getState (←getEnv)
    IO.println s!"[scoped1] Before: {before.entries.size} entries"

    -- Directly add an entry to scopedTestExtension (for comparison with addTrTranslation's behavior)
    scopedTestExtension.add { value := 42 }

    let after := scopedTestExtension.getState (←getEnv)
    IO.println s!"[scoped1] After in MetaM: {after.entries.size} entries"

    return [g]

  let afterTactic := scopedTestExtension.getState (←getEnv)
  IO.println s!"[scoped1] After in TacticM: {afterTactic.entries.size} entries"

example : True := by
  test_scoped_1
  trivial

elab "test_scoped_2" : tactic => do
  let (count, newEnv) ← liftMetaMAtMain fun _ => do
    let before := scopedTestExtension.getState (←getEnv)
    IO.println s!"[scoped2] Before: {before.entries.size} entries"

    scopedTestExtension.add { value := 99 }

    let after := scopedTestExtension.getState (←getEnv)
    IO.println s!"[scoped2] After in MetaM: {after.entries.size} entries"

    return (after.entries.size, ←getEnv)

  setEnv newEnv

  let afterSetEnv := scopedTestExtension.getState (←getEnv)
  IO.println s!"[scoped2] After setEnv in TacticM: {afterSetEnv.entries.size} entries"

example : True := by
  test_scoped_2
  trivial
