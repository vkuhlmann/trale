import Lean


open Lean Meta Elab Tactic

-- Simple environment extension to track a counter
structure TestState where
  counter : Nat := 0
  deriving Inhabited

def TestState.increment (s : TestState) : TestState :=
  { counter := s.counter + 1 }

initialize testExtension : SimplePersistentEnvExtension Nat TestState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => { counter := s.counter + n }
    addImportedFn := fun es => { counter := es.foldl (init := 0) fun acc arr => acc + arr.foldl (init := 0) (·+·) }
  }



structure ScopedTestEntry where
  value : Nat
  deriving Inhabited, BEq

structure ScopedTestState where
  entries : Array ScopedTestEntry := #[]
  deriving Inhabited

def addScopedEntry (s : ScopedTestState) (e : ScopedTestEntry) : ScopedTestState :=
  { entries := s.entries.push e }

initialize scopedTestExtension : SimpleScopedEnvExtension ScopedTestEntry ScopedTestState ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := addScopedEntry
  }
