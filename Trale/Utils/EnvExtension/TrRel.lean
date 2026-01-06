import Batteries
import Batteries.Tactic.Trans
import Batteries.Lean.NameMapAttribute
import Aesop
import Qq
namespace Trale.Utils

open Lean Meta Elab Command Std Qq Trale.Utils Term

abbrev TrRelKey := DiscrTree.Key
structure TrRelEntry where
  keys     : Array TrRelKey
  val      : Expr
  globalName? : Option Name := none
  deriving Inhabited, Repr

instance : BEq TrRelEntry where
  beq e1 e2 := e1.val == e2.val

abbrev TrRelTree := DiscrTree TrRelEntry

structure TrRels where
  tree : TrRelTree := DiscrTree.empty
  deriving Inhabited

def addTrRelEntry (d : TrRels) (entry : TrRelEntry) : TrRels :=
  { d with tree := d.tree.insertCore entry.keys entry }

initialize trRelsExtension : PersistentEnvExtension TrRelEntry TrRelEntry TrRels ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun entries => do
      let mut state : TrRels := {}
      for arr in entries do
        for entry in arr do
          state := addTrRelEntry state entry
      pure state
    addEntryFn := addTrRelEntry
    exportEntriesFn := fun s =>
      s.tree.fold (init := #[]) fun acc _ e => acc.push e
    asyncMode := .sync
  }

private def mkTrRelsKey (e : Expr) : MetaM (Array TrRelKey) := do
  let type ← inferType e
  withNewMCtxDepth do
    let (_, _, type) ← forallMetaTelescopeReducing type
    DiscrTree.mkPath type

def addTrRel (src : Name) : MetaM Unit := do
  let val ← mkConstWithLevelParams src
  let keys ← mkTrRelsKey val
  modifyEnv fun env => trRelsExtension.addEntry env { keys, val, globalName? := some src }

end Trale.Utils
