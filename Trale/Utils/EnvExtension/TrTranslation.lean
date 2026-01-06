import Batteries.Lean.NameMapAttribute
import Qq

import Trale.Core.Param
import Trale.Utils.ExpressionHelpers

namespace Trale.Utils
open Lean Meta Elab Command Std Qq Trale.Utils Term

abbrev TranslationKey := DiscrTree.Key

structure TranslationEntry where
  keys        : Array TranslationKey
  fromType    : Expr
  toType      : Expr
  rel         : Option Expr
  priority    : Nat
  globalName? : Option Name := none
  deriving Inhabited, Repr

instance : BEq TranslationEntry where
  beq e₁ e₂ := e₁.fromType == e₂.fromType

instance : ToFormat TranslationEntry where
  format e := match e.globalName? with
    | some n => format n
    | _      => "<local>"

abbrev TrTranslationTree := DiscrTree TranslationEntry

structure TrTranslations where
  discrTree     : TrTranslationTree := DiscrTree.empty
  instanceNames : PHashMap Name TranslationEntry := {}
  deriving Inhabited

def addTranslationEntry (d : TrTranslations) (e : TranslationEntry) : TrTranslations :=
  match e.globalName? with
  | some n => { d with discrTree := d.discrTree.insertCore e.keys e, instanceNames := d.instanceNames.insert n e }
  | none   => { d with discrTree := d.discrTree.insertCore e.keys e }


-- initialize trTranslationExtension : SimpleScopedEnvExtension TranslationEntry TrTranslations ←
--   registerSimpleScopedEnvExtension {
--     initial  := {}
--     addEntry := addTranslationEntry
--     exportEntry? := fun level e =>
--       guard (level == .private || e.globalName?.any (!isPrivateName ·)) *> e
--   }
initialize trTranslationExtension : PersistentEnvExtension TranslationEntry TranslationEntry TrTranslations ←
  registerPersistentEnvExtension {
    mkInitial  := pure {}
    addImportedFn := fun entries => do
      let mut state : TrTranslations := {}
      for arr in entries do
        for entry in arr do
          state := addTranslationEntry state entry
      pure state
    addEntryFn := addTranslationEntry
    exportEntriesFn := fun s =>
      s.discrTree.fold (init := #[]) fun acc _ e =>
        if e.globalName?.any (!isPrivateName ·) then acc.push e else acc
    -- We can set the asyncMode to sync, and then remove the asyncMode annotation in
    -- addTrTranslation. Then, the registrations will remain persistent, but
    -- probably at some performance cost.
    -- asyncMode := .sync
  }


private def mkTrTranslationKey (e : Expr) : MetaM (Array TranslationKey) := do
  withNewMCtxDepth do
    let (_, _, type) ← forallMetaTelescopeReducing e
    DiscrTree.mkPath type

def addTrTranslation (fromExpr toExpr : Expr) (rel : Option Expr) (src : Option Name := none) : MetaM Unit := do
  let keys ← mkTrTranslationKey fromExpr
  let entry : TranslationEntry :=
    { keys, fromType := fromExpr, toType := toExpr,
      rel := rel,
      priority := 100, globalName? := src }
  -- trTranslationExtension.add (kind := .local) entry
  modifyEnv fun env => trTranslationExtension.addEntry (asyncMode := .local) env entry
