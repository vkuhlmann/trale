import Batteries
import Batteries.Tactic.Trans
import Batteries.Lean.NameMapAttribute
import Lean.Elab.Tactic.Ext
import Lean.Meta.Tactic.Rfl
import Lean.Meta.Tactic.Symm
import Lean.Meta.Tactic.TryThis
import Aesop
import Qq
import Lean.PrettyPrinter

import Trale.Core.Param
import Trale.Utils.AddFlipped
import Trale.Utils.ExpressionHelpers
import Trale.Utils.EnvExtension.TrRel
import Trale.Utils.EnvExtension.TrTranslation
import Trale.Utils.Basic

-- https://github.com/leanprover-community/aesop

/-!
# The `trale` Tactic and Attribute

This module implements the main `trale` tactic for proof transfer, along with
the `@[trale]` attribute for registering transport theorems.

## Overview

The `trale` tactic:
1. Analyzes the goal to understand its type structure
2. Finds appropriate `Param` instances connecting the types
3. Recursively translates the goal to a simpler type
4. Uses Aesop with registered `@[trale]` lemmas to solve parametricity obligations

The `@[trale]` attribute marks transport lemmas for automatic use by the tactic.

## Commands

- `#tr_add_translations_from_instances`: Scans for Param instances and registers them
- `#tr_translate term`: Shows how a term would be translated

## Attribution

Based on:
- Mathlib4's `to_additive` tactic by the mathlib4 community
- Lean 4's instance system by Microsoft Corporation, Leonardo de Moura, and community
-/

-- Based on https://github.com/leanprover-community/mathlib4/blob/18a54b03b696bfa1a81859f884c01077592a7775/Mathlib/Tactic/ToAdditive/Frontend.lean
-- by the mathlib4 community.
-- Some code is verbatim, some is modified.

-- Based on ~/.elan/toolchains/leanprover--lean4---v4.23.0-rc2/src/lean/Lean/Meta/Instances.lean
-- by Microsoft Corporation, Leonardo de Moura, and Lean prover community.
-- Some code is verbatim, some is modified.

open Lean Meta Elab Command Std Qq Trale.Utils Term Trale.Utils

namespace Trale.Attr

/-- Command to scan all Param instances and register them as translations.
    This populates the translation table used by the trale tactic. -/
elab "#tr_add_translations_from_instances" : command => do
  let x := instanceExtension
  let state := x.getState (←getEnv)
  let tree := state.discrTree

  discard <| liftCoreM <| MetaM.run do

  let levelU ← mkFreshLevelMVar
  let levelV ← mkFreshLevelMVar
  let levelW ← mkFreshLevelMVar

  let (args, argsBi, expr) ← forallMetaTelescope q(∀ cov con α β, Param.{levelW, levelU, levelV} cov con α β)

  let y ← tree.getUnify expr
  IO.println s!"Found {y.size} instances"

  for h : i in 0...y.size do
    let result := y[i]
    let name := (result.globalName?.map format).getD "(missing)"
    -- IO.println s!"Expression {i}: {name}"
    let type ← inferType result.val
    -- let val := (←Meta.unfoldDefinition? result.val).getD result.val
    let (args2, argsBi2, expr2) ← forallMetaTelescope type

    let parts ← getParamParts? expr2

    match parts with
      | .ok parts =>
        let headName := getHeadConst parts.fromType
        if headName.isSome then
          -- IO.println s!"     {parts.fromType} -> {parts.toType}"
          -- IO.println s!"     ({parts.conMapType}, {parts.conMapType})"

          addTrTranslation parts.fromType parts.toType result.val result.globalName?

      | .error err =>
        IO.println s!"Expression {i}: {name}"
        IO.println s!"Expression {i} (error: {err})"


/-- Translate a term to its target type using registered translations.
    Returns `some e'` if a translation is found, `none` otherwise. -/
def translateTerm (transl : TrTranslations) (e : Expr) : MetaM (Option Expr) := do
  let eType ← inferType e
  if !eType.isSort then
    let entries ← transl.discrTree.getMatch eType

    trace[debug] s!"Got {entries.size} results for type of {e} ({eType})"
    if h : entries.size > 0 then
      let entry := entries[0]

      match entry.rel with
      | .none => return .none
      | .some rel =>

      let relType ← inferType rel

      trace[debug] s!"[TrTranslateRecursive] relType: {relType}"

      let parts ← getParamParts? relType
      match parts with
        | .ok parts =>
          let levelW := parts.levelW
          let p ←
            mkFreshExprMVarQ
              q(Param.{levelW} $parts.covMapType $parts.conMapType
                $parts.fromType $parts.toType)

          p.mvarId!.assignIfDefEq rel

          let e' ← mkFreshExprMVarQ q($parts.fromType)
          e'.mvarId!.assignIfDefEq e

          let h ← mkFreshExprMVarQ q(MapType.Map1 ≤ $parts.covMapType)
          synthesizeDecidable! h
          return .some q(Param.right $p (h := $h) $e')

          -- let relFromHead := result.rel
          -- let relToHead :=
          --   match parts.conMapType with
          --   | some conMapType =>
          --     let conMapTypeApp := conMapType.mkApp e
          --     trace[debug] s!"Applying contravariant map: {conMapTypeApp}"
          --     conMapTypeApp
          --   | none =>
          --     trace[debug] s!"No contravariant map"
          --     e

          -- trace[debug] s!"relFromHead: {relFromHead}"
          -- trace[debug] s!"relToHead: {relToHead}"

          -- return .some relToHead

        | .error err =>
          trace[debug] s!"Error getting param parts: {err}"
          throwError err
  return .none


def TrTranslateRecursive (transl : TrTranslations) (e : Expr) : MetaM Expr :=
  replaceExprM f e

  where f e := do
    let entries ← transl.discrTree.getMatch e

    trace[debug] s!"Got {entries.size} results for {e} of type ({←inferType e})"
    if h : entries.size > 0 then
      return .some entries[0].toType

    -- Handle literals in the expression
    -- return (←translateTerm transl e)
    return .none



elab "#tr_translate" a:term : command => do
  let x ← liftTermElabM <| elabTerm a .none

  let state := trTranslationExtension.getState (←getEnv)

  let (result, _) ← liftCoreM <| MetaM.run do
    let x ← instantiateMVars x

    -- let entries ← state.discrTree.getUnify x

    -- match h : entries.size with
    -- | 0 => pure Option.none
    -- | n+1 =>
    --   let entry := entries[0]
    --   pure <| .some entry.target

    let result ← TrTranslateRecursive state x

    if (←isDefEq x result) then
      pure Option.none
    else
      pure <| .some result

    -- return Option.some result

    -- return entry.

  IO.println s!"Term: {x}"
  IO.println s!"Translated: {result}"
  IO.println s!""
  match result with
  | .some result =>
      let (prettyPrinted, _) ← liftCoreM <| MetaM.run (Lean.PrettyPrinter.delab result)
      let formatted ← ppTerm {env := ← getEnv} <| prettyPrinted
      IO.println s!"Translated: {formatted}"
  | _ => pure ()

  return ()

open Tactic in
elab "trale'" : tactic => do
  liftMetaTactic fun g => do
    let orig ← g.getType'

    let state := trTranslationExtension.getState (←getEnv)
    let dest ← TrTranslateRecursive state orig

    let levelU ← mkFreshLevelMVar
    let levelW ← mkFreshLevelMVar

    let origQ ← mkFreshExprMVarQ q(Sort $levelU)
    let destQ ← mkFreshExprMVarQ q(Sort $levelU)

    if !(←isDefEq origQ orig) then
      throwTacticEx `trale g
        "Wrong orig type"

    if !(←isDefEq destQ dest) then
      throwTacticEx `trale g
        "Wrong dest type"

    let paramGoal ← mkFreshExprMVarQ q(Param10.{levelW} $destQ $origQ) (userName := `p)
    let goalDest ← mkFreshExprMVarQ q($destQ) (userName := `translatedGoal)

    g.assignIfDefEq q((Param.right' $paramGoal $goalDest) : $origQ)

    return [paramGoal.mvarId!, goalDest.mvarId!]

macro "trale" : tactic => `(tactic|
  focus
    trale'
    change Param.{0} _ _ _ _
    tr_solve
  )

declare_aesop_rule_sets [trale]

-- open Lean Meta Elab Command Std in
initialize tr_test1 : NameMapExtension Name ← Lean.registerNameMapExtension _



syntax attrTraleRest := ppSpace (str)?
  -- toAdditiveNameHint (ppSpace toAdditiveOption)* (ppSpace ident)? (ppSpace (str <|> docComment))?
syntax (name := attr_trale) "trale" "?"? : attr

-- @[inherit_doc to_additive]
-- macro "to_additive?" rest:toAdditiveRest : attr => `(attr| to_additive ? $rest)


abbrev TraleTheoremKey := DiscrTree.Key

structure TraleTheorem where
  proof       : Expr
  deriving Inhabited

structure TraleTheorems where
  -- thms : TraleTheoremTree
  thms : Array TraleTheorem
  deriving Inhabited

def TraleTheorems.addThm (a : TraleTheorems) (b : TraleTheorem) : TraleTheorems :=
  {
    a with
    thms := a.thms.push b
  }


abbrev TraleExtension := SimpleScopedEnvExtension TraleTheorem TraleTheorems


builtin_initialize tr_test2 : TraleExtension ← do
  let ext ← registerSimpleScopedEnvExtension {
        name     := `tr_test2
        initial  := {
          thms := #[]
        }
        addEntry := fun d e => d.addThm e
    }
  -- mkSimpAttr attrName attrDescr ext ref -- Remark: it will fail if it is not performed during initialization
  -- registerBuiltinAttribute {
  --   ref   := ref
  --   name  := attrName
  --   descr := attrDescr
  -- }
  -- simpExtensionMapRef.modify fun map => map.insert attrName ext
  return ext


/-- `Config` is the type of the arguments that can be provided to `to_additive`. -/
structure AttrTraleConfig : Type where
  trace : Bool := false
  ref : Syntax
  deriving Repr



-- builtin_initialize simpExtension : SimpExtension ← registerSimpAttr `simp "simplification theorem"

open Tactic.TryThis in
-- open private addSuggestionCore in addSuggestion in
/-- Elaboration of the configuration options for `to_additive`. -/
def elabAttrTrale : Syntax → CoreM AttrTraleConfig
  | `(attr| trale%$tk $[?%$trace]?)
  -- | `(attr| trale%$tk $[?%$trace]? $existing?)
      -- $[$opts:toAdditiveOption]* $[$tgt]? $[$doc]?)
      => do
    -- let mut attrs := #[]
    -- let mut reorder := []
    -- let mut relevantArg? := none
    -- let mut dontTranslate := []
    -- for stx in opts do
    --   match stx with
    --   | `(toAdditiveOption| (attr := $[$stxs],*)) =>
    --     attrs := attrs ++ stxs
    --   | `(toAdditiveOption| (reorder := $[$[$reorders:num]*],*)) =>
    --     for cycle in reorders do
    --       if h : cycle.size = 1 then
    --         throwErrorAt cycle[0] "\
    --           invalid cycle `{cycle[0]}`, a cycle must have at least 2 elements.\n\
    --           `(reorder := ...)` uses cycle notation to specify a permutation.\n\
    --           For example `(reorder := 1 2, 5 6)` swaps the first two arguments with each other \
    --           and the fifth and the sixth argument and `(reorder := 3 4 5)` will move \
    --           the fifth argument before the third argument."
    --       let cycle ← cycle.toList.mapM fun n => match n.getNat with
    --         | 0 => throwErrorAt n "invalid position `{n}`, positions are counted starting from 1."
    --         | n+1 => pure n
    --       reorder := cycle :: reorder
    --   | `(toAdditiveOption| (relevant_arg := $n)) =>
    --     if let some arg := relevantArg? then
    --       throwErrorAt stx "cannot specify `relevant_arg` multiple times"
    --     else
    --       relevantArg? := n.getNat.pred
    --   | `(toAdditiveOption| (dont_translate := $[$types:ident]*)) =>
    --     dontTranslate := dontTranslate ++ types.toList
    --   | _ => throwUnsupportedSyntax
    -- let (existing, self) := match existing? with
    --   | `(toAdditiveNameHint| existing) => (true, false)
    --   | `(toAdditiveNameHint| self) => (true, true)
    --   | _ => (false, false)
    -- if self && !attrs.isEmpty then
    --   throwError "invalid `(attr := ...)` after `self`, \
    --     as there is only one declaration for the attributes.\n\
    --     Instead, you can write the attributes in the usual way."
    -- trace[to_additive_detail] "attributes: {attrs}; reorder arguments: {reorder}"
    -- let doc ← doc.mapM fun
    --   | `(str|$doc:str) => open Linter in do
    --     -- Deprecate `str` docstring syntax (since := "2025-08-12")
    --     if getLinterValue linter.deprecated (← getLinterOptions) then
    --       logWarningAt doc <| .tagged ``Linter.deprecatedAttr
    --         m!"String syntax for `to_additive` docstrings is deprecated: Use \
    --           docstring syntax instead (e.g. `@[to_additive /-- example -/]`)"
    --       addSuggestionCore doc
    --         (header := "Update deprecated syntax to:\n")
    --         (codeActionPrefix? := "Update to: ")
    --         (isInline := true)
    --         #[{
    --           suggestion := "/-- " ++ doc.getString.trim ++ " -/"
    --         }]
    --     return doc.getString
    --   | `(docComment|$doc:docComment) => do
    --     -- TODO: rely on `addDocString`s call to `validateDocComment` after removing `str` support
    --     validateDocComment doc
    --     /- Note: the following replicates the behavior of `addDocString`. However, this means that
    --     trailing whitespace might appear in docstrings added via `docComment` syntax when compared
    --     to those added via `str` syntax. See this [Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Why.20do.20docstrings.20include.20trailing.20whitespace.3F/with/533553356). -/
    --     return (← getDocStringText doc).removeLeadingSpaces
    --   | _ => throwUnsupportedSyntax
    return {
      trace := trace.isSome
      ref := tk
    }
  | _ => throwUnsupportedSyntax

private def etaReduceR
  : Expr → Expr → (Expr × Expr)

  | .app f (.mvar _), .app g (.mvar _) => etaReduceR f g
  | e1, e2 => (e1, e2)


def addTrTranslationFromConst (src : Name) : MetaM Unit := do
  let info ← getConstInfo src
  let srcType := info.type

  let (_, _, srcHeadType) ← forallMetaTelescope srcType
  let ⟨srcHeadType, _, _⟩ ← unfold srcHeadType ``tr.R

  let parts ← getParamParts? srcHeadType

  let (fromType, toType) ← match parts with
    | .ok parts =>
      let headName := getHeadConst parts.fromType
      if headName.isSome then
        pure (parts.fromType, parts.toType)
      else
        throwError s!"Cannot get head const of {parts.fromType}"

    | _ =>
      let cov ← mkFreshExprMVarQ q(MapType)
      let con ← mkFreshExprMVarQ q(MapType)
      let levelU ← mkFreshLevelMVar
      let levelV ← mkFreshLevelMVar
      let levelW ← mkFreshLevelMVar

      let fromType ← mkFreshExprMVarQ q(Sort $levelU)
      let toType ← mkFreshExprMVarQ q(Sort $levelV)

      let param ← mkFreshExprMVarQ q(Trale.Param.{levelW} $cov $con $fromType $toType)

      let relFrom ← mkFreshExprMVarQ q($fromType)
      let relTo ← mkFreshExprMVarQ q($toType)
      let capture := q(@Trale.Param.R _ _ _ _ $param $relFrom $relTo)

      if !(← isDefEq capture srcHeadType) then
        IO.println s!"The telescoped type of {src} is not a Param.R or Param"
        return

      let relFrom ← instantiateExprMVars relFrom
      let relTo ← instantiateExprMVars relTo

      let (relFromHead, relToHead) := etaReduceR relFrom relTo
      IO.println s!"relFromHead: {relFromHead}"
      IO.println s!"relToHead: {relToHead}"
      pure (relFromHead, relToHead)

    addTrTranslation fromType toType q($src) src


partial def addTraleAttr (src : Name) (cfg : AttrTraleConfig) (kind := AttributeKind.global) :
    AttrM Unit := do
  if (kind != AttributeKind.global) then
    throwError "`trale` can only be used as a global attribute"

  discard <| MetaM.run <| addTrRel src
  discard <| MetaM.run <| addTrTranslationFromConst src

  liftCommandElabM do
    let srcName : TSyntax `ident := ⟨.ident SourceInfo.none src.toString.toSubstring src []⟩
    elabCommand (←`(command| attribute [aesop 90% apply (rule_sets := [trale])] $srcName))
    elabCommand (←`(command| add_aesop_rules 10% (by apply $srcName) (rule_sets := [trale])))
    elabCommand (←`(command| add_aesop_rules 5% (by
      focus
        apply Param.forget
        case' p =>
          apply $srcName
        case h1 => decide
        case h2 => decide
      ) (rule_sets := [trale])))

  -- withOptions (· |>.updateBool `trace.tr.utils (cfg.trace || ·)) <| do
  --   IO.println s!"Registering {src}"
  --   -- let keys ← mkTrTranslationKey parts.fromType
  --   -- let constantInfo ← getConstInfo src
  --   -- let ((type, value), _) ← MetaM.run do
  --   --   let (args, argsBi, tail) ← forallMetaTelescope constantInfo.type
  --   --   let parts ← getParamParts! tail
  --   -- let val := constantInfo.value!
  --   -- trExt.add { keys,
  --   --       val,
  --   --       target := parts.toType,
  --   --       priority := 100 }
  --   return

initialize registerBuiltinAttribute {
    name := `attr_trale
    descr := "Register a theorem to be used by trale"
    add :=
      fun src stx kind ↦ do _ ← addTraleAttr src (← elabAttrTrale stx) kind
  }
end Trale.Attr
