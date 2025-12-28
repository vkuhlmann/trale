import Lean
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

-- https://github.com/leanprover-community/aesop

-- Based on https://github.com/leanprover-community/mathlib4/blob/18a54b03b696bfa1a81859f884c01077592a7775/Mathlib/Tactic/ToAdditive/Frontend.lean
-- by the mathlib4 community.
-- Some code is verbatim, some is modified.

-- Based on ~/.elan/toolchains/leanprover--lean4---v4.23.0-rc2/src/lean/Lean/Meta/Instances.lean
-- by Microsoft Corporation, Leonardo de Moura, and Lean prover community.
-- Some code is verbatim, some is modified.

open Lean Meta Elab Command Std Qq Trale.Utils Term

namespace Trale.Attr

#check PRange


abbrev TranslationKey := DiscrTree.Key

structure TranslationEntry where
  keys        : Array TranslationKey
  val         : Expr
  target      : Expr
  priority    : Nat
  globalName? : Option Name := none
  deriving Inhabited, Repr

instance : BEq TranslationEntry where
  beq e₁ e₂ := e₁.val == e₂.val

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


initialize trTranslationExtension : SimpleScopedEnvExtension TranslationEntry TrTranslations ←
  registerSimpleScopedEnvExtension {
    initial  := {}
    addEntry := addTranslationEntry
    exportEntry? := fun level e =>
      guard (level == .private || e.globalName?.any (!isPrivateName ·)) *> e
  }

private def mkTrTranslationKey (e : Expr) : MetaM (Array TranslationKey) := do
  withNewMCtxDepth do
    let (_, _, type) ← forallMetaTelescopeReducing e
    DiscrTree.mkPath type


elab "#printTraleInstances" : command => do
  let x := instanceExtension
  let state := x.getState (←getEnv)
  let tree := state.discrTree

  let e ← liftCoreM do
    let metaState ← MetaM.run do
      let levelU ← mkFreshLevelMVar
      let levelV ← mkFreshLevelMVar
      let levelW ← mkFreshLevelMVar

      let (args, argsBi, expr) ← forallMetaTelescope q(∀ cov con α β, Param.{levelW, levelU, levelV} cov con α β)

      -- let cov ← mkFreshLevelMVar

      -- let (y, _) ← tree.getMatchLiberal expr--q(Param _ _ _ _)
      let y ← tree.getUnify expr
      IO.println s!"Found {y.size} instances"

      -- let n := min y.size 5
      -- let range := (1...=n)
      -- for i in range do
      let mut i := 0
      while h : i < y.size ∧ i < 35 do
        let result := y[i]
        IO.println s!"Expression {i}: {result.globalName?}"
        -- let z := 4
        -- pure ()
        i := i + 1

    return ()
  return ()

elab "#printTraleImpliedTranslations" : command => do
  let x := instanceExtension
  let state := x.getState (←getEnv)
  let tree := state.discrTree

  let e ← liftCoreM do
    let metaState ← MetaM.run do
      let levelU ← mkFreshLevelMVar
      let levelV ← mkFreshLevelMVar
      let levelW ← mkFreshLevelMVar

      let (args, argsBi, expr) ← forallMetaTelescope q(∀ cov con α β, Param.{levelW, levelU, levelV} cov con α β)

      let y ← tree.getUnify expr
      IO.println s!"Found {y.size} instances"

      let mut i := 0
      while h : i < y.size ∧ i < 35 do
        let result := y[i]
        let name := (result.globalName?.map format).getD "(missing)"
        IO.println s!"Expression {i}: {name}"
        let type ← inferType result.val
        -- IO.println s!"   Type: {type}"
        -- let val := (←Meta.unfoldDefinition? result.val).getD result.val
        let (args2, argsBi2, expr2) ← forallMetaTelescope type
        -- IO.println s!"   Expr2: {expr2}"

        let parts ← getParamParts? expr2

        match parts with
          | .ok parts =>
            let headName := getHeadConst parts.fromType
            if headName.isSome then
              IO.println s!"     {parts.fromType} -> {parts.toType}"
              IO.println s!"     ({parts.conMapType}, {parts.conMapType})"

          | .error err => IO.println s!"Expression {i} (error: {err})"

        i := i + 1

    return ()
  return ()


elab "#tr_add_translations_from_instances" : command => do
  let x := instanceExtension
  let state := x.getState (←getEnv)
  let tree := state.discrTree

  -- let trTree =

  let trExt := trTranslationExtension

  let e ← liftCoreM do
    let metaState ← MetaM.run do
      let levelU ← mkFreshLevelMVar
      let levelV ← mkFreshLevelMVar
      let levelW ← mkFreshLevelMVar

      let (args, argsBi, expr) ← forallMetaTelescope q(∀ cov con α β, Param.{levelW, levelU, levelV} cov con α β)

      let y ← tree.getUnify expr
      IO.println s!"Found {y.size} instances"

      let mut i := 0
      while h : i < y.size ∧ i < 35 do
        let result := y[i]
        let name := (result.globalName?.map format).getD "(missing)"
        IO.println s!"Expression {i}: {name}"
        let type ← inferType result.val
        -- IO.println s!"   Type: {type}"
        -- let val := (←Meta.unfoldDefinition? result.val).getD result.val
        let (args2, argsBi2, expr2) ← forallMetaTelescope type
        -- IO.println s!"   Expr2: {expr2}"

        let parts ← getParamParts? expr2

        match parts with
          | .ok parts =>
            let headName := getHeadConst parts.fromType
            if headName.isSome then
              IO.println s!"     {parts.fromType} -> {parts.toType}"
              IO.println s!"     ({parts.conMapType}, {parts.conMapType})"

              let keys ← mkTrTranslationKey parts.fromType
              let val := parts.fromType

              trExt.add { keys,
                          val,
                          target := parts.toType,
                          priority := 100 }

          | .error err => IO.println s!"Expression {i} (error: {err})"

        i := i + 1

    return ()

  let translations := trTranslationExtension.getState (←getEnv)
  let treeSize := translations.discrTree.size
  IO.println s!"Translations is ({treeSize}): "
  let vals := translations.discrTree.elements.map (fun x => (format x.val).pretty)
  -- let valsString := vals.toList.foldl (· ++ ·) ""
  IO.println s!"  : {vals}"

  return ()

partial def TrTranslateRecursive (transl : TrTranslations) (e : Expr) : MetaM Expr :=
  visit e

  where visit (e : Expr) := do
    let entries ← transl.discrTree.getMatch e

    trace[debug] s!"Got {entries.size} results for {e} of type ({←inferType e})"
    if h : entries.size > 0 then
      return entries[0].target

    match e with
    | .forallE n bt body bi =>
        -- pure <| e.updateForallE! (←visit bt) (←visit body)
        let bt ← visit bt

        let arg ← mkFreshExprMVar (.some bt) (userName := n)
        let body := body.instantiateRev #[arg]
        let body ← visit body

        mkForallFVars #[arg] body (binderInfoForMVars := bi)

        -- let (args, argsBi, body') ← forallMetaTelescope body
        -- let body'' ←
        --   (args.zip argsBi).foldrM
        --     (fun (arg, bi) body =>
        --       mkForallFVars #[arg] body
        --       (binderInfoForMVars := bi)
        --     )
        --     (←visit body')

        -- pure <| body''
        -- pure <| .forallE n bt body bi
        -- pure <| e'

    | .lam n d b bi =>
        -- pure <| .lam n (←visit d) (←visit b) bi
        let d ← visit d
        let (args, argsBi, body) ← lambdaMetaTelescope b
        let e' ←
          (args.zip argsBi).foldrM
            (fun (arg, bi) body =>
              mkLambdaFVars #[arg] body
              (binderInfoForMVars := bi)
            )
            (←visit body)

        pure <| e'

    | .mdata data b =>
        pure <| .mdata data (←visit b)

    | .letE n t v b nondep =>
        pure <| .letE n (←visit t) (←visit v) (←visit b) nondep

    | .app f a =>
        pure <| .app (←visit f) (←visit a)

    | .proj n idx b =>
        pure <| .proj n idx (←visit b)

    | _ =>
      pure e




elab "#tr_translate" a:term : command => do
  let x ← liftTermElabM <| elabTerm a .none

  let state := trTranslationExtension.getState (←getEnv)

  let (result, metaState) ← liftCoreM <| MetaM.run do
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
elab "trale" : tactic => do
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

#check Array
#printTraleInstances

-- #tr_add_translations_from_instances

declare_aesop_rule_sets [trale]

#check PersistentEnvExtension
#check SimpleScopedEnvExtension

-- open Lean Meta Elab Command Std in
initialize tr_test1 : NameMapExtension Name ← Lean.registerNameMapExtension _


#check Lean.registerSimplePersistentEnvExtension

syntax attrTraleRest := ppSpace (str)?
  -- toAdditiveNameHint (ppSpace toAdditiveOption)* (ppSpace ident)? (ppSpace (str <|> docComment))?
syntax (name := attr_trale) "trale" "?"? : attr

-- @[inherit_doc to_additive]
-- macro "to_additive?" rest:toAdditiveRest : attr => `(attr| to_additive ? $rest)


abbrev TraleTheoremKey := DiscrTree.Key

structure TraleTheorem where
  proof       : Expr
  deriving Inhabited

-- inductive TraleEntry where
--   | thm      : TraleTheorem → TraleEntry

-- abbrev TraleTheoremTree := DiscrTree TraleTheorem

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


-- #check tr_test1.getEntries

/-- `Config` is the type of the arguments that can be provided to `to_additive`. -/
structure Config : Type where
  /-- View the trace of the to_additive procedure.
  Equivalent to `set_option trace.to_additive true`. -/
  trace : Bool := false
  /-- The name of the target (the additive declaration). -/
  tgt : Name := Name.anonymous
  /-- An optional doc string. -/
  doc : Option String := none
  /-- If `allowAutoName` is `false` (default) then
  `@[to_additive]` will check whether the given name can be auto-generated. -/
  allowAutoName : Bool := false
  /-- The arguments that should be reordered by `to_additive`, using cycle notation. -/
  reorder : List (List Nat) := []
  /-- The argument used to determine whether this constant should be translated. -/
  relevantArg? : Option Nat := none
  /-- The attributes which we want to give to both the multiplicative and additive versions.
  For `simps` this will also add generated lemmas to the translation dictionary. -/
  attrs : Array Syntax := #[]
  /-- A list of type variables that should not be translated by `to_additive`. -/
  dontTranslate : List Ident := []
  /-- The `Syntax` element corresponding to the original multiplicative declaration
  (or the `to_additive` attribute if it is added later),
  which we need for adding definition ranges. -/
  ref : Syntax
  /-- An optional flag stating that the additive declaration already exists.
  If this flag is wrong about whether the additive declaration exists, `to_additive` will
  raise a linter error.
  Note: the linter will never raise an error for inductive types and structures. -/
  existing : Bool := false
  /-- An optional flag stating that the target of the translation is the target itself.
  This can be used to reorder arguments, such as in
  `attribute [to_dual self (reorder := 3 4)] LE.le`.
  It can also be used to give a hint to `additiveTest`, such as in
  `attribute [to_additive self] Unit`.
  If `self := true`, we should also have `existing := true`. -/
  self : Bool := false
  deriving Repr



-- builtin_initialize simpExtension : SimpExtension ← registerSimpAttr `simp "simplification theorem"

open Tactic.TryThis in
-- open private addSuggestionCore in addSuggestion in
/-- Elaboration of the configuration options for `to_additive`. -/
def elabAttrTrale : Syntax → CoreM Config
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
      -- tgt := match tgt with | some tgt => tgt.getId | none => Name.anonymous
      -- doc
      allowAutoName := false
      -- attrs, reorder, relevantArg?, dontTranslate, existing, self
      -- ref := (tgt.map (·.raw)).getD tk }
      ref := tk
    }
  | _ => throwUnsupportedSyntax


--/-- `addToAdditiveAttr src cfg` adds a `@[to_additive]` attribute to `src` with configuration `cfg`.
--See the attribute implementation for more details.
--It returns an array with names of additive declarations (usually 1, but more if there are nested
--`to_additive` calls. -/
partial def addToAdditiveAttr (src : Name) (cfg : Config) (kind := AttributeKind.global) :
    AttrM Unit := do
  if (kind != AttributeKind.global) then
    throwError "`trale` can only be used as a global attribute"
  IO.println s!"trale running on {src}"

  let trExt := trTranslationExtension

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
      --fun src stx kind ↦ do
      -- return
    fun src stx kind ↦ do _ ← addToAdditiveAttr src (← elabAttrTrale stx) kind
    -- we (presumably) need to run after compilation to properly add the `simp` attribute
    -- applicationTime := .afterCompilation
  }
end Trale.Attr
