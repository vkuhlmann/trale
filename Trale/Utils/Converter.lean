import Lean
import Lean.Meta
import Lean.Expr
import Trale.Core.Param
-- import Testing1.zmod5
-- import Mathlib.Algebra
import Qq open Qq Lean

namespace Converter

open Lean Meta Elab Tactic Term in
def openFVar (val type : Expr) : TacticM (Expr × Expr) := do
  match val with
    | Expr.fvar n => do
      let decl ← n.getDecl

      let insideType := decl.type
      let insideVal := decl.value?

      -- IO.println s!"[Trale openFVar] opening {n.name} (isSome: {insideVal.isSome})"

      match insideVal with
      | none => return (val, type)
      | some insideVal => return (insideVal, insideType)

    | _ =>
      IO.println s!"[Trale openFVar] Not an fvar: {reprStr val}"
      return (val, type)

open Lean Meta Elab Tactic Term in
def openConstant (val type : Expr) : TacticM (Expr × Expr) := do
  match val with
    | Expr.const n ls => do
      let env ← getEnv
      let decl := env.find? n

      match decl with
      | none => return (val, type)
      | some decl => do
        let insideType := decl.type
        let insideVal := decl.value?

        match insideVal with
        | none => return (val, type)
        | some insideVal =>
            let insideVal := insideVal.instantiateLevelParams decl.levelParams ls
            let insideType := insideType.instantiateLevelParams decl.levelParams ls

            IO.println s!"InsideVal contains levels: {insideVal.hasLevelParam}"
            IO.println s!"InsideType contains levels: {insideType.hasLevelParam}"

            -- IO.println s!"InsideVal: {insideVal}"
            -- IO.println s!"InsideType: {insideType}"
            return (insideVal, insideType)
    -- | Expr.fvar n => do
    --   let decl ← n.getDecl

    --   let insideType := decl.type
    --   let insideVal := decl.value?

    --   match insideVal with
    --   | none => return (val, type)
    --   | some insideVal => return (insideVal, insideType)

    | _ =>
      IO.println s!"[Trale openConstant] Not a constant: {reprStr val}"
      return (val, type)



namespace Conversion

variable {αName βName : Name}

def substType (e : Expr) : Expr :=
  e.replace (match . with
    | Expr.const n ls =>
      if n == αName then
        Expr.const βName ls
      else
        none
    | _ => none
  )


-- open Lean Meta Elab Tactic Term in
-- def substType (e : Expr) : TacticM Expr := do
--   e.replace (match . with
--     | Expr.const n ls =>
--         if n == αName then
--           return some (Expr.const βName ls)
--         else
--           let env <- Expr.getEnv
--           let decl := env.find? n
--           substType e

--           return none
--         -- none
--     | _ => return none
--   )

structure MyTest where
  α : Nat
  β : Nat

#eval q(Nat -> MyTest)


open Lean Meta Elab Tactic Term in
-- def trale (αName : Name) (βName : Name) (e : Expr) : TacticM Expr := do
partial def trale (e : Expr) : TacticM Expr := do
  -- let recurse := trale αName βName

  -- return e.replace (match . with
  --   | Expr.const n ls =>
  --     if n == αName then
  --       none
  --       -- Expr.const βName ls
  --     else
  --       if n == βName then
  --         none
  --       else
  --         none
  --   | _ => none
  -- )

  let _ := αName
  let _ := βName

  match e with
  | .app f a => do
    let f ← trale f
    let a ← trale a
    return Expr.app f a

  | .lam n d b bi => return .lam n (← trale d) (← trale b) bi
  | .forallE n d b bi => return .forallE n (← trale d) (← trale b) bi
  | .letE n t v b nonDep => return .letE n (← trale t) (← trale v) (← trale b) nonDep
  | .mdata d e => return .mdata d (← trale e)
  | .proj n i e => return .proj n i (← trale e)
  | Expr.lit v => do
      -- let v := (← Meta.instantiateMVars v).kind
      let w <- match v with
        | Literal.natVal val =>
           if αName == ``Nat then
             let requiredType : Expr := Lean.Expr.forallE
                Lean.Name.anonymous
                (Lean.Expr.const αName [])
                (Lean.Expr.const βName [])
                (Lean.BinderInfo.default)

              let existingMatch : Option MVarId <- withMainContext do
                let goals ← getGoals
                for goal in goals do
                  let goalType ← goal.getType''
                  if ← Meta.isExprDefEq goalType requiredType then
                    return goal
                return .none

              let conversionFunction : Expr <-
              match existingMatch with
              | some mvarId => return .mvar mvarId
              | none => withMainContext do
                let newGoal <- mkFreshExprMVar requiredType MetavarKind.syntheticOpaque `mapRight
                let mainGoalId ← getMainGoal
                replaceMainGoal [mainGoalId, newGoal.mvarId!]
                return newGoal

              return .app conversionFunction (.lit <| .natVal val)

           else
             return .lit v

        | Literal.strVal val => return .lit v

  | .sort l => return .sort l

  | .const n ls =>
    let env ← getEnv
    let decl := env.find? n

    match decl with
    | none => return e
    | some decl => do

      if n == αName then
        return .const βName ls

      let origType := decl.type.instantiateLevelParams decl.levelParams ls
      -- let newType := substType (αName := αName) (βName := βName) origType
      let newType <- trale origType

      if ← Meta.isExprDefEq origType newType then
        return e

      -- let ctx ← getLCtx
      -- ctx.forM fun localDecl => do
      --   let localDeclType ← instantiateMVars localDecl.type

      --   if ← Meta.isExprDefEq localDeclType origType then
      --     return

      --   let newLocalDeclType := substType (αName := αName) (βName := βName) localDeclType
      --   if ← Meta.isExprDefEq localDeclType newLocalDeclType then
      --     return localDecl

      let goals ← getGoals
      for goal in goals do
        let doesMatch : Bool <- goal.withContext do
          -- TODO Question: is there a nicer monadic way to do this?
          let decl := (← getLCtx).findFromUserName? `orig
          if decl.isNone then
            -- return true
            return false
          let decl := decl.get!

          let (declVal, declType) <- Converter.openFVar decl.toExpr decl.type

          match declVal with
          | .const n' ls' => return (n' == n) && (ls' == ls)
          | _ => return false

        -- FIXME This is for testing only
        if doesMatch || true then
          let goalType ← goal.getType''
          if ← Meta.isExprDefEq goalType newType then
            -- IO.println s!"[trale] used orig to avoid repeating of: {n}"
            return Expr.mvar goal



      -- for goal in goals do
        -- let a := 3
        -- try
        --   let doesMatch : Nat <- goal.withContext do
        --     -- let decl := (← getLCtx).findFromUserName? `orig
        --     -- let decl : Option String := some "test"
        --     -- let decl : Option Nat := some default
        --     let decl : Option Nat := none
        --     -- Option Nat
        --     -- let abc : String := default
        --     let decl <- decl

        --   --   -- let abc := Name

        --     return 4

        -- catch e =>
        --   let msg <- e.toMessageData.toString
        --   IO.println s!"[trale] Error running doesMatch: {msg}"

        -- -- IO.println s!"[trale] doesMatch: {doesMatch}"
        -- let defaultString : String := default

        -- IO.println s!"[trale] default String length: {defaultString.length}"

          -- -- return `test

          -- -- if decl.hasValue then
          -- --   return false

          -- -- let decl -> do try
          --   -- return
          -- let decl <- getLocalDeclFromUserName `orig
          -- -- catch e =>
          -- --   return

          -- let (declVal, declType) <- Converter.openConstant decl.toExpr decl.type

          -- match declVal with
          -- | .const n' ls' => return n' == n
          -- | _ => return false

          -- -- let declType := decl.type

          -- -- match declVal with

        -- if doesMatch then
        --   let goalType ← goal.getType''
        --   if ← Meta.isExprDefEq goalType newType then
        --     return Expr.mvar goal

      let origTypeType <- inferType origType
      -- IO.println s!"[trale] origTypeType: {origTypeType} ({reprStr origTypeType})"

      if origTypeType.isProp then
        -- match origTypeType.
        -- if origType.sort then
        --   return e
        for goal in goals do
          let goalType ← goal.getType''
          if ← Meta.isExprDefEq goalType newType then
            return Expr.mvar goal

      -- try

      --   let localDecl ← getLocalDeclFromUserName n
      --   let localDeclType := localDecl.type

      --   if ← Meta.isExprDefEq localDeclType newType then
      --     return localDecl.toExpr

      --   none
      -- catch e =>
      --   IO.println s!"Not found: {n}"
      --   some e

      -- let err := try
      --   let localDecl ← getLocalDeclFromUserName n
      --   let localDeclType := localDecl.type

      --   if ← Meta.isExprDefEq localDeclType origType then
      --     return localDecl.toExpr

      --   none
      -- catch e => some e

      -- let newName := n.appendBefore s!"{βName} equivalent for {αName}'s "

      -- let newName := Name.mkStr Name.anonymous s!" {βName} equivalent for {αName}'s {n} "
      -- let newName := Name.mkStr Name.anonymous s!" Equivalent for {n} using {βName} instead of {αName} "
      -- let newName := Name.mkStr Name.anonymous s!"[{αName}→{βName}] {n}"
      -- let newName := Name.mkStr Name.anonymous s!"'{n}' [{βName.lastComponentAsString}/{αName}]"
      let newName := Name.mkStr Name.anonymous s!"{n.lastComponentAsString}'"
      -- let newName := Name.mkStr Name.anonymous s!"{n}'"

      IO.println s!"[trale] adding goal of type: {newType}"

      let newType <- instantiateMVars newType

      let p ← mkFreshExprMVar newType MetavarKind.syntheticOpaque newName

      -- let p ← mkFreshExprMVar newType MetavarKind.synthetic n

      let mvarId : MVarId := p.mvarId!
      -- let mvarIdOrig : MVarId := ⟨Name.str mvarId.name "orig"⟩
      -- let lctx ← getLCtx
      -- let localInstances ← getLocalInstances
      -- IO.println s!"[trale] Would assign to {mvarIdOrig.name}"


      -- let mvarIdNew ← mvarId.define `orig origType e
      -- let (_, mvarIdNew) ← mvarIdNew.intro1P
      let mvarIdNew := mvarId


      -- let mvarIdNew := mvarId

      -- let mvarIdNew := mvarId

      -- modifyMCtx fun mctx => mctx.addExprMVarDecl mvarIdOrig Name.anonymous lctx localInstances origType MetavarKind.natural;
      -- mvarIdOrig.assignIfDefeq e

      let mainGoalId ← getMainGoal
      replaceMainGoal [mainGoalId, mvarIdNew]
      return p
      -- return e



      -- let val := decl.value!
      -- let val ← trale val
      -- return e
      -- return .const n ls

    -- return .const n ls

  | .fvar n => return .fvar n
  | .bvar i => return .bvar i
  | .mvar n => return .mvar n
  -- | _ => return e

end Conversion

open Lean Meta Elab Tactic Term in
elab "trale_add_transformed" " [" alphaName:ident " -> " betaName:ident "] " n:ident " := " td:term  : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let origVal ← Tactic.elabTermEnsuringType td none
    let origType ← inferType origVal
    let (origVal, origType) <- openFVar origVal origType
    let (origVal, origType) ← openConstant origVal origType

    let origVal <- instantiateMVars origVal
    let origType <- instantiateMVars origType

    IO.println s!"[add_transf] origVal: {reprStr origVal}"
    IO.println s!"[add_transf] origType: {reprStr origType}"

    -- let origType ← instantiateMVars origType
    -- let αName := ``Nat
    -- let βName := ``Mod5AddSurj.Zmod5

    let αName := alphaName.getId
    let βName := betaName.getId

    let lctx ← getLCtx
    let localInstances ← getLocalInstances

    let αNameVar : MVarId := ⟨`traleTypeAlpha⟩
    let βNameVar : MVarId := ⟨`traleTypeBeta⟩

    let u1 ← mkFreshLevelMVar
    let mvarType1 ← mkFreshExprMVarAt lctx localInstances (mkSort u1) MetavarKind.natural Name.anonymous

    let u2 ← mkFreshLevelMVar
    let mvarType2 ← mkFreshExprMVarAt lctx localInstances (mkSort u2) MetavarKind.natural Name.anonymous

    modifyMCtx fun mctx => mctx.addExprMVarDecl αNameVar Name.anonymous lctx localInstances mvarType1 MetavarKind.natural;
    modifyMCtx fun mctx => mctx.addExprMVarDecl βNameVar Name.anonymous lctx localInstances mvarType2 MetavarKind.natural;


    if !(← αNameVar.isAssigned) then
      αNameVar.assignIfDefeq <| Expr.const αName []

    if !(← βNameVar.isAssigned) then
      βNameVar.assignIfDefeq <| Expr.const βName []


    let transformed ← Conversion.trale (αName := αName) (βName := βName) origVal
    -- let transformedType ← inferType transformed
    -- let transformedType := Conversion.substType (αName := ``Nat) (βName := ``Mod5AddSurj.Zmod5) origType
    let transformedType <- Conversion.trale (αName := αName) (βName := βName) origType

    -- let inferredType ← Meta.inferType transformed

    -- IO.println s!"[add_transf] transformedType: {reprStr transformedType}"
    -- IO.println s!"[add_transf] inferred type: {reprStr inferredType}"


    -- let isTypeCorrect <- Meta.isExprDefEq (<- instantiateMVars transformedType) (<- Meta.inferType (<- instantiateMVars transformed))
    -- let isCloseCorrect <- Meta.isExprDefEq transformedType (<- mvarId.getType'')
--
    -- IO.println s!"[add_transf] isTypeCorrect: {isTypeCorrect}"
    -- IO.println s!"[add_transf] would close: {isCloseCorrect}"

    -- let mvarId1 : MVarId := ⟨`alphaName⟩

    -- let decl <- Lean.MVarId.findDecl? mvarId1
    -- mvarId1.assignIfDefeq
    -- mvar


    -- let existingMvar1 <- Lean.Meta.getMVarDecl n.getId

    -- let mvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `alphaName)
    -- let mvar2 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `betaName)

    -- mvar1.mvarId!.assign (.const ``Nat.zero [])
    -- mvar2.mvarId!.assign (.const ``Nat.zero [])

    liftMetaTactic fun mvarId => do
      -- let mvarIdNew ← mvarId.define n.getId origType origVal
      let mvarIdNew ← mvarId.define n.getId transformedType transformed
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]

    -- let ctx ← Lean.MonadLCtx.getLCtx

open Lean Meta Elab Tactic Term in
elab "trale_refine " : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let decl : LocalDecl ← Lean.Meta.getLocalDeclFromUserName `orig
    -- IO.println s!"[refine] Found orig: {reprStr decl.toExpr}"


    -- let mvarIdOrig : MVarId := ⟨Name.str mvarId.name "orig"⟩

    -- let decl <- mvarIdOrig.findDecl?
    -- if decl.isNone then
    --   throwTacticEx `traleRefine mvarId "No original declaration found"
    -- let decl := decl.get!
    -- let expr ← instantiateMVars <| .mvar mvarIdOrig

    let expr ← instantiateMVars <| decl.toExpr

    -- let (origVal, origType) ← openFVar expr (← instantiateMVars decl.type)

    let (origVal, origType) ← openFVar expr (← instantiateMVars decl.type)
    let (origVal, origType) ← openConstant origVal (← instantiateMVars origType)

    -- let origVal := expr
    -- let origType := decl.type


    -- IO.println s!"[trale refine] After opening: {reprStr origVal}"

    let αNameVar : MVarId := ⟨`traleTypeAlpha⟩
    let βNameVar : MVarId := ⟨`traleTypeBeta⟩

    let αNameValue ← instantiateMVars <| .mvar αNameVar
    let βNameValue ← instantiateMVars <| .mvar βNameVar

    let αName := αNameValue.constName!
    let βName := βNameValue.constName!

    -- IO.println s!"αName: {αName}"
    -- IO.println s!"βName: {βName}"
    -- IO.println s!"[refine] origVal: {origVal}"
    -- IO.println s!"[refine] origType: {origType}"

    trace[info] s!"[refine] αName: {αName}"

    IO.println s!"[refine] mainGoal init: {mvarId.name}"

    IO.println s!"[refine] mainGoal before: {(<- getMainGoal).name}"
    let transformed ← Conversion.trale (αName := αName) (βName := βName) origVal
    -- IO.println s!"[refine] mainGoal after: {(<- getMainGoal).name}"

    let transformedType <- Conversion.trale (αName := αName) (βName := βName) origType

    -- mvarId.assignIfDefeq transformed
    -- mvarId.

    -- closeMainGoal (.lam `trap q(String) transformed BinderInfo.default) (checkUnassigned := false)

    -- let isTypeCorrect <- Meta.isExprDefEq transformedType (<- Meta.inferType transformed)
    -- let isCloseCorrect <- Meta.isExprDefEq transformedType (<- mvarId.getType'')

    -- IO.println s!"[refine] isTypeCorrect: {isTypeCorrect}"
    -- IO.println s!"[refine] isCloseCorrect: {isCloseCorrect}"

    closeMainGoal `trale_refine transformed (checkUnassigned := false)


    -- liftMetaTactic fun mvarId => do

    --   let mvarIdNew ← mvarId.define n.getId transformedType transformed
    --   -- let mvarIdNew ← mvarId.define n.getId origType origVal
    --   let (_, mvarIdNew) ← mvarIdNew.intro1P
    --   return [mvarIdNew]

    -- throwTacticEx `traleRefine mvarId "Found, but not implemented yet"




  --   let origVal ← Tactic.elabTermEnsuringType td none
  --   let origType ← inferType origVal
  --   let (origVal, origType) ← openConstant origVal origType

  --   -- let origType ← instantiateMVars origType
  --   -- let αName := ``Nat
  --   -- let βName := ``Mod5AddSurj.Zmod5

  --   let αName := alphaName.getId
  --   let βName := betaName.getId


  --   let transformed ← Conversion.trale (αName := αName) (βName := βName) origVal
  --   -- let transformedType ← inferType transformed
  --   -- let transformedType := Conversion.substType (αName := ``Nat) (βName := ``Mod5AddSurj.Zmod5) origType
  --   let transformedType <- Conversion.trale (αName := αName) (βName := βName) origType

  --   liftMetaTactic fun mvarId => do
  --     -- let mvarIdNew ← mvarId.define n.getId origType origVal
  --     let mvarIdNew ← mvarId.define n.getId transformedType transformed
  --     let (_, mvarIdNew) ← mvarIdNew.intro1P
  --     return [mvarIdNew]




  -- Lean.Elab.Tactic.withMainContext do
  --   let goal ← Lean.Elab.Tactic.getMainGoal
  --   let goalType ← Lean.Elab.Tactic.getMainTarget
  --   let ctx ← Lean.MonadLCtx.getLCtx
  --   let option_matching_expr ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
  --     let declExpr := decl.toExpr
  --     let declType ← Lean.Meta.inferType declExpr
  --     if ← Lean.Meta.isExprDefEq declType goalType
  --       then return Option.some declExpr
  --       else return Option.none
  --   match option_matching_expr with
  --   | some e => Lean.Elab.Tactic.closeMainGoal e
  --   | none =>
  --     Lean.Meta.throwTacticEx `custom_assump_2 goal
  --       (m!"unable to find matching hypothesis of type ({goalType})")


end Converter
