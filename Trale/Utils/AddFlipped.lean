import Lean
import Trale.Utils.Trace
import Trale.Utils.Glueing
import Trale.Theories.Flip
import Qq

open Lean Meta Elab Std Qq Command Term


namespace Trale.Utils

syntax (name := tr_add_flipped) "tr_add_flipped" (ppSpace ident) (ppSpace ident) ? : attr

structure Config : Type where
  -- valR : Expr
  RR : Expr

structure ParamParts where
  levelU : Level
  levelV : Level
  levelW : Level

  fromType : Q(Sort $levelU)
  toType : Q(Sort $levelV)
  covMapType : Q(MapType)
  conMapType : Q(MapType)

-- inductive ParamParseError
--   | NotParam : "Not a param"

def getParamParts (e : Expr) : MetaM (Except String ParamParts) := do
  let levelU <- mkFreshLevelMVar
  let levelV <- mkFreshLevelMVar
  let levelW <- mkFreshLevelMVar

  let fromType : Q(Sort $levelU) ← mkFreshExprMVar .none (userName := `fromType)
  let toType : Q(Sort $levelV) ← mkFreshExprMVar .none (userName := `toType)

  let covMapType : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `covMapType)
  let conMapType : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `conMapType)

  let matcher : Q(Type (max levelU levelV levelW)) := q(Param.{levelW, levelU, levelV} $covMapType $conMapType $fromType $toType)

  if !(← isExprDefEq matcher e) then
    -- throwError "goal should be of type Param"
    return .error "goal should be of type Param"

  let fromType : Q(Sort $levelU) ← instantiateMVars fromType
  let toType : Q(Sort $levelV) ← instantiateMVars toType
  let covMapType : Q(MapType) ← instantiateMVars covMapType
  let conMapType : Q(MapType) ← instantiateMVars conMapType

  let levelU ← instantiateLevelMVars levelU
  let levelV ← instantiateLevelMVars levelV
  let levelW ← instantiateLevelMVars levelW

  return .ok {
    levelU, levelV, levelW, fromType, toType, covMapType, conMapType
  }

def flipParamCore (p : ParamParts) : Σ l : Level, Q(Sort $l) :=
  let {
    levelU, levelV, levelW, fromType, toType, covMapType, conMapType
  } := p

  ⟨_, q(Param.{levelW, levelV, levelU} $conMapType $covMapType $toType $fromType)⟩

def flipParam (e : Expr) : MetaM Expr := do
  let p ← (getParamParts e)
  match p with
  | .error s => throwError s
  | .ok p =>
  let ⟨_, expr⟩ := flipParamCore p

  return expr



def elabAddFlipped : Syntax → CoreM Config
  | `(attr| tr_add_flipped%$tk $RR) => do
    -- trace[tr.utils] s!"valR: ${valR}"
    trace[tr.utils] s!"RR: ${RR}"

    -- let valR_name := valR.getId
    let RR_name := RR.getId

    return {
      -- valR := ←mkConstWithLevelParams valR_name,
      RR := ←mkConstWithLevelParams RR_name
      -- valR := ← elabTermEnsuringTypeQ
      -- valR := ←(Term.elabTerm valR .none)
    }
  | _ => throwUnsupportedSyntax

def tryFlip (m : MVarId) : MetaM (Option Expr) := do
  let p ← (getParamParts (←m.getType))
  match p with
  | .error _ => return .none
  | .ok p =>

  -- let ⟨_, flipped⟩ := flipParamCore p
  let {
    levelU, levelV, levelW, fromType, toType, covMapType, conMapType
  } := p

  let flipped : Q(Type (max levelU levelV levelW)) := q(Param.{levelW, levelV, levelU} $conMapType $covMapType $toType $fromType)

  let newMVar : Q($flipped) ← mkFreshExprMVar (.some flipped) (userName := ←m.getTag)

  m.assign q(Param.flip $newMVar)
  return newMVar

def tryToBottom (m : MVarId) : MetaM (Option Expr) := do
  let p ← (getParamParts (←m.getType))
  match p with
  | .error _ => return .none
  | .ok p =>

  -- let ⟨_, flipped⟩ := flipParamCore p
  let {
    levelU, levelV, levelW, fromType, toType, covMapType, conMapType
  } := p

  let mType : Q(Type (max levelU levelV levelW)) := q(
    Param.{levelW, levelU, levelV} $covMapType $conMapType $fromType $toType
  )

  let mVal ← mkFreshExprMVarQ mType
  if !(←isDefEq mVal (.mvar m)) then
    throwError "In tryToBottom: isDefEq check failed"

  return q(Param.toBottom $mVal)


initialize registerBuiltinAttribute {
    name := `tr_add_flipped
    descr := "Register the flipped variation"
    add := fun src stx kind ↦ do
      trace[tr.utils] s!"The name is {src}"

      let name : Name :=
        match src with
        | .str a b => .str a (b ++ "_flipped")
        | _ => .str src "flipped"

      let info ← getConstVal src
      let levelParams := info.levelParams
      let origValue : Expr := .const src (levelParams.map mkLevelParam)
      -- let type : Expr ← liftAttrM (liftMetaM (inferType value))
      let origType := info.type

      -- trace[tr.utils] s!"Type is {repr type}"

      let config ← elabAddFlipped stx
      -- trace[tr.utils] s!"Config valR: {config.valR}"
      trace[tr.utils] s!"Config RR: {config.RR}"

      -- liftCoreM <|
      let ((covMapType, conMapType, tail, levelX, type, args, body), state) ← MetaM.run do
        trace[tr.utils] s!"Orig type: {repr origType}"

        let (args, argsBi, tail) ← forallMetaTelescope info.type

        -- let {covMapType, conMapType, ..} ← patternMatchParam tail
        -- let {
        --   covMapType, conMapType, levelU, levelV, levelW, fromType, toType
        -- } ← getParamParts tail
        let p ←
          match (← getParamParts tail) with
          | .error s => throwError s
          | .ok a => pure a

        -- let flippedType := q(Param.{levelW, levelV, levelU} .Map0 $covMapType $toType $fromType)
        let ⟨level, flippedType⟩ := flipParamCore p

        trace[tr.utils] s!"Trace test from within the MetaM run"

        let flippedArgs ← args.mapM fun e => do
          pure $ (← tryFlip e.mvarId!).getD e

        let flippedArgsToBottom ← flippedArgs.mapM fun e => do
          pure $ (← tryToBottom e.mvarId!).getD e

        let argsTypes ← (args.map (·.mvarId!)).mapM Lean.MVarId.getType'
        let flippedTypes ← flippedArgs.mapM inferType

        trace[tr.utils] s!"Args types: {argsTypes}"
        trace[tr.utils] s!"Flipped types: {argsTypes}"

        -- let levelY ← mkFreshLevelMVar

        let RR_type ←
          match config.RR with
          | .const a levels => pure (←getConstInfo a).type
          | a => inferType a

        let RR_full ← reduce $ mkAppN config.RR flippedArgsToBottom
        trace[tr.utils] s!"RR_full: {RR_full}"

        trace[tr.utils] s!"RR_type (1): {RR_type}"
        -- let RR_type := mkAppN RR_type flippedArgsToBottom
        -- trace[tr.utils] s!"RR_type (2): {RR_type}"
        -- let RR_type ← reduce RR_type
        -- trace[tr.utils] s!"RR_type (3): {RR_type}"
        let (RR_type_args, RR_type_args_bi, RR_type_tail) ← forallMetaTelescope RR_type

        for (a, b) in RR_type_args.zip flippedArgsToBottom do
          if !(←isDefEq a b) then
            throwError s!"Failed to unify {a} with {b}"

        let RR_type_args_extra := RR_type_args.extract flippedArgsToBottom.size


        -- let RR_applied := mkAppN RR_type flippedArgs
        -- let RR_tail ← whnf $ mkAppN RR_applied #[←mkFreshExprMVar .none, ←mkFreshExprMVar .none]

        trace[tr.utils] s!"RR_type_args: {RR_type_args}"
        trace[tr.utils] s!"Tail is {RR_type_tail}"

        let RR_type_tail_parts ←
          match (←getParamParts RR_type_tail) with
          | .error s => throwError s
          | .ok a => pure a

        -- let completeType ← mkLambdaFVars flippedArgs flippedType
        let completeType ←
          (flippedArgs.zip argsBi).foldrM
            (fun (arg, bi) body =>
              mkForallFVars #[arg] body
              (binderInfoForMVars := bi)
            )
            flippedType

        let baseCovMapType : Q(MapType) := p.covMapType
        let baseConMapType : Q(MapType) := p.conMapType
        let baseLevelU := p.levelU
        let baseLevelV := p.levelV
        let baseLevelW := p.levelW
        let baseFromType : Q(Sort baseLevelU) := p.fromType
        -- let baseFromType ← mkFreshExprMVarQ q(Sort baseLevelU)
        let baseToType : Q(Sort baseLevelV) := p.toType
        -- let baseToType ← mkFreshExprMVarQ q(Sort baseLevelV)

        let base ← mkFreshExprMVarQ q(
          Param.{baseLevelW} $baseCovMapType $baseConMapType $baseFromType
          $baseToType
        )

        let baseCandidate ← whnf (mkAppN origValue args)
        if !(← isExprDefEq base baseCandidate) then
          throwTypeMismatchError
            "Failed to unify base with the expected type"
            (← inferType base) (← inferType baseCandidate) baseCandidate

        -- #check Array
        let valR_inferred ←
          mkLambdaFVars RR_type_args --(RR_args.extract args.size)
          RR_type_tail_parts.toType

        let RR_type_tail_cov := RR_type_tail_parts.covMapType
        let RR_type_tail_con := RR_type_tail_parts.conMapType

        let donorCondition := q($RR_type_tail_cov ≥ MapType.Map1)
        let decidableCondition <- mkFreshExprMVarQ q(Decidable $donorCondition) (kind := .natural) (userName := `extendDonorConditionDecidable)
        let donorConditionValue <- mkFreshExprMVarQ q($donorCondition) (kind := .natural) (userName := `extendDonorConditionValue)

        -- #check (runTermElabM)
        let (a, state) ← TermElabM.run do
          -- runTermElabM (←synthesizeInstMVarCore decidableCondition.mvarId!)
          -- let decidableCondition <- mkFreshExprMVarQ q(Decidable ($RR_tail_cov ≥ MapType.Map1)) (kind := .natural) (userName := `extendDonorConditionDecidable)
          if  !(←synthesizeInstMVarCore decidableCondition.mvarId!) then
            throwError s!"Failed to decide on ({donorCondition}"

          return decidableCondition

        if !(<- isExprDefEq decidableCondition q(Decidable.isTrue $donorConditionValue)) then
          throwError  s!"Failed to proof ({donorCondition}) is true"


        trace[tr.utils] s!"DecidableCondition (1): {decidableCondition}"
        let decidableCondition ← instantiateMVars decidableCondition
        trace[tr.utils] s!"DecidableCondition (2): {decidableCondition}"

        trace[tr.utils] s!"Condition value (1): {donorConditionValue}"
        let donorConditionValue ← instantiateMVars donorConditionValue
        trace[tr.utils] s!"Condition value (2): {donorConditionValue}"

        -- if !(←isDefEq valR_inferred config.valR) then
        --   throwTypeMismatchError
        --     "Failed to unify valR with the inferred one"
        --     (←inferType config.valR) (←inferType valR_inferred) valR_inferred

        -- let abc := q(2)
        -- let body2 ← q(flip2a $base)

        -- #check instDecidableLEMapType
        -- #check sorryAx

        let (RR_full_args, _, RR_full_tail) ← lambdaMetaTelescope RR_full

        for (a, b) in RR_type_args_extra.zip RR_full_args do
          if !(←isDefEq a b) then
            throwError s!"Failed to unify {a} with {b}"

        trace[tr.utils] s!"RR_full_args: {RR_full_args}"

        let RR_forget ←
          -- mkLambdaFVars (RR_args.extract flippedArgsToBottom.size)
          mkLambdaFVars RR_full_args
          -- =<< (mkLambdaFVars RR_type_args_extra
            $ mkAppN
            (.const ``Param.forget [RR_type_tail_parts.levelW, RR_type_tail_parts.levelU, RR_type_tail_parts.levelV])
            #[
              RR_type_tail_parts.fromType, RR_type_tail_parts.toType,
              -- q(sorry : Sort $RR_tail_parts.levelU),
              -- q(sorry : Sort $RR_tail_parts.levelV),
              RR_type_tail_cov, RR_type_tail_con,
              q(MapType.Map1), q(MapType.Map0),
              donorConditionValue,
              -- q(sorry : MapType.Map1 ≤ MapType.Map1),
              q(@map0bottom $RR_type_tail_con),
              -- q(instDecidableLEMapType MapType.Map0 MapType.Map0),
              -- RR_full
              RR_full_tail
            ]
          -- )

        trace[tr.utils] s!"RR_full: {RR_full}"

        trace[tr.utils] s!"RR_forget (1): {RR_forget}"

        trace[tr.utils] s!"RR_forget (2): {←instantiateMVars RR_forget}"


        trace[tr.utils] s!"RR_forget tye: {←inferType RR_forget}"

        trace[tr.utils] s!"RR_full type: {←inferType RR_full}"

        let body ← mkLambdaFVars flippedArgs (
          mkAppN
          -- (←mkConstWithLevelParams ``flip2a) -- the universe levels of this need to be filled in
          (.const ``flip2a [p.levelV, p.levelU, p.levelW, RR_type_tail_parts.levelW])
          #[
            p.toType,
            p.fromType,
            base,
            -- mkAppN config.valR flippedArgsToBottom,
            mkAppN valR_inferred flippedArgsToBottom,
            RR_forget
          ]
        )

--         (kernel) application type mismatch
--   @flip2a (@Map2a_arrow α α' β β' p1.flip p2.flip)
-- argument has type
--   Param2a0 (α → β) (α' → β')
-- but function has type
--   {α β : Sort (imax u v)} →
--     (base : Param2a0 β α) →
--       (R : α → β → Sort (imax u u u_1 u_2)) →
--         ({a : α} → {b : β} → Param10 (Param.R MapType.Map2a MapType.Map0 b a) (R a b)) → Param02a α β

/-

(kernel) application type mismatch
  flip2a (@Map2a_arrow α α' β β' p1.flip p2.flip) (@arrowR α α' β β' p1.toBottom p2.toBottom)
    (@arrowR_rel α α' β β' p1.toBottom p2.toBottom)
argument has type
  {f : α' → β'} →
    {f' : α → β} →
      Param10 (@arrowR α α' β β' p1.toBottom p2.toBottom f f')
        (@arrowR α' α β' β (Param.flip p1.toBottom) (Param.flip p2.toBottom) f' f)
but function has type
  ({a : α' → β'} →
      {b : α → β} → Param10 (Param.R MapType.Map2a MapType.Map0 b a) (@arrowR α α' β β' p1.toBottom p2.toBottom a b)) →
    Param02a (α' → β') (α → β)

-/

        trace[tr.utils] s!"Body is {body}"

          -- pure .const `test []

        -- let completeType ← mkForallFVars args flippedType

        let levelX ← mkFreshLevelMVar
        -- let type ← mkFreshExprMVarQ q(Sort $levelX)

        trace[tr.utils] s!"Complete type (1) is {repr completeType}"
        let completeTypeType ← inferType completeType
        trace[tr.utils] s!"Complete type type (1) is {repr completeTypeType}"

        if !(←isExprDefEq q(Sort $levelX) completeTypeType) then
          throwError "Failed to unify flipped type with Sort _"

        -- let type : Q() ← instantiateMVars type
        return (
          p.covMapType, p.conMapType, tail, ←instantiateLevelMVars levelX,
          completeType, args, body
        )

      trace[tr.utils] s!"Tail is {repr tail}"


      trace[tr.utils] s!"Args: {args}"

      trace[tr.utils] s!"Complete type is {type}"
      trace[tr.utils] s!"Level is {levelX}"

      -- let value := mkAppN (.const ``sorryAx [levelX]) #[type, q(false)]
      let value := body

      addDecl <| .defnDecl {
        name,
        value,
        levelParams,
        type := type,
        hints := ReducibilityHints.regular 100,
        safety := DefinitionSafety.safe
      }

      trace[tr.utils] s!"Registered {name}"


      -- addInstance (src.)
      -- sorry
    -- applicationTime := .afterCompilation
  }



/- def Param02a_arrow''
  [p1 : Param2b0 α α']
  [p2 : Param02a β β']
  : Param02a (α → β) (α' → β') :=
   flip2a Map2a_arrow (arrowR p1 p2) (
    fun {f f'} =>
      (arrowR_rel (f := f) (f' := f') (p1 := p1.forget) (p2 := p2.forget)).flip.forget
  ) -/
