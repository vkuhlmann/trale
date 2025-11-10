import Lean
import Trale.Utils.Trace
import Trale.Utils.Glueing
import Trale.Theories.Flip
import Qq

open Lean Meta Elab Std Qq Command Term


namespace Trale.Utils

syntax (name := tr_add_flipped) "tr_add_flipped" (ppSpace ident) (ppSpace ident) ? : attr

structure AddFlippedConfig : Type where
  RR : Expr

structure ParamParts where
  levelU : Level
  levelV : Level
  levelW : Level

  fromType : Q(Sort $levelU)
  toType : Q(Sort $levelV)
  covMapType : Q(MapType)
  conMapType : Q(MapType)

def getParamParts? (e : Expr) : MetaM (Except String ParamParts) := do
  let levelU <- mkFreshLevelMVar
  let levelV <- mkFreshLevelMVar
  let levelW <- mkFreshLevelMVar

  let fromType : Q(Sort $levelU) ← mkFreshExprMVar .none (userName := `fromType)
  let toType : Q(Sort $levelV) ← mkFreshExprMVar .none (userName := `toType)

  let covMapType : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `covMapType)
  let conMapType : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `conMapType)

  let matcher : Q(Type (max levelU levelV levelW)) := q(Param.{levelW, levelU, levelV} $covMapType $conMapType $fromType $toType)

  if !(← isExprDefEq matcher e) then
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

def getParamParts! (e : Expr) := do
  match (← getParamParts? e) with
    | .error s => throwError s
    | .ok a => pure a

def flipParamCore (p : ParamParts) : Σ l : Level, Q(Sort $l) :=
  let {
    levelU, levelV, levelW, fromType, toType, covMapType, conMapType
  } := p

  ⟨_, q(Param.{levelW, levelV, levelU} $conMapType $covMapType $toType $fromType)⟩

def flipParam (e : Expr) : MetaM Expr := do
  let p ← (getParamParts? e)
  match p with
  | .error s => throwError s
  | .ok p =>
  let ⟨_, expr⟩ := flipParamCore p

  return expr

def synthesizeDecidable! (proofOutput : Expr) : MetaM Unit := do
  let proposition ← mkFreshExprMVarQ q(Prop)
  if !(←isDefEq proposition (← inferType proofOutput)) then
    throwError "Failed to match the type to decide with Prop"

  let decidable ← mkFreshExprMVarQ q(Decidable $proposition)
  let proof ← mkFreshExprMVarQ q($proposition)

  let (_, _) ← TermElabM.run do
    if  !(←synthesizeInstMVarCore decidable.mvarId!) then
      throwError s!"Failed to decide on ({proposition})"

  if !(←isExprDefEq decidable q(Decidable.isTrue $proof)) then
    throwError  s!"Failed to proof ({proposition}) is true"

  let proof ← instantiateMVars proof
  if !(←isDefEq proofOutput proof) then
    throwError s!"Failed to output the decided value to the expression"

def synthesizeForget (param : Expr) (destParts : ParamParts) (srcParts : ParamParts) := do
    let covWeaken ← mkFreshExprMVarQ q($srcParts.covMapType ≥ $destParts.covMapType)
    let conWeaken ← mkFreshExprMVarQ q($srcParts.conMapType ≥ $destParts.conMapType)

    synthesizeDecidable! covWeaken
    synthesizeDecidable! conWeaken

    let RR_forget := mkAppN
        (.const ``Param.forget [srcParts.levelW, srcParts.levelU, srcParts.levelV])
        #[
          srcParts.fromType, srcParts.toType,
          srcParts.covMapType, srcParts.conMapType,
          destParts.covMapType, destParts.conMapType,
          covWeaken,
          conWeaken,
          param
        ]
    return RR_forget


def getAddFlippedConfig : Syntax → CoreM AddFlippedConfig
  | `(attr| tr_add_flipped $RR) => do
    let RR_name := RR.getId
    return {
      RR := ←mkConstWithLevelParams RR_name
    }
  | _ => throwUnsupportedSyntax

def tryFlip (m : MVarId) : MetaM (Option Expr) := do
  let p ← (getParamParts? (←m.getType))
  match p with
  | .error _ => return .none
  | .ok p =>

  let {
    levelU, levelV, levelW, fromType, toType, covMapType, conMapType
  } := p

  let flipped : Q(Type (max levelU levelV levelW)) :=
    q(Param.{levelW, levelV, levelU} $conMapType $covMapType $toType $fromType)

  let newMVar ← mkFreshExprMVarQ q($flipped) (userName := ←m.getTag)

  m.assign q(Param.flip $newMVar)
  return newMVar

def tryToBottom (m : MVarId) : MetaM (Option Expr) := do
  let p ← (getParamParts? (←m.getType))
  match p with
  | .error _ => return .none
  | .ok p =>

  let {
    levelU, levelV, levelW, fromType, toType, covMapType, conMapType
  } := p

  let mType : Q(Type (max levelU levelV levelW)) :=
    q(Param.{levelW, levelU, levelV} $covMapType $conMapType $fromType $toType)

  let mVal ← mkFreshExprMVarQ mType
  if !(←isDefEq mVal (.mvar m)) then
    throwError "In tryToBottom: isDefEq check failed"

  return q(Param.toBottom $mVal)

def apply_eRR_and_seal
  (eRR_to_body RR : Expr)
  (RR_type_tail_parts : ParamParts)
  (RR_type_args flippedArgsToBottom flippedArgs : Array Expr)
  := do

  let RR_type ← match eRR_to_body with
    | .lam _ bt _ _ => pure bt
    | _ => throwError "Failed to infer type of the flip method's conv parameter"

  let (eRR_type_args, _, eRR_type_tail)
    ← forallMetaBoundedTelescope RR_type 2

  let RR ← reduce $ mkAppN RR flippedArgsToBottom
  let (RR_args, _, RR_tail) ← lambdaMetaTelescope RR
  for (a, b) in eRR_type_args.zip RR_args do
    if !(←isDefEq a b) then
      throwError s!"Failed to unify {a} (type: {← inferType a}) with {b} (type: {←inferType b})"

  let eRR_parts ← getParamParts! eRR_type_tail

  let RR_type_args_extra := RR_type_args.extract flippedArgsToBottom.size

  for (a, b) in RR_type_args_extra.zip RR_args do
    if !(←isDefEq a b) then
      throwError s!"Failed to unify {a} with {b}"

  let RR_forget ←
    mkLambdaFVars RR_args
    (← synthesizeForget RR_tail eRR_parts RR_type_tail_parts)

  let value ← mkLambdaFVars flippedArgs (
    mkAppN
    eRR_to_body
    #[
      RR_forget
    ]
  )
  pure value

def instantiateBase
  (base : Expr) (info : ConstantVal) (args : Array Expr)
  := do
  let levelParams := info.levelParams
  let origValue := Expr.const info.name (levelParams.map mkLevelParam)
  let baseCandidate := mkAppN origValue args

  if !(← isExprDefEq base baseCandidate) then
    throwTypeMismatchError
      "Failed to unify base with the expected type"
      (← inferType base) (← inferType baseCandidate) baseCandidate


initialize registerBuiltinAttribute {
    name := `tr_add_flipped
    descr := "Register the flipped variation"
    add := fun src stx kind ↦ do
      let name : Name :=
        match src with
        | .str a b => .str a (b ++ "_flipped")
        | _ => .str src "flipped"

      let info ← getConstVal src
      let levelParams := info.levelParams

      let config ← getAddFlippedConfig stx

      let ((type, value), _) ← MetaM.run do
        let (args, argsBi, tail) ← forallMetaTelescope info.type

        let parts ← getParamParts! tail

        let baseLevelW := parts.levelW
        let base ← mkFreshExprMVarQ q(
          Param.{baseLevelW} $parts.covMapType $parts.conMapType $parts.fromType
          $parts.toType
        )
        instantiateBase base info args

        let flippedArgs ← args.mapM fun e => do
          pure $ (← tryFlip e.mvarId!).getD e

        let flippedArgsToBottom ← flippedArgs.mapM fun e => do
          pure $ (← tryToBottom e.mvarId!).getD e


        let RR_type ← inferType config.RR
        let (RR_type_args, RR_type_args_bi, RR_type_tail) ← forallMetaTelescope RR_type

        for (a, b) in RR_type_args.zip flippedArgsToBottom do
          if !(←isDefEq a b) then
            throwError s!"Failed to unify {a} with {b}"

        let type ←
          (flippedArgs.zip argsBi).foldrM
            (fun (arg, bi) body =>
              mkForallFVars #[arg] body
              (binderInfoForMVars := bi)
            )
            (flipParamCore parts).2


        let RR_type_tail_parts ← getParamParts! RR_type_tail
        let R ←
          mkLambdaFVars RR_type_args RR_type_tail_parts.toType

        let baseCov ← recoverMapTypeFromExpr! parts.covMapType

        let flipFunc := match baseCov with
          | .Map4 => ``flip4
          | .Map3 => ``flip3
          | .Map2a => ``flip2a
          | .Map2b => ``flip2b
          | .Map1 => ``flip1
          | .Map0 => ``flip0

        let eRR_to_body ← reduce <| mkAppN
          (.const flipFunc [parts.levelV, parts.levelU, parts.levelW, RR_type_tail_parts.levelW])
          #[
            parts.toType,
            parts.fromType,
            base,
            mkAppN R flippedArgsToBottom
          ]

        let value ← apply_eRR_and_seal
          eRR_to_body config.RR RR_type_tail_parts RR_type_args
          flippedArgsToBottom flippedArgs


        return (type, value)

      addAndCompile <| .defnDecl {
        name,
        value,
        levelParams,
        type := type,
        hints := ReducibilityHints.regular 100,
        safety := DefinitionSafety.safe
      }

      let (_, _) ← MetaM.run <| addInstance name AttributeKind.global 1000

      trace[tr.utils] s!"Registered {name}"
  }
