import Lean
import Trale.Utils.Trace
import Trale.Utils.Glueing
import Trale.Theories.Flip
import Qq

open Lean Meta Elab Std Qq Command


namespace Trale.Utils

syntax (name := tr_add_flipped) "tr_add_flipped" (ppSpace ident) (ppSpace ident) ? : attr

structure Config : Type where
  valR : Expr
  RR : Expr

structure ParamParts where
  levelU : Level
  levelV : Level
  levelW : Level

  fromType : Q(Sort $levelU)
  toType : Q(Sort $levelV)
  covMapType : Q(MapType)
  conMapType : Q(MapType)


def getParamParts (e : Expr) : MetaM ParamParts := do
  let levelU <- mkFreshLevelMVar
  let levelV <- mkFreshLevelMVar
  let levelW <- mkFreshLevelMVar

  let fromType : Q(Sort $levelU) ← mkFreshExprMVar .none (userName := `fromType)
  let toType : Q(Sort $levelV) ← mkFreshExprMVar .none (userName := `toType)

  let covMapType : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `covMapType)
  let conMapType : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `conMapType)

  let matcher : Q(Type (max levelU levelV levelW)) := q(Param.{levelW, levelU, levelV} $covMapType $conMapType $fromType $toType)

  if !(← isExprDefEq matcher e) then
    throwError "goal should be of type Param"

  let fromType : Q(Sort $levelU) ← instantiateMVars fromType
  let toType : Q(Sort $levelV) ← instantiateMVars toType
  let covMapType : Q(MapType) ← instantiateMVars covMapType
  let conMapType : Q(MapType) ← instantiateMVars conMapType

  return {
    levelU, levelV, levelW, fromType, toType,
    covMapType, conMapType
  }

def flipParamCore (p : ParamParts) : Σ l : Level, Q(Sort $l) :=
  let {
    levelU, levelV, levelW, fromType, toType, covMapType, conMapType
  } := p

  ⟨_, q(Param.{levelW, levelV, levelU} $conMapType $covMapType $toType $fromType)⟩

def flipParam (e : Expr) : MetaM Expr := do
  let p ← getParamParts e
  let ⟨_, expr⟩ := flipParamCore p

  return expr



def elabAddFlipped : Syntax → CoreM Config
  | `(attr| tr_add_flipped%$tk $valR $RR) => do
    trace[tr.utils] s!"valR: ${valR}"
    trace[tr.utils] s!"RR: ${RR}"

    let valR_name := valR.getId
    let RR_name := RR.getId

    return {
      valR := ←mkConstWithLevelParams valR_name,
      RR := ←mkConstWithLevelParams RR_name
      -- valR := ← elabTermEnsuringTypeQ
      -- valR := ←(Term.elabTerm valR .none)
    }
  | _ => throwUnsupportedSyntax

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
      let value : Expr := .const src (levelParams.map mkLevelParam)
      -- let type : Expr ← liftAttrM (liftMetaM (inferType value))
      let type := info.type

      -- trace[tr.utils] s!"Type is {repr type}"

      let config ← elabAddFlipped stx
      trace[tr.utils] s!"Config valR: {config.valR}"
      trace[tr.utils] s!"Config RR: {config.RR}"

      -- liftCoreM <|
      let ((covMapType, conMapType, tail, completeType, args), state) ← MetaM.run do
        let (args, argsBi, tail) ← forallMetaTelescope info.type

        -- let {covMapType, conMapType, ..} ← patternMatchParam tail
        -- let {
        --   covMapType, conMapType, levelU, levelV, levelW, fromType, toType
        -- } ← getParamParts tail
        let p ← getParamParts tail

        -- let flippedType := q(Param.{levelW, levelV, levelU} .Map0 $covMapType $toType $fromType)
        let ⟨level, flippedType⟩ := flipParamCore p

        trace[tr.utils] s!"Trace test from within the MetaM run"


        let argsTypes ← (args.map (·.mvarId!)).mapM Lean.MVarId.getType'


        trace[tr.utils] s!"Args types: {argsTypes}"

        let completeType ← mkLambdaFVars args flippedType




        return (p.covMapType, p.conMapType, tail, completeType, args)

      trace[tr.utils] s!"Tail is {repr tail}"


      trace[tr.utils] s!"Args: {args}"

      -- trace[tr.utils] s!"Flipped type is {repr flippedType}"
      trace[tr.utils] s!"Complete type is {completeType}"


      addDecl <| .defnDecl {
        name,
        value
        levelParams,
        type,
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
