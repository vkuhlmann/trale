import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Lean.Util
import Qq
open Qq Lean Elab Command Tactic Term Expr Meta

-- axiom functionRelationApplication
--   (p1 : Param10 (A -> B) (A' -> B'))
--   (p2 : Param10 A A')
--   (p3 : Param10 B B')
--   :
--   ∀ f f' (_ : p1.R f f'),
--   ∀ a a' (_ : p2.R a a'), p3.R (f a) (f' a')

initialize Lean.registerTraceClass `tr.utils
-- builtin_initialize Lean.registerTraceClass `tr_split_application

-- #eval show IO Unit from do
--   Lean.registerTraceClass `tr_split_application

def forallApplication
  {α α' : Sort _}
  {β : α -> Sort _}
  {β' : α' -> Sort _}
  (p1 : Param10 α α')
  (a : α)
  (a' : α')
  (aR : p1.R a a')
  (p2 : ∀ a a' (_ : p1.R a a'), Param10 (β a) (β' a'))
  :
  Param10 (β a) (β' a') :=
    by
    tr_constructor

    case R =>
      exact (p2 a a' aR).R

    case right =>
      exact (p2 a a' aR).right

elab "tr_inspect_expr" td:term : tactic =>
  withMainContext do
    let expr ← Tactic.elabTerm td .none

    trace[tr.utils] s!"Type as expression is\n  {repr expr}"

    match expr with
    | .fvar fvarId =>
      --
      let ldecl ← getFVarLocalDecl expr
      trace[tr.utils] s!"Fvar value is\n  {repr ldecl.value}"

    | _ => return ()


elab "tr_split_application" : tactic =>
  -- TODO Is there a more elegant way to write the constant function?
  Lean.withTraceNode `tr.utils (fun _ => return "tr_split_application") do
    withMainContext do
      let goal ← getMainGoal
      let goalType ← getMainTarget

      -- trace[tr.utils] s!"Type is {goalType}"
      -- trace[tr.utils] s!"Type as expression is {repr goalType}"

      let levelU ← mkFreshLevelMVar
      let levelV ← mkFreshLevelMVar
      let levelW ← mkFreshLevelMVar

      let fromType : Q(Sort $levelU) ← mkFreshExprMVar .none (userName := `fromType)
      let toType : Q(Sort $levelV) ← mkFreshExprMVar .none (userName := `toType)

      let covMapType : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `covMapType)
      let conMapType : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `conMapType)

      let matcher : Q(Type (max levelU levelV levelW)) := q(Param $fromType $toType $covMapType $conMapType)

      if !(← isExprDefEq matcher goalType) then
        throwTacticEx `tr_constructor goal ("goal should be of type Param")

      let fromType : Q(Sort $levelU) ← instantiateMVars fromType
      let toType : Q(Sort $levelV) ← instantiateMVars toType
      let covMapType : Q(MapType) ← instantiateMVars covMapType
      let conMapType : Q(MapType) ← instantiateMVars conMapType

      trace[tr.utils] s!"fromType: {fromType}"
      trace[tr.utils] s!"toType: {toType}"
      trace[tr.utils] s!"covMap: {covMapType}"
      trace[tr.utils] s!"conMap: {conMapType}"


      let rec findFirstNonFvars
        (fromType toType : (Expr × List Expr))
        : MetaM ((Expr × Option Expr × List Expr) × (Expr × Option Expr × List Expr)) := do
        let (fromType, fromArgs) := fromType
        let (toType, toArgs) := toType

        let depth := fromArgs.length
        let pref := s!"({depth}) "

        match fromType, toType with
        | .app f a, .app g b =>
          match a, b with
          | .fvar _, .fvar _ =>
            trace[tr.utils] s!"{pref}Both final arguments are fvars"
            findFirstNonFvars
              (f, a :: fromArgs)
              (g, b :: toArgs)

          | _, _ =>
            match a, b with
            | .fvar _, _
            | _, .fvar _ =>
              trace[tr.utils] s!"{pref}One of the final arguments is not an fvar"
            | _, _ =>
              trace[tr.utils] s!"{pref}Final arguments are not fvar"

            return (
              (f, .some a, fromArgs),
              (g, .some b, toArgs),
            )
        | _, _ =>
          trace[tr.utils] s!"{pref}No application"
          return (
              (fromType, .none, fromArgs),
              (toType, .none, toArgs),
            )

      let result ← findFirstNonFvars (fromType, []) (toType, [])
      trace[tr.utils] s!"Got result {result}"


      -- match fromType, toType with
      -- | .app f a, .app g b =>
      --   match a, b with
      --   | .fvar _, .fvar _ =>
      --     trace[tr.utils] s!"Both final arguments are fvars"
      --   | .fvar _, _
      --   | _, .fvar _ =>
      --     trace[tr.utils] s!"One of the final arguments is not an fvar"
      --   | _, _ =>
      --     trace[tr.utils] s!"Final arguments are not fvar"
      -- | _, _ =>
      --   trace[tr.utils] s!"No application"

      -- getForallArity



#check Lean.LMVarId
