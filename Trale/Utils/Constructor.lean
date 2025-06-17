import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Qq open Qq Lean
open Lean Elab Command Tactic Term Expr Meta

elab "tr_constructor'" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget

    let levelU <- mkFreshLevelMVar
    let levelV <- mkFreshLevelMVar
    let levelW <- mkFreshLevelMVar

    let fromType : Q(Sort $levelU) ← mkFreshExprMVar .none (userName := `fromType)
    let toType : Q(Sort $levelV) ← mkFreshExprMVar .none (userName := `toType)

    let covMapType : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `covMapType)
    let conMapType : Q(MapType) ← mkFreshExprMVar (.some q(MapType)) (userName := `conMapType)

    let matcher : Q(Type (max levelU levelV levelW)) := q(Param $fromType $toType $covMapType $conMapType)

    if !(← isExprDefEq matcher goalType) then
      throwTacticEx `tr_constructor goal
        ("goal should be of type Param")

    let fromType : Q(Sort $levelU) ← instantiateMVars fromType
    let toType : Q(Sort $levelV) ← instantiateMVars toType
    let covMapType : Q(MapType) ← instantiateMVars covMapType
    let conMapType : Q(MapType) ← instantiateMVars conMapType

    dbg_trace s!"[tr_constructor] fromType: {fromType}"
    dbg_trace s!"[tr_constructor] toType: {toType}"
    dbg_trace s!"[tr_constructor] covMap: {covMapType}"
    dbg_trace s!"[tr_constructor] conMap: {conMapType}"

    -- let holeR : Q($fromType → $toType -> Sort $levelW)
    --     ← mkFreshExprMVar q($fromType → $toType -> Sort $levelW) .syntheticOpaque (userName := `Param.R)
    -- let holeCov : Q(MapType.interp $covMapType $holeR)
    --     ← mkFreshExprMVar q(MapType.interp $covMapType $holeR) .syntheticOpaque (userName := `Param.covariant)
    -- let holeCon : Q(MapType.interp $conMapType (flipRel $holeR))
    --     ← mkFreshExprMVar q(MapType.interp $conMapType (flipRel $holeR)) .syntheticOpaque (userName := `Param.contravariant)

    -- let covGoals := []

    let ghi : TacticM (TSyntax `tactic) := `(tactic |
      constructor <;>
      try constructor <;>
      try constructor <;>
      try constructor <;>
      try constructor <;>
      try constructor)

    let subgoals ← evalTacticAt (← ghi) (← getMainGoal)

    let translationMap := [
      (`R.R, `R),
      (`covariant.map, `right),
      (`covariant.map_in_R, `right_implies_R),
      (`covariant.R_in_map, `R_implies_right),
      (`covariant.R_in_mapK, `R_implies_rightK),
      (`contravariant.map, `left),
      (`contravariant.map_in_R, `left_implies_R),
      (`contravariant.R_in_map, `R_implies_left),
      (`contravariant.R_in_mapK, `R_implies_leftK)
    ].toAssocList'

    let mut newGoals : AssocList Name MVarId := .empty

    for subgoal in subgoals do
      -- let name := subgoal.name
      let name <- subgoal.getTag
      IO.println s!"[tr_constructor] processing subgoal: {name}"
      -- let name <- MetavarContext.findUserName? subgoal

      let root := name.getRoot
      if !name.isStr then
        IO.println s!"[tr_constructor] subgoal name is not a string: {name}"
        continue

      let suffix := name.getString!

      let query := (root.str suffix)
      IO.println s!"[tr_constructor] query: {query}"

      let translated := translationMap.find? query

      IO.println s!"[tr_constructor] translated: {translated}"

      let finalTag := match translated with
        | .none => name
        | .some v => v

      -- if translated.isNone then
      --   continue

      -- subgoal.setTag translated.get!
      subgoal.setTag finalTag

      -- let translated := translated.get!

      -- let var <- mkFreshExprMVar (← subgoal.getType') .synthetic (userName := translated)
      -- subgoal.assign var

      -- newGoals := newGoals.insert translated var.mvarId!
      -- newGoals := newGoals.insert translated.get! subgoal
      newGoals := newGoals.insert finalTag subgoal

    IO.println s!"[tr_constructor] newGoals length: {newGoals.toList.length}"


    let mut newGoalsOrdered : List MVarId := []
    for (_, v) in translationMap do
      let val := newGoals.find? v
      if val.isNone then
        continue

      newGoals := newGoals.erase v
      newGoalsOrdered := newGoalsOrdered ++ [val.get!]

    replaceMainGoal (newGoalsOrdered ++ newGoals.toList.map (·.snd))

macro "tr_constructor" : tactic =>
  -- `(tactic| tr_constructor' <;> try simp)
  `(tactic| tr_constructor')


example : Param40 String Nat := by
  constructor

  case R =>
    intro s n
    exact s.length = n


  case covariant =>
    exact {
      map := by sorry
      map_in_R := by sorry
      R_in_map := by sorry
      R_in_mapK := by sorry
    }

  case contravariant =>
    exact { }


example : Param40 String Nat := by
  constructor <;>
    try constructor <;>
    try constructor <;>
    try constructor <;>
    try constructor <;>
    try constructor

  simp at *


  case R =>
    intro s n
    exact s.length = n

  /-
  case covariant.R_in_mapK
  ⊢ ∀ (a : String) (b : Nat) (r : a.length = b), ⋯ = r

  case covariant.toMap3.R_in_map
  ⊢ ∀ (a : String) (b : Nat),
    a.length = b →
      { map := ?covariant.toMap3.toMap2a.toMap1.map, map_in_R := ?covariant.toMap3.toMap2a.map_in_R }.map a = b

  case covariant.toMap3.toMap2a.map_in_R
  ⊢ ∀ (a : String) (b : Nat), { map := ?covariant.toMap3.toMap2a.toMap1.map }.map a = b → a.length = b

  case covariant.toMap3.toMap2a.toMap1.map
  ⊢ String → Nat

  -/

  repeat sorry
