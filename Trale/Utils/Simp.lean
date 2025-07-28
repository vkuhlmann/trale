import Trale.Theories.Forall
import Trale.Theories.Arrow
import Trale.Theories.Option
import Trale.Theories.Sigma
import Trale.Theories.Exists
import Trale.Utils.ParamFromFunction
import Lean


macro "tr_simp_R" "at" a:Lean.Parser.Tactic.locationHyp : tactic => `(tactic|
  simp [Param_arrow.Map2a_arrow, Param_from_map, Param.forget, CoeDep.coe,
  CoeTC.coe, Coe.coe, SplitSurj.toParam, inferInstance
  ] at $a
)


macro "tr_simp_R" : tactic => `(tactic|
  tr_simp_R at ⊢
)

open Lean Expr Elab Tactic MVarId in
elab "tr_whnf" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalType ← Lean.Elab.Tactic.getMainTarget
    -- trace[tr.utils] s!"Goal is {goalType}"

    let goal2 ← Lean.Meta.whnf goalType
    -- trace[tr.utils] s!"Goal2 is {goal2}"

    let newGoal ← goal.replaceTargetDefEq goal2
    replaceMainGoal [newGoal]
