-- import Trale.Theories.Forall
-- import Trale.Theories.Arrow
-- import Trale.Theories.Option
-- import Trale.Theories.Sigma
-- import Trale.Theories.Exists

macro "tr_simp_R" "at" a:Lean.Parser.Tactic.locationHyp : tactic => `(tactic|
  simp [Param_arrow.Map2a_arrow, Param_from_map, Param.forget, CoeDep.coe,
  CoeTC.coe, Coe.coe, SplitSurj.toParam
  ] at $a
)


macro "tr_simp_R" : tactic => `(tactic|
  tr_simp_R at ⊢
)
