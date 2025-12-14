import Trale.Theories.Forall
import Trale.Theories.Arrow
import Trale.Theories.Option
import Trale.Theories.Sigma
import Trale.Theories.Exists
import Trale.Utils.ParamFromFunction
import Trale.Utils.Whnf
import Lean

open Trale.Utils

macro "tr_simp_R" "at" a:Lean.Parser.Tactic.locationHyp : tactic => `(tactic|
  simp [Trale.Map2a_arrow, paramFromMap, Param.forget, CoeDep.coe,
  CoeTC.coe, Coe.coe, paramFromSurjection, inferInstance
  ] at $a
)


macro "tr_simp_R" : tactic => `(tactic|
  tr_simp_R at ⊢
)
