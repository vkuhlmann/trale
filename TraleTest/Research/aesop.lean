import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

import TraleTest.Lemmas.SummableSequence

set_option trace.tr.utils true

namespace TraleTest.Research.Aesop
open TraleTest.Lemmas Trale



@[aesop safe]
theorem R_add_xnnR_bis
  (a : nnR) (a' : xnnR) (aR : tr.R a a')
  (b : nnR) (b' : xnnR) (bR : tr.R b b')
  : Param.R .Map0 .Map0 (a + b) (a' + b') := by

  tr_whnf
  show extend (a + b) = a' + b'

  tr_subst a a' aR
  tr_subst b b' bR

  exact add_xnnR_homeo a b


macro "tr_advance" : tactic => `(tactic|
  first
  | assumption
  | tr_intro _ _ _
  | (tr_split_application; try (
        (case' p2 => intro _ _ _);rotate_left 1))

  | aesop (rule_sets := [default, builtin, trale])
--   | apply R_add_xnnR
  | refine R_sum_xnnR _ _ ?_
  | exact R_eq
  | apply seq_nnR_add
  | fail "No step available"
  )

#check Aesop.runRuleTac

example
  (a : nnR) (a' : xnnR)
  (b : nnR) (b' : xnnR)
  (_ : tr.R a a')
  (_ : tr.R b b')
  : Param.R .Map0 .Map0 (a + b) (a' + b') := by

  -- choose a using xxx

  -- aesop (rule_sets := [trale])
  aesop

  apply R_add_xnnR_bis
  assumption
  assumption

example (a b c : nnR)
    : (a + b) + c = c + (b + a) := by

  -- rw [nnR_comm]
  --  aesop
    sorry
