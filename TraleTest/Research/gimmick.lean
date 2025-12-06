import Lean
import Trale.Utils.Trace
import Trale.Utils.Glueing
import Trale.Theories.Flip
import Qq

open Lean Meta Elab Std Qq Command Term Tactic


class Understanding (a : Type)

def QuantumPhysics : Type := Nat



-- instance
-- : Understanding QuantumPhysics := by

--   -- let c := 5

--   run_tac
--     let c ← mkFreshExprMVar q(Nat)
--     (←getMainGoal).assign c


-- open Tactic in

-- def our_knowledge_of_the_universe : Nat := by
--   run_tac
--     let c ← mkFreshExprMVar q(Nat)
--     (←getMainGoal).assign c
