import Lean

namespace Trale.Research.Backtrace

axiom P : Prop
axiom Q : Prop
axiom R : Prop

axiom P_to_Q : P -> Q
axiom R_to_Q : R -> Q
axiom P_true : P

macro "test_tac" : tactic => `(tactic|
  ((first
  | (run_tac
      trace[debug] "Point A")
    ; skip
  | (run_tac
      trace[debug] "Point B")
    ; apply P_to_Q
  ); exact P_true)
  )


macro "test_tac2" : tactic => `(tactic|
  (first
  | (run_tac
      trace[debug] "Point A")
    ; skip
    ; exact P_true
  | (run_tac
      trace[debug] "Point B")
    ; apply P_to_Q
    ; exact P_true
  ))

-- macro "test_tac3" : tactic => `(tactic|
--   (let cont := `(tactic|exact P_true)
--   (first
--   | (run_tac
--       trace[debug] "Point A")
--     ; skip
--     ; exact P_true
--   | (run_tac
--       trace[debug] "Point B")
--     ; apply P_to_Q
--     ; exact P_true
--   )))

macro "test_tac3" : tactic => do
  -- let cont : Lean.Elab.Tactic.TacticM (Lean.TSyntax `tactic)
  let cont ← `(tactic|exact P_true)
  `(tactic|
    (
    (first
    | (run_tac
        trace[debug] "Point A")
      ; skip
      ; $cont
    | (run_tac
        trace[debug] "Point B")
      ; apply P_to_Q
      -- ; run_tac `(tactic|exact P_true)
      ; $cont
  )))

-- macro "test_tac4" : tactic => do
--   let cont : Lean.MacroM (Lean.TSyntax `tactic) := `(tactic|exact P_true);
--   -- let cont2 : Lean.MacroM tactic := `(tactic|exact P_true);
--   -- let cont := `(tactic|exact P_true);
--   `(tactic|
--     (
--     (first
--     | (run_tac
--         trace[debug] "Point A")
--       ; skip
--       -- ; $cont
--     | (run_tac
--         trace[debug] "Point B")
--       ; apply P_to_Q
--       ; run_tac $cont
--       -- ; $cont
--   )))

macro "test_tac5" : tactic => do
  `(tactic|
    (
      try apply R_to_Q;
      try apply P_to_Q;
      exact P_true
    )
  )


set_option trace.debug true
example : Q := by
  -- apply P_to_Q
  -- exact P_true

  -- This fails:
  -- test_tac

  -- This succeeds:
  -- test_tac2
  -- output: Point A, Point B

  -- This succeeds too:
  test_tac3

  -- This fails:
  -- test_tac5


set_option trace.debug true
example : 2 * 2 + 1 = 5 + 2 * 0 := by
  exact Nat.add_zero _
  -- test_tac
  -- run_tac
  -- apply Eq.symm
  -- exact Nat.add_zero _

example : (4, 5) = (3 + 1, 5) := by
  rfl
