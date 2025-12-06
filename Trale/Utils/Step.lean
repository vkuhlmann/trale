import Lean
import Lean.Elab.Tactic
import Qq

open Lean Elab Tactic Qq


syntax "repeat_max " term ", " tacticSeq : tactic
macro_rules
  | `(tactic| repeat_max $count, $seq) => do

    let c <- Lean.Elab.Tactic.elabTermEnsuringType count (.some q(Nat))



    `(tactic| first | ($seq); repeat $seq | skip)
