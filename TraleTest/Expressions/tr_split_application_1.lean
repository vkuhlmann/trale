import Lean
import Trale.Core.Param
open Lean Elab Tactic Expr Meta Trale

def mkNumUniqLM : Nat -> LMVarId := sorry
def mkNumUniqF : Nat -> FVarId := sorry

-- This could be the goal type that tr_split_application gets.
def example1 : Expr :=
  -- Param10 (Σ (a + b) = c) (Σ (a' + b') = c')
  .app
    (.app
      (.const ``Param10 [Level.mvar (mkNumUniqLM 3072), Level.zero, Level.zero])
      --
      -- α = (Σ (a + b) = c)
      (.app
        (.app
          (.app (.const `Eq [Level.succ (Level.zero)]) (.const `xnnR []))
          --
          -- Σ (a + b)
          (.app
            (.app
              (.app
                (.app
                  (.const `SequenceSummation.sum [Level.zero, Level.zero])
                  (.const `seq_xnnR []))
                (.const `xnnR []))
              (.const `instSequenceSummationSeq_xnnRXnnR []))
            (.app
              (.app
                (.app
                  (.app
                    (.app
                      (.app
                        (.const `HAdd.hAdd [Level.zero, Level.zero, Level.zero])
                        (.const `seq_xnnR []))
                      (.const `seq_xnnR []))
                    (.const `seq_xnnR []))
                  (.app
                    (.app (.const `instHAdd [Level.zero]) (.const `seq_xnnR []))
                    (.const `instAddSeq_xnnR [])))
                -- a
                (.fvar (mkNumUniqF 1344)))
              -- b
              (.fvar (mkNumUniqF 2306)))))
        --
        -- c
        (.fvar (mkNumUniqF 4944))))
    --
    -- β = (Σ (a' + b') = c')
    (.app
      (.app
        (.app (.const `Eq [Level.succ (Level.zero)]) (.const `nnR []))
        --
        -- Σ (a' + b')
        (.app
          (.app
            (.app
              (.app
                (.const `SequenceSummation.sum [Level.zero, Level.zero])
                (.const `summable []))
              (.const `nnR []))
            (.const `instSummationSummable []))
          (.app
            (.app
              (.app
                (.app
                  (.app
                    (.app
                      (.const `HAdd.hAdd [Level.zero, Level.zero, Level.zero])
                      (.const `summable []))
                    (.const `summable []))
                  (.const `summable []))
                (.app
                  (.app (.const `instHAdd [Level.zero]) (.const `summable []))
                  (.const `instAddSummable [])))
              -- a'
              (.fvar (mkNumUniqF 1347)))
            -- b'
            (.fvar (mkNumUniqF 2309)))))
      --
      -- c'
      (.fvar (mkNumUniqF 4947)))
