import Lean
open Lean Elab Tactic Expr Meta

def mkNumUniqLM : Nat -> LMVarId := sorry
def mkNumUniqM : Nat -> MVarId := sorry
def mkNumUniqF : Nat -> FVarId := sorry

-- sed -Ei 's/Lean\.Level\.mvar \(Lean\.Name\.mkNum `_uniq ([0-9]+)\)/.mvar (mkNumUniqLM \1)/g' xx.lean
-- sed -Ei 's/Lean\.Expr\.mvar \(Lean\.Name\.mkNum `_uniq ([0-9]+)\)/.mvar (mkNumUniqM \1)/g' xx.lean
-- sed -Ei 's/Lean\.Expr\.fvar \(Lean\.Name\.mkNum `_uniq ([0-9]+)\)/.fvar (mkNumUniqF \1)/g' xx.lean
-- sed -Ei 's/Lean\.Name\.mkNum `_uniq ([0-9]+)/.fvar (mkNumUniqF \1)/g' xx.lean

def G1 : Expr :=
  -- (@Eq xnnR . c)
  .lam
    (Lean.Name.mkNum `x._.TraleTest.Transfer.SummableSequence._hyg 807)
    (.const `xnnR [])
    (.app
      (.app
        (.app (.const `Eq [.mvar (mkNumUniqLM 5298)]) (.const `xnnR []))
        (.bvar 0))
      -- c
      (.fvar (mkNumUniqF 4944)))
    (Lean.BinderInfo.default)

def B1 : Expr :=
  -- Σ (a + b)
  .app
    (.app
      (.app
        (.app
          (.const
            `SequenceSummation.sum
            [.mvar (mkNumUniqLM 5308), .mvar (mkNumUniqLM 5307)])
          (.mvar (mkNumUniqM 5309)))
        (.mvar (mkNumUniqM 5311)))
      (.mvar (mkNumUniqM 5312)))
    (.app
      (.app
        (.app
          (.app
            (.app
              (.app
                (.const
                  `HAdd.hAdd
                  [.mvar (mkNumUniqLM 5315),
                    .mvar (mkNumUniqLM 5314),
                    .mvar (mkNumUniqLM 5313)])
                (.mvar (mkNumUniqM 5321)))
              (.mvar (mkNumUniqM 5322)))
            (.mvar (mkNumUniqM 5323)))
          (.mvar (mkNumUniqM 5324)))
        -- a
        (.fvar (mkNumUniqF 1344)))
      -- b
      (.fvar (mkNumUniqF 2306)))

def G2 : Expr :=
  -- (@Eq nnR . c')
  .lam
    (Lean.Name.mkNum `x._.TraleTest.Transfer.SummableSequence._hyg 855)
    (.const `nnR [])
    (.app
      (.app
        (.app (.const `Eq [.mvar (mkNumUniqLM 5353)]) (.const `nnR []))
        (.bvar 0))
      -- c'
      (.fvar (mkNumUniqF 4947)))
    (Lean.BinderInfo.default)

def B2 : Expr :=
  -- Σ (a' + b')
  .app
    (.app
      (.app
        (.app
          (.const
            `SequenceSummation.sum
            [.mvar (mkNumUniqLM 5363), .mvar (mkNumUniqLM 5362)])
          (.mvar (mkNumUniqM 5364)))
        (.mvar (mkNumUniqM 5366)))
      (.mvar (mkNumUniqM 5367)))
    (.app
      (.app
        (.app
          (.app
            (.app
              (.app
                (.const
                  `HAdd.hAdd
                  [.mvar (mkNumUniqLM 5370),
                    .mvar (mkNumUniqLM 5369),
                    .mvar (mkNumUniqLM 5368)])
                (.mvar (mkNumUniqM 5374)))
              (.mvar (mkNumUniqM 5375)))
            (.mvar (mkNumUniqM 5376)))
          (.mvar (mkNumUniqM 5377)))
        -- a'
        (.fvar (mkNumUniqF 1347)))
      -- b'
      (.fvar (mkNumUniqF 2309)))

-- What we expect example1 (tr_split_application_1.lean) to become
def example2_raw : Expr :=
  .app
    (.app
      (.const `Param10 [.mvar (mkNumUniqLM 5405), Lean.Level.zero, Lean.Level.zero])
      (.app (.fvar (mkNumUniqF 5301)) (.fvar (mkNumUniqF 5344))))
    (.app (.fvar (mkNumUniqF 5356)) (.fvar (mkNumUniqF 5397)))

def example2 : Expr :=
  .app
    (.app
      (.const `Param10 [.mvar (mkNumUniqLM 5405), Lean.Level.zero, Lean.Level.zero])
      (.app G1 B1))
    (.app G2 B2)
