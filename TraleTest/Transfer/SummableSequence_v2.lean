import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application

import TraleTest.Utils.Lemmas.SummableSequence

set_option trace.tr.utils false

-- Code based on 'summable.v' example by Trocq Rocq plugin developers.

theorem sum_nnR_add : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_by sum_xnnR_add

  -- We use these Params
  let _ := paramNNR
  let _ := param_summable_seq

  -- Part 1: split the foralls
  show
    Param10
    (∀ (f g : seq_xnnR), Σ (f + g) = Σ f + Σ g)
    (∀ (u v : summable), Σ (u + v) = Σ u + Σ v)


  tr_split'
  case p1 =>
    infer_instance

  intro a a' R

  tr_split'
  case p1 =>
    infer_instance

  intro b b' bR

  show Param10 (Σ (a + b) = Σ a + Σ b) (Σ (a' + b') = Σ a' + Σ b')

  show Param10 (Eq (Σ (a + b)) (Σ a + Σ b)) (Eq (Σ (a' + b')) (Σ a' + Σ b'))

  show Param10 ((fun (x : ) => (Eq (Σ (a + b))) x) (Σ a + Σ b)) ((fun (x : _) => Eq (Σ (a' + b')) x) (Σ a' + Σ b'))

  -- Part 2: Relate rhs:  X  =  *X*
  --                            ___
  --
  -- let F1 := (fun x => (Σ (a + b)) = x)
  -- let A1 := (Σ a + Σ b)

  -- let F2 := (fun x => (Σ (a' + b')) = x)
  -- let A2 := (Σ a' + Σ b')

  -- show Param10 ((_ = .) _) ((_ = .) _)
  -- show Param10 (F1 A1) (F2 A2)

  tr_split_application'

  -- apply forallApplication

  case p1 =>
    show Param00 xnnR nnR
    infer_instance

  case aR =>
    -- show tr.map A2 = A1; dsimp
    show .fin (Σ a' + Σ b') = Σ a + Σ b

    -- If you change this to a 'let', the `subst` won't work because it will see
    -- it as a hypothesis instead of an equality.
    have aF : seq_extend a' = a := tr.R_implies_map a' a R
    have bF : seq_extend b' = b := tr.R_implies_map b' b bR

    subst aF bF

    repeat rw [summationHomeo]
    rw [add_xnnR_homeo]

  -- subst F1 F2 A1 A2

  simp
  intro c c' cR

  -- tr_split_application
  /-
  (0) Both final arguments are fvars
  (1) Final arguments are not fvar
  Got result (
    (
      Eq.{1} xnnR,
      (
        (
          some (SequenceSummation.sum.{0, 0} seq_xnnR xnnR
          instSequenceSummationSeq_xnnRXnnR (HAdd.hAdd.{0, 0, 0} seq_xnnR seq_xnnR
          seq_xnnR (instHAdd.{0} seq_xnnR instAddSeq_xnnR) _uniq.1344 _uniq.2306))
        ),
        [_uniq.4944]
      )
    ),
    (
      Eq.{1} nnR,
      (
        (
          some (SequenceSummation.sum.{0, 0} summable nnR instSummationSummable
          (HAdd.hAdd.{0, 0, 0} summable summable summable (instHAdd.{0} summable
          instAddSummable) _uniq.1347 _uniq.2309))
        ),
        [_uniq.4947]
      )
    )
  )
  -/

  -- show Param10 ((_ = .) c) ((_ = .) c')

  have cF := tr.R_implies_map c' c cR
  dsimp at cF

  have cF2 := tr.R_implies_map c' c cR
  dsimp at cF2

  -- Part 3: Relate lhs:  *X*  =  X
  --                      ___
  --
  let G1 := (@Eq xnnR . c)
  let B1 := Σ (a + b)

  let G2 := (@Eq nnR . c')
  let B2 := Σ (a' + b')
  -- show Param10 (G1 B1) (G2 B2)
  tr_split_application'

  run_tac do
    trace[tr.utils] "Hello"


  -- apply forallApplication
  -- refine' forallApplication ?_ ?_ ?_ ?_ ?_

  case p1 =>
    show Param00 xnnR nnR
    infer_instance

  case aR =>

    show .fin (Σ (a' + b')) = Σ (a + b)
    -- show .fin B2 = B1

    -- If you change this to a 'let', the `subst` won't work because it will see
    -- it as a hypothesis instead of an equality.
    have aF : seq_extend a' = a := tr.R_implies_map a' a R
    have bF : seq_extend b' = b := tr.R_implies_map b' b bR

    subst aF bF
    -- unfold B1 B2

    have h1 : seq_extend a'.seq + seq_extend b'.seq = seq_extend (a' + b').seq := by
      congr

    rw [h1]
    rw [summationHomeo]

  simp
  intro d d' dR

  show Param10 (G1 d) (G2 d')

  show Param10 (d = c) (d' = c')


  -- Part 4: Relate eq:  X  *=*  X
  --                        ___
  --
  let H1 := fun (f : _ -> _ -> Sort _) => (f d c)
  let C1 := @Eq xnnR

  let H2 := fun (f : _ -> _ -> Sort _) => (f d' c')
  let C2 := @Eq nnR

  -- tr_split_application

  -- This and variations do not work
  -- show Param10 ((. _ _) _ _) ((. _ _) _ _)
  -- show Param10 ((fun (f : _ -> _ -> Sort _) => f _ _) _) ((fun (f : _ -> _ -> Sort _) => f _ _) _)

  let eqParam : Param00 (xnnR → xnnR → Prop) (nnR → nnR → Prop) := by
    tr_split'
    case p1 => infer_instance

    tr_split'
    case p1 => infer_instance

    -- TODO: Make this work with infer_instance
    exact propParam.forget


    /-
    Previous approach:

    ```
    -- Use Prop related to Prop by identity.
    infer_instance
    ```

    Approach before that:
    ```
    apply Param_from_map
    intro f x y
    exact f (.fin x) (.fin y)
    ```
    -/

  -- Why can't we simplify the value of a hypothesis? (Only the type)
  -- simp [inferInstance, eqParam, Param_arrow.Map4_arrow] at eqParam

  show Param10 (H1 C1) (H2 C2)
  apply forallApplication

  /-
  Currently, we can't use `tr_split_application` here yet, because the
  implicit argument gets converted, and also we haven't implemented
  transferring the function head itself:

  ```plaintext
  Would relate:    (@Eq.{1} xnnR d c) (@Eq.{1} nnR d' c')
                            ----               ---
  ```
  -/


  case p1 =>
    show Param00 (xnnR → xnnR → Prop) (nnR → nnR → Prop)
    infer_instance

  case aR =>
    tr_whnf; intro x x' xR
    tr_whnf; intro y y' yR
    tr_whnf

    show x = y → x' = y'

    have xF := tr.R_implies_map x x' xR
    have yF := tr.R_implies_map y y' yR

    dsimp at xF yF
    subst xF yF

    show x = y → tr.map x = tr.map y
    exact congrArg _

    -- Previous approach:
    -- -- Since we related Props by id, we have to prove the two Props are equal.
    -- -- Ideally we would only want to proof the implication. This would be
    -- -- addressed by implementing translation of the types in the propositions
    -- -- using registed Param instances.
    -- show C1 x y = C2 x' y'

    -- unfold C1 C2
    -- show (x = y) = (x' = y')

    -- apply propext

    -- constructor
    -- · show (x = y → x' = y')
    --   have xF := tr.R_implies_map x x' xR
    --   have yF := tr.R_implies_map y y' yR

    --   dsimp at xF yF
    --   subst xF yF

    --   intro h
    --   congr

    -- · show (x' = y' → x = y)
    --   have xF := tr.R_implies_map x' x xR
    --   have yF := tr.R_implies_map y' y yR

    --   dsimp at xF yF
    --   subst xF yF

    --   intro h
    --   congr

  simp
  intro e e' eR

  show Param10 (H1 e) (H2 e')

  -- let eF := tr.R_implies_map e e' eR
  -- dsimp at eF


  -- Part 5: Use relations to make the relation trivial
  --
  show Param10 (e d c) (e' d' c')
  dsimp [inferInstance, eqParam, Param_arrow.Map0_arrow, propParam] at eR

  tr_from_map
  show e d c → e' d' c'

  exact eR d d' dR c c' cR

  -- Previous approach
  -- tr_ident
  -- show e d c = e' d' c'
  -- ...
