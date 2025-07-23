import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent

import TraleTest.Utils.Lemmas.SummableSequence

-- Code based on 'summable.v' example by Trocq Rocq plugin developers.

axiom functionRelationApplication
  (p1 : Param10 (A -> B) (A' -> B'))
  (p2 : Param10 A A')
  (p3 : Param10 B B')
  :
  ∀ f f' (_ : p1.R f f'),
  ∀ a a' (_ : p2.R a a'), p3.R (f a) (f' a')

def abstractLambda
  {α α' : Type _}
  {β : α -> Type _}
  {β' : α' -> Type _}
  (p1 : Param10 α α')
  (p2 : ∀ a a' (_ : p1.R a a'), Param10 (β a) (β' a'))
  :
  Param10 (∀ (a : α), β a) (∀ (a' : α'), β' a') :=
    by sorry

def forallApplication
  {α α' : Sort _}
  {β : α -> Sort _}
  {β' : α' -> Sort _}
  (p1 : Param10 α α')
  (a : α)
  (a' : α')
  -- (p1 : ∀ a, β a)
  (aR : p1.R a a')
  (p2 : ∀ a a' (_ : p1.R a a'), Param10 (β a) (β' a'))
  :
  Param10 (β a) (β' a') :=
    by
    tr_constructor

    case R =>
      -- intro x x'
      -- exact ∀ (aR : p1.R a a'), (p2 a a' aR).R x x'
      -- exact (p2 a a' aR).R x x'
      exact (p2 a a' aR).R

    case right =>
      exact (p2 a a' aR).right


def forallApplication'
  {α α' : Sort _}
  {β : α -> Sort _}
  {β' : α' -> Sort _}
  (a : α)
  (a' : α')
  -- (p1 : ∀ a, β a)
  (p1 : Param10 α α')
  (p2 : ∀ a a' (_ : p1.R a a'), Param10 (β a) (β' a'))
  :
  (β a) -> (β' a') :=
    by sorry

def mapApplication
  {α α' : Type _}
  {β : α -> Type _}
  {β' : α' -> Type _}
  (a : α)
  (a' : α')
  -- (p1 : ∀ a, β a)
  (p1 : Param10 α α')
  (p2 : ∀ a a' (_ : p1.R a a'), Param10 (β a) (β' a'))
  :
  (β a) -> (β' a') :=
    by sorry

-- axiom functionRelationConsistency
--   (p1 : Param10 (A -> B) (A' -> B'))
--   (p2 : Param10 A A')
--   :

-- def arg_param (f : α -> β) (g : α' -> β') (p1 : Param10 α α')
--     (p2 : Param10 β β')
--   : ∀ Param10 ()
--   : ∀ a a' (aR : p1.R a a'), p2.R (f a) (g a') := by

--   intro a a' aR
--   sorry
  -- exact p2.map aR

-- def two_arg_param (f : α -> β -> γ) (g : α' -> β' -> γ') (Param10 α α')
--   (Param10 b b')

#check Lean.Meta.Simp.Config

theorem sum_nnR_add : ∀ (u v : summable), (Σ (u + v) = Σ u + Σ v) := by
  tr_by sum_xnnR_add

  show
    Param10
    (∀ (f g : seq_xnnR), Σ (f + g) = Σ f + Σ g)
    (∀ (u v : summable), Σ (u + v) = Σ u + Σ v)

  let p1 : Param04 seq_xnnR summable := param_summable_seq.flip

  tr_split
  case p1 =>
    exact p1.forget

  intro a a' R

  tr_split
  case p1 =>
    exact p1.forget

  intro b b' bR

  show Param10 (Σ (a + b) = Σ a + Σ b) (Σ (a' + b') = Σ a' + Σ b')

  show Param10 (Eq (Σ (a + b)) (Σ a + Σ b)) (Eq (Σ (a' + b')) (Σ a' + Σ b'))

  show Param10 ((fun (x : ) => (Eq (Σ (a + b))) x) (Σ a + Σ b)) ((fun (x : _) => Eq (Σ (a' + b')) x) (Σ a' + Σ b'))


  let F1 := (fun x => (Σ (a + b)) = x)
  let A1 := (Σ a + Σ b)

  let F2 := (fun x => (Σ (a' + b')) = x)
  let A2 := (Σ a' + Σ b')

  show Param10 (F1 A1) (F2 A2)

  apply forallApplication

  case p1 =>
    show Param10 xnnR nnR
    exact paramNNR.flip.forget

  case aR =>
    -- show ?p2.p2.p1.R A1 A2
    -- show @Param.R _ _ _ _ ?p2.p2.p1.R A1 A2
    -- simp [paramNNR]
    -- simp [SplitInj.toParam]

    show .fin A2 = A1

    -- simp [extend]

    -- If you change this to a 'let', the `subst` won't work because it will see
    -- it as a hypothesis instead of an equality.
    have aF : seq_extend a' = a := p1.forget.R_implies_left a a' R
    have bF : seq_extend b' = b := p1.forget.R_implies_left b b' bR

    -- dsimp at aF
    -- simp [p1, param_summable_seq, Param_from_map, param_NNR_seq, param_summable_NNR_seq] at aF bF

    subst aF bF
    unfold A1 A2

    repeat rw [summationHomeo]
    rw [add_xnnR_homeo]

  -- case p2 =>
  simp
  intro c c' cR

  show Param10 (F1 c) (F2 c')

  have cF := paramNNR.R_implies_right c' c cR
  dsimp at cF

  have cF2 := paramNNR.R_implies_left c' c cR
  dsimp at cF2

  let G1 := (@Eq xnnR . c)
  let B1 := Σ (a + b)

  let G2 := (@Eq nnR . c')
  let B2 := Σ (a' + b')

  show Param10 (G1 B1) (G2 B2)

  -- subst cF

  apply forallApplication

  case p1 =>
    show Param10 xnnR nnR
    exact paramNNR.flip.forget

  case aR =>
    show .fin B2 = B1

    -- If you change this to a 'let', the `subst` won't work because it will see
    -- it as a hypothesis instead of an equality.
    have aF : seq_extend a' = a := p1.forget.R_implies_left a a' R
    have bF : seq_extend b' = b := p1.forget.R_implies_left b b' bR

    subst aF bF
    unfold B1 B2

    have h1 : seq_extend a'.seq + seq_extend b'.seq = seq_extend (a' + b').seq := by
      congr

    rw [h1]
    rw [summationHomeo]

  simp
  intro d d' dR

  show Param10 (G1 d) (G2 d')

  have dF := paramNNR.R_implies_right d' d dR
  dsimp at dF

  have dF2 := paramNNR.R_implies_left d' d dR
  dsimp at dF2

  show Param10 (d = c) (d' = c')

  let H1 := fun (f : _ -> _ -> Sort _) => (f d c)
  let C1 := @Eq xnnR

  let H2 := fun (f : _ -> _ -> Sort _) => (f d' c')
  let C2 := @Eq nnR

  show Param10 (H1 C1) (H2 C2)


  let eqParam : Param40 (xnnR → xnnR → Prop) (nnR → nnR → Prop) := by
    apply Param_from_map
    intro f x y
    exact f (.fin x) (.fin y)

  apply forallApplication

  case p1 =>
    show Param10 (xnnR → xnnR → Prop) (nnR → nnR → Prop)
    -- apply (Param_from_map _).forget

    -- intro f x y
    -- exact f (.fin x) (.fin y)
    exact eqParam.forget

  case aR =>
    dsimp [Param_from_map]
    funext x y

    show C1 (xnnR.fin x) (xnnR.fin y) = C2 x y

    unfold C1 C2
    show (xnnR.fin x = xnnR.fin y) = (x = y)
    simp

  simp
  intro e e' eR

  show Param10 (H1 e) (H2 e')

  let eF := eqParam.R_implies_right e e' eR
  dsimp at eF

  show Param10 (e d c) (e' d' c')

  apply (Param_id' _).forget

  show e d c = e' d' c'

  rw [← eF]
  dsimp [eqParam, Param_from_map]

  show e d c = e (xnnR.fin d') (xnnR.fin c')

  subst dF cF

  congr


  -- apply (Param_from_map _).forget

  -- -- have F1 := (fun (x : _) => Eq (Σ (a + b)) x)
  -- -- have A1 := (Σ a + Σ b)

  -- -- have F2 := (fun (x : _) => Eq (Σ (a' + b')) x)
  -- -- have A2 := (Σ a' + Σ b')


  -- show ((fun x => (Σ (a + b)) = x) (Σ a + Σ b))
  --   -> ((fun x => (Σ (a' + b')) = x) (Σ a' + Σ b'))

  -- show (F1 A1) -> (F2 A2)

  -- apply forallApplication'

  -- sorry





  -- dsimp





  -- -- have FA1 := ((fun (x : _) => @Eq xnnR (Σ (a + b)) x) (Σ a + Σ b))
  -- have FA1 : Prop := ((@Eq xnnR (Σ (a + b)) (Σ a + Σ b)))
  -- show Param10 FA1 ((fun (x : _) => Eq (Σ (a' + b')) x) (Σ a' + Σ b'))


  -- show Param10 (F1 A1) (F2 A2)

  -- apply forallApplication



  -- refine (arg_param Eq Eq ?_ ?_) ?_ ?_ ?_












  -- tr_sorry sorry


-- #check Sum
-- #check ∑(fun x => 1)
-- #check Σ abc
