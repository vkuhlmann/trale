import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent

import TraleTest.Utils.Lemmas.SummableSequence

-- Code based on 'summable.v' example by Trocq Rocq plugin developers.

-- axiom functionRelationApplication
--   (p1 : Param10 (A -> B) (A' -> B'))
--   (p2 : Param10 A A')
--   (p3 : Param10 B B')
--   :
--   ∀ f f' (_ : p1.R f f'),
--   ∀ a a' (_ : p2.R a a'), p3.R (f a) (f' a')

def forallApplication
  {α α' : Sort _}
  {β : α -> Sort _}
  {β' : α' -> Sort _}
  (p1 : Param10 α α')
  (a : α)
  (a' : α')
  (aR : p1.R a a')
  (p2 : ∀ a a' (_ : p1.R a a'), Param10 (β a) (β' a'))
  :
  Param10 (β a) (β' a') :=
    by
    tr_constructor

    case R =>
      exact (p2 a a' aR).R

    case right =>
      exact (p2 a a' aR).right


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
  let F1 := (fun x => (Σ (a + b)) = x)
  let A1 := (Σ a + Σ b)

  let F2 := (fun x => (Σ (a' + b')) = x)
  let A2 := (Σ a' + Σ b')

  -- show Param10 ((_ = .) _) ((_ = .) _)
  show Param10 (F1 A1) (F2 A2)

  apply forallApplication

  case p1 =>
    show Param10 xnnR nnR
    infer_instance

  case aR =>
    show tr.map A2 = A1; dsimp
    show .fin (Σ a' + Σ b') = Σ a + Σ b

    -- If you change this to a 'let', the `subst` won't work because it will see
    -- it as a hypothesis instead of an equality.
    have aF : seq_extend a' = a := tr.R_implies_map a' a R
    have bF : seq_extend b' = b := tr.R_implies_map b' b bR

    subst aF bF

    repeat rw [summationHomeo]
    rw [add_xnnR_homeo]

  subst F1 F2 A1 A2

  simp
  intro c c' cR

  show Param10 ((_ = .) c) ((_ = .) c')

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

  show Param10 (G1 B1) (G2 B2)
  apply forallApplication

  case p1 =>
    show Param10 xnnR nnR
    infer_instance

  case aR =>
    show .fin B2 = B1

    -- If you change this to a 'let', the `subst` won't work because it will see
    -- it as a hypothesis instead of an equality.
    have aF : seq_extend a' = a := tr.R_implies_map a' a R
    have bF : seq_extend b' = b := tr.R_implies_map b' b bR

    subst aF bF
    unfold B1 B2

    have h1 : seq_extend a'.seq + seq_extend b'.seq = seq_extend (a' + b').seq := by
      congr

    rw [h1]
    rw [summationHomeo]

  simp
  intro d d' dR

  show Param10 (G1 d) (G2 d')

  have dF := tr.R_implies_map d' d dR
  dsimp at dF

  have dF2 := tr.R_implies_map d' d dR
  dsimp at dF2

  show Param10 (d = c) (d' = c')


  -- Part 4: Relate eq:  X  *=*  X
  --                        ___
  --
  let H1 := fun (f : _ -> _ -> Sort _) => (f d c)
  let C1 := @Eq xnnR

  let H2 := fun (f : _ -> _ -> Sort _) => (f d' c')
  let C2 := @Eq nnR

  -- This and variations do not work
  -- show Param10 ((. _ _) _ _) ((. _ _) _ _)
  -- show Param10 ((fun (f : _ -> _ -> Sort _) => f _ _) _) ((fun (f : _ -> _ -> Sort _) => f _ _) _)

  let eqParam : Param40 (xnnR → xnnR → Prop) (nnR → nnR → Prop) := by
    apply Param_from_map
    intro f x y
    exact f (.fin x) (.fin y)

  show Param10 (H1 C1) (H2 C2)
  apply forallApplication

  case p1 =>
    show Param10 (xnnR → xnnR → Prop) (nnR → nnR → Prop)
    infer_instance

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

  let eF := tr.R_implies_map e e' eR
  dsimp at eF


  -- Part 5: Use relations to make the relation trivial
  --
  show Param10 (e d c) (e' d' c')
  apply (Param_id' _).forget
  show e d c = e' d' c'

  rw [← eF]
  show e d c = e (xnnR.fin d') (xnnR.fin c')

  subst dF cF
  congr
