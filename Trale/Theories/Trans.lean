import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Whnf
import Qq open Qq Lean

#check default
example : ∀ a : α, @default _ (Inhabited.mk a) = a := by
  sorry


/-
In Trocq plugin:

```
Definition R_trans {A B C : Type} (R1 : A -> B -> Type) (R2 : B -> C -> Type) : A -> C -> Type :=
  fun a c => {b : B & R1 a b * R2 b c}.
```
-/

def Map0_trans
  (p1 : Param00 α β)
  (p2 : Param00 β γ)
  : Param00 α γ := by
  tr_constructor

  intro a c
  exact Σ' b, p1.R a b ×' p2.R b c

def Map1_trans
  (p1 : Param10 α β)
  (p2 : Param10 β γ)
  : Param10 α γ := by
  tr_extend Map0_trans p1 p2.forget

  exact p2.right ∘ p1.right

def Map2a_trans
  (p1 : Param2a0 α β)
  (p2 : Param2a0 β γ)
  : Param2a0 α γ := by
  tr_extend Map1_trans p1 p2.forget

  dsimp
  intro a c acF

  let b := p1.forget.right a
  let abR := p1.right_implies_R a b (by rfl)
  let bcR := p2.right_implies_R b c (by congr)

  /-
  Type mismatch
    (b, abR, bcR)
  has type
    β × Param.R MapType.Map2a MapType.Map0 a b × Param.R MapType.Map2a MapType.Map0 b c
  but is expected to have type
    (b : β) ×' p1.1 a b ×' Param.R MapType.Map2a MapType.Map0 b c

  -- exact (b, abR, bcR)
  -/

  exact ⟨b, abR, bcR⟩

def Map2b_trans
  (p1 : Param2b0 α β)
  (p2 : Param2b0 β γ)
  : Param2b0 α γ := by
  tr_extend Map1_trans p1 p2.forget

  dsimp
  intro a c acR
  have ⟨b, abR, bcR⟩ := acR

  show tr.map (tr.map a) = c

  have abF := tr.R_implies_map _ _ abR
  have bcF := tr.R_implies_map _ _ bcR

  subst bcF
  subst abF
  rfl

def Map3_trans
  (p1 : Param30 α β)
  (p2 : Param30 β γ)
  : Param30 α γ := by
  tr_extend_multiple [Map2a_trans p1 p2.forget, Map2b_trans p1 p2.forget]

theorem Map2b_prop1
  (p1 : Param2b0 α α')
  (aR : p1.R a a')
  : p1.forget.right a = a' := by

  exact p1.R_implies_right _ _ aR

theorem Map2b_prop2
  (p1 : Param2b0 α β)
  (ab1R : p1.R a b1)
  (ab2R : p1.R a b2)
  : b1 = b2 := by

  have ab1F := tr.R_implies_map _ _ ab1R
  have ab2F := tr.R_implies_map _ _ ab2R

  subst ab1F ab2F
  rfl



def Map4_trans
  (p1 : Param40 α β)
  (p2 : Param40 β γ)
  : Param40 α γ := by
  tr_extend Map3_trans p1 p2.forget

  dsimp
  intro a c acR

  -- This errors:
  -- show tr.map_implies_R _ _ (tr.R_implies_map _ _ acR) = (acR : @Param.R _ _ _ _ ?paramBase a c)

  -- This works:
  -- show tr.map_implies_R _ _ (tr.R_implies_map _ _ acR) = (acR : Param.R _ _ a c)

  -- This fails:
  -- have lhs : Param.R _ _ a c := tr.map_implies_R _ _ (tr.R_implies_map _ _ acR)
  -- show lhs = acR

  show ?lhs = acR
  let lhs := ?lhs
  show lhs = acR

  have ⟨b, abR, bcR⟩ := acR
  have ⟨b', abR', bcR'⟩ := lhs

  have bEq : b = b' := by
    exact Map2b_prop2 _ abR' abR

    sorry



  -- suffices ((abR = abR') ∧ (bcR = bcR')) by
  -- · congr








  have ⟨b, abR, bcR⟩ := acR

  have abK := tr.R_implies_mapK _ _ abR
  have bcK := tr.R_implies_mapK _ _ bcR



  -- unfold tr.map_implies_R
  -- unfold Map2a.map_in_R
  -- unfold instParamMap2aOfMap3
  apply Eq.trans
  case b =>
    tr_whnf
    simp
    exact ⟨b, ⟨abR, bcR⟩⟩








  simp

  -- match ⊢ with
  -- | ⟨b', ⟨abR', bcR'⟩⟩ = ⟨b, ⟨abR, bcR⟩⟩ =>
  --   sorry




  -- show (⟨_, _⟩ : Param.R _ _ a c) = ⟨_, _⟩
  show (_ : Param.R _ _ a c) = ⟨_, _⟩
