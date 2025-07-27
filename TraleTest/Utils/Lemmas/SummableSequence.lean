import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent

-- Code based on 'summable.v' example by Trocq Rocq plugin developers.


-- axiom nnR : Type
-- axiom zero_nnR : nnR
-- axiom one_nnR : nnR

def nnR := Nat

instance : OfNat nnR n where
  ofNat := n
instance : Zero nnR where
  zero := 0
def zero_nnR : nnR := 0

instance : Add nnR where
  add := Nat.add

inductive xnnR where
  | fin : nnR -> xnnR
  | inf : xnnR

def add_xnnR (a b : xnnR) : xnnR :=
  match a, b with
  | .fin a', .fin b' => .fin (a' + b')
  | _, _ => .inf

instance : Add xnnR where
  add := add_xnnR

theorem add_xnnR_homeo
  (a b : nnR)
  : (xnnR.fin (a + b) = xnnR.fin a + xnnR.fin b) := by
  show xnnR.fin (a + b) = add_xnnR (xnnR.fin a) (xnnR.fin b)

  unfold add_xnnR
  dsimp only


def seq_nnR := Nat → nnR
def seq_xnnR := Nat → xnnR

def add_seq_xnnR (f g : seq_xnnR) : seq_xnnR :=
  fun n => (f n) + (g n)

instance : Add (seq_xnnR) where
  add := add_seq_xnnR

axiom sum_xnnR : seq_xnnR -> xnnR

axiom abc : seq_xnnR

-- class SequenceSummation (seq : Type _) where
--   sumT : Type _
--   sum : seq → sumT

class SequenceSummation (seq : Type _) (sumT : outParam (Type _)) where
  sum : seq → sumT

noncomputable
instance : SequenceSummation seq_xnnR xnnR  where
  sum := sum_xnnR

noncomputable
instance : SequenceSummation (Nat → xnnR) xnnR  where
  sum := sum_xnnR

notation "Σ " a:68 => SequenceSummation.sum a

axiom sum_xnnR_add :
  ∀ (f g : seq_xnnR), Σ (f + g) = (Σ f + Σ g)

def isFin (x : xnnR) : Bool :=
  match x with
  | .fin _ => True
  | .inf => False

def isSummable (f : seq_nnR) : Prop :=
  isFin (Σ (.fin ∘ f : seq_xnnR))

def extend : nnR → xnnR := .fin

def truncate : xnnR → nnR := (
  match . with
  | .inf => zero_nnR
  | .fin r => r
  )

def truncate_extend (r : nnR) : truncate (extend r) = r := by
  simp only [truncate, extend]

structure summable where
  seq : seq_nnR
  is_summable : isSummable seq

instance : Coe summable (seq_nnR) where
  coe s := s.seq

instance : CoeFun summable (fun _ => (Nat → nnR)) where
  coe s := s.seq

def seq_extend : seq_nnR → seq_xnnR := (extend ∘ .)

axiom summable_add :
  ∀ u v : summable, isSummable (fun n => u n + v n)

instance : Add summable where
  add a b := ⟨_, summable_add a b⟩

noncomputable
instance instSummationSummable : SequenceSummation summable nnR where
  sum a := truncate (Σ (xnnR.fin ∘ a))

-- theorem summableSummationDoesNotTruncate
--   (a : summable)
--   : truncate (Σ (xnnR.fin ∘ a)) = .isFin

theorem summationHomeo (a : summable) : Σ seq_extend a.seq = .fin (Σ a) := by
  let h1 := a.is_summable
  unfold isSummable at h1

  let extended := Σ xnnR.fin ∘ a.seq

  show extended = xnnR.fin (truncate extended)

  replace h1 : isFin extended = true := h1

  match extended with
  | .fin b =>
    dsimp only [truncate]

  | .inf =>
    dsimp only [isFin] at h1
    contradiction


def paramNNR : Param42b nnR xnnR
  := SplitInj.toParam truncate_extend

def param_NNR_seq : Param40 seq_nnR seq_xnnR
  := Param_from_map seq_extend


def param_summable_NNR_seq : Param40 summable seq_nnR
  := Param_from_map summable.seq

def param_summable_seq : Param40 summable seq_xnnR
  := Param_from_map (param_NNR_seq.right ∘ param_summable_NNR_seq.forget.right)

-- prop1 and prop2 are related if prop1 implies prop2.
instance propParam : Param2a2a Prop Prop := by
  tr_constructor

  -- R
  · intro x y
    exact x → y

  -- 2a
  · exact id
  · intro a a' aR
    subst aR
    simp

  -- 2a
  · exact id
  · intro a a' aR
    subst aR
    simp

/-
TODO: Make a Prop relation which translates types it comes across. That would
prevent needing to show equivalence of the propositions, where in some cases
only an implication is needed or possible.

```
let eqParam2 : Param10 (xnnR → xnnR → Prop) (nnR → nnR → Prop) := by
  tr_split
  case p1 => infer_instance

  tr_split
  case p1 => infer_instance

  infer_instance
```
-/
