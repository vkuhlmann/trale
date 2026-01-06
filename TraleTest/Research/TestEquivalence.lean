import Trale.Utils.Basic
import Trale.Utils.Attr
import Trale.Utils.TrAdvance
import Trale.Utils.Split

namespace TraleTest.Utils

open Trale

-- Test 1: Using tr_from_equivalence with explicit functions and proofs
section Test1
  -- Define a simple bijection between Bool and Fin 2
  def boolToFin2 : Bool → Fin 2
    | true => 1
    | false => 0

  def fin2ToBool : Fin 2 → Bool
    | 0 => false
    | 1 => true
    | ⟨n+2, h⟩ => False.elim (by omega : False)

  theorem boolToFin2_inv : ∀ b : Bool, fin2ToBool (boolToFin2 b) = b := by
    intro b
    cases b <;> rfl

  theorem fin2ToBool_inv : ∀ f : Fin 2, boolToFin2 (fin2ToBool f) = f := by
    intro f
    match f with
    | 0 => rfl
    | 1 => rfl
    | ⟨n+2, h⟩ => omega

  -- Test the tactic with explicit components
  instance : Param44 Bool (Fin 2) := by
    tr_from_equivalence boolToFin2_inv, fin2ToBool_inv

  #tr_add_translations_from_instances

  -- Verify it works by checking the relation
  example : tr.R true (1 : Fin 2) := rfl
  example : tr.R false (0 : Fin 2) := rfl

end Test1

-- Test 2: Using tr_from_involution for symmetric bijections
section Test2
  -- Define a flip function that swaps pairs
  def flipPair : (α × β) → (β × α)
    | (a, b) => (b, a)

  theorem flipPair_involution : ∀ p : α × β, flipPair (flipPair p) = p := by
    intro p
    cases p
    rfl

  instance : Param44 (α × β) (β × α) := by
    tr_from_involution flipPair

  -- Verify the relation
  example (a : Nat) (b : String) : tr.R (a, b) (b, a) := rfl

end Test2

-- Test 3: Simple equivalence using tuple notation
section Test3
  -- Another simple bijection
  def natToBool (n : Nat) : Bool := n % 2 == 1
  def boolToNat (b : Bool) : Nat := if b then 1 else 0

  -- This won't form a true equivalence since natToBool isn't injective,
  -- but we can still construct a Param for demonstration

  def optionToList : Option α → List α
    | none => []
    | some a => [a]

  def listToOption : List α → Option α
    | [] => none
    | a :: _ => some a

  theorem optionToList_inv : ∀ o : Option α, listToOption (optionToList o) = o := by
    intro o
    cases o <;> rfl

  -- Note: This is NOT a true inverse (listToOption ∘ optionToList is not identity)
  -- This demonstrates that we can construct a split surjection

  def listHead? : List α → Option α
    | [] => none
    | a :: _ => some a

  theorem listHead_roundtrip : ∀ o : Option α, listHead? (optionToList o) = o := by
    intro o
    cases o <;> rfl

  -- Use tr_from_map for split injection
  instance : Param42b (Option α) (List α) := by
    tr_from_map listHead_roundtrip

end Test3

-- Test 4: Test proof transfer with the equivalence
section Test4
  -- Use the Bool/Fin2 equivalence from Test1

  theorem bool_and_comm (a b : Bool) : (a && b) = (b && a) := by
    cases a <;> cases b <;> rfl

  -- Define and operation on Fin 2 (0 = false, 1 = true)
  def fin2And : Fin 2 → Fin 2 → Fin 2
    | 1, 1 => 1
    | _, _ => 0


  -- instance : HAndThen (Fin 2) (Fin 2) (Fin 2) where
  --   hAndThen x y _ := fin2And x y

  -- Register the transport lemma for the and operation
  @[trale]
  def R_and_bool_fin2
    (a b : Bool) (a' b' : Fin 2)
    (aR : tr.R a a') (bR : tr.R b b')
    : tr.R (a && b) (fin2And a' b') := by
    subst aR bR
    cases a <;> cases b <;> rfl

  -- Now we can transfer the theorem
  theorem fin2_and_comm (a b : Fin 2) : fin2And a b = fin2And b a := by
    revert a b

    tr_by bool_and_comm
    tr_intro a a' aR
    tr_intro b b' bR
    apply (R_eq _ _ _ _ _ _).forget
    apply R_and_bool_fin2
    assumption
    assumption
    apply R_and_bool_fin2
    assumption
    assumption


end Test4

-- Test 5: Verify the relation properties
section Test5
  -- Check that we can use the constructed Param
  example (p : Param44 α β) (a : α) : ∃ b : β, p.R a b := by
    exists p.right a
    exact p.right_implies_R a (p.right a) rfl

  example (p : Param44 α β) (b : β) : ∃ a : α, p.R a b := by
    exists p.left b
    exact p.forget.left_implies_R _ _ rfl

  -- Check roundtrip properties
  example (p : Param44 α β) (a : α) : p.left (p.right a) = a := by
    let b := p.right a
    have aRb : p.R a b := p.right_implies_R a b rfl
    exact p.R_implies_left a b aRb

  example (p : Param44 α β) (b : β) : p.right (p.left b) = b := by
    let a := p.left b
    have aRb : p.R a b := p.left_implies_R a b rfl
    exact p.R_implies_right a b aRb

end Test5

end TraleTest.Utils
