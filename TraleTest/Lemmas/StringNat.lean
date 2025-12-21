import Trale.Utils.Basic

namespace TraleTest.Lemmas

def repeatChar (c : Char) : Nat -> String
  | 0 => ""
  | n + 1 => ⟨c :: (repeatChar c n).data⟩

def repeatCharHasLength : (repeatChar a n).length = n := by
  induction n
  case zero => rfl
  case succ m h =>
    simp [repeatChar, String.length]
    exact h

-- Prove that we can roundtrip Nat -> String -> Nat
def defaultStringK (n : Nat) : (repeatChar 'a' n).length = n :=
  repeatCharHasLength

scoped instance : Param42a String Nat := by
  tr_from_map defaultStringK
