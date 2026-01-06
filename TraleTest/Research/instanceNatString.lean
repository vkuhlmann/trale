import Trale.Core.Param
import Trale.Theories.Arrow
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application

open Trale

def repeatChar (c : Char) : Nat -> String
  | 0 => ""
  | n + 1 => ⟨c :: (repeatChar c n).data⟩

def repeatCharHasLength : (repeatChar a n).length = n := by
  induction n
  case zero => rfl
  case succ m h =>
    simp [repeatChar, String.length]
    exact h


instance : Param2a0 Nat String := {
    R := fun x y => x = y.length,
    covariant := {
      map := fun x => repeatChar 'a' x,
      map_in_R := by
        intro a a' aF
        subst aF
        exact repeatCharHasLength.symm
    },
    contravariant := {}
  }

instance : Param2a0 Nat String := by
  tr_constructor

  -- R
  exact fun x y => x = y.length

  -- 2a
  exact fun x => repeatChar 'a' x

  intro a a' aF
  subst aF
  exact repeatCharHasLength.symm
