import Trale.Core.Param
import Trale.Theories.Arrow
import Trale.Theories.Prod
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Utils.ParamFromFunction

open Trale.Utils

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

instance p : Param42a String Nat := by
  tr_from_map defaultStringK

  -- exact paramFromInjection

  -- -- tr_from_map defaultStringK
  -- tr_constructor

  -- -- R
  -- exact (· = ·.length)

  -- -- 4


example : Param10 (String × (Nat -> Nat)) (Nat × (String -> String)) :=
  by infer_instance


def succString (s : String) : String := "b" ++ s

def incrementKeepsRelation
  (a : Nat)
  (a' : String)
  (aR : tr.R a a')

  : tr.R (Nat.succ a) (succString a')

  := by
  tr_whnf
  subst aR
  congr

-- example : Param10
--   (∀ (n : Nat), (Nat.succ n) > 0)
--   (∀ (s : String), (succString "").length > 0)
--   := by

example : Param10
  (∀ (n : Nat), (Nat.succ n) > 0)
  (∀ (s : String), (succString "").length > 0)
  := by
  tr_intro a a' aR



  -- tr_split_application
  -- case aR =>
  --   show tr.R 0 0
  --   rfl



  tr_from_map

  -- instan

  sorry

-- (∀ P: String -> Prop, )


#eval p.left 6
#eval p.right "test"

#check inferInstanceAs (Param40 String Nat)
#check inferInstanceAs (Param04 (Nat × Nat) (String × String))



-- by
--   tr_constructor

--   exact (· = ·.length)

--   -- 2a
--   exact repeatChar 'a'
--   · intro a a' aF
--     subst aF
--     exact repeatCharHasLength.symm


--   -- 2a


--  {
--     R := fun x y => x = y.length,
--     covariant := {
--       map := fun x => repeatChar 'a' x,
--       map_in_R := by

--     },
--     contravariant := {}
--   }
