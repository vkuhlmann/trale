import Trale.Utils.Basic
import Trale.Utils.Split
import TraleTest.Lemmas.StringNat

open Trale TraleTest.Lemmas

def usingSortParam (f : ∀ (u : Sort _), u → u → (u × u × String))
  : (String × String × String)
  := f String "hello" "hi"

def usingSortParam' (f : ∀ (u : Sort _), u → u → (u × u × Nat))
  : (Nat × Nat × Nat)
  := by

  revert f
  tr_by usingSortParam

  tr_intro f f' fR

  case p1 =>
    tr_flip; tr_intro u u' uR
    tr_intro a a' aR

    show Param01 u u'

    exact (inferInstanceAs <| Param42a String Nat).forget
