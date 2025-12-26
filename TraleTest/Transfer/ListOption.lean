import Lean
import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Theories.Sorts

open Trale

theorem map_compose (as : List α) (f : α → β) (g : β → γ) :
  (as.map f).map g = as.map (fun x => g (f x)) := by
  sorry

def list_to_option (as : List α) : Option α :=
  match as with
  | .nil => .none
  | .cons a _ => a

theorem option_list_inj (ao : Option α) : list_to_option ao.toList = ao := by
  cases ao
  congr
  congr

instance : Param42b.{0} (Option α) (List α) :=
  by tr_from_map option_list_inj

-- instance [Param42b α α'] : Param42b.{0} (Option α) (List α') := by
--   tr_constructor

--   · intro ao as
--     exact as = ao.toList

--   repeat sorry


-- example
--   (xo : Option α)
--   (f : α → β) (g : β → γ) :
--   (xo.map f).map g = xo.map (fun x => g (f x))
--   := by

--   revert g f xo
--   tr_by @map_compose α β γ

--   tr_intro as


--   tr_sorry sorry
