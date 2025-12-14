import Trale.Core.Param
import Trale.Theories.Arrow
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

open Trale

def A : Type := sorry
def A' : Type := sorry

def B : Type := sorry
def B' : Type := sorry

instance p1 : Param33.{2} A A' := sorry
instance p2 : Param44.{1} B B' := sorry

#check
  let C : Sort _ := ?C
  let D : Sort _ := ?D
  (C → D)


def makeArrowType (C : Sort _) (D : Sort _) : (C → D : Sort _) :=
  sorry

def p3 : Param44 (A → B) (A' → B') := by
  let cov : Param40 (A → B) (A' → B') := inferInstance
  let con : Param04 (A → B) (A' → B') := inferInstance
  -- Error: Application type mismatch
  -- let mytest := normalizeR (p := cov) cov.R
  sorry

  -- -- let con : Param40 (A' → B') (A → B) := inferInstance
  -- -- let conFlip := con.flip

  -- have flipR : normalizeR cov.R = normalizeR (p := con) con.R := by
  --   congr


  --   sorry

  -- tr_constructor
  -- any_goals tr_fill_from cov

  -- tr_fill_from conFlip


  -- tr_fill_from con.flip
  -- tr_fill_from con.flip
  -- tr_fill_from con.flip
  -- tr_fill_from con.flip
  -- tr_fill_from con.flip
  -- tr_fill_from con.flip





  -- -- by apply Map4_arrow

  -- sorry
