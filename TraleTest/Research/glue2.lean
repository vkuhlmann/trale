import Trale.Core.Param
import Trale.Theories.Arrow
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter

open Param_arrow Trale.Utils

def glued
  (p1 : Param cov .Map0 α β)
  (p2 : Param .Map0 con α β)
  (h : p1.R = p2.R) :
  Param cov con α β := by
  constructor

  case R => exact p1.toBottom.R
  case covariant => exact p1.covariant
  /-
  Error: Type mismatch
      Param.contravariant
    has type
      con.interp (flipRel (Param.R MapType.Map0 con))
    but is expected to have type
      con.interp (flipRel (Param.R cov MapType.Map0))
  -/
  case contravariant =>
    -- constructor

    have a := p2.contravariant
    -- rw [R_eq_normalize_R] at a
    suffices p1.toBottom.R = p2.toBottom.R by
      rw [this]
      exact a
    exact h


  -- sorry

  -- {
  --   R := p1.R,
  --   covariant := p1.covariant,
  --   contravariant := p2.contravariant,
  --   : Param cov con α β
  -- }


-- def A : Type := sorry
-- def A' : Type := sorry

-- def B : Type := sorry
-- def B' : Type := sorry

-- instance p1 : Param33.{0} A A' := sorry
-- instance p2 : Param44.{0} B B' := sorry

-- #check
--   let C : Sort _ := ?C
--   let D : Sort _ := ?D
--   (C → D)


-- #check normalizeR

-- def makeArrowType (C : Sort _) (D : Sort _) : (C → D : Sort _) :=
--   sorry

-- def p3 : Param44.{0} (A → B) (A' → B') := by
--   let cov : Param40.{0} (A → B) (A' → B') := inferInstance
--   let con : Param04.{0} (A → B) (A' → B') := inferInstance
--   -- sorry
--   /-
--   Error: Application type mismatch: The argument
--       Param.R MapType.Map4 MapType.Map0
--     has type
--       (A → B) → (A' → B') → Prop
--     of sort `Type` but is expected to have type
--       Param.R MapType.Map4 MapType.Map0 ?m.15 ?m.16
--     of sort `Prop` in the application
--       normalizeR (Param.R MapType.Map4 MapType.Map0)
--   -/
--   let covR := cov.R
--   let mytest := normalizeR (p := cov) cov.R
--   sorry

--   -- -- let con : Param40 (A' → B') (A → B) := inferInstance
--   -- -- let conFlip := con.flip

--   -- have flipR : normalizeR cov.R = normalizeR (p := con) con.R := by
--   --   congr


--   --   sorry

--   -- tr_constructor
--   -- any_goals tr_fill_from cov

--   -- tr_fill_from conFlip


--   -- tr_fill_from con.flip
--   -- tr_fill_from con.flip
--   -- tr_fill_from con.flip
--   -- tr_fill_from con.flip
--   -- tr_fill_from con.flip
--   -- tr_fill_from con.flip





--   -- -- by apply Map4_arrow

--   -- sorry
