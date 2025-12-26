import Trale.Core.Param
import Trale.Utils.Normalize

namespace Trale.Utils

def glued
  (p1 : Param cov .Map0 α β)
  (p2 : Param .Map0 con α β)
  (h : p1.R = p2.R) :
  Param cov con α β := {
    R := p1.R,
    covariant := p1.covariant,
    contravariant := by
      rw [h]
      exact p2.contravariant
  }
  -- by
  -- constructor

  -- case R => exact p1.toBottom.R
  -- case covariant => exact p1.covariant
  -- /-
  -- Error: Type mismatch
  --     Param.contravariant
  --   has type
  --     con.interp (flipRel (Param.R MapType.Map0 con))
  --   but is expected to have type
  --     con.interp (flipRel (Param.R cov MapType.Map0))
  -- -/
  -- case contravariant =>
  --   rw [←R_eq_normalize_R, h]
  --   exact p2.contravariant

def inferGlued
  [p1 : Param cov .Map0 α β]
  [p2 : Param .Map0 con α β]
  (h : p1.R = p2.R := by rfl) :
  Param cov con α β :=
  glued p1 p2 h
