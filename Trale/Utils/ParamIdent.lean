import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command
import Trale.Core.Param
import Trale.Utils.Extend
import Qq open Qq Lean

namespace Param_ident

universe u

variable {α : Sort u}

@[simp]
def ident_R := Eq (α := α)

def symm_eq : (a = b) = (b = a) := by
  simp
  constructor
  case mp =>
    intro h
    rw [Eq.symm h]
  case mpr =>
    intro h
    rw [Eq.symm h]


-- @[simp]
-- def _root_.Map4_ident : @Map4 α α ident_R := by
--   constructor

--   case map =>
--     exact id

--   case map_in_R =>
--     simp [ident_R]

--   case R_in_map =>
--     simp [ident_R]

--   case R_in_mapK =>
--     simp [ident_R]

@[simp]
def _root_.Map4_ident : @Map4 α α ident_R := by
  constructor

  case toMap3 =>
    constructor

    case toMap2a =>
      constructor

      case toMap1 =>
        constructor
        case map =>
          exact id

        case toMap0 =>
          constructor

      case map_in_R =>
        simp [ident_R]

    case R_in_map =>
      simp [ident_R]

  case R_in_mapK =>
    simp [ident_R]

@[simp]
def _root_.Param44_ident'
  : Param44 α α
  := by
    constructor

    case normativeDirection =>
      exact .this

    case R =>
      exact ident_R

    case covariant =>
      exact Map4_ident

    case contravariant =>
      have h1 : flipRel (@ident_R α) = ident_R := by
        funext a b
        exact symm_eq

      rw [h1]
      exact Map4_ident


@[simp]
def _root_.Param44_ident
  : Param44 α α
  := by
    tr_constructor

    exact Eq

    exact id
    repeat simp

    exact id
    repeat simp


@[simp]
def _root_.Param44_ident''
  (h : α = β) : Param44 α β
  := by
    subst h
    exact Param44_ident

@[simp]
instance : Param α α con cov
  := Param44_ident.forget
      (h1 := Param.map4top)
      (h2 := Param.map4top)
