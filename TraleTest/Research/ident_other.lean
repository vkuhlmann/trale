import Trale.Core.Param
import Trale.Theories.Ident
open Trale

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


def symm_eq : (a = b) = (b = a) := propext ⟨Eq.symm, Eq.symm⟩

@[simp]
def _root_.Param44_ident'
  : Param44 α α
  := {
    R := ident_R,
    covariant := Map4_ident,
    contravariant := by
      have h1 : flipRel (@ident_R α) = ident_R := by
        funext a b
        exact symm_eq

      rw [h1]
      exact Map4_ident
  }
