import Trale.Core.Param
import Trale.Theories.Arrow
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application

open Trale

---------------------------------------

/-
# Listing 8a
-/
namespace WithConstructor
instance Map1_prod
  [p1 : Param10 α α']
  [p2 : Param10 β β']
  : Param10 (α × β) (α' × β') := by
  constructor
  case R =>
    intro (a, b) (a', b')
    exact (p1.R a a') × (p2.R b b')

  case covariant =>
    constructor
    case toMap0 => constructor

    case map =>
      intro (a, b)
      exact (p1.right a, p2.right b)
  case contravariant =>
    constructor

instance Map2a_prod
  [p1 : Param2a0 α α']
  [p2 : Param2a0 β β']
  : Param2a0 (α × β) (α' × β') := by
  constructor
  case R => exact Map1_prod.R
  case covariant =>
    constructor
    case toMap1 => exact Map1_prod.covariant
    case map_in_R => sorry
  case contravariant => constructor

end WithConstructor


---------------------------------------

/-
# Listing 8b
-/
namespace WithStructureInstance
instance Map1_prod
  [p1 : Param10 α α']
  [p2 : Param10 β β']
  : Param10 (α × β) (α' × β') := {
    R := by
      intro (a, b) (a', b')
      exact (p1.R a a') × (p2.R b b'),
    covariant.map := by
        intro (a, b)
        exact (p1.right a, p2.right b)
    contravariant := {}
  }


instance Map2a_prod
  [p1 : Param2a0 α α']
  [p2 : Param2a0 β β']
  : Param2a0 (α × β) (α' × β') := {
    Map1_prod with

    covariant.map_in_R := by sorry
  }
end WithStructureInstance


---------------------------------------


/-
# Omitted intermediary listing
-/
namespace WithStructureInstancesClassic
  instance Map1_prod
  [p1 : Param10 α α']
  [p2 : Param10 β β']
  : Param10 (α × β) (α' × β') := {
    R := by
      intro (a, b) (a', b')
      exact (p1.R a a') × (p2.R b b'),
    covariant := {
      map := by
        intro (a, b)
        exact (p1.right a, p2.right b)
    },
    contravariant := {}
  }


instance Map2a_prod
  [p1 : Param2a0 α α']
  [p2 : Param2a0 β β']
  : Param2a0 (α × β) (α' × β') := {
    Map1_prod with

    covariant := {
      Map1_prod.covariant with

      map_in_R := by sorry
    },
  }
end WithStructureInstancesClassic

---------------------------------------


/-
# Listing 9a
-/

namespace WithTrale
instance Map1_prod
  [p1 : Param10 α α'] [p2 : Param10 β β']
  : Param10 (α × β) (α' × β') := by
    tr_constructor

    -- R
    case R =>
      intro (a, b) (a', b')
      exact (p1.R a a') × (p2.R b b')

    -- 1
    case right =>
      intro (a, b)
      exact (p1.right a, p2.right b)


instance Map2a_prod
  [p1 : Param2a0 α α'] [p2 : Param2a0 β β']
  : Param2a0 (α × β) (α' × β') := by
    tr_extend Map1_prod

    case right_implies_R =>
      sorry
end WithTrale

---------------------------------------

namespace WithTrale2
/-
# Listing 9b
-/


instance Map1_prod
  [Param10 α α'] [Param10 β β']
  : Param10 (α × β) (α' × β') := by
    tr_constructor

    -- R
    intro (a, b) (a', b')
    exact (tr.R a a') × (tr.R b b')

    -- 1
    intro (a, b)
    exact (tr.map a, tr.map b)


instance Map2a_prod
  [Param2a0 α α'] [Param2a0 β β']
  : Param2a0 (α × β) (α' × β') := by
    tr_extend Map1_prod
    sorry

instance Map2b_prod
  [Param2b0 α α'] [Param2b0 β β']
  : Param2b0 (α × β) (α' × β') := by
    tr_extend Map1_prod
    sorry


---------------------------------------


/-
# Listing 10a
-/

instance Map3_prod
  [Param30 α α'] [Param30 β β']
  : Param30 (α × β) (α' × β') := by
  tr_extend_multiple [
    Map2a_prod,
    Map2b_prod
  ]


---------------------------------------


/-
# Listing 10b
-/

def Param2a1_prod
  [Param2a1 α α'] [Param2a1 β β']
  : Param2a1 (α × β) (α' × β') := by
  tr_extend_multiple [
    Map2a_prod,
    Map1_prod.flip
  ]
end WithTrale2
