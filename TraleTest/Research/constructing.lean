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

namespace WithTrale
-- instance Map0_prod
--   [p1 : Param00 α α']
--   [p2 : Param00 β β']
--   : Param00 (α × β) (α' × β') := by
--   tr_constructor

--   intro (a, b) (a', b')
--   exact (p1.R a a') × (p2.R b b')

instance Map1_prod
  [p1 : Param10 α α']
  [p2 : Param10 β β']
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
  [p1 : Param2a0 α α']
  [p2 : Param2a0 β β']
  : Param2a0 (α × β) (α' × β') := by
    tr_extend Map1_prod

    case right_implies_R =>
      sorry


end WithTrale


namespace WithTrale2
-- instance Map0_prod
--   [p1 : Param00 α α']
--   [p2 : Param00 β β']
--   : Param00 (α × β) (α' × β') := by
--   tr_constructor

--   intro (a, b) (a', b')
--   exact (p1.R a a') × (p2.R b b')

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

instance Map3_prod
  [Param30 α α'] [Param30 β β']
  : Param30 (α × β) (α' × β') := by
    tr_extend_multiple [Map2a_prod, Map2b_prod]

end WithTrale2

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


-- def
