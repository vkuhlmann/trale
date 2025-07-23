import Trale.Utils.Extend

def par_ext_1 : Param10 String Nat := by
  tr_constructor

  case R =>
    intro s n
    exact s.length = n

  case right =>
    intro s
    exact s.length

  -- repeat simp


def par_ext : Param40 String Nat := by
  -- tr_extend (by
  --   tr_constructor

  --   case R =>
  --     intro s n
  --     exact s.length = n

  --   case right =>
  --     intro s
  --     exact s.length

  --   : Param10 String Nat)

  tr_constructor

  case R =>
    intro s n
    exact s.length = n

  case right =>
    intro s
    exact s.length

  repeat simp


def par_ext_2' : Param2a0 String Nat := let aa := 3; by
  tr_add_param_base param_base := par_ext_1;
  tr_extend' par_ext_1

  /-
  type mismatch
    par_ext_1
  has type
    Param10 String Nat : Type 1
  but is expected to have type
    Param String Int ?covMapTypeBase ?conMapTypeBase : Type (max 1 ?u.3492)
  -/

  -- case R =>
  --   intro s n
  --   exact s.length = n

  case right_implies_R =>
    simp only []

    simp


def par_ext_2 : Param2a0 String Nat := by
  tr_extend par_ext_1

  case right_implies_R =>
    --   ⊢ ∀ (a : String), a.length = a.length
    simp

    -- intro s
    -- rfl
    -- dsimp only [Param.right]

    -- intro s

    -- trivial
    -- unfold par_ext_1

    -- rw [Param.R]
    -- simp only [Param.forget, coeMap]



    -- simp


    -- simp only [par_ext_1]
    -- simp


def par_ext_3 : Param40 String Nat := by
  tr_extend par_ext_2

  simp
  simp

  -- case right_implies_R =>
  --   intro s

  --   unfold par_ext_1

  --   -- simp [par_ext_2]
  --   simp [par_ext_1]

  -- case R_implies_right =>
  --   intro s s' sR
  --   simp [par_ext_2, par_ext_1] at *
  --   exact sR
