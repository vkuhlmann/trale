import Trale.Utils.Constructor
import Mathlib.Logic.Equiv.Defs

def paramFromEquiv (h : Equiv α β)
  : Param44 α β := by
  tr_constructor

  -- R
  · exact (h · = ·)

  -- 4
  · exact (h : _ → _)
  repeat (intro _ _ aF; subst aF; simp)
  -- · intro _ _ aF; subst aF; dsimp only
  -- · intro _ _ aR; subst aR; dsimp only
  -- · intro _ _ aR; subst aR; dsimp only

  -- 4
  · exact (h.symm : _ → _)
  repeat (intro _ _ aF; subst aF; simp)
  -- · intro _ _ aF; subst aF; simp only [flipRel, Equiv.apply_symm_apply]
  -- · intro _ _ aR; subst aR; simp only [Equiv.symm_apply_apply]
  -- · intro _ _ aR; subst aR; dsimp only [flipRel]
