import Trale.Core.Param
import Trale.Utils.Constructor
import Trale.Utils.ParamIdent

namespace Trale.Utils

def Param_id : Param44 α α := Param44_ident

def Param_id' {α α' : Sort u} (h : α = α') : Param44 α α' := by
  rw [h]
  exact Param_id

@[simp]
def paramFromMap
  (f : α → α')
: Param40 α α' := by
  tr_constructor

  -- R
  exact (f . = .) -- R

  -- 4
  exact f
  repeat simp

-- Split surjection.
def paramFromSurjection
  {sect : α → α'} {retract : α' → α}
  (sectK : ∀ a, retract (sect a) = a)
  : Param42a α' α := by
  tr_extend paramFromMap retract

  -- 2a
  · exact sect
  · intro _ _  aF; subst aF
    exact sectK _

-- Split injection.
def paramFromInjection
  {sect : α → α'} {retract : α' → α}
  (sectK : ∀ a, retract (sect a) = a)
  : Param42b α α' := by
  tr_extend paramFromMap sect

  -- 2b
  · exact retract
  · intro _ _  aR; subst aR
    exact sectK _


theorem transportRoundtrip
  (p :  Param2a2b A B)
  (x : A)
  : p.left (p.right x) = x := by

  let x' := p.right x
  let xR : p.R x x' := p.right_implies_R x x' rfl

  exact p.R_implies_left x x' xR


def paramFromInvolution
  {flipR : α → β}
  {flipR' : β → α}
  (h : ∀ a, flipR' (flipR a) = a)
  (h' : ∀ b, flipR (flipR' b) = b := by exact h)

  : Param44 α β := by

  tr_constructor

   -- R
  exact (flipR · = ·)

  -- 4
  exact flipR
  simp
  simp
  simp

  -- 4
  exact flipR'
  simp

  apply h'
  · intro x x' xR
    subst xR
    apply  h
  simp

def paramFromEquiv
  {f : α → β}
  {g : β → α}
  (h1 : ∀ x, g (f x) = x)
  (h2 : ∀ x, f (g x) = x)
  : Param44 α β := by
  tr_extend paramFromMap f

  -- 4
  exact g
  · intro _ _ aF; subst aF; exact h2 _
  · intro _ _ aR; subst aR; exact h1 _
  · intro _ _ aR; rfl
