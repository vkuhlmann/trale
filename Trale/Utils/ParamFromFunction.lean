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
def paramFromSurjection'
  {retract : α → β} {sect : β → α}
  (sectK : forall (b : β), retract (sect b) = b)
  : Param42a α β :=
  { R := (retract · = ·),
    covariant := {
      map := retract,
      map_in_R := (fun a b => (by
        intros; assumption
      )),
      R_in_map := fun a b => (by
        intros; assumption
      ),
      R_in_mapK := fun a b => (by
        simp
      )
    },
    contravariant := {
      map := sect,
      map_in_R := fun b a => (
      by
        intros h
        rw [flipRel]
        rw [h.symm]
        exact sectK b
      )
     } }


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

  -- 2a
  · exact retract
  · intro _ _  aF; subst aF
    exact sectK _


-- Split injection.
def paramFromInjection'
  {sect : α → β} {retract : β → α}
  (sectK : forall a, retract (sect a) = a)
  : Param42b α β := by
  tr_constructor

  -- R
  · exact (sect . = .)

  -- 4
  · exact sect
  repeat simp only [imp_self, implies_true]

  -- 2b
  · exact retract
  · dsimp
    intro x x' xR
    subst xR
    exact sectK _


theorem injectiveFunctionInvert'
  (p :  Param42b A B)
  (x : A)
  : p.left (p.right x) = x := by

  let x' := (p : Param10 _ B).right x
  let xR : p.R x x' := p.right_implies_R x x' rfl

  show p.left x' = x
  exact p.R_implies_left x x' xR

theorem injectiveFunctionInvert
  (p :  Param .Map4 .Map2b A B)
  (x : A)
  : p.contravariant.map (p.covariant.map x) = x := by

  let x' := p.covariant.map x
  let xR : p.R x x' := p.covariant.map_in_R x x' rfl

  show p.contravariant.map x' = x
  exact p.contravariant.R_in_map x' x xR

-- from involution

def paramFromInvolution
  {flipR : α → β}
  {flipR' : β → α}
  -- {flipT : Sort _ → Sort _}
  -- (flipT_involution : flipT (flipT α) = α)
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


-- def paramFromSectionK
--   {sect : α → β} {retract : β → α}
--   (sectK : forall a, retract (sect a) = a)
--   : Param2a4 α β := by
--   tr_constructor

--   -- R
--   · exact (. = retract .)

--   -- 4
--   · exact sect
--   · intro a a' aF
--     subst aF
--     exact (sectK _).symm
--   · intro a a' aR
--     subst aR

--     exact (sectK _)

--   repeat simp only [imp_self, implies_true]

--   -- 2b
--   · exact retract
--   · dsimp
--     intro x x' xR
--     subst xR
--     exact sectK _
