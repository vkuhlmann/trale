import Trale.Core.Param
import Trale.Utils.Constructor
import Trale.Utils.ParamIdent

def Param_id : Param44 α α := Param44_ident

def Param_id' {α α' : Sort u} (h : α = α') : Param44 α α' := by
  rw [h]
  exact Param_id

def Param_from_map
  (f : α -> α')
: Param40 α α' := by
  tr_constructor

  exact (f . = .) -- R
  exact f         -- right
  simp
  simp
  simp

namespace SplitSurj
def toParam
  {retract : α → β} {sect : β → α}
  (sectK : forall (b : β), retract (sect b) = b)
  : Param42a α β :=
  { R := fun a b => retract a = b,
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
end SplitSurj


namespace SplitInj
def toParam
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


end SplitInj
