import Trale.Core.Param

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
