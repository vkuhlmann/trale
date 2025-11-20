import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Split
import Trale.Utils.Simp
import Trale.Utils.ParamIdent
import Trale.Utils.Application
import Trale.Utils.Converter
import Trale.Theories.Sorts
import TraleTest.Lemmas.Modulo

open TraleTest.Lemmas

set_option trace.tr.utils true

namespace Approach0

theorem doubleCommutesNat : forall (a b c : Nat), (a + b) + c = c + (b + a) := by
  omega

theorem doubleCommutesMod : forall (a b c : Modulo 5), (a + b) + c = c + (b + a) := by
  -- Error: omega could not prove the goal: No usable constraints found
  -- omega
  sorry

end Approach0


namespace Approach1
theorem doubleCommutesNat : forall (a b c : Nat), (a + b) + c = c + (b + a) := by
  intros a b c
  rw [Nat.add_comm _ c]
  rw [Nat.add_comm a _]

lemma mod_comm (a b : Modulo 5) : a + b = b + a := by
  simp [HAdd.hAdd, instAddModulo]
  apply Nat.add_comm

theorem doubleCommutesMod : forall (a b c : Modulo 5), (a + b) + c = c + (b + a) := by
  intros a b c
  rw [mod_comm _ c]
  rw [mod_comm a _]
end Approach1


namespace Approach2

theorem doubleCommutes {G : Type*} [AddCommMagma G]
  : forall (a b c : G), (a + b) + c = c + (b + a) := by
  intros a b c
  rw [AddCommMagma.add_comm _ c]
  rw [AddCommMagma.add_comm a _]



end Approach2

--
