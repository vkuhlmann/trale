import Trale.Utils.TrRefold
import Trale.Utils.Basic

open Trale

def mytest : Param .Map1 .Map0 Nat Nat := by
  let z : Nat → Param .Map2a .Map0 Nat Nat := fun z => by tr_ident
  tr_refold at *
  exact (z 4).forget
