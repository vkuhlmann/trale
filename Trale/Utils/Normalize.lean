import Trale.Core.Param
import Trale.Utils.Whnf
import Lean

def Param.toBottom (p : Param cov con α β) : Param00 α β :=
  p.forget (h1 := Param.map0bottom) (h2 := Param.map0bottom)


namespace Trale.Utils

def flipR [p : Param cov con α β] (r : p.R a b)
  : (p.flip.R b a) := by
    exact r

def flipR' [p : Param cov con α β] (r : p.flip.R a b)
  : (p.R b a) := by
    exact r


def normalizeR [p : Param cov con α β] (r : p.R a b)
  : p.toBottom.R a b := by
    exact r

def denormalizeR [p : Param cov con α β] (r : p.toBottom.R a b)
  : p.R a b := by
    exact r

theorem R_eq_normalize_R [p : Param cov con α β]
  : p.R = p.toBottom.R := by rfl


theorem flipFlipCancels [p : Param cov con α β] : p.flip.flip = p := by
  congr

macro "tr_flip" : tactic => `(tactic|
  first |apply Param.flip |apply flipR |apply flipR'
  )

macro "tr_root_R" : tactic => `(tactic|
  first |apply Param.flip |apply flipR |apply flipR'
  )
