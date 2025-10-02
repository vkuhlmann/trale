import Trale.Core.Param
import Trale.Utils.ParamIdent

class Related (α : Type _) (β : Type _) where
  mapCov : MapType
  mapCon : MapType

  param : Param mapCov mapCon α β

instance : Related α α where
  mapCov := .Map4
  mapCon := .Map4

  param := Param44_ident

-- instance [p : Param00 α β] : Related α β where
--   mapCov := .Map0
--   mapCon := .Map0
--   param := p

-- instance [p : Param44 α β] : Related α β where
--   mapCov := .Map4
--   mapCon := .Map4
--   param := p
