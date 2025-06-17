import Trale.Core.Param
import Trale.Utils.ParamIdent

class Related (α : Type _) (β : Type _) where
  mapCov : MapType
  mapCon : MapType

  param : Param α β mapCov mapCon

#check Related.mapCov
#check @Related.mapCov

instance : Related α α where
  mapCov := .Map4
  mapCon := .Map4

  param := Param44_ident
