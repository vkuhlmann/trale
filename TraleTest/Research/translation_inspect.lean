import Batteries.Lean.NameMapAttribute
import Qq

import Trale.Core.Param
import Trale.Utils.ExpressionHelpers
import Trale.Utils.EnvExtension.TrRel
import Trale.Utils.EnvExtension.TrTranslation
import Trale.Utils.Basic

open Lean Meta Elab Command Std Qq Term Trale.Utils Trale

namespace TraleTest.Research

elab "#printTraleInstances" : command => do
  let x := instanceExtension
  let state := x.getState (←getEnv)
  let tree := state.discrTree

  let e ← liftCoreM do
    let metaState ← MetaM.run do
      let levelU ← mkFreshLevelMVar
      let levelV ← mkFreshLevelMVar
      let levelW ← mkFreshLevelMVar

      let (args, argsBi, expr) ← forallMetaTelescope q(∀ cov con α β, Param.{levelW, levelU, levelV} cov con α β)

      -- let cov ← mkFreshLevelMVar

      -- let (y, _) ← tree.getMatchLiberal expr--q(Param _ _ _ _)
      let y ← tree.getUnify expr
      IO.println s!"Found {y.size} instances"

      -- let n := min y.size 5
      -- let range := (1...=n)
      -- for i in range do
      let mut i := 0
      while h : i < y.size ∧ i < 35 do
        let result := y[i]
        IO.println s!"Expression {i}: {result.globalName?}"
        -- let z := 4
        -- pure ()
        i := i + 1

    return ()
  return ()

elab "#printTraleImpliedTranslations" : command => do
  let x := instanceExtension
  let state := x.getState (←getEnv)
  let tree := state.discrTree

  let e ← liftCoreM do
    let metaState ← MetaM.run do
      let levelU ← mkFreshLevelMVar
      let levelV ← mkFreshLevelMVar
      let levelW ← mkFreshLevelMVar

      let (args, argsBi, expr) ← forallMetaTelescope q(∀ cov con α β, Param.{levelW, levelU, levelV} cov con α β)

      let y ← tree.getUnify expr
      IO.println s!"Found {y.size} instances"

      let mut i := 0
      while h : i < y.size ∧ i < 35 do
        let result := y[i]
        let name := (result.globalName?.map format).getD "(missing)"
        IO.println s!"Expression {i}: {name}"
        let type ← inferType result.val
        -- IO.println s!"   Type: {type}"
        -- let val := (←Meta.unfoldDefinition? result.val).getD result.val
        let (args2, argsBi2, expr2) ← forallMetaTelescope type
        -- IO.println s!"   Expr2: {expr2}"

        let parts ← getParamParts? expr2

        match parts with
          | .ok parts =>
            let headName := getHeadConst parts.fromType
            if headName.isSome then
              IO.println s!"     {parts.fromType} -> {parts.toType}"
              IO.println s!"     ({parts.conMapType}, {parts.conMapType})"

          | .error err => IO.println s!"Expression {i} (error: {err})"

        i := i + 1

    return ()
  return ()

elab "#printTraleTranslations" : command => do
  let translations := trTranslationExtension.getState (←getEnv)
  let treeSize := translations.discrTree.size
  IO.println s!"Translations is ({treeSize}): "
  let vals := translations.discrTree.elements.map (fun x => (format x.fromType).pretty)
  -- let valsString := vals.toList.foldl (· ++ ·) ""
  IO.println s!"  : {vals}"


#printTraleInstances
