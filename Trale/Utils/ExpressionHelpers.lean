import Lean
import Batteries
import Batteries.Tactic.Trans
import Batteries.Lean.NameMapAttribute
import Lean.Elab.Tactic.Ext
import Lean.Meta.Tactic.Rfl
import Lean.Meta.Tactic.Symm
import Lean.Meta.Tactic.TryThis
import Aesop
import Qq
import Lean.PrettyPrinter

import Trale.Core.Param
import Trale.Utils.AddFlipped

open Lean Meta Elab Command Std Qq Trale.Utils Term

namespace Trale.Utils
partial def replaceExprM (f: Expr → MetaM (Option Expr)) (e : Expr) : MetaM Expr :=
  visit e

  where visit (e : Expr) := do
    let res ← f e
    match res with
    | .some x => pure x
    | .none =>

    match e with
    | .forallE n bt body bi =>
        let bt ← visit bt

        let arg ← mkFreshExprMVar (.some bt) (userName := n)
        let body := body.instantiateRev #[arg]
        let body ← visit body

        mkForallFVars #[arg] body (binderInfoForMVars := bi)

    | .lam n bt body bi =>
        let bt ← visit bt

        let arg ← mkFreshExprMVar (.some bt) (userName := n)
        let body := body.instantiateRev #[arg]
        let body ← visit body

        mkLambdaFVars #[arg] body (binderInfoForMVars := bi)

        -- let (args, argsBi, body) ← lambdaMetaTelescope b
        -- let e' ←
        --   (args.zip argsBi).foldrM
        --     (fun (arg, bi) body =>
        --       mkLambdaFVars #[arg] body
        --       (binderInfoForMVars := bi)
        --     )
        --     (←visit body)
        -- pure <| e'

    | .mdata data b =>
        pure <| .mdata data (←visit b)

    | .letE n t v b nondep =>
        pure <| .letE n (←visit t) (←visit v) (←visit b) nondep

    | .app f a =>
        pure <| .app (←visit f) (←visit a)

    | .proj n idx b =>
        pure <| .proj n idx (←visit b)

    | _ =>
      pure e
