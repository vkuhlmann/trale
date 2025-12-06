import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command

import Trale.Core.Param
import Trale.Utils.Extend
import Trale.Utils.Glueing
import Trale.Utils.AddFlipped

import Qq open Qq Lean
open Trale Trale.Utils

namespace Param_prod

universe u v x w w1 w2 w3

variable {α : Type u} {α' : Type u} {β : Type v} {β' : Type v}
variable {αR : α -> α' -> Sort w1}
variable {βR : β -> β' -> Sort w2}

def prodR
  {α' α : Type u}
  {β' β : Type v}
  (p1 : Param00 α α')
  (p2 : Param00 β β')
  : (α × β) → (α' × β') → Sort _
  :=
  fun (a, b) (a', b') => (p1.R a a') ×' (p2.R b b')

def flipProdR
  {p1 : Param00 α α'}
  {p2 : Param00 β β'}
  (r : prodR p1 p2 x y)
  : prodR p1.flip p2.flip y x
  := match r with
    | ⟨aR, bR⟩ => ⟨flipR aR, flipR bR⟩

theorem flipProdR_involution
  : flipProdR (flipProdR r) = r := by rfl

instance R_flip_prod
  {α' α : Type u}
  {β' β : Type v}
  [p1 : Param00 α α']
  [p2 : Param00 β β']
  {x x'}
  : Param44 (prodR p1.flip p2.flip x' x) (prodR p1 p2 x x') := by
  tr_constructor

  -- R
  exact (flipProdR · = ·)

  -- 4
  exact flipProdR
  simp
  simp
  simp

  -- 4
  exact flipProdR
  simp
  apply flipProdR_involution
  · intro x x' xR
    subst xR
    exact flipProdR_involution
  simp


@[tr_add_flipped Param_prod.R_flip_prod]
instance Map0_prod
  [p1 : Param00 α α']
  [p2 : Param00 β β']
  : Param00 (α × β) (α' × β') := by
  tr_constructor

  case R =>
    intro (a, b) (a', b')
    exact (tr.R a a') ×' (tr.R b b')

@[tr_add_flipped Param_prod.R_flip_prod]
instance Map1_prod
  [Param10 α α']
  [Param10 β β']
  : Param10 (α × β) (α' × β') := by
  tr_extend Map0_prod

  intro (a, b)
  exact (tr.map a, tr.map b)

@[tr_add_flipped Param_prod.R_flip_prod]
instance Map2a_prod
  [Param2a0 α α']
  [Param2a0 β β']
  : Param2a0 (α × β) (α' × β') := by

  tr_extend Map1_prod

  simp
  intro x x' h

  constructor
  · exact tr.map_implies_R x.fst x'.fst (Prod.mk.inj h).1
  . exact tr.map_implies_R x.snd x'.snd (Prod.mk.inj h).2

@[tr_add_flipped Param_prod.R_flip_prod]
instance Map2b_prod
  [Param2b0 α α']
  [Param2b0 β β']
  : Param2b0 (α × β) (α' × β') := by

  tr_extend Map1_prod

  intro (a, b) (a', b')
  intro R
  simp

  constructor
  · exact tr.R_implies_map a a' R.1
  . exact tr.R_implies_map b b' R.2

@[tr_add_flipped Param_prod.R_flip_prod]
instance Map3_prod
  [Param30 α α']
  [Param30 β β']
  : Param30 (α × β) (α' × β') := by

  tr_extend_multiple [
    Map2a_prod,
    Map2b_prod,
  ]

@[tr_add_flipped Param_prod.R_flip_prod]
instance Map4_prod
  [p1 : Param40 α α']
  [p2 : Param40 β β']
  : Param40 (α × β) (α' × β') := by

  tr_extend Map3_prod

  intro (a, b) (a', b') ⟨aR, bR⟩
  dsimp

  rw [PProd.mk.injEq]

  constructor
  · exact tr.R_implies_mapK a a' aR
  · exact tr.R_implies_mapK b b' bR
