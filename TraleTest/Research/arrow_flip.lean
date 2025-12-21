import Trale.Theories.Arrow
import Trale.Theories.Prod
import Trale.Utils.Glueing
import Trale.Theories.Flip
import Lean

open Trale
open Trale.Utils

namespace TraleTest.Research

open Param_prod Trale.Utils

example
  [p1 : Param2a1 α α']
  [p2 : Param2a1 β β']
  : Param2a1 (α × β) (α' × β') :=
  glued Map2a_prod Map1_prod.flip rfl
  -- inferGlued
  -- by
  -- exact Trale.Utils.glued Map2a_prod Map1_prod.flip rfl

  -- funext (a, b) (a', b')
  -- simp [Map2a_prod]


  -- show ((p1.R a a') ×' (p2.R b b'))
  --       =
  --      ((p1.flip.R a' a) ×' (p2.flip.R b' b))

  -- show ((p1.R a a') ×' (p2.R b b'))
  --       =
  --      ((p1.R a a') ×' (p2.R b b'))

  -- rfl
  -- show ((tr.R a a') × (tr.R b b')) = ((tr.R b b') × (tr.R a a'))


-- example
--   : Param32a (α → β) (α' → β')

-- example
--   [p1 : Param2a1 α α']
--   [p2 : Param2a1 β β']
--   : Param2a1 (α × β) (α' × β')

-- def Param11_prod'
--   [Param11 α α']
--   [Param11 β β']
--   : Param11 (α × β) (α' × β') := by

--   tr_extend_multiple [
--     Map1_prod
--   ]


def Param2a1_arrow
  [p1 : Param12b α α']
  [p2 : Param2a1 β β']
  : Param2a1 (α → β) (α' → β') := inferGlued



def Param2a1_arrow_prop''
  [p1 : Param12b α α']
  [p2 : Param2a1.{0} β β']
  : Param2a1 (α → β) (α' → β') := by
  tr_extend_multiple [
    Map2a_arrow,
    Map1_arrow_flipped
  ]

def Param2a1_prod
  [p1 : Param2a1 α α']
  [p2 : Param2a1 β β']
  : Param2a1 (α × β) (α' × β') := by

  tr_extend_multiple [
    Map2a_prod,
    Map1_prod_flipped
  ]


def Param02a_arrow
  [p1 : Param2b0 α α']
  [p2 : Param02a β β']
  : Param02a (α → β) (α' → β') := by

  let base : Param2a0 (α' → β') (α → β) := Map2a_arrow

  tr_constructor
  exact arrowR p1 p2

  exact base.right
  exact (flipArrowR $ base.right_implies_R . . .)

def Param02a_arrow'
  [p1 : Param2b0 α α']
  [p2 : Param02a β β']
  : Param02a (α → β) (α' → β') := by

  apply flip2a Map2a_arrow --(arrowR p1 p2)

  intro f f'
  let h := arrowR_rel (f := f) (f' := f') (p1 := p1.forget) (p2 := p2.forget)

  exact h.forget

def Param02a_arrow''
  [p1 : Param2b0 α α']
  [p2 : Param02a β β']
  : Param02a (α → β) (α' → β')
  :=
   flip2a Map2a_arrow (--(arrowR p1.toBottom p2.toBottom) (
    fun {f f'} =>
      (arrowR_rel (f := f) (f' := f') (p1 := p1.toBottom) (p2 := p2.toBottom)).forget
  )


def Param02a_arrow_minimal
  [p1 : Param2b0 α α']
  [p2 : Param02a β β']
  : Param02a (α → β) (α' → β')
  :=
   flip2a Map2a_arrow arrowR_rel.forget

def Param01_arrow_minimal
  [p1 : Param10 α α']
  [p2 : Param01 β β']
  : Param01 (α → β) (α' → β')
  :=
   flip1 Map1_arrow arrowR_rel.forget


open Lean Meta Elab Command in
set_option trace.debug true in
#eval show CommandElabM Unit from do
  let decl ← getConstInfo ``Param02a_arrow'
  trace[debug] s!"{format decl.value?}"


def Param02b_arrow'
  [p1 : Param2a0 α α']
  [p2 : Param02b β β']
  : Param02b (α → β) (α' → β') := by

  apply flip2b Map2b_arrow

  intro f f'
  let h := arrowR_rel (f := f) (f' := f') (p1 := p1.forget) (p2 := p2.forget)

  exact h.forget


-- def Param03_arrow'
--   [p1 : Param30 α α']
--   [p2 : Param03 β β']
--   : Param03 (α → β) (α' → β') := by

--   apply flip3 Map3_arrow (arrowR p1 p2)

--   intro f f'
--   let h := arrowR_rel (f := f) (f' := f') (p1 := p1.forget) (p2 := p2.forget)

--   exact h.flip.forget


def Param2a2a_arrow
  [p1 : Param2b2b α α']
  [p2 : Param2a2a β β']
  : Param2a2a (α → β) (α' → β') := by

  -- We can't inference like this, presumably because typeclass inference
  -- doesn't like metavariables at this level.
  -- exact glued Map2a_arrow Param02a_arrow rfl

  let base1 := Map2a_arrow (p1 := p1.forget) (p2 := p2.forget)
  let base2 := Param02a_arrow (p1 := p1.forget) (p2 := p2.forget)

  exact glued base1 base2 rfl


def Param2a1_arrow_prop
  -- {α α' β β' : Type}
  [p1 : Param12b α α']
  [p2 : Param2a1.{0} β β']
  : Param2a1 (α → β) (α' → β') := by

  -- let base1 := Map2a_arrow (p1 := p1.forget) (p2 := p2.forget)
  -- let base1 : Param2a0 (α → β) (α' → β') := Map2a_arrow
  -- -- let base2 := (Map1_arrow (p1 := p1.flip.forget) (p2 := p2.flip.forget)).flip
  -- let base2 : Param01 (α → β) (α' → β') := Map1_arrow.flip

  -- apply glued base1 base2
  apply glued Map2a_arrow Map1_arrow.flip

  -- unfold base1 base2
  -- unfold Map2a_arrow Map1_arrow
  -- unfold Param.R
  -- dsimp
  -- unfold flipRel

  funext f f'
  show _ = _
  -- dsimp


  -- funext a a'

  -- funext a

  -- congr
  apply propext
  constructor
  exact fun x a' a => x a a'
  exact fun x a a' => x a' a
  -- · intro x
  --   intro a' a
  --   exact x a a'
  -- · intro y
  --   intro a a'
  --   exact y a' a

def Param2a1_arrow_any_sort
  [p1 : Param12b α α']
  [p2 : Param2a1.{z} β β']
  : Param2a1 (α → β) (α' → β') := by

  let base1 := Map2a_arrow (p1 := p1.forget) (p2 := p2.forget)
  let base2 := (Map1_arrow (p1 := p1.flip.forget) (p2 := p2.flip.forget)).flip

  apply glued base1 base2

  funext f f'
  show arrowR _ _ _ _ = arrowR _ _ _ _
  unfold arrowR
  dsimp

  show (∀ (a : _) (a' : _), _ → _) = (∀ (a' : _) (a : _), _ → _)


  -- rw[R_eq_normalize_R]
  -- unfold base2
  -- change @Param.R .Map0 .Map0 _ _ base1.forget _ _ = @Param.R .Map0 .Map0 _ _ base2.forget _ _
  -- unfold base2


  -- apply propext -- This fails
  sorry


def Param12a_arrow_prop
  [p1 : Param2b1 α α']
  [p2 : Param12a.{0} β β']
  : Param12a (α → β) (α' → β') := by

  apply glued Map1_arrow Map2a_arrow.flip

  funext f f'
  show _ = _
  apply propext
  constructor
  exact fun x a' a => x a a'
  exact fun x a a' => x a' a


def Param12a_arrow_any_sort
  [Param2b1 α α']
  [Param12a.{z} β β']
  : Param12a (α → β) (α' → β') := by

  apply glued Map1_arrow Map2a_arrow.flip

  funext f f'
  -- apply propext -- This fails
  sorry


def Param12a_arrow_any_sort'
  [Param2b1 α α']
  [Param12a.{z} β β']
  : Param12a (α → β) (α' → β') :=
  -- glued Map1_arrow Param02a_arrow_minimal rfl
  glued Map1_arrow (flip2a Map2a_arrow arrowR_rel.forget) rfl

-- noncomputable
def Param12a_arrow_any_sort''
  [Param2b1 α α']
  [Param12a.{z} β β']
  : Param12a (α → β) (α' → β') := inferGlued

#reduce (Param12a_arrow_any_sort'' : Param12a (Nat -> Nat) (Nat -> Nat))

/-
theorem Param2a_flip_R_eq
  [p1 : Param02b α α']
  [p2 : Param2a0 β β']

  -- (p3 : Map2a_arrow (p1 := p1.forget) (p2 := p2.forget))
  -- (p4 : Param02a_arrow)
  :
  (Map2a_arrow (p1 := p1) (p2 := p2)).R a b = Param02a_arrow.R b a
  := by

  dsimp [Map2a_arrow, Param02a_arrow]
  congr


  rw [R_eq_normalize_R]

  congr

  sorry
-/


#check
  let p1 : Param02a String Nat := ?p1
  let p2 : Param02b Nat Nat := ?p2
  let p3 : Param11 String String := ?p3

  let p_lhs := Map2a_arrow (p1 := p2) (p2 := p1.flip)
  let p_rhs : Param02a (Nat -> String) (Nat -> Nat) := ?p_rhs
  -- p_rhs.left_implies_R
  Param42b
  -- p_lhs.right_implies_R
  ((a : Nat → Nat) → (b : Nat → String) → p_lhs.covariant.map a = b → p_lhs.R a b)
  ((b : Nat → String) → (a : Nat → Nat)  → p_rhs.contravariant.map a = b → p_rhs.R b a)
  -- (Param.right_implies_R (Map2a_arrow (p1 := p2) (p2 := p1.flip)))
    -- (Param.right_implies_R (Map2a_arrow (p1 := p2) (p2 := p1.flip)))


#check Map2a_arrow_flipped
#print axioms Map2a_arrow_flipped -- 'Trale.Map2a_arrow_flipped' does not depend on any axioms
#print Map2a_arrow_flipped

#reduce
  let : Param42a String Nat := ?p
  -- inferInstanceAs (Param2a0 (Nat -> Nat) (Nat -> String))
  inferInstanceAs (Param02a (Nat -> Nat) (Nat -> String))

example [Param2a1 String Nat]
  : Param12a (Nat -> Nat) (Nat -> String)
  := inferGlued


#check Map2b_arrow_flipped

-- def abc
--   {α α' : Sort u} {β β' : Sort v}
--   [p1 : Param MapType.Map2a MapType.Map0 α' α] [p2 : Param MapType.Map0 MapType.Map2b β' β] :
--   Param MapType.Map0 MapType.Map2b (α' → β') (α → β)
--   := flip2b Map2b_arrow _ Trale.arrowR_rel

example [Param2b1 String Nat]
  : Param12b (Nat -> Nat) (Nat -> String)
  := inferGlued


example [Param42a String Nat]
  : Param2a3 (Nat -> Nat) (Nat -> String)
  := inferGlued


-- def flip02a_arrow



def instMap11_arrow
  [p1 : Param11 α α']
  [p2 : Param11 β β']
  : Param11 (α → β) (α' → β') := by

  let cov : Param10 (α → β) (α' → β') := Map1_arrow (p1 := p1) (p2 := p2)
  let con : Param10 (α' → β') (α → β) := Map1_arrow (p1 := p1.flip) (p2 := p2.flip)

  apply glued cov con.flip
  simp only [Param.flip]
  rw [R_eq_normalize_R (p := cov)]
  rw [R_eq_normalize_R (p := con)]

  congr
  -- show arrowR (p1 := p1.toBottom) (p2 := p2.toBottom) = _

  simp [Param.toBottom, cov, con]
  simp [Map1_arrow]
  show arrowR (p1 := _) (p2 := _) = flipRel (arrowR (p1 := _) (p2 := _))
  show
    arrowR (p1 := p1.toBottom) (p2 := p2.toBottom)
    =
    flipRel (arrowR (p1 := p1.flip.toBottom) (p2 := p2.flip.toBottom))


  unfold flipRel
  unfold arrowR
  -- simp
  funext f f'

  sorry


instance Map1_arrow'
  [p1 : Param10 α' α]
  [p2 : Param01 β' β]
  : Param01 (α' → β') (α → β) := by

  let base := Map1_arrow (p1 := p1.flip) (p2 := p2.flip)

  constructor

  case R => exact arrowR p1 p2

  case covariant => constructor

  case contravariant =>

    -- suffices base.R = flipArrowR (arrowR p1 p2) by


    -- exact base.covariant
    suffices base.R = (flipRel (arrowR p1 p2)) by

      rw [←this]
      exact base.covariant

    unfold flipRel arrowR


    sorry


-- instance flipMap1arrow
--   [p1 : Param01 α α']
--   [p2 : Param10 β β']
--   : Param44 (Map1_arrow)


-- instance MapAB_arrow
--   [p1 : Param cov .Map0 (α → β) (α' → β')]
--   [p2 : Param con .Map0 (α' → β') (α → β)]
--   : Param cov con  (α → β) (α' → β') := by
--   apply glued p1 p2.flip
--   repeat sorry


-- exact arrowR p1 p2



  -- show (Map0_arrow (p1 := _) (p2 := _)).R = _
  -- (Map0_arrow (p1 := ?_) (p2 := ?_)).R





open Lean Elab Command Tactic Term Expr Meta

#check CommandElabM
#check MetaM

elab "#register_glued_arrows" : command => do
  let ctx ← getEnv
  -- let abc ← getContext
  -- #check Impl.determineLocalInstances
  -- #check Meta.instanceExtension
  -- #check Meta.addInstance
  -- #check classExtension
  -- #check

  -- let mytest <- whnf (.const `Test [])

  liftTermElabM
    (addInstance
      `instMap11_arrow
      .global
      1000)

  -- discard <| addInstance `instMap11_arrow .global 1000 |>.run {} {}

  return



  -- #check
  -- sorry




#check
  let p : Param11 String Nat := ?p
  -- Map1_arrow (p1 := p.flip) (p2 := p)
  -- inferInstanceAs (Param10 (Nat -> String) (String -> Nat))
  inferInstanceAs (Param10 (String -> Nat) (Nat -> String))
  -- inferInstanceAs (Param11 (String -> Nat) (Nat -> String))



-- def arrowR_iff_arrowR_flipped
--   [p1 : Param00 α α']
--   [p2 : Param00 β β']
--   : arrowR p1 p2 ≃ arrowR p1.flip p2.flip := by
--   sorry


-- instance MapAB_arrow
--   [p1 : Param cov .Map0 (α → β) (α' → β')]
--   [p2 : Param con .Map0 (α' → β') (α → β)]
--   : Param cov con  (α → β) (α' → β') := by


--   apply glued
--   repeat sorry
