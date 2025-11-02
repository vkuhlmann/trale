import Lean
import Lean.Meta
import Lean.Expr
import Lean.Elab.Command

section Map
universe w u v

section RExplicit
variable {α: Sort u} {β : Sort v}
variable (R : α -> β -> Sort w)

@[simp]
def flipRel : β -> α -> Sort w := fun a b => R b a

structure Map0 (R : α -> β -> Sort w) : Type (max u v w)

structure Map1 extends Map0 R where
  map : α -> β

structure Map2a extends Map1 R where
  map_in_R : forall (a : α) (b : β), map a = b -> R a b

structure Map2b extends Map1 R where
  R_in_map : forall (a : α) (b : β), R a b -> map a = b

structure Map3 extends Map2a R, Map2b R where

structure Map4 extends Map3 R where
  R_in_mapK : forall (a : α) (b : β) (r : R a b),
              (map_in_R a b (R_in_map a b r)) = r

end RExplicit

inductive MapType where
  | Map0
  | Map1
  | Map2a
  | Map2b
  | Map3
  | Map4
deriving DecidableEq, Repr

instance : Inhabited MapType := ⟨.Map0⟩

instance : ToString MapType where
  toString
    | .Map0 => "Map0"
    | .Map1 => "Map1"
    | .Map2a => "Map2a"
    | .Map2b => "Map2b"
    | .Map3 => "Map3"
    | .Map4 => "Map4"

@[reducible, simp] def MapType.interp
  (mapType : MapType)
  (R : α -> β -> Sort w) :=
  match mapType with
  | .Map0 => _root_.Map0 R
  | .Map1 => _root_.Map1 R
  | .Map2a => _root_.Map2a R
  | .Map2b => _root_.Map2b R
  | .Map3 => _root_.Map3 R
  | .Map4 => _root_.Map4 R

def leMapType (a b : MapType) : Bool :=
  match a, b with
    | .Map0, _
    | .Map1, .Map1
    | .Map1, .Map2a
    | .Map1, .Map2b
    | .Map1, .Map3
    | .Map1, .Map4
    | .Map2a, .Map2a
    | .Map2a, .Map3
    | .Map2a, .Map4
    | .Map2b, .Map2b
    | .Map2b, .Map3
    | .Map2b, .Map4
    | .Map3, .Map3
    | .Map3, .Map4
    | .Map4, .Map4 => true
    | _, _ => false

@[reducible]
instance : LE MapType where
  le a b : Bool := leMapType a b

instance : DecidableLE MapType :=
  fun s t => by
    simp [LE.le, leMapType]

    split
    rotate_right 1

    · -- The cases '_, _' from leMapType
      show Decidable (false = true)
      exact Decidable.isFalse (Bool.false_ne_true)

    -- The cases '.MapX, .MapY' from leMapType
    repeat (
      show Decidable (true = true)
      exact Decidable.isTrue rfl
    )

theorem mapTypeTrans {a b c : MapType} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  simp [LE.le, leMapType]
  cases a <;> cases c <;> simp <;> cases b <;> contradiction

theorem mapTypeTrans' {a b c : MapType} (h1 : a ≥ b) (h2 : b ≥ c) : a ≥ c := by
  apply mapTypeTrans h2 h1

instance : @Trans MapType MapType MapType LE.le LE.le LE.le where
  trans := mapTypeTrans

instance : Union MapType where
  union
    | .Map2a, .Map2b => .Map3
    | .Map2b, .Map2a => .Map3
    | a, b =>
      if a ≤ b then
        b
      else
        a

theorem maptype_U_maptype_symm
  (a b : MapType)
  : a ∪ b = b ∪ a := by

  cases a <;> cases b <;> rfl

theorem maptype_U_maptype_geq_maptype
  (a b : MapType)
  : a ∪ b ≥ a := by

  cases a <;> cases b <;> decide

/-
 theorem maptype_U_maptype_tight
   (a b c : MapType)
   (h : a ∪ b ≥ c)
   : (a ≥ c ∨ b ≥ c) := by

   cases a <;> cases b <;> cases c
   any_goals first
     | left; decide
     | right; decide

   all_goals
     exfalso; simp [Union.union, LE.le, leMapType] at h

   fail "False statement"
-/

theorem maptype_U_maptype_monotone
  (a b c : MapType)
  (h : a ≥ c)
  : a ∪ b ≥ c ∪ b := by

  cases a <;>
    cases b <;>
      cases c <;> first
        | decide
        | contradiction


instance : Inter MapType where
  inter
    | .Map2a, .Map2b => .Map1
    | .Map2b, .Map2a => .Map1
    | a, b =>
      if a ≤ b then
        a
      else
        b

theorem maptype_inter_symm
  (a b : MapType)
  : a ∩ b = b ∩ a := by

  cases a <;> cases b <;> rfl

theorem maptype_inter_leq_maptype
  (a b : MapType)
  : a ∩ b ≤ a := by

  cases a <;> cases b <;> rfl


theorem maptype_inter_monotone
  (a b c : MapType)
  (h : a ≥ c)
  : a ∩ b ≥ c ∩ b := by

  cases a <;>
    cases b <;>
      cases c <;> first
        | decide
        | contradiction



  -- decidableLe a b : Decidable (a ≤ b) := by
  --   unfold LE.le
  --   unfold instLEMapType
  --   simp
  --   cases a <;> cases b <;> (
  --     first
  --     | exact isTrue true
  --     | exact isFalse false
  --   )

@[reducible] def MapType.interp' (mapType : MapType) (R : α -> β -> Sort w) : Type _ :=
  MapType.casesOn (motive := fun _ => Type _) mapType
  (_root_.Map0 R)
  (_root_.Map1 R)
  (_root_.Map2a R)
  (_root_.Map2b R)
  (_root_.Map3 R)
  (_root_.Map4 R)


  -- MapType.casesOn (motive := fun _ => Type _) mapType
  --   (fun _ => Map0 R)
  --   (fun _ => Map1 R)
  --   (fun _ => Map2a R)
  --   (fun _ => Map2b R)
  --   (fun _ => Map3 R)
  --   (fun _ => Map4 R)



-- instance : Coe (@Map4.{1,1,0} α β) (Map0.{1,1,0}) where
--   coe _ := { }


-- instance : Coe (Map4_former.{1,1,0}) (Map0.{1,1,0}) where
--   coe _ := { }


instance : Coe (Map1 R) (Map0 R) where
  coe m := m.toMap0

instance : Coe (Map2a R) (Map1 R) where
  coe m := m.toMap1

instance : Coe (Map2b R) (Map1 R) where
  coe m := m.toMap1

instance : Coe (Map3 R) (Map2a R) where
  coe m := m.toMap2a

instance : Coe (Map3 R) (Map2b R) where
  coe m := m.toMap2b

instance : Coe (Map4 R) (Map3 R) where
  coe m := m.toMap3


@[simp]
def coeMap {m1 m2 : MapType} {R : α -> β -> Sort w}
  (m : m1.interp R) (h : m2 ≤ m1) : m2.interp R := by

  match m1, m2 with
  | .Map4, .Map0 => constructor
  | .Map4, .Map1 => exact (m : Map1 R)
  | .Map4, .Map2a => exact (m : Map2a R)
  | .Map4, .Map2b => exact (m : Map2b R)
  | .Map4, .Map3 => exact (m : Map3 R)
  | .Map4, .Map4 => exact (m : Map4 R)
  | .Map3, .Map0 => constructor
  | .Map3, .Map1 => exact (m : Map1 R)
  | .Map3, .Map2a => exact (m : Map2a R)
  | .Map3, .Map2b => exact (m : Map2b R)
  | .Map3, .Map3 => exact (m : Map3 R)
  | .Map2a, .Map0 => constructor
  | .Map2a, .Map1 => exact (m : Map1 R)
  | .Map2a, .Map2a => exact (m : Map2a R)
  | .Map2b, .Map0 => constructor
  | .Map2b, .Map1 => exact (m : Map1 R)
  | .Map2b, .Map2b => exact (m : Map2b R)
  | .Map1, .Map0 => constructor
  | .Map1, .Map1 => exact (m : Map1 R)
  | .Map0, .Map0 => constructor


@[simp]
def coeMap' {m1 m2 : MapType} {R : α -> β -> Sort w}
  (m : m1.interp R) (h : m2 ≤ m1) : m2.interp R := by

  cases m1 <;> cases m2

  -- Aesthetic, removes the `MapType.interp` invocations.
  all_goals (
    dsimp only [MapType.interp] at m ⊢
  )

  -- Solves the 16 impossible goals. Eg, for Map2a <= Map0
  all_goals (try (
    -- Do not use exfalso directly, because if followed by a simp on the goal, the
    -- goal will not be backtracked after exiting try, causing it to stay False
    -- for possible cases.
    -- FIXME: Why is that happening?

    dsimp [LE.le, instLEMapType, leMapType] at h
    suffices false = true by
      exfalso
      simp at this

    exact h
  ))

  -- Solves the 20 possible goals. Eg. Map0 <= Map2a
  all_goals
  (
    -- Now that the bad cases are ruled out, the types should be coercable.
    -- We simply invoke class inference on CoeT to find the right coercion.
    -- If any case fails, it means:
    --    1. a coercion is missing, or,
    --    2. `LE MapType` is incorrectly true for m1 and m2
    --    3. the above filtering code is incorrect.
    exact CoeT.coe m
  )
