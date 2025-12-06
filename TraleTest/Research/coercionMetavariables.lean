
---- Part 1: This works ----

axiom Foo1 : Type
axiom Bar1 : Type

def func1
  (p: Bar1) : Nat := 0

instance : Coe Foo1 Bar1 where
  coe p := sorry

axiom val1 : Foo1

#check func1 val1
-- Works


---- Part 2: This fails ----

-- def func2'
--   {α : Type}
--   {U : Type -> Type}
--   (p: U α)
--   [CoeT (U α) (Bar2 α)]
--    : Nat := 0

namespace Part2

axiom Foo : Type -> Type
axiom Bar : Type -> Type

def func (_: Bar α) := 0

-- instance : CoeOut (Foo α) (Bar (outParam α)) where
--   coe p := sorry

class MyCoe1 (α : Sort u) (β : semiOutParam (Sort v)) where
  coe : α → β

class MyCoe2 (α : Sort u) (β : outParam (Sort v)) where
  coe : α → β

instance : MyCoe1 (Foo α) (Bar α) where
  coe p := sorry

instance : MyCoe2 (Foo α) (Bar α) where
  coe p := sorry

-- Error: typeclass instance problem is stuck
-- example := inferInstanceAs (MyCoe1 (Foo Nat) (Bar _))

-- This works
example := inferInstanceAs (MyCoe2 (Foo Nat) (Bar _))


instance : CoeOut (Foo α) (Bar α) where
  coe p := sorry

instance : CoeTail (Foo α) (Bar α) where
  coe p := sorry

axiom val : Foo Nat

-- #eval
--   let Y : Type := ?Y
--   inferInstanceAs (CoeOut (Foo Y) (Bar Y))
-- #eval inferInstanceAs (CoeOut (Foo Nat) (Bar _))
-- #eval inferInstanceAs (CoeOut (Foo Nat) (Bar Nat))

-- #eval inferInstanceAs (MyFooCoe1 (Foo Nat) (Bar Nat))

-- This fails
-- #check func val
/-
  Error:

   Application type mismatch: The argument
     val
   has type
     Foo Nat
   but is expected to have type
     Bar ?m.1
   in the application
     func val
-/

-- This works
#check @func Nat val

end Part2

namespace Part3


axiom Foo : Type -> Type
axiom Bar : Type -> Type

def func (_: Bar α) := 0

-- instance : CoeOut (Foo α) (Bar (outParam α)) where
--   coe p := sorry

class MyCoe1 (α : Sort u) (β : semiOutParam (Sort v)) where
  coe : α → β

class MyCoe2 (α : Sort u) (β : outParam (Sort v)) where
  coe : α → β

instance : MyCoe1 (Foo α) α where
  coe p := sorry

instance : MyCoe2 (Foo α) α where
  coe p := sorry

-- Error: typeclass instance problem is stuck
-- example := inferInstanceAs (MyCoe1 (Foo Nat) _)

-- This works
example := inferInstanceAs (MyCoe2 (Foo Nat) _)
