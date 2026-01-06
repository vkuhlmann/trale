# Using Trale - Guide for AI Agents

This guide is for AI agents that need to **use** Trale to perform proof transfer in Lean 4. If you're trying to understand the project itself, see [AGENTS.md](AGENTS.md).

## Quick Start

**Goal**: Prove a theorem on a custom type by transferring a proof from a simpler type.

### Three-Step Process

1. **Set up the connection** between your custom type and a simpler type
2. **Define transport lemmas** for operations using `@[trale]`
3. **Use the `trale` tactic** to transfer proofs

## Step-by-Step Workflow

### Step 1: Define Transport Functions

Connect your custom type to a simpler type:

```lean
import Trale.Utils.Attr

-- Your custom type
abbrev Zmod5 := Fin 5

-- Functions connecting the types
def repr5 (a : Zmod5) : Nat := a.val      -- Zmod5 → Nat
def mod5 (n : Nat) : Zmod5 := ⟨n % 5, by omega⟩  -- Nat → Zmod5

-- Prove they form a retraction (one direction)
lemma repr5K : ∀ (a : Zmod5), mod5 (repr5 a) = a := by
  intro a
  simp [repr5, mod5]
```

### Step 2: Create a Param Instance

Register the connection with Trale:

```lean
open Trale

instance : Param2a4 Zmod5 Nat := by tr_from_map repr5K
```

**Common Param types:**
- `Param44`: Full equivalence (types are isomorphic)
- `Param42b`: Split injection (one type embeds into another)
- `Param42a`: Split surjection (quotient-like)
- `Param2a4`: Very common for quotient-like situations

### Step 3: Define Transport Lemmas for Operations

For each operation on your custom type, define how it relates to the simpler type:

```lean
@[trale]
def R_add_Zmod5
  (a b : Zmod5) (a' b' : Nat)
  (aR : tr.R a a')  -- a and a' are related
  (bR : tr.R b b')  -- b and b' are related
  : tr.R (a + b) (a' + b') := by
  -- Prove that addition preserves the relation
  tr_whnf          -- Unfold tr.R definition
  subst aR bR      -- Use that repr5 a = a' and repr5 b = b'
  -- Now prove: repr5 (a + b) = a' + b'
  simp [repr5, Fin.add]
  omega
```

**Key points:**
- Mark with `@[trale]` attribute (essential!)
- Take related inputs: `(a : CustomType) (a' : SimpleType) (aR : tr.R a a')`
- Return related output: `tr.R (operation a ...) (operation a' ...)`

### Step 4: Use the `trale` Tactic

Transfer proofs automatically:

```lean
-- Proof on simple type (Nat)
theorem nat_theorem (a b : Nat) : a + b = b + a := by omega

-- Transfer to custom type (Zmod5)
theorem zmod5_theorem (a b : Zmod5) : a + b = b + a := by
  trale
  -- Goal is now: ∀ (a' b' : Nat), a' + b' = b' + a'
  omega
```

## Preferred Syntax

### ✅ DO USE

```lean
-- 1. The trale tactic (main entry point)
theorem my_theorem : ∀ (a b : MyType), ... := by
  trale
  -- Now work with the simpler type
  omega

-- 2. The @[trale] attribute
@[trale]
def R_operation ... := by ...

-- 3. Helper tactics for creating Param instances
instance : Param2a4 MyType Nat := by tr_from_map my_retraction

instance : Param44 α β := by tr_from_equivalence to_from, from_to
```

### ❌ AVOID (low-level commands)

```lean
-- DON'T use tr_solve directly (it's internal to trale)
theorem my_theorem : ... := by
  tr_by some_theorem
  tr_solve  -- ❌ Avoid

-- DON'T use tr_exact directly (use trale instead)
theorem my_theorem : ... := by
  tr_exact some_theorem  -- ❌ Avoid - use trale

-- INSTEAD, use trale:
theorem my_theorem : ... := by
  trale
  exact some_theorem  -- ✅ Much better
```

**Why?** The project is working towards full coverage where the `trale` tactic handles everything automatically without needing low-level commands.

## Complete Example: Zmod5

Here's a complete working example from `TraleTest/Lemmas/Zmod5.lean`:

```lean
import Mathlib
import Trale.Utils.Attr

namespace MyExample
open Trale

-- Define the type
abbrev Zmod5 := Fin 5

-- Define conversions
def mod5 (n : Nat) : Zmod5 := ⟨n % 5, by omega⟩
def repr5 (a : Zmod5) : Nat := a.val

-- Prove retraction
lemma repr5K : ∀ (a : Zmod5), mod5 (repr5 a) = a := by
  intro a
  simp [repr5, mod5]

-- Create Param instance
instance : Param2a4 Zmod5 Nat := by tr_from_map repr5K

-- Transport lemma for addition
@[trale]
def R_add_Zmod5
  (a b : Zmod5) (a' b' : Nat)
  (aR : tr.R a a') (bR : tr.R b b')
  : tr.R (a + b) (a' + b') := by
  tr_whnf
  subst aR bR
  -- Prove repr5 (a + b) = a' + b'
  simp [repr5, Fin.add]
  omega

-- Now use it!
theorem zmod5_comm (a b : Zmod5) : a + b = b + a := by
  trale
  omega

theorem zmod5_assoc (a b c : Zmod5) : (a + b) + c = a + (b + c) := by
  trale
  omega
```

## Common Patterns

### Pattern 1: Operations with Multiple Arguments

```lean
@[trale]
def R_binop
  (a b : MyType) (a' b' : SimplerType)
  (aR : tr.R a a') (bR : tr.R b b')
  : tr.R (binop a b) (binop a' b') := by
  tr_whnf
  subst aR bR
  -- Prove the operation respects the encoding
  ...
```

### Pattern 2: Constants and Literals

```lean
@[trale]
def R_zero : tr.R (0 : MyType) (0 : SimplerType) := by rfl

@[trale]
def R_one : tr.R (1 : MyType) (1 : SimplerType) := by rfl
```

### Pattern 3: Unary Operations

```lean
@[trale]
def R_neg
  (a : MyType) (a' : SimplerType)
  (aR : tr.R a a')
  : tr.R (-a) (-a') := by
  tr_whnf
  subst aR
  ...
```

### Pattern 4: Transferring from Existing Theorems

```lean
-- Have a theorem on Nat
theorem nat_theorem (a b c : Nat) : (a + b) + c = (c + b) + a := by omega

-- Transfer it to MyType
theorem my_theorem (a b c : MyType) : (a + b) + c = (c + b) + a := by
  trale
  -- Goal is now on Nat
  exact nat_theorem _ _ _
```

## Workflow Tips

### When Setting Up a New Type

1. **Start with conversions**: Define `to_simpler` and `from_simpler`
2. **Prove the retraction**: Usually `∀ a, from_simpler (to_simpler a) = a`
3. **Create Param instance**: Use `tr_from_map`
4. **Add operations one by one**: Define `@[trale]` lemmas as needed
5. **Test with simple theorems**: Start with commutativity, associativity, etc.

### When Trale Gets Stuck

1. **Check for missing transport lemmas**:
   - Look at the unsolved goal after `trale`
   - Identify which operation is missing
   - Define an `@[trale]` lemma for it

2. **Check Param instance is in scope**:
   - Add `open Trale` if needed
   - Verify the instance is defined

3. **Check the map class is strong enough**:
   - Some type constructors need `Param42b` or `Param44`
   - Try upgrading from `Param10` to `Param2a4`

### Debugging Transport Lemmas

```lean
@[trale]
def R_operation ... := by
  tr_whnf           -- Unfold tr.R to see what it means
  -- Now you see the actual proof obligation
  subst ...         -- Use the relation hypotheses
  -- Prove the encoding respects the operation
  ...
```

## Understanding tr.R

The relation `tr.R a b` connects an element `a` of your custom type with an element `b` of the simpler type.

**Typical meaning**: `tr.R a b` means `repr a = b` (the representation of `a` is `b`)

Example with Zmod5:
- `tr.R (⟨2⟩ : Zmod5) (2 : Nat)` holds (repr ⟨2⟩ = 2)
- `tr.R (⟨2⟩ : Zmod5) (7 : Nat)` also holds (repr ⟨2⟩ = 2, and 7 % 5 = 2)
- In general for Zmod5: `tr.R ⟨k⟩ n` holds when `n % 5 = k`

## Advanced Usage

### Custom Instance Search

```lean
-- Sometimes you need to guide instance search
theorem my_theorem : ... := by
  trale
  -- If instance search fails, you can provide instances manually
  have : Param10 α β := ...
  omega
```

### Partial Transfer

```lean
-- Transfer only some variables
theorem my_theorem (a : MyType) (n : Nat) : ... := by
  revert a  -- Only revert what you want to transfer
  trale
  intro a'
  -- Now a' is Nat, but n is still Nat
  ...
```

### Combining with Other Tactics

```lean
theorem my_theorem : ... := by
  trale
  -- Now use any standard Lean tactics
  intro a b
  cases a
  · omega
  · omega
```

## Common Errors and Solutions

### Error: "failed to synthesize instance Param..."

**Problem**: Trale can't find a parametric relation.

**Solution**:
```lean
-- Make sure you have the Param instance
instance : Param2a4 MyType SimplerType := by tr_from_map my_retraction

-- And that Trale is open
open Trale
```

### Error: "unsolved goals" after trale

**Problem**: Missing transport lemma for an operation.

**Solution**: Look at the goal to identify the missing operation, then:
```lean
@[trale]
def R_missing_op ... := by ...
```

### Error: Transport lemma doesn't work

**Problem**: The lemma isn't registered or has the wrong shape.

**Solution**:
- Check you added `@[trale]` attribute
- Verify the signature matches the pattern: `(a : α) (a' : β) (aR : tr.R a a') → ...`
- Make sure the lemma is in scope where you use `trale`

## Next Steps

1. **Study the complete example**: See `TraleTest/Lemmas/Zmod5.lean`
2. **Read the getting started guide**: See `docs/getting-started.md`
3. **Understand the theory**: See `docs/theory.md` for map classes and property levels
4. **Explore examples**: Browse `TraleTest/Transfer/` for real use cases

## Quick Reference

### Essential Tactics

```lean
trale              -- Main tactic: automatically transfer proof
tr_from_map pf     -- Create Param instance from retraction proof
tr_from_equivalence pf1, pf2  -- Create Param from two proofs
tr_whnf            -- Unfold tr.R in transport lemmas
```

### Essential Attributes

```lean
@[trale]           -- Mark transport lemma for automatic use
```

### Common Param Instances

```lean
Param44 α β        -- Full equivalence
Param42b α β       -- Split injection (α ↪ β)
Param42a α β       -- Split surjection (α ↠ β)
Param2a4 α β       -- Common for quotients
```

## Remember

- **Use `trale`, not `tr_solve` or `tr_exact`** - we prefer high-level tactics
- **Mark all transport lemmas with `@[trale]`** - this makes them discoverable
- **Start simple** - prove commutativity and associativity first
- **Build incrementally** - add operations one at a time

---

**Happy proof transferring!** 🎉

For more information:
- **[AGENTS.md](AGENTS.md)** - Understanding the Trale project
- **[README.md](README.md)** - General project overview  
- **[docs/getting-started.md](docs/getting-started.md)** - Detailed tutorial
- **[TraleTest/Lemmas/Zmod5.lean](TraleTest/Lemmas/Zmod5.lean)** - Complete working example
