# Trale - Documentation for AI Agents

This document provides a comprehensive overview of the Trale project for AI agents that need to understand, maintain, or contribute to this codebase.

## What is Trale?

**Trale** is a Lean 4 library implementing the [Trocq framework](https://arxiv.org/abs/2310.14022) for **proof transfer** using parametricity and relational reasoning. It allows you to:

1. Prove theorems on simpler types (e.g., `Nat`)
2. Automatically transfer those proofs to more complex types (e.g., custom `Zmod5`)
3. Leverage type-specific automation that wouldn't work on abstract types

### Core Idea

Instead of writing generic proofs or duplicating proofs for similar structures, Trale enables **proof transfer**:
- Define a parametric relation between your custom type and a simpler type
- Prove the theorem on the simpler type where you have better automation (like `omega` for `Nat`)
- Use the `trale` tactic to automatically transfer the proof

## Project Structure

```
Trale/
├── Core/              # Core definitions
│   ├── Param.lean     # Parametricity classes and relations (the heart of the system)
│   └── Map.lean       # Mapping types for relations
├── Theories/          # Theory-specific transport theorems
│   ├── Arrow.lean     # Function types
│   ├── Forall.lean    # Universal quantification
│   ├── Exists.lean    # Existential quantification
│   ├── Eq.lean        # Equality
│   └── ...
└── Utils/             # Utilities and tactics
    ├── Attr.lean      # The `trale` tactic and @[trale] attribute
    ├── Basic.lean     # Basic tactics (tr_by, tr_solve, tr_exact)
    ├── Split.lean     # Goal splitting utilities
    └── ...

TraleTest/             # Examples and test cases
├── Lemmas/            # Example setups (e.g., Zmod5, StringNat)
│   ├── Zmod5.lean     # Complete example: modular arithmetic
│   └── ...
└── Transfer/          # Transfer examples and use cases
    ├── lst20_22_reverse_sum_trale.lean
    └── ...
```

## Key Concepts

### 1. Parametricity and `Param`

The core of Trale is the **parametric relation type** `Param`:

```lean
class Param (cov con : Map) (α β : Sort*) where
  R : α → β → Sort w
  -- plus covariant and contravariant properties
```

- `R : α → β → Sort w` is the relation connecting types `α` and `β`
- `cov` and `con` are **map classes** (0, 1, 2a, 2b, 3, 4) indicating what properties hold
- Map classes form a hierarchy: `0 < 1 < 2a < 3 < 4` and `0 < 1 < 2b < 3 < 4`

**Common Param instances:**
- `Param44 α β`: Types are equivalent (full equivalence)
- `Param42b α β`: Split injection (α injects into β with explicit right inverse)
- `Param42a α β`: Split surjection (α surjects onto β with explicit left inverse)
- `Param2a4 α β`: Common for quotient-like situations
- `Param40 α β`: Simple mapping from α to β
- `Param10 α β`: Just a covariant map function
- `Param00 α β`: Just the relation

### 2. The Transport Relation `tr.R`

When you have `instance : Param2a4 Zmod5 Nat`, the relation `tr.R a b` typically means the representation of `a` equals `b`.

Example: `tr.R (⟨2⟩ : Zmod5) (2 : Nat)` holds because `repr5 ⟨2⟩ = 2`.

### 3. Transport Functions

Typical setup:
- **Representation function**: `repr : α → β` (e.g., `repr5 : Zmod5 → Nat`)
- **Construction function**: `mk : β → α` (e.g., `mod5 : Nat → Zmod5`)
- **Retraction proof**: `∀ a, mk (repr a) = a` or vice versa

### 4. The `trale` Tactic

Main entry point for proof transfer:

```lean
theorem my_theorem : ∀ (a b : Zmod5), a + b = b + a := by
  trale
  omega
```

**What it does:**
1. Automatically discovers and registers `Param` instances (lazy loading with caching)
2. Analyzes the goal structure
3. Finds appropriate `Param` instances connecting the types
4. Recursively translates the goal to the simpler type
5. Uses Aesop automation with `@[trale]` lemmas to solve parametricity obligations

### 5. The `@[trale]` Attribute

Mark transport lemmas for automatic discovery:

```lean
@[trale]
def R_add_Zmod5
  (a b : Zmod5) (a' b' : Nat)
  (aR : tr.R a a')  -- a and a' are related
  (bR : tr.R b b')  -- b and b' are related
  : tr.R (a + b) (a' + b') := by  -- operation preserves the relation
  ...
```

**Structure:** Transport lemmas show that operations on the custom type correspond to operations on the simpler type through the relation `tr.R`.

## Important Conventions

### Preferred Syntax

**✅ DO USE:**
- `trale` tactic - the main, high-level tactic for proof transfer
- `@[trale]` attribute for transport lemmas
- `tr_from_map` for creating `Param` instances from retractions

**❌ AVOID (low-level):**
- `tr_solve` - low-level tactic for solving parametricity obligations (internal to `trale`)
- `tr_exact` - low-level tactic combining `tr_by` and `tr_solve`

**Reasoning:** We are working towards full coverage where users don't need low-level commands. The `trale` tactic should handle everything automatically.

### Coding Style

- Use the `trale` tactic for proof transfer
- Mark all transport lemmas with `@[trale]`
- Create `Param` instances using helper tactics like `tr_from_map`, `tr_from_equivalence`
- Follow Lean 4 and Mathlib4 naming conventions
- Document complex transport lemmas

## Common Patterns

### Pattern 1: Setting up a Custom Type for Transfer

```lean
-- 1. Define your type
abbrev MyType := ...

-- 2. Define transport functions
def toSimpler (a : MyType) : SimplerType := ...
def fromSimpler (b : SimplerType) : MyType := ...

-- 3. Prove retraction
lemma from_to : ∀ (a : MyType), fromSimpler (toSimpler a) = a := by ...

-- 4. Create Param instance
instance : Param2a4 MyType SimplerType := by tr_from_map from_to

-- 5. Define transport for operations
@[trale]
def R_operation
  (a : MyType) (a' : SimplerType) (aR : tr.R a a')
  : tr.R (operation a) (operation a') := by ...
```

### Pattern 2: Using Trale

```lean
-- Prove on the simpler type
theorem simple_theorem (a b : Nat) : ... := by omega

-- Transfer to custom type
theorem custom_theorem (a b : MyType) : ... := by
  trale
  -- Goal is now on Nat
  exact simple_theorem _ _
```

## Build System

- **Lake**: Lean's build system (like Cargo for Rust)
- Main command: `lake build`
- Test command: `lake build TraleTest`
- Dependencies: Mathlib, Qq, Aesop

### Key Commands

```bash
lake build                    # Build the library
lake build TraleTest          # Build and run tests
lake exe cache get            # Get Mathlib cache (saves hours!)
lake build TraleTest.Lemmas.Zmod5  # Build specific test
```

## Dependencies

- **Lean 4**: v4.23.0-rc2
- **Mathlib**: Mathematical library (used in tests)
- **Qq**: Quoted expressions library (for metaprogramming)
- **Aesop**: Automation framework (used by `trale` tactic)

## Testing

Tests are in `TraleTest/` directory:
- `TraleTest/Lemmas/`: Complete setups for various types
  - `Zmod5.lean`: Canonical example of modular arithmetic
  - `StringNat.lean`: Relating naturals with strings
- `TraleTest/Transfer/`: Actual proof transfer examples
- `TraleTest/Research/`: Experimental features

## Development Workflow

1. **Understanding**: Study `TraleTest/Lemmas/Zmod5.lean` for a complete example
2. **Building**: Always run `lake exe cache get` first to avoid long builds
3. **Testing**: Build specific test files with `lake build TraleTest.Module.File`
4. **Adding features**: 
   - New transport lemmas go in appropriate `Trale/Theories/` files
   - Mark with `@[trale]` attribute
   - Add tests in `TraleTest/`

## Important Files for Understanding Trale

1. **`Trale/Core/Param.lean`** - Defines the `Param` class (most important)
2. **`Trale/Utils/Attr.lean`** - Implements the `trale` tactic
3. **`Trale/Utils/Basic.lean`** - Basic tactics and macros
4. **`TraleTest/Lemmas/Zmod5.lean`** - Complete working example
5. **`README.md`** - User-facing documentation
6. **`docs/theory.md`** - Mathematical foundations
7. **`docs/getting-started.md`** - Tutorial for beginners

## Key Insights for Agents

1. **Trale is metaprogramming-heavy**: Uses Lean's metaprogramming features extensively
2. **The `trale` tactic is complex**: It performs instance search, type analysis, and proof construction
3. **Transport lemmas are crucial**: Without proper `@[trale]` lemmas, the `trale` tactic gets stuck
4. **Map classes matter**: The numeric suffixes (0, 1, 2a, 2b, 3, 4) indicate different property levels
5. **Aesop integration**: The `trale` tactic uses Aesop for automation

## Common Issues and Solutions

1. **"failed to synthesize instance Param..."**
   - Missing `Param` instance between types
   - Check that the instance is defined and in scope

2. **"unsolved goals" after `trale`**
   - Missing transport lemma for an operation
   - Need to define `@[trale]` lemma for that operation

3. **Slow builds**
   - Run `lake exe cache get` to get Mathlib cache
   - Build only what you need, not the full test suite

## References

- **Trocq Paper**: [arXiv:2310.14022](https://arxiv.org/abs/2310.14022)
- **Repository**: [github.com/vkuhlmann/trale](https://github.com/vkuhlmann/trale)
- **Lean 4 Docs**: [lean-lang.org/lean4/doc/](https://lean-lang.org/lean4/doc/)

## Author

Vincent Kuhlmann ([@vkuhlmann](https://github.com/vkuhlmann))  
Master's Thesis, Utrecht University (December 2025)

---

For more details, see:
- **[AGENTS_USAGE.md](AGENTS_USAGE.md)** - Guide for using Trale
- **[README.md](README.md)** - General project overview
- **[docs/getting-started.md](docs/getting-started.md)** - Tutorial
- **[docs/theory.md](docs/theory.md)** - Mathematical foundations
