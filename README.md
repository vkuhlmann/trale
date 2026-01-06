# Trale

**Trale** is a Lean 4 library for transporting theorems and proofs across types using parametricity and relational reasoning. It enables you to prove theorems on simpler types (like `Nat`) and automatically transfer those results to more complex types (like custom `Zmod5`), provided you define appropriate transport theorems between them.

## Overview

Trale implements a proof technique based on **parametricity** and **proof transfer**. Instead of duplicating proofs for similar structures, you can:

1. Define a relation (parametricity) between your custom type and a simpler type
2. Prove the theorem on the simpler type
3. Use the `trale` tactic to automatically transfer the proof

This approach is particularly useful when working with:
- Custom numeric types (e.g., modular arithmetic)
- Abstract algebraic structures
- Types that are isomorphic to simpler types
- Cases where direct proofs would be tedious but the result is "morally obvious"

## Quick Example

```lean4
import Mathlib
import TraleTest.Lemmas.Zmod5
open TraleTest.Lemmas

theorem sum_eq_reverse_sum_Zmod5 : ∀ (a b c : Zmod5),
  (a + b) + c = (c + b) + a := by
  trale
  omega

example : ∀ (a b c d e : Zmod5),
  a + (b + c * e) * d = d * b + c * d * e + a * 1 := by
  trale
  intro a b c d e
  rw [add_mul, mul_comm b d, mul_assoc c e d,
      mul_assoc c d e, mul_comm e d]
  omega
```

The `trale` tactic automatically translates the goal from `Zmod5` to `Nat`, where we can use standard tactics like `omega`.

## Installation

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.23.0-rc2)
- [Lake](https://github.com/leanprover/lake) (Lean's build system, comes with Lean 4)

### Setup

1. Clone the repository:
   ```bash
   git clone https://github.com/vkuhlmann/trale.git
   cd trale
   ```

2. Get Mathlib cache (recommended to avoid long build times):
   ```bash
   lake exe cache get
   ```

3. Build the project:
   ```bash
   lake build
   ```

4. (Optional) Build and run tests:
   ```bash
   lake build TraleTest
   ```

## Usage

### Basic Setup

To use Trale with a custom type, you need to:

1. **Define your custom type** (e.g., `Zmod5 := Fin 5`)

2. **Define transport functions** to the simpler type:
   ```lean4
   def repr5 (a : Zmod5) : Nat := a.val
   def mod5 (n : Nat) : Zmod5 := ⟨n % 5, mod5_le5⟩
   ```

3. **Create a `Param` instance** linking your types:
   ```lean4
   lemma repr5K : ∀ (a : Zmod5), mod5 (repr5 a) = a := ...

   instance : Param2a4 Zmod5 Nat := by tr_from_map repr5K
   ```

4. **Define transport lemmas** for each operation using the `@[trale]` attribute:
   ```lean4
   @[trale]
   def R_add_Zmod5
     (a b : Zmod5) (a' b' : Nat)
     (aR : tr.R a a')
     (bR : tr.R b b')
     : (tr.R (a + b) (a' + b')) := ...
   ```

5. **Register translations** from instances:
   ```lean4
   #tr_add_translations_from_instances
   ```

### Complete Example

See [`TraleTest/Lemmas/Zmod5.lean`](TraleTest/Lemmas/Zmod5.lean) for a complete working example showing how to set up Trale for modular arithmetic on `Zmod5`.

## Project Structure

```
Trale/
├── Core/              # Core definitions
│   ├── Param.lean     # Parametricity classes and relations
│   └── Map.lean       # Mapping types for relations
├── Theories/          # Theory-specific transport theorems
│   ├── Arrow.lean     # Function types
│   ├── Forall.lean    # Universal quantification
│   ├── Exists.lean    # Existential quantification
│   └── ...
└── Utils/             # Utilities and tactics
    ├── Attr.lean      # The `trale` tactic and attribute
    ├── Split.lean     # Goal splitting utilities
    └── ...

TraleTest/             # Examples and test cases
├── Lemmas/            # Example setups (e.g., Zmod5, StringNat)
└── Transfer/          # Transfer examples and use cases
```

## Key Concepts

### Parametricity (`Param`)

The `Param` class defines a relation `R` between two types along with proof obligations for covariance and contravariance. Different `ParamXY` abbreviations correspond to different mapping structures (e.g., `Param2a4` for standard bijections).

### The `trale` Tactic

The main entry point is the `trale` tactic, which:
1. Analyzes the goal
2. Finds appropriate `Param` instances and transport lemmas
3. Translates the goal to a simpler type
4. Attempts to solve the parametricity obligations using the Aesop tactic

### The `@[trale]` Attribute

Mark lemmas with `@[trale]` to register them as transport theorems. These lemmas describe how operations on your custom type relate to operations on the simpler type.

## Examples

The `TraleTest/` directory contains numerous examples:

- **`TraleTest/Lemmas/Zmod5.lean`**: Modular arithmetic transport
- **`TraleTest/Transfer/lst01_reverse_sum_generic.lean`**: Comparing different proof approaches
- **`TraleTest/Transfer/lst20_22_reverse_sum_trale.lean`**: Manual vs. automated proof transfer

## Development

### Running Tests

```bash
# Build all tests
lake build TraleTest

# Build a specific test file
lake build TraleTest.Transfer.lst01_reverse_sum_generic
```

### Dependencies

- **Lean 4**: Core language and proof assistant
- **Mathlib**: Mathematical library (required for tests)
- **Qq**: Quoted expressions library
- **Aesop**: Automation framework (used by the `trale` tactic)

## Contributing

Contributions are welcome! Please feel free to submit issues or pull requests.

## License

MIT License

## References

- Based on techniques from parametricity and proof transfer
- Inspired by similar mechanisms in other proof assistants (e.g., Coq's `transfer` tactic)

## Authors

Vincent Kuhlmann (@vkuhlmann)

## Acknowledgments

Some code is based on or inspired by:
- Mathlib4 community (particularly the `to_additive` tactic)
- Code from the Lean prover community, and from Microsoft Corporation
