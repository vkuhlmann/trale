# Trale

**Trale** is a Lean 4 library for transporting theorems and proofs across types using parametricity and relational reasoning. It enables you to prove theorems on simpler types (like `Nat`) and automatically transfer those results to more complex types (like custom `Zmod5`), provided you define appropriate transport theorems between them.

> **Based on the Trocq framework**  
> Trale implements the [Trocq framework](https://arxiv.org/abs/2310.14022) in Lean 4. The framework was developed by Cyril Cohen, Enzo Crance, and Assia Mahboubi for Coq/Rocq.

## Overview

Trale implements a proof technique based on **parametricity** and **proof transfer**. Instead of duplicating proofs for similar structures, you can:

1. **Define a parametric relation** between your custom type and a simpler type
2. **Prove the theorem** on the simpler type where you have better automation
3. **Use the `trale` tactic** to automatically transfer the proof

This approach is particularly useful when:
- Working with custom numeric types (e.g., modular arithmetic, finite fields)
- Dealing with abstract algebraic structures
- Types are isomorphic, equivalent, or in quotient relationships
- Direct proofs would be tedious but the result is "morally obvious"
- Type-specific automation (like `omega` for `Nat`) cannot be easily abstracted

### Why Use Proof Transfer?

**Compared to generic proofs:**
- Leverage type-specific tactics and automation (like `omega` for naturals)
- More natural incremental development (prove for concrete types first, generalize later)
- Better readability without requiring deep knowledge of abstract typeclasses
- Complexity scales with type complexity rather than proof complexity

**When proof transfer excels:**
- The type structure is simpler than the proof logic
- You need type-specific automation that doesn't generalize
- The proof naturally belongs to a concrete type but you need it elsewhere

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

### Parametricity and the `Param` Type

At the core of Trale is the **parametric relation type** `Param`, which relates two types through a graph-like relation `R : α → β → Sort w`. This is accompanied by:

- **Covariant properties**: How to map from `α` to `β` while preserving `R`
- **Contravariant properties**: How to map from `β` to `α` while preserving `R`

The `Param` class is indexed by two **map classes** that specify which properties hold in each direction:
- `Param00`: Just the relation (no functions)
- `Param10`: Covariant map function
- `Param2a0`: Covariant map with proof it captures the relation
- `Param2b0`: Covariant map with proof relations imply equality
- `Param40`: Full equivalence in covariant direction (split surjection when combined with `Param42b`)
- `Param44`: Full equivalence (types are equivalent)

These classes form a hierarchy: `0 < 1 < 2a < 3 < 4` and `0 < 1 < 2b < 3 < 4`, where `2a` and `2b` are incomparable.

**Examples of map classes:**
- `Param44 α β`: Types `α` and `β` are equivalent
- `Param42b α β`: `α` injects into `β` with explicit right inverse (split injection)
- `Param42a α β`: `α` surjects onto `β` with explicit left inverse (split surjection)
- `Param40 α β`: Simple mapping from `α` to `β`

### The `trale` Tactic

The main entry point is the `trale` tactic, which:
1. **Analyzes the goal** to understand its type structure
2. **Finds appropriate `Param` instances** connecting the types
3. **Recursively translates** the goal to a simpler type
4. **Solves parametricity obligations** using the Aesop automation framework with registered `@[trale]` lemmas

The translation preserves logical structure: universal quantifiers, implications, function types, and equalities are all handled systematically.

### The `@[trale]` Attribute

Mark transport lemmas with `@[trale]` to register them for automatic use by the `trale` tactic. These lemmas describe how operations on your custom type relate to operations on the simpler type.

**Structure of a transport lemma:**
```lean
@[trale]
def R_operation
  (a : α) (a' : β) (aR : tr.R a a')  -- Related inputs
  (b : α) (b' : β) (bR : tr.R b b')
  : tr.R (operation a b) (operation a' b')  -- Related outputs
```

### Transport Functions and Relations

A typical setup involves:
- A **representation function** `repr : α → β` (e.g., `repr5 : Zmod5 → Nat`)
- A **construction function** `mk : β → α` (e.g., `mod5 : Nat → Zmod5`)
- A **retraction proof** showing `mk ∘ repr ∼ id` or vice versa

The relation `R a b` typically means `repr a = b`, capturing when elements correspond across the type boundary.

## Examples

The `TraleTest/` directory contains some examples:

### Basic Examples
- **`TraleTest/Lemmas/Zmod5.lean`**: Complete setup for modular arithmetic on ℤ/5ℤ
- **`TraleTest/Lemmas/StringNat.lean`**: Relating natural numbers with strings by length
- **`TraleTest/Transfer/lst01_reverse_sum_generic.lean`**: Comparing three approaches:
  1. Parallel proofs on each type
  2. Generic proofs using typeclasses
  3. Proof transfer (introduced later)

### Proof Transfer Examples
- **`TraleTest/Transfer/lst20_22_reverse_sum_trale.lean`**: Manual vs. automated proof transfer
- **`TraleTest/Transfer/DoubleCommuntes.lean`**: Transferring commutativity properties
- **`TraleTest/Transfer/ModuloFin.lean`**: Working with modular arithmetic

### Advanced Examples
- **`TraleTest/Transfer/InductionPrinciple_*.lean`**: Series showing transfer of induction principles
- **`TraleTest/Transfer/SummableSequence_*.lean`**: Working with infinite sequences
- **`TraleTest/Transfer/lst29_MetricQuestionFromZulip.lean`**: Real-world example from community
- **`TraleTest/Transfer/lst30_GenRewrite.lean`**: Generalized rewriting with Trale

### Research Examples
The `TraleTest/Research/` directory contains experimental features and investigations into the framework's capabilities.

## Documentation

For more detailed information, see the [`docs/`](docs/) directory:

- **[Getting Started Guide](docs/getting-started.md)**: Step-by-step tutorial for beginners
- **[Theory Overview](docs/theory.md)**: Mathematical foundations of the Trocq framework
- **[Implementation Details](docs/implementation.md)**: Technical details of the Lean implementation
- **[Examples Guide](docs/examples.md)**: Walkthrough of key examples with explanations

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

- **Trocq Paper**: Cohen, C., Crance, E., & Mahboubi, A. (2024). [Trocq: Proof Transfer for Free, With or Without Univalence](https://arxiv.org/abs/2310.14022). arXiv:2310.14022
- **Lean 4 Documentation**: [https://lean-lang.org/lean4/doc/](https://lean-lang.org/lean4/doc/)
- **Homotopy Type Theory**: The Univalent Foundations Program. (2013). [Homotopy Type Theory: Univalent Foundations of Mathematics](https://homotopytypetheory.org/book)

## Authors

**Vincent Kuhlmann** ([@vkuhlmann](https://github.com/vkuhlmann))

Master's Thesis, Utrecht University (December 2025)  
Supervisors: Dr. Johan Commelin and Dr. Wouter Swierstra

## Acknowledgments

- **Trocq Framework Authors**: Cyril Cohen, Enzo Crance, and Assia Mahboubi for developing the theoretical framework
- **Mathlib4 Community**: For code demonstrating implementation of tactics, like `to_additive`, which inspired parts of the implementation
- **Aesop Authors**: Jannis Limperg and Asta Halkjær From for the automation framework used in `trale`

<!-- ## Citation

If you use Trale in your research, please cite both this implementation and the original Trocq paper:

```bibtex
@mastersthesis{kuhlmann2025trale,
  author = {Vincent Kuhlmann},
  title = {Proof transfer in Lean: implementing the Trocq framework},
  school = {Utrecht University},
  year = {2025},
  month = {December}
}

@article{cohen2024trocq,
  title={Trocq: Proof Transfer for Free, With or Without Univalence},
  author={Cohen, Cyril and Crance, Enzo and Mahboubi, Assia},
  journal={arXiv preprint arXiv:2310.14022},
  year={2024}
}
``` -->
