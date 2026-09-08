# VQ: 833-qubit ECDLP verification

VQ is a Lean 4 framework for exact functional verification and formally
certified logical-resource analysis of quantum algorithms for cryptography and
cryptanalysis.

This repository contains the Lean sources for an 833-qubit secp256k1 ECDLP
program and its Palomar statement and proofs.
The program uses complete controlled point translations, semiclassical Fourier
sampling, measurement, reset, and classical feed-forward.  The public point
determines the program.  Correctness and recovery assume a valid public point
`Q = dG`, with `0 < d < q`, where `q` is the secp256k1 subgroup order.

## Verified results

The [public statement](Challenge.lean) specifies the execution, recovery,
and resource results.  [Solution](Solution.lean) supplies the program and
proofs, which pass Lean 4.34.0-rc2, complete statement comparison, and
independent Lean and NanoDa checks.  Their transitive axioms are confined to
`propext`, `Classical.choice`, and `Quot.sound`.

| Claim | Scope |
|---|---|
| Functional correctness | Both scalar loops, exact branch amplitudes, restored quantum workspace, and preserved immutable input under the stated initialization and public-key hypotheses |
| Quantum allocation | Exactly 833 logical qubits, giving a peak-live upper bound |
| Classical allocation | 768 mutable bits and zero declared immutable input bits |
| Toffoli-class cost | Exactly 588,551,462,912 compiled CCZ operations on every execution path, for every public-point code |
| Expected Toffoli-class cost | The same count under semantic branch probabilities for every in-width basis input and immutable input value, with zero initial mutable storage |
| One-run recovery | Selected-event probability at least `((q − 1)/q) × (2401/14641)`, with correct decoding and public-key checking for every selected outcome |
| Independent repetition | Probability greater than `99/100` of a recoverable selected outcome in 26 independent executions under the product-law model |

The functional and probability theorems use the specified initialized state
and phase level at least 257.  The repetition theorem concerns a finite product
law and a mathematical decoder.  Compiled repetition and decoding costs,
approximate phase synthesis, and physical error correction require further
results.

## Palomar preparation

[Challenge](Challenge.lean) defines the public statement using complex
amplitudes and Mathlib.  Solution translates the VQ program and proves that
the public execution preserves its amplitudes, measurement probabilities,
recovery guarantees, and resource counts.  The complete Challenge/Solution
comparison and independent Lean and NanoDa checks pass for the source revision
identified in the [verification guide](docs/verification.md).
The [technical report](docs/report.md) explains the algorithm, proof structure,
resource calculations, and limits.  The [submission metadata](formalization.yaml)
records authorship, sources, automation, and review.

## Build

The project pins Lean 4.34.0-rc2, Mathlib, and `hex-matrix` in
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.  The
[Lean installation guide](https://lean-lang.org/install/manual/) describes
Elan installation.

The default build checks Challenge and Solution:

```sh
lake build
```

Solution can also be checked alone:

```sh
lake build Solution
```

The [verification guide](docs/verification.md) gives the independent-checker
revisions and comparison command.

## Source and documentation

| Source | Purpose |
|---|---|
| [Program construction](VQMathlib/ECDLP/PackedAffine/ProgramResources.lean) | Public-point parameter, program definition, allocation, and valid indices |
| [Scalar execution](VQMathlib/ECDLP/PackedAffine/TwoScalarLoop.lean) | Complete scalar-loop semantics |
| [Recovery](VQMathlib/ECDLP/PackedAffine/ProgramRecovery.lean) | Selected outcomes, decoding, and public-key checking |
| [Repetition](VQMathlib/ECDLP/PackedAffine/ProgramRepetition.lean) | Independent-run probability and recovery |
| [Pathwise resources](VQMathlib/ECDLP/PackedAffine/ToffoliResources.lean) | Exact compiled CCZ count |
| [Expected resources](VQBridge/Palomar833/Resources.lean) | Probability-weighted executed CCZ count |
| [Technical report](docs/report.md) | Algorithm, mathematical results, resource derivation, and limits |
| [Verification guide](docs/verification.md) | Source identity, dependency pins, independent checking, and recorded results |

Definitions and proofs reside under `VQ`, `VQMathlib`, and `VQBridge`.
Every included Lean module belongs to Challenge or Solution's dependency tree.

The repository uses the [MIT license](LICENSE), with copyright held by
Morphism LLC.  The maintainer is [js@morphism.com](mailto:js@morphism.com).
