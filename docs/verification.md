# Verification

## Source identity

The definitions, proofs, toolchain selection, comparison configuration, and
license come from VQ branch `833` at
`a9c56bf24a8e1db3b35a6193ff87ef200d91b8d9`.  Dependency cleanup removed
an unused matrix package and its source comment.  The definitions and proofs
retain their original text.

The [public statement](../Challenge.lean) gives the algorithm's mathematical
specification.  Its proof holes are the inputs to the statement comparison.
The [Solution](../Solution.lean) supplies the proofs and program definition
through its imports.  The [comparison configuration](../comparator.json)
selects the declarations and permits propositional extensionality, classical
choice, and quotient soundness.

The [technical report](report.md) explains the program and the quantified
claims.  The repository includes the local Lean dependency trees of Challenge
and Solution.  Lake downloads external packages at the revisions pinned in
the manifest.

## Build

Install [Elan](https://lean-lang.org/install/manual/) and run from the
repository root:

```sh
lake build
```

The default targets are Challenge and Solution.  Lake reads
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` to obtain the
fixed Lean version and dependency revisions.

| Dependency | Revision |
|---|---|
| Lean | `leanprover/lean4:v4.34.0-rc2` |
| Mathlib | `85e3a25e006c35636f0e53b0e9296caca2685bc0` |

The manifest fixes the remaining transitive dependencies.  Build output
belongs in the ignored `.lake` directory.

## Independent comparison

The recorded comparison used these upstream tool revisions:

| Tool | Revision | Build toolchain |
|---|---|---|
| [Comparator](https://github.com/leanprover/comparator) | `575674928e239f5bc452aab72d1dd7b0f1326494` | Lean 4.34.0-rc1 |
| [lean4export](https://github.com/leanprover/lean4export) | `cacf989bd75f608700820f6afc595f32e7a99a4d` | Lean 4.34.0-rc2 |
| [NanoDa](https://github.com/robsimmons/nanoda_lib) | `68d5ca9db226849b41a6fff59d796ff19d0a8840` | Rust 1.85.0, locked dependencies |
| [Landrun](https://github.com/zouuup/landrun) | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` | Go 1.25.5 |

Follow the
[Comparator installation instructions](https://github.com/leanprover/comparator/blob/575674928e239f5bc452aab72d1dd7b0f1326494/README.md)
for its tool and sandbox requirements.  With the binaries installed, set
their paths and run:

```sh
COMPARATOR_LANDRUN=/path/to/landrun \
COMPARATOR_LEAN4EXPORT=/path/to/lean4export \
COMPARATOR_NANODA=/path/to/nanoda_bin \
lake env /path/to/comparator comparator.json
```

Comparator builds and exports both modules, compares the selected
statements and definition, checks the transitive axiom restriction, and
passes the Solution export to NanoDa and its independent Lean kernel.
The supplied NanoDa setting is enabled.  This command checks the proof
and statement comparison locally.  Palomar submission additionally checks
the public repository and metadata and requests editorial review.

## Recorded results

The initial prepared copy, committed as
`430e668b94d600fe5fa042f4d331fbe2d89b289d`, passed these checks on
8 September 2026:

| Check | Result |
|---|---|
| Source identity | Every Lean file and fixed build input matches the recorded source revision |
| Import audit | The included Lean files equal the union of the Challenge and Solution import trees.  Challenge imports Mathlib. |
| Source-rehashing build | Challenge and Solution pass with exit status zero |
| Complete comparison | Every configured statement and the supplied program definition pass comparison |
| Axiom audit | The transitive axioms satisfy the configured restriction |
| NanoDa | The unchanged checker accepts the Solution export |
| Independent Lean kernel | The checker accepts the Solution export |
| Metadata and documentation | Metadata validation, local links, whitespace checks, and exact report arithmetic pass |

Build job `vq833a-build-20260908-1` ran from 15:22:34 to 15:30:01 UTC.
Comparison job `vq833a-comparison-20260908-1` returned zero after
16 minutes 27.69 seconds, with peak resident memory 7,278,456 KiB.
Both ran on Linux x86-64 with 20 GiB memory high, 24 GiB maximum, zero
swap, four CPUs, and a 2,400-second limit.  Source and runner checksum
comparisons passed before execution.  The final source comparison also
passed after the independent checks.

These times and memory figures describe proof checking on the verification
host.  The algorithm's logical resources are specified in the report and
proved in Lean.  Metadata validation used PalomarSubmission revision
`c605f23466450a52999fcfb3c6d68ed8febc56bf`.  The source-identity audit also
compared the retained inputs with the original checked proof revision
`9d865f6f2ea73ec456bed87356b70ac8dd9d7f73`.

Palomar editorial review and registration remain pending.
