# Verification

## Source identity

The definitions, proofs, toolchain selection, comparison configuration, and
license come from VQ branch `833` at
`a9c56bf24a8e1db3b35a6193ff87ef200d91b8d9`.  Dependency cleanup removed
an unused matrix package and its source comment.  Challenge documentation
explains each compared claim and the definitions used by those claims.
The definitions, theorem statements, and proofs retain their original code.

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

Commit
[`6bbe2c6c06e3ddf536f119454f041f09cb32611a`](https://github.com/jsmorph/vq833a/tree/6bbe2c6c06e3ddf536f119454f041f09cb32611a)
passed the full Palomar mechanical workflow on 8 September 2026 at
22:51:52 UTC.  The checker sources matched published PalomarSubmission
revision
[`ef2fa1eadcb246c2346ddba39b52eaa53d4bb763`](https://github.com/PalomarRegistry/PalomarSubmission/tree/ef2fa1eadcb246c2346ddba39b52eaa53d4bb763)
byte for byte before and after execution.

| Check | Result |
|---|---|
| Full workflow | Report status `pass`, stage `complete`, and exit status zero |
| Source identity | The checker fetched the published commit from GitHub.  The checkout remained clean and matched the local source by checksum. |
| Canonical Challenge | The protected statement compiles against verified canonical Mathlib |
| Solution | A fresh build passes inside the checker's confined environment |
| Complete comparison | Every configured statement and the supplied program definition pass comparison |
| Axiom audit | The transitive axioms satisfy the configured restriction |
| NanoDa | The unchanged checker accepts the Solution export |
| Independent Lean kernel | The checker accepts the Solution export |
| Repository checks | Metadata, MIT-license detection, dependency provenance, and source checks pass |
| Local audit | Import coverage, document links, whitespace checks, and exact report arithmetic pass |

The checker reported a non-blocking warning about Challenge's preferred
review length.  The enforced source limits passed.  Lean also reports
existing deprecation, unused-argument, and exponentiation-threshold warnings.

The Comparator phase, including the fresh Solution build, took 1,348.402
seconds, with peak resident memory 7,283,428 KiB, on Linux x86-64.  Host
resource controls limited checker services to 40 GiB and eight CPUs, with
zero swap.  Preparation and full execution both returned zero.
The retained machine report has SHA-256
`7ff103c3ddea1b704b675035025c5c6cfaadf4564a10aac330950fc5d373d7f3`.

## Submission

Palomar editorial review and registration await maintainer authorization.
The [submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
defines the repository requirements.  The
[protocol specification](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/docs/specification.md)
governs verification, review, registration, and publication.  The
[agent instructions](https://submit.palomar-registry.org/llms.txt)
describe the API.  The binding policy takes precedence when a summary differs.

| Submission field | Selection |
|---|---|
| Repository | `jsmorph/vq833a` |
| Commit | Full SHA of the chosen public commit |
| Project directory | Repository root |
| Comparator configuration | Explicit path `comparator.json` |
| Metadata | `formalization.yaml` |
| Authorization relationship | `maintainer`, after confirmation by the person authorizing submission |

The metadata records `quant-ph`, `cs.CR`, and `cs.LO`.  The current policy
accepts these classifications and permits omission of MSC codes.

Before intake, the maintainer confirms the repository, full commit SHA,
Comparator path, and authorization relationship.  The agent route requires
authenticated GitHub access that can create and delete a repository tag and
a secret gist.  After `POST /api/submit`, the agent creates the requested tag
at the chosen commit and a fresh secret gist containing Palomar's challenge,
then calls `POST /api/verify`.  These steps must finish within 15 minutes.
After successful authentication, the agent deletes the tag and gist and
retains the returned access token as a private credential.  Browser sign-in
requires the human submitter.

Palomar runs its verification workflow on the chosen commit.  A mechanical
pass starts the private editorial review.  The agent monitors
`GET /api/submission` with the access token and retrieves the review through
`GET /api/review`.  The documented polling interval is one minute during
execution and five minutes while awaiting review.  Corrected source enters
as a new submission at a new commit.

The repository, commit, authorization declaration, and mechanical workflow
are public from verification onward.  Operators, GitHub, and the model
provider can access the private review, which Palomar retains indefinitely.

Registration requires a separate maintainer decision after reading the
delivered review.  If the review identifies no blocking problem and the
maintainer approves publication, `POST /register` carries that review's
exact `review_sha256`.  Registration publishes the record and redacted
review and preserves the source and dependencies in public forks with
immutable tags.  It creates permanent publication history when Palomar
merges the database change.  The maintainer can withdraw while the submission
is awaiting a registration decision.
Later corrections use a new version of the existing Palomar identifier.
