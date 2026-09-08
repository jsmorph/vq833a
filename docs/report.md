# Windowed Euclidean Arithmetic in an 833-Qubit secp256k1 ECDLP Program

Jamie Stephens · js@morphism.com · 8 September 2026

## Abstract

We verify a secp256k1 elliptic-curve discrete-logarithm program with a fixed
allocation of 833 logical qubits and exactly 588,551,462,912 Toffoli-class
operations per execution.  The program shares temporary storage between
field arithmetic and exceptional-point handling.  Bounds on Euclidean
coefficients restrict reversible endpoint searches according to the round
number.  Lean checks the arithmetic, workspace restoration, complete point
translation, both semiclassical scalar loops, and the analytic recovery
distribution.  For every valid nonzero public key, a selected family of
outcomes has probability at least $((q-1)/q)(2401/14641)$, where $q$ is the
subgroup order, and its outcomes decode to the secret scalar.  Under the
product law for 26 independent executions, the probability of a recoverable
selected outcome exceeds $99/100$.  Each execution path has the stated gate
count, which also equals the semantic expectation.  Lean and NanoDa accept
the public statement's proofs with propositional extensionality, classical
choice, and quotient soundness as their transitive axioms.

## Program and results

The program implements the double-scalar quantum computation used by Shor's
discrete-logarithm algorithm.  Let $G$ be the standard secp256k1 generator,
$q$ its prime order, and $Q=[d]G$ a valid public point with $0<d<q$.
For $N=2^{256}$, its scalar computation ranges over $0\leq a,b<N$ and forms

$$
[a]G+[b]Q=[a+db]G.
$$

The program is determined by the public point $Q$.  It performs complete
controlled point translations and uses a semiclassical Fourier transform,
measurement, reset, and classical feed-forward to record the scalar
outcomes.  A recycled control qubit supplies the scalar bits.  The point
register starts at the identity, and the arithmetic workspace starts clear.
Each point translation handles ordinary addition, the identity, inverse
pairs, and doubling, and restores its temporary storage.

| Result | Quantified scope |
|---|---|
| Curve parameters | Primality of the field modulus and subgroup order, nonzero discriminant, validity of the standard generator, and its exact order |
| Scalar computation | Exact complex amplitudes after both scalar loops for every valid $Q=[d]G$, $0<d<q$, and the specified initialization |
| Workspace | Every final branch has support confined to the point-coordinate fields, with the remaining quantum bits clear |
| Outcome distribution | Nonnegative outcome masses summing to one for every public-point code and immutable input value |
| One-run recovery | Selected-event mass at least $((q-1)/q)(2401/14641)$, with correct decoding and public-key checking on every selected outcome |
| Independent repetition | Selected-event probability greater than $99/100$ in the product law for 26 executions |
| Quantum allocation | Exactly 833 allocated logical qubits, with valid indices throughout the program, giving a peak-live upper bound of 833 |
| Classical allocation | 768 mutable bits and zero declared immutable input bits |
| Pathwise cost | Exactly 588,551,462,912 additional CCZ operations on every execution path, for every public-point code and initial branch |
| Expected cost | The same count for every public-point code, immutable input value, and basis input within the allocated quantum register, starting with zero mutable storage |

Functional correctness starts with the all-zero quantum state and permits
arbitrary initial classical storage and measurement history.  The probability
statements start with zero quantum and mutable classical registers.
Functional correctness and the recovery bounds assume a valid public key
and exact phase representation at level at least 257.  The allocation and
cost statements cover every natural-number public-point code.  The semantic
immutable input value is preserved.  The declared classical allocation
counts the program's registers.  Measurement histories index branches in the
mathematical semantics.

VQ is a Lean 4 framework for exact functional verification and formally
certified logical-resource analysis of quantum algorithms for cryptography
and cryptanalysis.  It represents reversible circuits and quantum programs
with measurement, reset, classical storage, and feed-forward.  Exact
amplitude semantics retain the measurement branches.  Functional proofs
relate the generated operations to mathematical specifications, and
resource functions count allocation and gates in those same operations.
This development uses Mathlib for finite sums, complex analysis, modular
arithmetic, and elliptic-curve groups.

## Point translation and storage

The field modulus is $p=2^{256}-2^{32}-977$, and the curve is
$y^2=x^3+7$ over the field of residues modulo $p$.  Reduced coordinate
pairs encode finite points.  The pair $(0,0)$ encodes the identity.
The coordinate fields occupy bit intervals $[0,256)$ and $[259,515)$.
The spacing accommodates arithmetic extensions during a translation.

Complete point translation combines field arithmetic with exceptional-case
correction.  Reversible comparisons record which exceptional case applies.
Totalized division and multiplication replace a zero factor by one during
an arithmetic stage and record that replacement in a temporary bit.  The
correction stage gives the required group sum and erases the case tags.
Measured arithmetic cleanup includes the phase corrections needed to
preserve coherent branch amplitudes.

Logical qubit 832, using zero-based indexing, serves as the zero-factor
temporary during field arithmetic and the equality temporary during point
comparisons.  Its uses occur in this order:

1. Input comparisons compute the exceptional-case tags and clear the
   equality temporary after each comparison.
2. Retained division computes and clears the zero-factor temporary.
3. Retained multiplication computes and clears the zero-factor temporary.
4. Controlled negation uses and clears the equality temporary.
5. Output correction and tag erasure use the equality temporary, clearing
   it after each comparison.

The component proofs establish the temporary's required state at every
change of use.  The composed proof establishes the group operation and
workspace restoration.

| Register allocation | Logical qubits |
|---|---:|
| Field registers | 768 |
| Recycled Fourier control | 1 |
| Euclidean arithmetic fields and temporary storage | 59 |
| Exceptional-case tags | 4 |
| Shared zero-factor and equality temporary | 1 |
| Total | 833 |

The Euclidean allocation includes six extension bits for two work registers,
four phase, iteration, and sign bits, 35 bits for operand lengths and shift
amount, and 14 arithmetic temporary bits.  Valid-index proofs cover every
gate, measurement, reset, and classical operation in the complete program.
Together with its fixed allocation, they establish the peak-live bound.

## Round-dependent Euclidean searches

Field arithmetic uses a fixed schedule of 1,620 packed binary-Euclidean
rounds.  Reversible searches recover operand endpoints at register
exchanges.  Coefficient and remainder bounds locate the endpoints within
intervals determined by the emitted round number.

For a nonempty completed quotient prefix $u_1,\ldots,u_m$, define
$C_{-1}=0$, $C_0=1$, and

$$
C_j=u_jC_{j-1}+C_{j-2}.
$$

Let $w$ be the sum of the quotient bit lengths and $C=C_m$.
The first quotient is at least two, and later quotients are positive.
The coefficient-growth theorem gives

$$
C\geq\eta\lambda^w,\qquad
\lambda=(2+\sqrt3)^{1/3},\qquad
\eta=\frac{4\sqrt3-3}{13}\lambda^2.
$$

An upper bound on the sum of consecutive coefficients gives a complementary
remainder bound.  A reachable-state invariant identifies the coefficients
in each Euclidean phase and relates the accumulated quotient weight to
the round index.  It covers quotient completion, partial shifts, register
exchange, and the terminal remainder.

The generator calculates search endpoints with integer arithmetic.  Write
$r=w\bmod49$, $s=r\bmod19$, and define

$$
B(w)=\max\!\left(1,
31\left\lfloor\frac{w}{49}\right\rfloor+
12\left\lfloor\frac{r}{19}\right\rfloor+
5\left\lfloor\frac{s}{8}\right\rfloor\right).
$$

The proved inequalities

$$
\eta>\tfrac12,\qquad
\lambda^{49}>2^{31},\qquad
\lambda^{19}>2^{12},\qquad
\lambda^8>2^5
$$

make $B(w)$ a lower bound on the coefficient bit length.  For one-based
emitted round $T$, set $w=\lfloor T/4\rfloor$.  The upper search uses a
prefix of width $\min(w+3,258)+1$.  The lower search uses the suffix from
zero-based source index $B(w)+1$ through index 258, of width $258-B(w)$.
The reachable-state proof places each selected endpoint in its search
interval and covers the encoded zero result.

Each search returns the endpoint required by the arithmetic step and
restores its temporary storage.  The round proof composes these searches
with the arithmetic update.  Separate inactive and terminal-state results
cover rounds that perform no Euclidean update, including wrap of the
terminal counter's low word.  The schedule reaches its required terminal
encoding for every admissible input.  Inverse extraction and reversal
return a reduced inverse and restore the prepared input.  Reversing input
preparation establishes the field caller's required workspace state.

## Fourier sampling and recovery

For scalar outcomes $(r,s)$, the ideal point-register state has amplitude

$$
\Psi_{d,r,s}(j)=\frac{1}{N^2}
\sum_{a=0}^{N-1}\sum_{b=0}^{N-1}
\exp\!\left(\frac{2\pi i(ar+bs)}{N}\right)
\mathbf1_{j=\operatorname{enc}([a+db]G)}.
$$

Here $\operatorname{enc}$ maps the identity to zero and a finite point
with reduced coordinates $(x,y)$ to $x+2^{259}y$.
The complete branch theorem gives $\alpha\Psi_{d,r,s}$ for every branch,
where $\alpha=(1/\sqrt2)^{512\cdot512}$ accounts for the arithmetic
cleanup measurements.  The outcome law sums squared amplitudes over
basis indices and all measurement branches with the recorded pair $(r,s)$.
This retains branch multiplicity and yields the normalized Fourier-sampling
distribution used by the recovery theorem.

For $0\leq t<q$, define the nearest Fourier bin

$$
J_N(t)=\left\lfloor\frac{2Nt+q}{2q}\right\rfloor.
$$

Writing $[x]_q$ for the least nonnegative residue modulo $q$, the selected
family consists of

$$
\bigl(J_N(t),J_N([dt]_q)\bigr),\qquad 0<t<q.
$$

The decoder rounds each observed bin $j$ to
$R(j)=\lfloor(2qj+N)/(2N)\rfloor$.  If $R(r)$ is nonzero modulo $q$,
it returns $R(s)R(r)^{-1}\bmod q$.  A candidate passes the public check
when it lies below $q$ and its multiple of $G$ equals $Q$.
Every selected pair decodes to $d$ and passes this check.

The analytic bound on the mass $p_{\mathrm{sel}}$ of the selected family is

$$
p_{\mathrm{sel}}\geq\frac{q-1}{q}\frac{2401}{14641}.
$$

The proof applies to the outcome distribution for each admissible public
key.  It uses finite-sum and Fourier estimates.  For 26 independent
executions, each starting from the specified initialized state, the
selected-event probability is

$$
1-(1-p_{\mathrm{sel}})^{26}>\frac{99}{100}.
$$

Every outcome tuple in this event contains a pair that decodes to the secret
and passes the public check.  The theorem specifies the product law and
mathematical decoding.  Compiling the repetition and decoding controller,
and bounding its additional resources, remain further work.

## Logical gate counts

The metric assigns one to each compiled CCZ operation.  A reversible
controlled-controlled-$X$ operation compiles to a CCZ conjugated by
Hadamard gates, so its cost in this metric is one.  Other primitive gates,
measurements, resets, and classical operations have cost zero.

The fixed part of a Euclidean round costs 77,405 Toffoli-class operations.
Endpoint searches and their surrounding controls cost 141,696,120 across
the schedule.  Input preparation costs 35,204.  The prepared forward
schedule therefore has count

$$
S=35{,}204+1{,}620\cdot77{,}405+141{,}696{,}120
=267{,}127{,}424.
$$

Lean derives these counts from the generated operations and composes them
through the callers:

| Operation | Composition | Toffoli-class count |
|---|---:|---:|
| Prepared forward schedule | $S$ | 267,127,424 |
| Retained division | $2S+30{,}323{,}778$ | 564,578,626 |
| Retained multiplication | $2S+30{,}323{,}778$ | 564,578,626 |
| Complete controlled point translation | $P=4S+81{,}004{,}880$ | 1,149,514,576 |
| Complete ECDLP execution | $512P$ | 588,551,462,912 |

Every execution path adds that complete-program count to its incoming
CCZ accumulator.  This statement permits every public-point code and
initial semantic branch.  For a normalized in-range basis input, zero
mutable storage, and any immutable input value, the probability-weighted
count consequently satisfies

$$
\mathbb E[\text{CCZ operations}]=588{,}551{,}462{,}912.
$$

The expected count concerns one program execution.  A physical resource
estimate requires phase synthesis, error correction, routing, factory
allocation, and a hardware model.  The fixed logical allocation gives the
stated peak-live bound.  Proving minimum width would require a lower bound
over an explicit class of implementations.

## Formal specification and verification

The public statement defines secp256k1, point encoding, primitive complex
gate actions, measured execution, recovery, and logical costs using Lean
core and Mathlib.  The program family is a definition whose only argument
is the public-point code.  Its proof supplies the generated VQ program and
establishes the connection to those public definitions.

Primitive interpretation results relate VQ's exact amplitudes to complex
amplitudes.  Structural induction transfers operation lists, measurement
projections, reset, and classical conditionals while preserving branch order,
multiplicity, and stored data.  The point-encoding and curve identities
connect the scalar computation to the public group specification.
Finite norm sums transfer branch probabilities.  A cost accumulator follows
the same execution, and normalization transfers the pathwise constant to
its expectation.  The independent-product identity supplies the repetition
bound.

The source pins Lean 4.34.0-rc2 and its dependencies.  The complete
statement comparison and independent Lean and unchanged NanoDa checks
accept the proof sources identified in the [verification guide](verification.md).
The transitive axiom set consists of propositional extensionality,
classical choice, and quotient soundness.  The guide gives source identity,
checker revisions, and reproduction commands.  The
[public statement](../Challenge.lean), [proof entry point](../Solution.lean),
and [comparison configuration](../comparator.json) identify the exact
declarations under review.

## Sources and authorship

The quantum computation follows the Fourier-sampling approach of
[Shor](https://doi.org/10.1137/S0097539795293172) and its elliptic-curve
formulation by [Proos and Zalka](https://doi.org/10.26421/QIC3.4-3).
The packed Euclidean design adapts the length-controlled register sharing
of [Luo and colleagues](https://arxiv.org/abs/2607.13816v2).
The endpoint selector follows the pruned prefix tree in their
[companion source](https://github.com/ZeroWang030221/Quantum-Algorithm-for-Elliptic-Curve-Discrete-Logarithms-with-Space-Efficient-Point-Addition/tree/e64aa3c1198d96aeb389e64bc7ae48edbb9712ec).
The repository contains the VQ arithmetic construction, its proof, and the
connection to the public statement.  Mathematical analysis, Lean development,
and document preparation used OpenAI Codex under maintainer direction.
The [metadata](../formalization.yaml) records authorship, automation, and
review.  Independent checker acceptance establishes the formal claims under
the recorded axioms.  Human peer review and a literature-based assessment
of novelty remain outstanding.
