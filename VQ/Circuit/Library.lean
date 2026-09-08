/-
Composite gates, expanded into primitives.

Every definition here expands a circuit into the primitive gate set.  The
selected Toffoli decomposition contributes seven T gates and six CNOTs to the
resource metrics.
-/
import VQ.Circuit.Resources

namespace VQ
namespace Circuit

open Gate

/--
The phase `exp (2 * pi * I / 2 ^ k)` on the `|1⟩` component of wire `q`, spelled
with whichever primitive is correct for `k`.  Levels zero through three are the
identity, `z`, `s`, and `t`.  Level four and above use `p`.  Routing through this
function is what keeps a caller from writing `p 3` and hiding a T gate from
`tCount`.
-/
def phase (k : Nat) (q : Nat) : List Gate :=
  match k with
  | 0 => []
  | 1 => [z q]
  | 2 => [s q]
  | 3 => [t q]
  | k + 4 => [p (k + 4) q]

/-- The inverse of `phase k q`. -/
def phaseInv (k : Nat) (q : Nat) : List Gate :=
  match k with
  | 0 => []
  | 1 => [z q]
  | 2 => [sdg q]
  | 3 => [tdg q]
  | k + 4 => [pdg (k + 4) q]

/-- Controlled-Z.  Two Hadamards and one CNOT use fewer gates than the phase
construction and introduce no non-Clifford gate. -/
def cz (a b : Nat) : List Gate :=
  [h b, cx a b, h b]

/-- Swap two wires.  Three CNOTs. -/
def swap (a b : Nat) : List Gate :=
  [cx a b, cx b a, cx a b]

/--
Controlled phase by `exp (2 * pi * I / 2 ^ k)`, which is `diag (1, 1, 1, ζ)`.

The construction is `P(k+1)` on each wire, then a CNOT, then `P(k+1)⁻¹` on the
target, then a CNOT.  On `|10⟩` and `|01⟩` the two half-phases cancel, and on
`|11⟩` they compose, so the result carries no spurious global phase.  For `k = 1`
this reduces to the phase form of controlled-Z, which uses two `s` gates, one
`sdg`, and two CNOTs.  The `cz` construction above uses three gates.
-/
def cphase (k : Nat) (a b : Nat) : List Gate :=
  phase (k + 1) a ++ phase (k + 1) b ++ [cx a b] ++ phaseInv (k + 1) b ++ [cx a b]

/--
CCZ in the Clifford+T basis: thirteen gates, seven T, six CNOTs.

Nielsen and Chuang figure 4.9 becomes this CCZ decomposition after removing the
two target Hadamards.  Seven is the known
minimum T count for a CCZ or a Toffoli without ancillas or measurement.
`Circuit.expand` rewrites every `ccz` into this list, and
`VQ.Semantics.denote_expand` proves the rewrite preserves the denotation.
-/
def cczT (a b c : Nat) : List Gate :=
  [ cx b c, tdg c
  , cx a c, t c
  , cx b c, tdg c
  , cx a c
  , t b, t c
  , cx a b, t a, tdg b
  , cx a b ]

/--
Toffoli: `h` on the target, `ccz`, `h` on the target.

A Toffoli counts as one Toffoli.  Under `Circuit.expand` it becomes fifteen
primitives with seven T gates.  The two counts describe the same operator under
different gate conventions.
-/
def ccx (a b c : Nat) : List Gate :=
  [h c] ++ [ccz a b c] ++ [h c]

/-- Toffoli in the Clifford+T basis: fifteen gates, seven T gates, six CNOTs,
and two Hadamards.  `ccx` denotes the same operator using one primitive `ccz`.
`expand (ofGates w (ccx a b c))` gives this decomposition with the two
Hadamards in different positions. -/
def ccxT (a b c : Nat) : List Gate :=
  [ h c
  , cx b c, tdg c
  , cx a c, t c
  , cx b c, tdg c
  , cx a c
  , t b, t c, h c
  , cx a b, t a, tdg b
  , cx a b ]

/-- Controlled-S, the `k = 2` case of `cphase`: three T gates and two CNOTs. -/
def cs (a b : Nat) : List Gate := cphase 2 a b

/--
The quantum Fourier transform on wires `w`, without the final wire reversal.

The list orders wires from most significant to least significant.  Wire `w[0]`
receives the first Hadamard, while wire `q` is bit `q` of a basis index.  Thus
`[0, 1, …, n-1]` yields `P · F · P` for the bit-reversal permutation `P`.  The
three-wire check gives `F` for `[2,1,0]`.  Wire `w[i]` receives a Hadamard and
controlled phases from every later wire.  A caller that consumes the output in
reverse order can omit the final swap gates. -/
def qftNoSwap (w : List Nat) : List Gate :=
  let rec go : List Nat → List Gate
    | [] => []
    | q :: rest =>
      h q :: (rest.zipIdx.flatMap fun (r, i) => cphase (i + 2) r q) ++ go rest
  go w

/-- The quantum Fourier transform on wires `w`, including the wire reversal
that puts the output in the same order as the input. -/
def qft (w : List Nat) : List Gate :=
  let n := w.length
  let pairs := (List.range (n / 2)).flatMap fun i =>
    match w[i]?, w[n - 1 - i]? with
    | some a, some b => swap a b
    | _, _ => []
  qftNoSwap w ++ pairs

/-- Build a circuit of the given width from a gate list. -/
def ofGates (width : Nat) (gs : List Gate) : Circuit := { width, gates := gs }

/-- One gate in the Clifford+T basis: `ccz` becomes its thirteen-gate
decomposition and every other primitive stands for itself. -/
def expandGate : Gate → List Gate
  | .ccz a b c => cczT a b c
  | g => [g]

/--
The same circuit with every `ccz` rewritten into Clifford+T.

The width is unchanged, because the decomposition uses no ancilla.  This is the
conversion between the two resource conventions: `toffoliCount c` and
`tCount (expand c)` measure the same circuit, and `VQ.Semantics.denote_expand`
proves that the two circuits denote the same matrix on the block their width
addresses.  Without that theorem the two numbers would be claims about two
unrelated objects.
-/
def expand (c : Circuit) : Circuit :=
  { width := c.width, gates := c.gates.flatMap expandGate }

/-!
## Expanded T counts

`ccz` is a primitive with two resource measures: a Toffoli count used by work
based on CCZ magic states, and a T count after decomposition into the elementary
basis.  One CCZ magic state converts into two T states, while the selected
decomposition contains seven T gates.  `tCount` gives zero for an unexpanded
`ccz`, and `expandedTCount` gives seven per `ccz`.

`VQ.Semantics.denote_expand` proves the expanded circuit denotes the same matrix
at level three or above.  The two metrics therefore describe semantically
equivalent representations of one circuit.
-/

/-- The T count after every `ccz` is rewritten into its seven-T form. -/
def expandedTCount (c : Circuit) : Nat := tCount (expand c)

/-- The gate count in the elementary basis, with no `ccz` left. -/
def expandedGateCount (c : Circuit) : Nat := gateCount (expand c)

/-- The T depth in the elementary basis. -/
def expandedTDepth (c : Circuit) : Nat := tDepth (expand c)

end Circuit
end VQ
