/-
Primitive gate set and circuit syntax.

Resource metrics are relative to a fixed gate basis.  Composite gates such as
CZ, SWAP, controlled phases, and multiply-controlled gates are expansions in
`VQ.Circuit.Library`.  Their counts therefore refer to the listed primitives.

`ccz` is primitive in this resource basis, which supports direct Toffoli counts.
Gidney and Fowler (arXiv:1812.01238) showed that one CCZ magic state converts
into two T states.  `toffoliCount` counts primitive `ccz` gates, while
`Circuit.expand` rewrites each one into thirteen primitives containing seven T
gates.  `VQ.Semantics.denote_expand` proves equality of the original and
expanded circuit matrices.
-/

namespace VQ

/--
A primitive gate.  Wire indices count from zero, and wire `q` is bit `q` of a
computational basis index.

`p k q` applies the phase `exp (2 * pi * I / 2 ^ k)` to the `|1⟩` component of
wire `q`, and `pdg k q` applies its inverse.  Well-formedness restricts `k` to
`4` and above, because `p 0`, `p 1`, `p 2`, and `p 3` are the identity, `z`,
`s`, and `t`, each of which has its own constructor.  Disjoint constructors make
`tCount` exact because `p 3` cannot provide an alternative T-gate encoding.

`ccz a b c` applies the phase `-1` to the one basis state where all three wires
are set.  It is diagonal, so it is symmetric in its three arguments and its
matrix is the identity with one entry negated.  `ccx`, the Toffoli, is
`h c; ccz a b c; h c` and is a library definition, so a Toffoli costs one `ccz`
and two Hadamards under this basis and thirteen primitives under `expand`.
-/
inductive Gate where
  | h   (q : Nat)
  | x   (q : Nat)
  | y   (q : Nat)
  | z   (q : Nat)
  | s   (q : Nat)
  | sdg (q : Nat)
  | t   (q : Nat)
  | tdg (q : Nat)
  | p   (k : Nat) (q : Nat)
  | pdg (k : Nat) (q : Nat)
  | cx  (ctrl : Nat) (tgt : Nat)
  | ccz (a : Nat) (b : Nat) (c : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Gate

/-- The wires a gate acts on, in no particular order. -/
def wires : Gate → List Nat
  | h q | x q | y q | z q | s q | sdg q | t q | tdg q => [q]
  | p _ q | pdg _ q => [q]
  | cx a b => [a, b]
  | ccz a b c => [a, b, c]

/-- Gates that act on two wires.  `ccz` acts on three and is not one of them. -/
def isTwoQubit : Gate → Bool
  | cx _ _ => true
  | _ => false

/-- Gates outside the Clifford group.  `ccz` belongs here: it sits in the third
level of the Clifford hierarchy, and a circuit of Cliffords and CCZ gates is no
more classically simulable than a Clifford+T circuit. -/
def isNonClifford : Gate → Bool
  | t _ | tdg _ | p _ _ | pdg _ _ | ccz _ _ _ => true
  | _ => false

/-- Occurrences of `t` and `tdg`.  Phase gates at level four and above are
counted separately by `phaseCount`, because their cost in T gates depends on the
synthesis method and is not one.  `ccz` is likewise counted separately, by
`toffoliCount`: it costs seven T gates to decompose and two T states to distil,
and folding either number into `tCount` would conflate those resource models. -/
def isT : Gate → Bool
  | t _ | tdg _ => true
  | _ => false

/-- Occurrences of the `p` and `pdg` constructors.  T gates have their own
counter.  Primitive `ccz` gates contribute to `toffoliCount`. -/
def isPhase : Gate → Bool
  | p _ _ | pdg _ _ => true
  | _ => false

/-- Occurrences of `ccz`, which is one Toffoli's worth of non-Clifford work. -/
def isCcz : Gate → Bool
  | ccz _ _ _ => true
  | _ => false

/-- The inverse gate.  `Gate.adjoint` is an involution on the primitive set. -/
def adjoint : Gate → Gate
  | h q => h q
  | x q => x q
  | y q => y q
  | z q => z q
  | s q => sdg q
  | sdg q => s q
  | t q => tdg q
  | tdg q => t q
  | p k q => pdg k q
  | pdg k q => p k q
  | cx a b => cx a b
  | ccz a b c => ccz a b c

/-- Apply a wire relabelling. -/
def map (f : Nat → Nat) : Gate → Gate
  | h q => h (f q)
  | x q => x (f q)
  | y q => y (f q)
  | z q => z (f q)
  | s q => s (f q)
  | sdg q => sdg (f q)
  | t q => t (f q)
  | tdg q => tdg (f q)
  | p k q => p k (f q)
  | pdg k q => pdg k (f q)
  | cx a b => cx (f a) (f b)
  | ccz a b c => ccz (f a) (f b) (f c)

/-- Every wire index is below `w`, the wires of a multi-wire gate are distinct,
and phase levels are at least four. -/
def wellFormed (w : Nat) : Gate → Bool
  | h q | x q | y q | z q | s q | sdg q | t q | tdg q => q < w
  | p k q | pdg k q => q < w && 4 ≤ k
  | cx a b => a < w && b < w && a ≠ b
  | ccz a b c => a < w && b < w && c < w && a ≠ b && b ≠ c && a ≠ c

/--
Well-formedness at a phase level.

Every gate carries a phase, and a phase lies in the amplitude ring only when the
ring's level is high enough to hold it.  `p 4` at level 3 has an entry outside
`R(3)`, so a gate list containing it has no semantics there, and
`Gate.wellFormed` cannot rule that out because it does not see the level.

The minimum levels ensure that each gate's phase belongs to the amplitude ring.
Without the `t` restriction, `t q` would pass at level 2, where
`exp(2 pi i / 8)` is outside the ring: the phase is computed as
`zeta ^ 2 ^ (level - 3)`, truncated subtraction turns the exponent into zero,
and the gate silently denotes `zeta` rather than its own phase.  A correctness
claim could then be verified against a semantics that misassigns phases.  `h`
needs level three for the same reason: `invSqrt2` is a square root of one half
only when four divides the degree, and the degree is `2 ^ (level - 1)`.

`ccz` needs level one, like `z`, and for the same reason: the only amplitude it
introduces is `-1`, which lies in `R(k)` for every `k ≥ 1`.  Its own expansion
into T gates needs level three, and that is a fact about the expansion rather
than about the gate.  `denote_expand` therefore carries `3 ≤ level` as a
hypothesis while this predicate does not.  A circuit of Cliffords and CCZ gates
has exact semantics at level one.  Rewriting it into the T basis requires the
eighth root of unity.
-/
def wellFormedAt (level w : Nat) : Gate → Bool
  | x q => q < w
  | z q => q < w && 1 ≤ level
  | y q | s q | sdg q => q < w && 2 ≤ level
  | h q | t q | tdg q => q < w && 3 ≤ level
  | p k q | pdg k q => q < w && 4 ≤ k && k ≤ level
  | cx a b => a < w && b < w && a ≠ b
  | ccz a b c => a < w && b < w && c < w && a ≠ b && b ≠ c && a ≠ c && 1 ≤ level

/-- Widening the wire count preserves well-formedness.  A circuit family whose
width grows with its parameter needs this at every inductive step, since the
gates carried over from the previous step were checked against a smaller
width. -/
theorem wellFormed_mono {g : Gate} {w w' : Nat} (hw : w ≤ w')
    (h : g.wellFormed w = true) : g.wellFormed w' = true := by
  cases g <;> simp_all [Gate.wellFormed] <;> omega

end Gate

/--
A circuit is a declared wire count together with an ordered gate list.  The
list reads left to right in time order, so `⟦[g₀, g₁]⟧` is the matrix product
`⟦g₁⟧ * ⟦g₀⟧`.
-/
structure Circuit where
  width : Nat
  gates : List Gate
  deriving DecidableEq, Repr, Inhabited

namespace Circuit

/-- Every gate acts within the declared width and satisfies its own
constraints.  Semantics remain total by assigning the zero map to an
out-of-range gate.  This predicate gives the author a separate obligation that
identifies an invalid wire index. -/
def wellFormed (c : Circuit) : Bool :=
  c.gates.all (Gate.wellFormed c.width)

instance (c : Circuit) : Decidable (c.wellFormed = true) :=
  inferInstanceAs (Decidable (_ = true))

/-- Widening a circuit preserves well-formedness. -/
theorem wellFormed_widen {gs : List Gate} {w w' : Nat} (hw : w ≤ w')
    (h : (Circuit.mk w gs).wellFormed = true) : (Circuit.mk w' gs).wellFormed = true := by
  simp only [Circuit.wellFormed, List.all_eq_true] at *
  intro g hg
  exact Gate.wellFormed_mono hw (h g hg)

/-- Every gate acts within the declared width and at a phase level the
amplitude ring can carry. -/
def wellFormedAt (level : Nat) (c : Circuit) : Bool :=
  c.gates.all (Gate.wellFormedAt level c.width)

/-- Widening the wire count preserves well-formedness at a fixed phase level.
A family whose width grows with its parameter needs this at every inductive
step.  It is the level-aware counterpart of `wellFormed_widen`: the level is a
property of the amplitude ring and does not change with the width. -/
theorem wellFormedAt_widen {gs : List Gate} {level w w' : Nat} (hw : w ≤ w')
    (h : (Circuit.mk w gs).wellFormedAt level = true) :
    (Circuit.mk w' gs).wellFormedAt level = true := by
  simp only [Circuit.wellFormedAt, List.all_eq_true] at *
  intro g hg
  have hgg := h g hg
  cases g <;> simp_all [Gate.wellFormedAt] <;> omega

/-- Sequential composition.  Both circuits must already have the same width.
`append` on differing widths takes the larger, which keeps the operation total
without changing the semantics of well-formed arguments. -/
def append (a b : Circuit) : Circuit :=
  { width := max a.width b.width, gates := a.gates ++ b.gates }

instance : Append Circuit := ⟨append⟩

/-- The empty circuit on `w` wires. -/
def id (w : Nat) : Circuit := { width := w, gates := [] }

/-- The inverse circuit: every gate inverted, in reverse order. -/
def adjoint (c : Circuit) : Circuit :=
  { width := c.width, gates := (c.gates.map Gate.adjoint).reverse }

/-- Relabel every wire.  Used to place a subcircuit on chosen wires. -/
def relabel (f : Nat → Nat) (w : Nat) (c : Circuit) : Circuit :=
  { width := w, gates := c.gates.map (Gate.map f) }

end Circuit

end VQ
