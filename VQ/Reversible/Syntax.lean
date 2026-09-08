/-
Syntax for the classical reversible fragment.

Every arithmetic component in this fragment is a permutation of the
computational basis, and its correctness is a statement about natural
numbers rather than about amplitudes.  A separate syntax for that fragment is
used by correctness proofs in `Nat`: `VQ.Reversible.act` is the
permutation, `VQ.Reversible.compile` is the circuit, and
`VQ.Reversible.Denote` is the one place the two meet.  Reasoning about a
256-bit adder through `Vec` would require the state, and the state has `2 ^ 256`
amplitudes.

The gate set is `x`, `cx`, and `ccx`, which generates every reversible function
given ancillas.  `ccx` is the Toffoli, and it is a constructor here so its count
remains explicit.  Its compilation costs one `ccz` and two Hadamards, which is
where the level-three condition below comes from.
-/

namespace VQ
namespace Reversible

/--
A classical reversible gate.  Wire indices count from zero, and wire `q` is bit
`q` of a computational basis index, the same convention `VQ.Gate` uses.

`x q` flips wire `q`.  `cx ctrl tgt` flips `tgt` when `ctrl` is set.
`ccx a b c` flips `c` when `a` and `b` are both set.
-/
inductive RGate where
  | x   (q : Nat)
  | cx  (ctrl : Nat) (tgt : Nat)
  | ccx (a : Nat) (b : Nat) (c : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace RGate

/-- The wires a gate acts on, in no particular order. -/
def wires : RGate → List Nat
  | x q => [q]
  | cx a b => [a, b]
  | ccx a b c => [a, b, c]

/-- Occurrences of the Toffoli.  This is the predicate the count identities in
`VQ.Reversible.Compile` are stated over, so a bound on a reversible circuit's
Toffoli count and a bound on its compilation's are the same number. -/
def isCcx : RGate → Bool
  | ccx _ _ _ => true
  | _ => false

/-- Occurrences of the CNOT, which is the only two-wire gate here and compiles
to the only two-wire primitive. -/
def isCx : RGate → Bool
  | cx _ _ => true
  | _ => false

/-- Apply a wire relabelling.  The classical analogue of `Gate.map`, and the
operation that places a component on chosen wires. -/
def map (f : Nat → Nat) : RGate → RGate
  | x q => x (f q)
  | cx a b => cx (f a) (f b)
  | ccx a b c => ccx (f a) (f b) (f c)

/-- Every wire index is below `w` and the wires of a multi-wire gate are
distinct.  Distinctness makes the gate a permutation: `cx a a` would
read and write one bit at once, and the action defined in `VQ.Reversible.Act`
would not be injective. -/
def wellFormed (w : Nat) : RGate → Bool
  | x q => q < w
  | cx a b => a < w && b < w && a ≠ b
  | ccx a b c => a < w && b < w && c < w && a ≠ b && b ≠ c && a ≠ c

/--
Well-formedness at a phase level.

The classical action ignores the level, so this predicate is about the
compilation rather than about the gate, in the same way `Gate.wellFormedAt`
carries what the amplitude ring must hold.  `x` and `cx` compile to primitives
that are exact at every level.  `ccx` compiles through two Hadamards, and
`Gate.wellFormedAt` requires level three of an `h`, so a `ccx` compiled below
level three denotes the zero map.  This predicate permits
`compile_wellFormedAt` to quantify over an arbitrary level.
-/
def wellFormedAt (level w : Nat) : RGate → Bool
  | x q => q < w
  | cx a b => a < w && b < w && a ≠ b
  | ccx a b c => a < w && b < w && c < w && a ≠ b && b ≠ c && a ≠ c && 3 ≤ level

/-- Widening the wire count preserves well-formedness.  A component placed in a
wider register needs this, since its gates were checked against the narrower
width. -/
theorem wellFormed_mono {g : RGate} {w w' : Nat} (hw : w ≤ w')
    (h : g.wellFormed w = true) : g.wellFormed w' = true := by
  cases g <;> simp_all [RGate.wellFormed] <;> omega

/-- At level three and above the two predicates agree, because the only level
condition either one carries is the Hadamard's. -/
theorem wellFormedAt_of_wellFormed {g : RGate} {level w : Nat} (hl : 3 ≤ level)
    (h : g.wellFormed w = true) : g.wellFormedAt level w = true := by
  cases g <;> simp_all [RGate.wellFormed, RGate.wellFormedAt]

/-- Well-formedness at a level is well-formedness, whatever the level. -/
theorem wellFormed_of_wellFormedAt {g : RGate} {level w : Nat}
    (h : g.wellFormedAt level w = true) : g.wellFormed w = true := by
  cases g <;> simp_all [RGate.wellFormed, RGate.wellFormedAt]

/-- Relabelling a gate relabels its wires. -/
theorem wires_map (f : Nat → Nat) (g : RGate) : (g.map f).wires = g.wires.map f := by
  cases g <;> rfl

/-- Relabelling preserves the kind of a gate, so it preserves every count. -/
theorem isCcx_map (f : Nat → Nat) (g : RGate) : (g.map f).isCcx = g.isCcx := by
  cases g <;> rfl

theorem isCx_map (f : Nat → Nat) (g : RGate) : (g.map f).isCx = g.isCx := by
  cases g <;> rfl

/-- A relabelling landing below `w'` and injective below `w` preserves
well-formedness.  Injectivity is spent on the distinctness clause alone, which
is the clause that makes the action injective. -/
theorem wellFormed_map {g : RGate} {w w' : Nat} {f : Nat → Nat}
    (hlt : ∀ q, q < w → f q < w')
    (hinj : ∀ x y, x < w → y < w → f x = f y → x = y)
    (h : g.wellFormed w = true) : (g.map f).wellFormed w' = true := by
  cases g with
  | x q =>
    simp only [RGate.map, RGate.wellFormed, decide_eq_true_eq] at h ⊢
    exact hlt q h
  | cx a b =>
    simp only [RGate.map, RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨ha, hb⟩, hab⟩ := h
    exact ⟨⟨hlt a ha, hlt b hb⟩, fun e => hab (hinj a b ha hb e)⟩
  | ccx a b c =>
    simp only [RGate.map, RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hbc⟩, hac⟩ := h
    exact ⟨⟨⟨⟨⟨hlt a ha, hlt b hb⟩, hlt c hc⟩,
      fun e => hab (hinj a b ha hb e)⟩,
      fun e => hbc (hinj b c hb hc e)⟩,
      fun e => hac (hinj a c ha hc e)⟩


/-- Placing a component at an offset: a gate well formed in a `w`-wire register
is well formed after a shift by `δ`, in any register wide enough to hold the
shifted block.  A constant shift is injective, which is the distinctness
clause. -/
theorem wellFormed_map_add {g : RGate} {w δ W : Nat} (hW : δ + w ≤ W)
    (h : g.wellFormed w = true) : (g.map (· + δ)).wellFormed W = true :=
  wellFormed_map (fun q hq => by omega) (fun x y _ _ hxy => by omega) h

end RGate

/--
A reversible circuit is a declared wire count together with an ordered gate
list.  The list reads left to right in time order, so the action of `[g₀, g₁]`
is the action of `g₁` after the action of `g₀`, matching `VQ.Circuit`.
-/
structure RCircuit where
  width : Nat
  gates : List RGate
  deriving DecidableEq, Repr, Inhabited

namespace RCircuit

/-- Every gate acts within the declared width and on distinct wires.  The action
is defined for every circuit, so this is an obligation a caller discharges rather
than a precondition the definitions rely on.  Without it the action is still a
function and is no longer injective. -/
def wellFormed (r : RCircuit) : Bool :=
  r.gates.all (RGate.wellFormed r.width)

instance (r : RCircuit) : Decidable (r.wellFormed = true) :=
  inferInstanceAs (Decidable (_ = true))

/-- Every gate acts within the declared width and at a phase level its
compilation can carry. -/
def wellFormedAt (level : Nat) (r : RCircuit) : Bool :=
  r.gates.all (RGate.wellFormedAt level r.width)

instance (level : Nat) (r : RCircuit) : Decidable (r.wellFormedAt level = true) :=
  inferInstanceAs (Decidable (_ = true))

/-- Each gate of a well-formed circuit is well formed at the declared width.
The inductions in `VQ.Reversible.Act` use this membership form. -/
theorem wellFormed_mem {r : RCircuit} (h : r.wellFormed = true) {g : RGate}
    (hg : g ∈ r.gates) : g.wellFormed r.width = true :=
  (List.all_eq_true.mp h) g hg

theorem wellFormedAt_mem {level : Nat} {r : RCircuit} (h : r.wellFormedAt level = true)
    {g : RGate} (hg : g ∈ r.gates) : g.wellFormedAt level r.width = true :=
  (List.all_eq_true.mp h) g hg

/-- At level three and above the two circuit predicates agree. -/
theorem wellFormedAt_of_wellFormed {level : Nat} {r : RCircuit} (hl : 3 ≤ level)
    (h : r.wellFormed = true) : r.wellFormedAt level = true :=
  List.all_eq_true.mpr (fun _ hg => RGate.wellFormedAt_of_wellFormed hl (wellFormed_mem h hg))

theorem wellFormed_of_wellFormedAt {level : Nat} {r : RCircuit}
    (h : r.wellFormedAt level = true) : r.wellFormed = true :=
  List.all_eq_true.mpr (fun _ hg => RGate.wellFormed_of_wellFormedAt (wellFormedAt_mem h hg))

/-- Sequential composition at a common width.  Both circuits must already have
the same width.  `append` on differing widths takes the larger, which keeps the
operation total without changing the action of well-formed arguments. -/
def append (a b : RCircuit) : RCircuit :=
  { width := max a.width b.width, gates := a.gates ++ b.gates }

instance : Append RCircuit := ⟨append⟩

/-- The empty circuit on `w` wires, whose action is the identity. -/
def id (w : Nat) : RCircuit := { width := w, gates := [] }

/-- Relabel every wire and declare a new width.  The classical analogue of
`Circuit.relabel`, and the operation that places a component inside a wider
circuit.  `VQ.Reversible.act_relabel` says what it does to the action. -/
def relabel (f : Nat → Nat) (w : Nat) (r : RCircuit) : RCircuit :=
  { width := w, gates := r.gates.map (RGate.map f) }

theorem gates_relabel (f : Nat → Nat) (w : Nat) (r : RCircuit) :
    (relabel f w r).gates = r.gates.map (RGate.map f) := rfl

/-- A relabelling that maps the wires below `r.width` injectively into the wires
below `w'` carries well-formedness to `w'`.  This is the placement lemma: a
component proved well formed on its own wires stays well formed wherever an
injective assignment puts it. -/
theorem wellFormed_relabel {r : RCircuit} {f : Nat → Nat} {w' : Nat}
    (hlt : ∀ q, q < r.width → f q < w')
    (hinj : ∀ x y, x < r.width → y < r.width → f x = f y → x = y)
    (h : r.wellFormed = true) : (relabel f w' r).wellFormed = true := by
  simp only [RCircuit.wellFormed, gates_relabel, List.all_eq_true, List.mem_map] at h ⊢
  rintro g ⟨g', hg', rfl⟩
  exact RGate.wellFormed_map hlt hinj (h g' hg')

end RCircuit

/-- A count over a relabelled gate list, for any predicate the relabelling
leaves alone. -/
theorem countP_map_gates {f : Nat → Nat} {p : RGate → Bool}
    (hp : ∀ g, p (RGate.map f g) = p g) (gs : List RGate) :
    (gs.map (RGate.map f)).countP p = gs.countP p := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [List.map_cons, List.countP_cons, List.countP_cons, ih, hp]

end Reversible
end VQ
