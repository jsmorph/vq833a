/-
Resource metrics.

Every metric is a computable function of the gate list, so a concrete bound is
decided by evaluation and a bound on a circuit family is proven by induction.
The scheduling metrics use a per-wire level vector rather than a hash map: the
vector has a deterministic fold order, supports induction directly, and costs
one traversal of the wire count per gate.
-/
import VQ.Circuit.Syntax

namespace VQ
namespace Circuit

/-- Total primitive gate count. -/
def gateCount (c : Circuit) : Nat := c.gates.length

/-- Occurrences of `t` and `tdg`. -/
def tCount (c : Circuit) : Nat :=
  c.gates.countP Gate.isT

/-- Occurrences of `p` and `pdg`, which are the non-Clifford phase gates at
level four and above.  Their cost in T gates depends on the synthesis method,
so they are reported separately rather than folded into `tCount`.

`phaseCount` reads the phase-gate constructors directly and counts `ccz`
separately through `toffoliCount`. -/
def phaseCount (c : Circuit) : Nat :=
  c.gates.countP Gate.isPhase

/--
Occurrences of `ccz`, which is the Toffoli count.

Work following Gidney and Fowler (arXiv:1812.01238) reports this unit because
one CCZ magic state yields two T states and a factory can distil Toffolis
directly.  A four-Toffoli circuit has `toffoliCount = 4` and, after
`Circuit.expand`, `tCount = 28`.  `VQ.Semantics.denote_expand` proves that
these gate-basis representations denote the same operator. -/
def toffoliCount (c : Circuit) : Nat :=
  c.gates.countP Gate.isCcz

/-- Occurrences of any gate outside the Clifford group. -/
def nonCliffordCount (c : Circuit) : Nat :=
  c.gates.countP Gate.isNonClifford

/-- Occurrences of Clifford gates. -/
def cliffordCount (c : Circuit) : Nat :=
  c.gates.countP fun g => !g.isNonClifford

/-- Occurrences of CNOT, the only two-wire primitive.  Named for what it counts
rather than for the class it happens to exhaust, since a later primitive set
with a second two-wire gate would make the general name wrong. -/
def cnotCount (c : Circuit) : Nat :=
  c.gates.countP Gate.isTwoQubit

theorem cliffordCount_le_gateCount (c : Circuit) :
    c.cliffordCount ≤ c.gateCount :=
  List.countP_le_length

theorem cnotCount_le_gateCount (c : Circuit) :
    c.cnotCount ≤ c.gateCount :=
  List.countP_le_length

/-- Per-wire scheduling levels, indexed by wire.  Wires at or beyond the length
read as level zero.  A gate naming a wire outside the declared width denotes the
zero map and contributes no layer. -/
abbrev Levels := List Nat

namespace Levels

def get (l : Levels) (q : Nat) : Nat := l.getD q 0

def peak (l : Levels) : Nat := l.foldl max 0

/-- The latest level occupied by any wire in `ws`. -/
def base (l : Levels) (ws : List Nat) : Nat :=
  ws.foldl (fun acc q => max acc (l.get q)) 0

/-- Set every wire of `ws` to `n`, ignoring wires outside the vector. -/
def setAll (l : Levels) (ws : List Nat) (n : Nat) : Levels :=
  ws.foldl (fun m q => m.set q n) l

/-- Advance every wire of `ws` past the latest of them, consuming a layer. -/
def step (l : Levels) (ws : List Nat) : Levels :=
  l.setAll ws (l.base ws + 1)

/-- Bring every wire of `ws` up to the latest of them without consuming a
layer.  A gate outside a counted class still orders the counted gates on its
wires, and this records that ordering without contributing depth. -/
def sync (l : Levels) (ws : List Nat) : Levels :=
  l.setAll ws (l.base ws)

end Levels

/-- A level vector with every wire at zero. -/
def initialLevels (c : Circuit) : Levels := List.replicate c.width 0

/--
Circuit depth: the number of layers under as-soon-as-possible scheduling, which
is the length of the longest chain of gates ordered by shared wires.  This is
the critical path of the circuit's dependency graph.
-/
def depth (c : Circuit) : Nat :=
  (c.gates.foldl (fun l g => l.step g.wires) c.initialLevels).peak

/--
Depth restricted to the gates satisfying `pred`.  Gates outside the class order
the ones inside it but do not consume a layer, so the result is the longest
chain of in-class gates.
-/
def depthOf (pred : Gate → Bool) (c : Circuit) : Nat :=
  (c.gates.foldl
    (fun l g => if pred g then l.step g.wires else l.sync g.wires)
    c.initialLevels).peak

/-- T-depth is the number of layers of T and T† gates.  In a resource model
where Clifford layers do not limit latency and each T gate consumes a distilled
magic state, T-depth bounds the corresponding latency. -/
def tDepth (c : Circuit) : Nat := depthOf Gate.isT c

/-- Depth counted over all non-Clifford gates. -/
def nonCliffordDepth (c : Circuit) : Nat := depthOf Gate.isNonClifford c

/--
Toffoli depth counts layers of `ccz`, the primitive emitted for each reversible
Toffoli.  Reversible-arithmetic resource estimates report this measure beside
the Toffoli count because surface-code distillation latency depends on the
number of sequential layers.

On a circuit that came from `Reversible.compile` this agrees with
`nonCliffordDepth`, since `ccz` is the only non-Clifford gate the compiler emits
and the Hadamards around it order the `ccz` gates without consuming a layer.  It
is a separate metric because a hand-written circuit may mix `t` and `p` gates
into the same list, and then the two differ.
-/
def toffoliDepth (c : Circuit) : Nat := depthOf Gate.isCcz c

/-- Wires beyond the `logical` wires named by the specification.  Cleanup
requires a separate semantic obligation that these wires return to `|0⟩`. -/
def ancillaCount (logical : Nat) (c : Circuit) : Nat := c.width - logical

/--
Every metric here is an upper bound on this gate list, under all-to-all
connectivity.  A certified `tCount ≤ B` bounds the supplied circuit, while the
minimum T count over equivalent circuits requires separate lower-bound or
optimization results.  Depth and `cnotCount` assume that any pair of wires can
interact.  Routing on fixed connectivity can increase both metrics.
-/
def resourceNote : String :=
  "upper bounds on the given gate list, assuming all-to-all connectivity"


/-- A gate kind ignores wire indices.  It partitions constructors more finely
than the class metrics.  For example, `cliffordCount` combines Hadamards with
the other Clifford gates. -/
inductive GateKind where
  | h | x | y | z | s | sdg | t | tdg | p | pdg | cx | ccz
  deriving DecidableEq, Repr, Inhabited

namespace GateKind

def key : GateKind → String
  | h => "h" | x => "x" | y => "y" | z => "z"
  | s => "s" | sdg => "sdg" | t => "t" | tdg => "tdg"
  | p => "p" | pdg => "pdg" | cx => "cx" | ccz => "ccz"

def all : List GateKind := [h, x, y, z, s, sdg, t, tdg, p, pdg, cx, ccz]

def ofKey? (str : String) : Option GateKind := all.find? fun k => k.key == str

end GateKind

/-- The kind of a gate.  Phase gates map to `p` and `pdg` at every level.  Their
level-independent class total remains available through `phaseCount`. -/
def _root_.VQ.Gate.kind : Gate → GateKind
  | .h _ => .h | .x _ => .x | .y _ => .y | .z _ => .z
  | .s _ => .s | .sdg _ => .sdg | .t _ => .t | .tdg _ => .tdg
  | .p _ _ => .p | .pdg _ _ => .pdg | .cx _ _ => .cx | .ccz _ _ _ => .ccz

/-- Occurrences of one kind of gate. -/
def countKind (k : GateKind) (c : Circuit) : Nat :=
  c.gates.countP fun g => g.kind == k

/-- The wires the circuit touches, without repetition.  The order is
unspecified.  Only the length is used. -/
def wiresUsed (c : Circuit) : List Nat :=
  (c.gates.flatMap Gate.wires).eraseDups

/--
The number of distinct wires the circuit touches.

`usedWires` counts wires carrying at least one operation.  `width` records the
declared register size.  A circuit may declare ten wires and touch three.  The
model allocates the full register for the circuit's duration, so a well-formed
circuit has peak live logical-qubit count `width`.
-/
def usedWires (c : Circuit) : Nat := c.wiresUsed.length

/-- One more than the largest wire index the circuit touches, or zero for a
circuit with no gates.  A well-formed circuit satisfies `wireBound c ≤ width c`,
and the gap is declared wires that are never used. -/
def wireBound (c : Circuit) : Nat :=
  c.gates.foldl (fun acc g => g.wires.foldl (fun a q => max a (q + 1)) acc) 0

/-! ## Bounding the wires a circuit uses

`usedWires` counts a deduplicated list, so bounding it is a pigeonhole: a list
with no repeats whose entries all come from a list of `K` entries has at most
`K` entries.  This property reduces circuit wire bounds to membership in a
finite range. -/

/-- A deduplicated list drawn from `s` is no longer than `s`.  The induction is
on a bound for `s.length` rather than on `s`, since the step removes an element
from `s` and filters `l`. -/
theorem eraseDups_length_le : ∀ (K : Nat) (s l : List Nat), s.length ≤ K →
    (∀ x ∈ l, x ∈ s) → l.eraseDups.length ≤ s.length := by
  intro K
  induction K with
  | zero =>
    intro s l hs hl
    cases l with
    | nil => simp
    | cons a as =>
      have hnil : s = [] := List.eq_nil_of_length_eq_zero (by omega)
      have := hl a List.mem_cons_self
      rw [hnil] at this
      exact absurd this (by simp)
  | succ K ih =>
    intro s l hs hl
    cases l with
    | nil => simp
    | cons a as =>
      have ha : a ∈ s := hl a List.mem_cons_self
      have hlen : (s.erase a).length + 1 = s.length := by
        rw [List.length_erase_of_mem ha]
        have hpos : 0 < s.length := by
          cases s with
          | nil => exact absurd ha (by simp)
          | cons x xs => simp
        omega
      have hsub : ∀ x ∈ as.filter (fun b => !b == a), x ∈ s.erase a := by
        intro x hx
        have hx' := List.mem_filter.mp hx
        have hne : x ≠ a := by
          have h2 := hx'.2
          simp at h2
          exact h2
        exact (List.mem_erase_of_ne hne).mpr (hl x (List.mem_cons_of_mem a hx'.1))
      have hrec := ih (s.erase a) (as.filter (fun b => !b == a)) (by omega) hsub
      rw [List.eraseDups_cons, List.length_cons]
      omega

/-- A circuit whose wires all come from a list uses at most that many.

`usedWires_le_of_mem` applies to sparse circuits.  A component holding its operand on
wires `0` to `k - 1` and its workspace on wires `n` to `n + w` has no constant
bound on its wire *indices*, but it has a constant bound on their *number*, and
`usedWires` counts the number. -/
theorem usedWires_le_of_mem {c : Circuit} {s : List Nat}
    (h : ∀ g ∈ c.gates, ∀ q ∈ g.wires, q ∈ s) : c.usedWires ≤ s.length := by
  refine eraseDups_length_le s.length s (c.gates.flatMap Gate.wires) (Nat.le_refl _) ?_
  intro x hx
  obtain ⟨g, hg, hq⟩ := List.exists_of_mem_flatMap hx
  exact h g hg x hq

/-- A circuit whose wires all lie below `W` uses at most `W` wires.  Resource
claims apply this theorem to a declared register width. -/
theorem usedWires_le_of_lt {c : Circuit} {W : Nat}
    (h : ∀ g ∈ c.gates, ∀ q ∈ g.wires, q < W) : c.usedWires ≤ W := by
  have hsub : ∀ x ∈ c.gates.flatMap Gate.wires, x ∈ List.range W := by
    intro x hx
    obtain ⟨g, hg, hq⟩ := List.exists_of_mem_flatMap hx
    exact List.mem_range.mpr (h g hg x hq)
  have := eraseDups_length_le W (List.range W) (c.gates.flatMap Gate.wires)
    (Nat.le_of_eq List.length_range) hsub
  rw [List.length_range] at this
  exact this

end Circuit
end VQ
