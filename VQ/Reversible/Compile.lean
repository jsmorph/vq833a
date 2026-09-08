/-
Compilation of the reversible fragment into the primitive gate set.

`x` and `cx` are primitives already.  `ccx a b c` becomes `h c; ccz a b c; h c`,
which is `Circuit.ccx`, so the Toffoli costs one `ccz` and two Hadamards under
the counting basis and fifteen primitives with seven T gates under
`Circuit.expand`.

The count identities connect resource bounds over a compiled circuit with
correctness results over its reversible source.  Each
identity below reads the compiled gate list on the left and the reversible gate
list on the right, so the two numbers are two readings of one object.
-/
import VQ.Reversible.Act
import VQ.Circuit.Library

namespace VQ
namespace Reversible

open VQ.Circuit

/-- The primitives one reversible gate compiles to.  `ccx` routes through
`Circuit.ccx` rather than repeating its three gates, so there is one definition
of what a Toffoli is. -/
def compileGate : RGate → List Gate
  | .x q => [Gate.x q]
  | .cx a b => [Gate.cx a b]
  | .ccx a b c => Circuit.ccx a b c

/-- The circuit a reversible circuit compiles to.  The width is unchanged,
because no clause uses an ancilla. -/
def compile (r : RCircuit) : Circuit :=
  { width := r.width, gates := r.gates.flatMap compileGate }

theorem width_compile (r : RCircuit) : (compile r).width = r.width := rfl

theorem gates_compile (r : RCircuit) :
    (compile r).gates = r.gates.flatMap compileGate := rfl

/-! ## Compilation counts

Each identity is one induction over the reversible gate list, with the three
constructors settled by evaluation of `countP` on a list of at most three
primitives. -/

/-- Toffoli count.  `ccz` occurs once per `ccx` and in no other clause. -/
theorem toffoliCount_compile (r : RCircuit) :
    Circuit.toffoliCount (compile r) = r.gates.countP RGate.isCcx := by
  show (r.gates.flatMap compileGate).countP Gate.isCcz = _
  induction r.gates with
  | nil => rfl
  | cons g gs ih =>
    cases g <;>
      simp [List.flatMap_cons, List.countP_cons, ih, compileGate, Circuit.ccx,
        Gate.isCcz, RGate.isCcx]

/-- Gate count.  `x` and `cx` cost one primitive and `ccx` costs three, so
the compiled length is the reversible length plus two per Toffoli. -/
theorem gateCount_compile (r : RCircuit) :
    Circuit.gateCount (compile r) = r.gates.length + 2 * r.gates.countP RGate.isCcx := by
  show (r.gates.flatMap compileGate).length = _
  induction r.gates with
  | nil => rfl
  | cons g gs ih =>
    cases g <;>
      simp [List.flatMap_cons, List.countP_cons, ih, compileGate, Circuit.ccx, RGate.isCcx] <;>
      omega

/-- CNOT count.  `Gate.cx` is the only two-wire primitive and it comes only
from `RGate.cx`: the Toffoli's compilation is a `ccz` and two Hadamards, none of
which `Gate.isTwoQubit` counts. -/
theorem cnotCount_compile (r : RCircuit) :
    Circuit.cnotCount (compile r) = r.gates.countP RGate.isCx := by
  show (r.gates.flatMap compileGate).countP Gate.isTwoQubit = _
  induction r.gates with
  | nil => rfl
  | cons g gs ih =>
    cases g <;>
      simp [List.flatMap_cons, List.countP_cons, ih, compileGate, Circuit.ccx,
        Gate.isTwoQubit, RGate.isCx]

/-- Clifford count.  Reversible `x` and `cx` gates each compile to one
Clifford gate, while a reversible `ccx` compiles to two Hadamards and one
non-Clifford `ccz`. -/
theorem cliffordCount_compile (r : RCircuit) :
    Circuit.cliffordCount (compile r) =
      r.gates.length + r.gates.countP RGate.isCcx := by
  show (r.gates.flatMap compileGate).countP (fun g => !g.isNonClifford) = _
  induction r.gates with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatMap_cons, List.countP_append, ih, List.length_cons,
      List.countP_cons]
    cases g <;>
      simp [compileGate, Circuit.ccx, Gate.isNonClifford, RGate.isCcx] <;> omega

/-! ## Well-formedness -/

/-- Each primitive a well-formed gate compiles to is well formed at the same
width.  `h` is what forces the level condition, and `RGate.wellFormedAt` carries
it for exactly that reason. -/
theorem wellFormedAt_compileGate {g : RGate} {level w : Nat}
    (hg : g.wellFormedAt level w = true) {p : Gate} (hp : p ∈ compileGate g) :
    p.wellFormedAt level w = true := by
  cases g with
  | x q =>
    have hpe : p = Gate.x q := by simpa [compileGate] using hp
    subst hpe
    simpa [Gate.wellFormedAt, RGate.wellFormedAt] using hg
  | cx a b =>
    have hpe : p = Gate.cx a b := by simpa [compileGate] using hp
    subst hpe
    simpa [Gate.wellFormedAt, RGate.wellFormedAt] using hg
  | ccx a b c =>
    simp only [RGate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] at hg
    have hmem : p = Gate.h c ∨ p = Gate.ccz a b c ∨ p = Gate.h c := by
      simpa [compileGate, Circuit.ccx] using hp
    rcases hmem with rfl | rfl | rfl <;>
      simp only [Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq] <;> omega

/-- A circuit well formed at a level compiles to a circuit well formed at that
level. -/
theorem wellFormedAt_compile {level : Nat} {r : RCircuit} (h : r.wellFormedAt level = true) :
    (compile r).wellFormedAt level = true := by
  refine List.all_eq_true.mpr (fun p hp => ?_)
  obtain ⟨g, hg, hpg⟩ := List.exists_of_mem_flatMap hp
  exact wellFormedAt_compileGate (RCircuit.wellFormedAt_mem h hg) hpg

/-- The compilation of a well-formed reversible circuit is well formed at
level three.  Level three is the least the amplitude ring can carry, because
the Toffoli's compilation contains a Hadamard and `1 / √2` enters the ring
there. -/
theorem wellFormedAt_three_compile {r : RCircuit} (h : r.wellFormed = true) :
    (compile r).wellFormedAt 3 = true :=
  wellFormedAt_compile (RCircuit.wellFormedAt_of_wellFormed (by omega) h)

/-! ## Compilation wire support

A resource claim on `usedWires` is stated over the compiled circuit while
everything an author controls is the reversible one, so the two have to be tied
together the way the counts are.  Compilation introduces no wire: the Hadamards
of the Toffoli sit on its target. -/

/-- Every wire of every primitive a gate compiles to is a wire of the gate. -/
theorem wires_compileGate {g : RGate} {p : Gate} (hp : p ∈ compileGate g)
    {q : Nat} (hq : q ∈ p.wires) : q ∈ g.wires := by
  cases g with
  | x a => simp [compileGate] at hp; subst hp; simpa [Gate.wires, RGate.wires] using hq
  | cx a b => simp [compileGate] at hp; subst hp; simpa [Gate.wires, RGate.wires] using hq
  | ccx a b c =>
    have hm : p = Gate.h c ∨ p = Gate.ccz a b c ∨ p = Gate.h c := by
      simpa [compileGate, Circuit.ccx] using hp
    rcases hm with rfl | rfl | rfl
    · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq; simp [RGate.wires]
    · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      simpa [RGate.wires] using hq
    · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq; simp [RGate.wires]

/-- A reversible circuit whose wires all come from a list compiles to one that
uses at most that many wires.  The form a sparse component needs: its wire
indices grow with the width, its wire count does not. -/
theorem usedWires_compile_le_of_mem {r : RCircuit} {s : List Nat}
    (h : ∀ g ∈ r.gates, ∀ q ∈ g.wires, q ∈ s) :
    Circuit.usedWires (compile r) ≤ s.length := by
  refine Circuit.usedWires_le_of_mem (fun pg hp q hq => ?_)
  obtain ⟨g, hg, hpg⟩ := List.exists_of_mem_flatMap hp
  exact h g hg q (wires_compileGate hpg hq)

/-- A reversible circuit whose wires lie below `W` compiles to one that uses
at most `W` wires. -/
theorem usedWires_compile_le_of_lt {r : RCircuit} {W : Nat}
    (h : ∀ g ∈ r.gates, ∀ q ∈ g.wires, q < W) :
    Circuit.usedWires (compile r) ≤ W := by
  refine Circuit.usedWires_le_of_lt (fun p hp q hq => ?_)
  obtain ⟨g, hg, hpg⟩ := List.exists_of_mem_flatMap hp
  exact h g hg q (wires_compileGate hpg hq)

/-- The form a submission states: a well-formed circuit uses no more wires than
it declares. -/
theorem usedWires_compile_le_width {r : RCircuit} (h : r.wellFormed = true) :
    Circuit.usedWires (compile r) ≤ r.width := by
  refine usedWires_compile_le_of_lt (fun g hg q hq => ?_)
  have := RCircuit.wellFormed_mem h hg
  cases g <;> simp_all [RGate.wellFormed, RGate.wires] <;> omega

/-! ## Compiled T count

Expanding a compiled reversible circuit produces seven T gates per Toffoli.
The `x` and `cx` constructors compile to primitives with zero T gates.  Each
`ccx` compiles to one `ccz`, whose expansion contains seven T gates. -/

theorem tCount_expandGate_compileGate (g : RGate) :
    ((compileGate g).flatMap Circuit.expandGate).countP Gate.isT
      = 7 * (if g.isCcx then 1 else 0) := by
  cases g <;> rfl

/-- A compiled reversible circuit has seven T gates per Toffoli. -/
theorem expandedTCount_compile (r : RCircuit) :
    Circuit.expandedTCount (compile r) = 7 * r.gates.countP RGate.isCcx := by
  show ((r.gates.flatMap compileGate).flatMap Circuit.expandGate).countP Gate.isT = _
  induction r.gates with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatMap_cons, List.flatMap_append, List.countP_append, ih,
      tCount_expandGate_compileGate, List.countP_cons]
    cases h : g.isCcx <;> simp <;> omega

/-- The form a submission states, against its own Toffoli bound. -/
theorem expandedTCount_le {r : RCircuit} {C : Nat}
    (h : Circuit.toffoliCount (compile r) ≤ C) :
    Circuit.expandedTCount (compile r) ≤ 7 * C := by
  rw [expandedTCount_compile]
  rw [toffoliCount_compile] at h
  omega

end Reversible
end VQ
