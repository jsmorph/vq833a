/-
Proof-carrying symbolic resource bounds for the reversible fragment and its
standard compilation path.  The certificate records upper bounds on one gate
list, and its constructors follow the list operations used by circuit families.
Compilation and program embedding cite the existing exact resource identities.
-/
import VQ.Reversible.Compile
import VQ.Program.OfCircuit

namespace VQ.Resource

open Reversible

structure ReversibleBounds where
  gates : Nat
  ccx : Nat
  cx : Nat
  deriving DecidableEq, Repr

namespace ReversibleBounds

def zero : ReversibleBounds :=
  { gates := 0, ccx := 0, cx := 0 }

def singleton (g : RGate) : ReversibleBounds :=
  { gates := 1,
    ccx := if g.isCcx then 1 else 0,
    cx := if g.isCx then 1 else 0 }

def add (a b : ReversibleBounds) : ReversibleBounds :=
  { gates := a.gates + b.gates,
    ccx := a.ccx + b.ccx,
    cx := a.cx + b.cx }

def scale (n : Nat) (b : ReversibleBounds) : ReversibleBounds :=
  { gates := n * b.gates,
    ccx := n * b.ccx,
    cx := n * b.cx }

end ReversibleBounds

structure ReversibleCertificate (gs : List RGate)
    (bound : ReversibleBounds) : Prop where
  gates_le : gs.length ≤ bound.gates
  ccx_le : gs.countP RGate.isCcx ≤ bound.ccx
  cx_le : gs.countP RGate.isCx ≤ bound.cx

namespace ReversibleCertificate

theorem nil : ReversibleCertificate [] ReversibleBounds.zero :=
  ⟨Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0⟩

theorem singleton (g : RGate) :
    ReversibleCertificate [g] (ReversibleBounds.singleton g) := by
  cases g <;> constructor <;>
    simp [ReversibleBounds.singleton, RGate.isCcx, RGate.isCx]

theorem exact (gs : List RGate) :
    ReversibleCertificate gs
      { gates := gs.length,
        ccx := gs.countP RGate.isCcx,
        cx := gs.countP RGate.isCx } :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem append {as bs : List RGate} {a b : ReversibleBounds}
    (ha : ReversibleCertificate as a) (hb : ReversibleCertificate bs b) :
    ReversibleCertificate (as ++ bs) (a.add b) := by
  constructor
  · simpa [ReversibleBounds.add] using Nat.add_le_add ha.gates_le hb.gates_le
  · simpa [ReversibleBounds.add, List.countP_append] using
      Nat.add_le_add ha.ccx_le hb.ccx_le
  · simpa [ReversibleBounds.add, List.countP_append] using
      Nat.add_le_add ha.cx_le hb.cx_le

theorem reverse {gs : List RGate} {bound : ReversibleBounds}
    (h : ReversibleCertificate gs bound) :
    ReversibleCertificate gs.reverse bound := by
  constructor
  · simpa using h.gates_le
  · simpa using h.ccx_le
  · simpa using h.cx_le

theorem weaken {gs : List RGate} {a b : ReversibleBounds}
    (h : ReversibleCertificate gs a)
    (hgates : a.gates ≤ b.gates) (hccx : a.ccx ≤ b.ccx)
    (hcx : a.cx ≤ b.cx) : ReversibleCertificate gs b :=
  ⟨Nat.le_trans h.gates_le hgates, Nat.le_trans h.ccx_le hccx,
    Nat.le_trans h.cx_le hcx⟩

def fixedRepeat (gs : List RGate) : Nat → List RGate
  | 0 => []
  | n + 1 => gs ++ fixedRepeat gs n

theorem fixed {gs : List RGate} {bound : ReversibleBounds}
    (h : ReversibleCertificate gs bound) :
    ∀ n, ReversibleCertificate (fixedRepeat gs n) (bound.scale n)
  | 0 => by
      simpa [fixedRepeat, ReversibleBounds.scale, ReversibleBounds.zero] using nil
  | n + 1 => by
      simpa [fixedRepeat, ReversibleBounds.add, ReversibleBounds.scale,
        Nat.succ_mul, Nat.add_comm] using
        append h (fixed h n)

end ReversibleCertificate

structure CircuitBounds where
  gates : Nat
  clifford : Nat
  cnot : Nat
  toffoli : Nat
  deriving DecidableEq, Repr

namespace ReversibleBounds

def compiled (b : ReversibleBounds) : CircuitBounds :=
  { gates := b.gates + 2 * b.ccx,
    clifford := b.gates + b.ccx,
    cnot := b.cx,
    toffoli := b.ccx }

end ReversibleBounds

structure CircuitCertificate (c : Circuit) (bound : CircuitBounds) : Prop where
  gates_le : c.gateCount ≤ bound.gates
  clifford_le : c.cliffordCount ≤ bound.clifford
  cnot_le : c.cnotCount ≤ bound.cnot
  toffoli_le : c.toffoliCount ≤ bound.toffoli

namespace ReversibleCertificate

theorem compile {gs : List RGate} {bound : ReversibleBounds}
    (h : ReversibleCertificate gs bound) (width : Nat) :
    CircuitCertificate
      (Reversible.compile { width := width, gates := gs }) bound.compiled := by
  constructor
  · rw [Reversible.gateCount_compile]
    exact Nat.add_le_add h.gates_le (Nat.mul_le_mul_left 2 h.ccx_le)
  · rw [Reversible.cliffordCount_compile]
    exact Nat.add_le_add h.gates_le h.ccx_le
  · simpa [Reversible.cnotCount_compile, ReversibleBounds.compiled] using h.cx_le
  · simpa [Reversible.toffoliCount_compile, ReversibleBounds.compiled] using h.ccx_le

end ReversibleCertificate

structure ProgramBounds where
  gates : Nat
  clifford : Nat
  cnot : Nat
  toffoli : Nat
  depth : Nat
  toffoliDepth : Nat
  deriving DecidableEq, Repr

namespace CircuitBounds

def inProgram (b : CircuitBounds) : ProgramBounds :=
  { gates := b.gates,
    clifford := b.clifford,
    cnot := b.cnot,
    toffoli := b.toffoli,
    depth := b.gates,
    toffoliDepth := b.toffoli }

end CircuitBounds

structure ProgramCertificate (p : Program) (bound : ProgramBounds) : Prop where
  gates_le : p.gateCount.hi ≤ bound.gates
  clifford_le : p.cliffordCount.hi ≤ bound.clifford
  cnot_le : p.cnotCount.hi ≤ bound.cnot
  toffoli_le : p.toffoliCount.hi ≤ bound.toffoli
  depth_le : p.depthRange.hi ≤ bound.depth
  toffoliDepth_le : p.toffoliDepthRange.hi ≤ bound.toffoliDepth

namespace CircuitCertificate

theorem ofCircuit {c : Circuit} {bound : CircuitBounds}
    (h : CircuitCertificate c bound) :
    ProgramCertificate (Program.ofCircuit c) bound.inProgram := by
  constructor
  · simpa [CircuitBounds.inProgram, Range.point] using h.gates_le
  · simpa [CircuitBounds.inProgram, Range.point] using h.clifford_le
  · simpa [CircuitBounds.inProgram, Range.point] using h.cnot_le
  · simpa [CircuitBounds.inProgram, Range.point] using h.toffoli_le
  · exact Nat.le_trans (Program.depthRange_ofCircuit_hi_le_gateCount c) h.gates_le
  · exact
      Nat.le_trans (Program.toffoliDepthRange_ofCircuit_hi_le_toffoliCount c)
        h.toffoli_le

end CircuitCertificate

end VQ.Resource
