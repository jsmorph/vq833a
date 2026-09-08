/-
Programs: circuits with measurement, reset, and classical control.

`Circuit` contains unitary gates.  `Program` adds measurement, reset, and
classical control, following SQIR's separation of `ucom` and `com`.  Separate
types let unitary theorems retain state-map semantics without hypotheses that
exclude nonunitary constructors.

Resource metrics derive counts and depth bounds from `Program` syntax.

Every metric on a program is a range.  Under a branch the cost depends on
which arm runs, and one number cannot say that.  `exact` is available when both
arms agree and is `none` otherwise.
-/
import VQ.Circuit.Coupling

namespace VQ

inductive CRef where
  | input (index : Nat)
  | localBit (index : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace CRef

def read (input localRegister : Nat) : CRef → Bool
  | .input index => input.testBit index
  | .localBit index => localRegister.testBit index

def inputBits : CRef → List Nat
  | .input index => [index]
  | .localBit _ => []

def localBits : CRef → List Nat
  | .input _ => []
  | .localBit index => [index]

def wellFormed (inputBits localBits : Nat) : CRef → Bool
  | .input index => index < inputBits
  | .localBit index => index < localBits

end CRef

/-
One operation.

`branch c t e` runs `t` when classical reference `c` holds one and `e` when it
holds zero.  An input reference reads an immutable value supplied when the
program starts, while a local reference reads program-declared mutable
storage.  Nesting supplies conjunctions without a separate Boolean-expression
language.
-/
inductive Op where
  | gate (g : Gate)
  /-- Measure qubit `q` in the computational basis, storing the outcome in
  classical bit `c`. -/
  | measure (q : Nat) (c : Nat)
  /- Return qubit `q` to `|0⟩`, discarding what was there. -/
  | reset (q : Nat)
  /-- Store a constant in mutable local bit `c`. -/
  | store (c : Nat) (value : Bool)
  /-- Invert mutable local bit `c`. -/
  | invert (c : Nat)
  | branch (c : CRef) (whenTrue : List Op) (whenFalse : List Op)
  deriving Repr, Inhabited

/- A program: a quantum register, immutable classical inputs, mutable local
classical storage, and a list of operations. -/
structure Program where
  width : Nat
  cbits : Nat
  ops : List Op
  inputBits : Nat := 0
  deriving Repr, Inhabited

namespace Op

/-- A global sign implemented on any valid quantum wire.  Its denotation is
proved in `VQ.Program.Semantics`.  The four gates contain no Toffoli. -/
def globalNeg (q : Nat) : List Op :=
  [gate (.x q), gate (.z q), gate (.x q), gate (.z q)]

/-- Apply the derived global sign when a classical reference holds one. -/
def controlledGlobalNeg (c : CRef) (q : Nat) : List Op :=
  [branch c (globalNeg q) []]

/- The quantum wires an operation touches, including everything inside a
branch. -/
mutual
def wires : Op → List Nat
  | gate g => g.wires
  | measure q _ => [q]
  | reset q => [q]
  | store _ _ => []
  | invert _ => []
  | branch _ t e => wiresOf t ++ wiresOf e

def wiresOf : List Op → List Nat
  | [] => []
  | o :: rest => o.wires ++ wiresOf rest
end

/- The classical bits an operation reads or writes. -/
mutual
def cbitsUsed : Op → List Nat
  | gate _ => []
  | measure _ c => [c]
  | reset _ => []
  | store c _ => [c]
  | invert c => [c]
  | branch c t e => c.localBits ++ cbitsOf t ++ cbitsOf e

def cbitsOf : List Op → List Nat
  | [] => []
  | o :: rest => o.cbitsUsed ++ cbitsOf rest
end

mutual
def inputBitsUsed : Op → List Nat
  | gate _ => []
  | measure _ _ => []
  | reset _ => []
  | store _ _ => []
  | invert _ => []
  | branch c t e => c.inputBits ++ inputBitsOf t ++ inputBitsOf e

def inputBitsOf : List Op → List Nat
  | [] => []
  | o :: rest => o.inputBitsUsed ++ inputBitsOf rest
end

mutual
def localReads : Op → List Nat
  | .gate _ | .measure _ _ | .reset _ | .store _ _ => []
  | .invert c => [c]
  | .branch c t e => c.localBits ++ localReadsOf t ++ localReadsOf e

def localReadsOf : List Op → List Nat
  | [] => []
  | o :: rest => o.localReads ++ localReadsOf rest
end

mutual
def localWrites : Op → List Nat
  | .gate _ | .reset _ => []
  | .measure _ c | .store c _ | .invert c => [c]
  | .branch _ t e => localWritesOf t ++ localWritesOf e

def localWritesOf : List Op → List Nat
  | [] => []
  | o :: rest => o.localWrites ++ localWritesOf rest
end

/- Whether an operation is a unitary gate, with no measurement, reset, or
branch anywhere inside it. -/
mutual
def isUnitary : Op → Bool
  | gate _ => true
  | measure _ _ => false
  | reset _ => false
  | store _ _ => false
  | invert _ => false
  | branch _ _ _ => false

def allUnitary : List Op → Bool
  | [] => true
  | o :: rest => o.isUnitary && allUnitary rest
end

end Op

/-
A closed interval of costs.

`lo` is the cost when every branch takes its lower-cost arm and `hi` when every
branch takes its higher-cost arm.  For straight-line code they coincide.
-/
structure Range where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Range

def point (n : Nat) : Range := ⟨n, n⟩

def add (a b : Range) : Range := ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- The range of a choice between two alternatives. -/
def choice (a b : Range) : Range := ⟨min a.lo b.lo, max a.hi b.hi⟩

/- The cost when it does not depend on which branch runs. -/
def exact (r : Range) : Option Nat := if r.lo == r.hi then some r.lo else none

instance : Add Range := ⟨add⟩

end Range

namespace Program

/- Accumulate a per-gate weight over a program, tracking best and worst case. -/
mutual
def weighOp (f : Gate → Nat) : Op → Range
  | .gate g => Range.point (f g)
  | .measure _ _ => Range.point 0
  | .reset _ => Range.point 0
  | .store _ _ => Range.point 0
  | .invert _ => Range.point 0
  | .branch _ t e => Range.choice (weighOps f t) (weighOps f e)

def weighOps (f : Gate → Nat) : List Op → Range
  | [] => Range.point 0
  | o :: rest => Range.add (weighOp f o) (weighOps f rest)
end

/- Accumulate a per-operation weight for counts such as measurements and
resets. -/
mutual
def tallyOp (f : Op → Nat) : Op → Range
  | .branch _ t e => Range.choice (tallyOps f t) (tallyOps f e)
  | o => Range.point (f o)

def tallyOps (f : Op → Nat) : List Op → Range
  | [] => Range.point 0
  | o :: rest => Range.add (tallyOp f o) (tallyOps f rest)
end

def gateCount (p : Program) : Range := weighOps (fun _ => 1) p.ops
def tCount (p : Program) : Range := weighOps (fun g => if g.isT then 1 else 0) p.ops
def cnotCount (p : Program) : Range :=
  weighOps (fun g => if g.isTwoQubit then 1 else 0) p.ops
def nonCliffordCount (p : Program) : Range :=
  weighOps (fun g => if g.isNonClifford then 1 else 0) p.ops
def cliffordCount (p : Program) : Range :=
  weighOps (fun g => if g.isNonClifford then 0 else 1) p.ops
def toffoliCount (p : Program) : Range :=
  weighOps (fun g => if g.isCcz then 1 else 0) p.ops
def countKind (k : Circuit.GateKind) (p : Program) : Range :=
  weighOps (fun g => if g.kind == k then 1 else 0) p.ops

/- Measurements performed. -/
def measureCount (p : Program) : Range :=
  tallyOps (fun o => match o with | .measure _ _ => 1 | _ => 0) p.ops

/-- Resets performed. -/
def resetCount (p : Program) : Range :=
  tallyOps (fun o => match o with | .reset _ => 1 | _ => 0) p.ops

/-- Measurements and resets together, which is the pair a scheduler charges for
as mid-circuit operations. -/
def measureResetCount (p : Program) : Range :=
  tallyOps (fun o => match o with | .measure _ _ | .reset _ => 1 | _ => 0) p.ops

mutual
def classicalOpCountOp : Op → Range
  | .measure _ _ | .store _ _ | .invert _ => Range.point 1
  | .branch _ t e => Range.add (Range.point 1)
      (Range.choice (classicalOpCountOps t) (classicalOpCountOps e))
  | _ => Range.point 0

def classicalOpCountOps : List Op → Range
  | [] => Range.point 0
  | o :: rest => Range.add (classicalOpCountOp o) (classicalOpCountOps rest)
end

/-- Runtime classical operations, including measurement writes and condition
tests. -/
def classicalOpCount (p : Program) : Range := classicalOpCountOps p.ops

/-- Distinct quantum wires the program touches. -/
def usedWires (p : Program) : Nat := (Op.wiresOf p.ops).eraseDups.length

/-- Distinct classical bits the program reads or writes.  This value measures
required classical storage.  `cbits` records the author's declaration. -/
def usedCbits (p : Program) : Nat := (Op.cbitsOf p.ops).eraseDups.length

/-- Distinct immutable input bits the program reads. -/
def usedInputBits (p : Program) : Nat := (Op.inputBitsOf p.ops).eraseDups.length

/-- Whether the program is a unitary circuit: no measurement, no reset, no
branch.  A correctness obligation over the unitary semantics applies only to a
program satisfying this. -/
def isUnitary (p : Program) : Bool := Op.allUnitary p.ops

/- Every wire index below the declared width, every classical bit below the
declared classical width, and every gate well formed at that width and phase
level. -/
mutual
def opWellFormed (level w iw cw : Nat) : Op → Bool
  | .gate g => g.wellFormedAt level w
  | .measure q c => q < w && c < cw
  | .reset q => q < w
  | .store c _ => c < cw
  | .invert c => c < cw
  | .branch c t e => c.wellFormed iw cw && opsWellFormed level w iw cw t
      && opsWellFormed level w iw cw e

def opsWellFormed (level w iw cw : Nat) : List Op → Bool
  | [] => true
  | o :: rest => opWellFormed level w iw cw o && opsWellFormed level w iw cw rest
end

def wellFormed (level : Nat) (p : Program) : Bool :=
  opsWellFormed level p.width p.inputBits p.cbits p.ops

theorem Range.add_assoc (a b c : Range) :
    Range.add a (Range.add b c) = Range.add (Range.add a b) c := by
  simp [Range.add, Nat.add_assoc]

/-
Compositional lemmas.

A family bound proceeds by induction on the index.  Each induction step splits
the operation list at an append.  These lemmas supply the corresponding weight
and range equations.
-/
theorem weighOps_append (f : Gate → Nat) (a b : List Op) :
    weighOps f (a ++ b) = Range.add (weighOps f a) (weighOps f b) := by
  induction a with
  | nil => simp [weighOps, Range.add, Range.point]
  | cons o rest ih =>
    simp only [List.cons_append, weighOps, ih, Range.add_assoc]

theorem tallyOps_append (f : Op → Nat) (a b : List Op) :
    tallyOps f (a ++ b) = Range.add (tallyOps f a) (tallyOps f b) := by
  induction a with
  | nil => simp [tallyOps, Range.add, Range.point]
  | cons o rest ih =>
    simp only [List.cons_append, tallyOps, ih, Range.add_assoc]

theorem classicalOpCountOps_append (a b : List Op) :
    classicalOpCountOps (a ++ b) =
      Range.add (classicalOpCountOps a) (classicalOpCountOps b) := by
  induction a with
  | nil => simp [classicalOpCountOps, Range.add, Range.point]
  | cons o rest ih =>
    simp only [List.cons_append, classicalOpCountOps, ih, Range.add_assoc]

theorem opsWellFormed_append (level w iw cw : Nat) (a b : List Op) :
    opsWellFormed level w iw cw (a ++ b)
      = (opsWellFormed level w iw cw a && opsWellFormed level w iw cw b) := by
  induction a with
  | nil => simp [opsWellFormed]
  | cons o rest ih => simp only [List.cons_append, opsWellFormed, ih, Bool.and_assoc]

/-- A unitary circuit as a program. -/
def ofCircuit (c : Circuit) : Program :=
  { width := c.width, inputBits := 0, cbits := 0, ops := c.gates.map Op.gate }

end Program
end VQ
