import VQ.Lookup.MeasuredUncompute
import VQ.Program.Place
import VQ.Reversible.Permutation

/-!
# Batched measured unlookup

The batched-uncompute construction erases a coherently loaded lookup output by
measurement.  For an `addressWidth` of `a`, an `outputWidth`
of `m`, and a `lowWidth` of `ℓ`, VQ sets the batch size to `K = 2^ℓ` and the
high-address width to `h = a - ℓ`.  Address wires `0, …, ℓ - 1` select an
entry inside a batch, while wires `ℓ, …, a - 1` select the batch.

The primary paper anchor is arXiv:2606.02235, Algorithm 1 and §2.
Schrottenloher's Algorithm 1 invokes QROM lookup and unlookup without defining a
batch parameter for any of its three phases or identifying such a parameter with
a low-address width.  The paper does not specify the low/high address split or
reuse the measured QROM-output wires as the unary register.  This module reuses
the first `K` output wires and therefore requires `K ≤ m`.  The paper also does
not specify how long measurement results remain available.  This module retains
all `m` output-measurement bits through correction and reserves cbit `m` for
each measurement-based AND cleanup, giving `m + 1` cbits.

Generic classically controlled correction and Walsh-transform syntax already
exists in VQ.  This module proves retained-cbit semantics for the complete
high-address correction tree, proves its Walsh-phase cancellation on basis
states, and composes the complete measured-unlookup Program and rootless-lookup
round trip.  The paper does not give correction syntax, a cost convention for
classically controlled corrections, or a Walsh-basis dynamic-correction
circuit.  This module measures each output after a Hadamard, prepares a unary
low-address state on the cleared output wires, applies Hadamards before and
after table-bit corrections expressed as `branch` operations, decodes the high
address in a selector region `[a + m, 2 * a + m)`, and supplies a generic
K=256 relabel theorem for a caller-proved 3,460-wire placement.

Section 2 estimates `2^w` Toffolis for a `2^w` lookup and describes unlookup as
“almost free”.  It does not state an exact unlookup count.  Under this module's
cost convention, classically controlled X and CX corrections cost no Toffolis,
each forward CCX costs one Toffoli, and each clean AND uncompute costs one
measurement.  VQ's exact construction has `U = (K - 1) + (2^h - 2)` Toffolis,
`m + U` measurements, zero resets, width `2 * a + m`, and `m + 1` cbits.  The
`2^a - 2` rootless lookup construction used elsewhere in VQ is also distinct
from the paper's estimate.  The paper does not state these placements or exact
gate-by-gate counts, so every concrete choice and formula in this paragraph is
a VQ contribution rather than a value attributed to the paper.

Algorithm 1 and §2 also omit the classical-state invariant needed by the
selector recursion.  In this construction, measurement-based selector cleanup
writes only cbit `m`, while every dynamic correction reads cbits below `m`.
The cleanup may leave its latest outcome in cbit `m`.  The next cleanup
overwrites that bit.  The retained-cbit semantics below records and composes
preservation of cbits below `m` rather than asserting that cbit `m` is zero.  It
supplies a VQ proof obligation needed by the high-address correction and its
Walsh cancellation.  The paper states neither the invariant nor a proof that the
same measurement mask remains available after selector cleanup.
-/

namespace VQ.Lookup.BatchedUncompute

open Algebra Reversible Semantics

def batchSize (lowWidth : Nat) : Nat := 2 ^ lowWidth

def highWidth (addressWidth lowWidth : Nat) : Nat := addressWidth - lowWidth

def width (addressWidth outputWidth : Nat) : Nat :=
  2 * addressWidth + outputWidth

def outputWire (addressWidth bit : Nat) : Nat := addressWidth + bit

def selectorWire (addressWidth outputWidth depth : Nat) : Nat :=
  addressWidth + outputWidth + depth

def scratchBit (outputWidth : Nat) : Nat := outputWidth

def gateOps (gates : List RGate) : List Op := Unary.gateOps gates

def measureOutputOps (addressWidth : Nat) : Nat → Nat → List Op
  | _, 0 => []
  | bit, count + 1 =>
      let q := outputWire addressWidth bit
      [.gate (.h q), .measure q bit,
        .branch (.localBit bit) [.gate (.x q)] []] ++
        measureOutputOps addressWidth (bit + 1) count

def unaryHadamardOps (addressWidth : Nat) : Nat → Nat → List Op
  | _, 0 => []
  | low, count + 1 =>
      .gate (.h (outputWire addressWidth low)) ::
        unaryHadamardOps addressWidth (low + 1) count

def prepareStageOps (addressWidth stage : Nat) : Nat → Nat → List Op
  | _, 0 => []
  | low, count + 1 =>
      gateOps (fredkin stage
        (outputWire addressWidth low)
        (outputWire addressWidth (low + 2 ^ stage))) ++
      prepareStageOps addressWidth stage (low + 1) count

def prepareUnaryOps (addressWidth : Nat) : Nat → List Op
  | 0 => [.gate (.x (outputWire addressWidth 0))]
  | lowWidth + 1 =>
      prepareUnaryOps addressWidth lowWidth ++
        prepareStageOps addressWidth lowWidth 0 (2 ^ lowWidth)

def clearStageOps (addressWidth outputWidth stage : Nat) : Nat → Nat → List Op
  | _, 0 => []
  | low, count + 1 =>
      let x := outputWire addressWidth low
      let y := outputWire addressWidth (low + 2 ^ stage)
      [.gate (.cx y x)] ++
        Semantics.andUncomputeClean stage x y (scratchBit outputWidth) ++
        clearStageOps addressWidth outputWidth stage (low + 1) count

def clearUnaryOps (addressWidth outputWidth : Nat) : Nat → List Op
  | 0 => [.gate (.x (outputWire addressWidth 0))]
  | lowWidth + 1 =>
      clearStageOps addressWidth outputWidth lowWidth 0 (2 ^ lowWidth) ++
        clearUnaryOps addressWidth outputWidth lowWidth

def correctionGate (addressWidth low : Nat) : Option Nat → RGate
  | none => .x (outputWire addressWidth low)
  | some selector => .cx selector (outputWire addressWidth low)

def correctionBitOps (table : List Nat) (addressWidth outputWidth lowWidth row low : Nat)
    (control : Option Nat) : Nat → Nat → List Op
  | _, 0 => []
  | bit, count + 1 =>
      let word := Lookup.value table outputWidth (row * batchSize lowWidth + low)
      let correction := gateOps [correctionGate addressWidth low control]
      (if word.testBit bit then
          [.branch (.localBit bit) correction []]
        else []) ++
        correctionBitOps table addressWidth outputWidth lowWidth row low control
          (bit + 1) count

def correctionLeafOps (table : List Nat) (addressWidth outputWidth lowWidth row : Nat)
    (control : Option Nat) : Nat → Nat → List Op
  | _, 0 => []
  | low, count + 1 =>
      correctionBitOps table addressWidth outputWidth lowWidth row low control 0 outputWidth ++
        correctionLeafOps table addressWidth outputWidth lowWidth row control
          (low + 1) count

def negativeAndGates (address parent child : Nat) : List RGate :=
  [.x address, .ccx parent address child, .x address]

def correctionNodeOps (table : List Nat) (addressWidth outputWidth lowWidth : Nat) :
    Nat → Nat → Nat → List Op
  | row, depth, 0 =>
      correctionLeafOps table addressWidth outputWidth lowWidth row
        (some (selectorWire addressWidth outputWidth depth)) 0 (batchSize lowWidth)
  | row, depth, remaining + 1 =>
      let address := lowWidth + remaining
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      gateOps (negativeAndGates address parent child) ++
        correctionNodeOps table addressWidth outputWidth lowWidth
          row (depth + 1) remaining ++
        gateOps [.cx parent child] ++
        correctionNodeOps table addressWidth outputWidth lowWidth
          (row + 2 ^ remaining) (depth + 1) remaining ++
        Semantics.andUncomputeClean parent address child (scratchBit outputWidth)

def correctionOps (table : List Nat) (addressWidth outputWidth lowWidth : Nat) :
    Nat → List Op
  | 0 =>
      correctionLeafOps table addressWidth outputWidth lowWidth 0 none
        0 (batchSize lowWidth)
  | remaining + 1 =>
      let address := lowWidth + remaining
      let root := selectorWire addressWidth outputWidth 0
      gateOps [.x address, .cx address root, .x address] ++
        correctionNodeOps table addressWidth outputWidth lowWidth 0 0 remaining ++
        gateOps [.x root] ++
        correctionNodeOps table addressWidth outputWidth lowWidth
          (2 ^ remaining) 0 remaining ++
        gateOps [.cx address root]

def unlookupOps (table : List Nat) (addressWidth outputWidth lowWidth : Nat) : List Op :=
  measureOutputOps addressWidth 0 outputWidth ++
    prepareUnaryOps addressWidth lowWidth ++
    unaryHadamardOps addressWidth 0 (batchSize lowWidth) ++
    correctionOps table addressWidth outputWidth lowWidth
      (highWidth addressWidth lowWidth) ++
    unaryHadamardOps addressWidth 0 (batchSize lowWidth) ++
    clearUnaryOps addressWidth outputWidth lowWidth

def program (table : List Nat) (addressWidth outputWidth lowWidth : Nat) : Program :=
  { width := width addressWidth outputWidth
    cbits := outputWidth + 1
    ops := unlookupOps table addressWidth outputWidth lowWidth }

def spec (table : List Nat) (addressWidth outputWidth : Nat) : RegSpec where
  width := width addressWidth outputWidth
  Pre := MeasuredUncompute.rangeReady table addressWidth outputWidth addressWidth 0 outputWidth
  Post i j := j = MeasuredUncompute.clearBits addressWidth 0 outputWidth i

def roundTripOps (table : List Nat) (addressWidth outputWidth lowWidth : Nat) : List Op :=
  Unary.Rootless.lookupOps table addressWidth outputWidth ++
    unlookupOps table addressWidth outputWidth lowWidth

def roundTripProgram (table : List Nat)
    (addressWidth outputWidth lowWidth : Nat) : Program :=
  { width := width addressWidth outputWidth
    cbits := outputWidth + 1
    ops := roundTripOps table addressWidth outputWidth lowWidth }

def roundTripSpec (addressWidth outputWidth : Nat) : RegSpec :=
  MeasuredUncompute.roundTripSpec addressWidth outputWidth addressWidth

def correctionToffoliCount (addressWidth lowWidth : Nat) : Nat :=
  2 ^ highWidth addressWidth lowWidth - 2

def unlookupToffoliCount (addressWidth lowWidth : Nat) : Nat :=
  batchSize lowWidth - 1 + correctionToffoliCount addressWidth lowWidth

def unlookupMeasurementCount
    (addressWidth outputWidth lowWidth : Nat) : Nat :=
  outputWidth + unlookupToffoliCount addressWidth lowWidth

theorem gateOps_toffoli (gates : List RGate) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0) (gateOps gates) =
      Range.point (gates.countP RGate.isCcx) :=
  Unary.gateOps_toffoli gates

theorem gateOps_measure (gates : List RGate) :
    Program.tallyOps Lookup3.measurementCost (gateOps gates) = Range.point 0 :=
  MeasuredUncompute.unaryGateOps_measure gates

theorem gateOps_reset (gates : List RGate) :
    Program.tallyOps Lookup3.resetCost (gateOps gates) = Range.point 0 :=
  MeasuredUncompute.unaryGateOps_reset gates

theorem correctionBitOps_toffoli (table : List Nat)
    (addressWidth outputWidth lowWidth row low : Nat) (control : Option Nat) :
    ∀ bit count,
      Program.weighOps (fun g => if g.isCcz then 1 else 0)
        (correctionBitOps table addressWidth outputWidth lowWidth row low control bit count) =
          Range.point 0 := by
  intro bit count
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      rw [correctionBitOps.eq_def, Program.weighOps_append, ih (bit + 1)]
      split <;> cases control <;> rfl

theorem correctionBitOps_measure (table : List Nat)
    (addressWidth outputWidth lowWidth row low : Nat) (control : Option Nat) :
    ∀ bit count,
      Program.tallyOps Lookup3.measurementCost
        (correctionBitOps table addressWidth outputWidth lowWidth row low control bit count) =
          Range.point 0 := by
  intro bit count
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      rw [correctionBitOps.eq_def, Program.tallyOps_append, ih (bit + 1)]
      split <;> cases control <;> rfl

theorem correctionBitOps_reset (table : List Nat)
    (addressWidth outputWidth lowWidth row low : Nat) (control : Option Nat) :
    ∀ bit count,
      Program.tallyOps Lookup3.resetCost
        (correctionBitOps table addressWidth outputWidth lowWidth row low control bit count) =
          Range.point 0 := by
  intro bit count
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      rw [correctionBitOps.eq_def, Program.tallyOps_append, ih (bit + 1)]
      split <;> cases control <;> rfl

theorem correctionLeafOps_toffoli (table : List Nat)
    (addressWidth outputWidth lowWidth row : Nat) (control : Option Nat) :
    ∀ low count,
      Program.weighOps (fun g => if g.isCcz then 1 else 0)
        (correctionLeafOps table addressWidth outputWidth lowWidth row control low count) =
          Range.point 0 := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      rw [correctionLeafOps, Program.weighOps_append,
        correctionBitOps_toffoli, ih]
      rfl

theorem correctionLeafOps_measure (table : List Nat)
    (addressWidth outputWidth lowWidth row : Nat) (control : Option Nat) :
    ∀ low count,
      Program.tallyOps Lookup3.measurementCost
        (correctionLeafOps table addressWidth outputWidth lowWidth row control low count) =
          Range.point 0 := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      rw [correctionLeafOps, Program.tallyOps_append,
        correctionBitOps_measure, ih]
      rfl

theorem correctionLeafOps_reset (table : List Nat)
    (addressWidth outputWidth lowWidth row : Nat) (control : Option Nat) :
    ∀ low count,
      Program.tallyOps Lookup3.resetCost
        (correctionLeafOps table addressWidth outputWidth lowWidth row control low count) =
          Range.point 0 := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      rw [correctionLeafOps, Program.tallyOps_append,
        correctionBitOps_reset, ih]
      rfl

theorem prepareStageOps_toffoli (addressWidth stage : Nat) : ∀ low count,
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (prepareStageOps addressWidth stage low count) = Range.point count := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      rw [prepareStageOps, Program.weighOps_append, gateOps_toffoli, ih]
      simp [fredkin, List.countP_cons, RGate.isCcx, Range.add, Range.point]
      omega

theorem prepareUnaryOps_toffoli (addressWidth lowWidth : Nat) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (prepareUnaryOps addressWidth lowWidth) = Range.point (batchSize lowWidth - 1) := by
  induction lowWidth with
  | zero => rfl
  | succ lowWidth ih =>
      rw [prepareUnaryOps, Program.weighOps_append, ih,
        prepareStageOps_toffoli]
      simp [batchSize, Range.add, Range.point, Nat.pow_succ]
      omega

theorem clearStageOps_toffoli (addressWidth outputWidth stage : Nat) : ∀ low count,
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (clearStageOps addressWidth outputWidth stage low count) = Range.point 0 := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      simp only [clearStageOps, Program.weighOps_append,
        Unary.andUncomputeClean_toffoli, ih]
      rfl

theorem clearUnaryOps_toffoli (addressWidth outputWidth lowWidth : Nat) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (clearUnaryOps addressWidth outputWidth lowWidth) = Range.point 0 := by
  induction lowWidth with
  | zero => rfl
  | succ lowWidth ih =>
      rw [clearUnaryOps, Program.weighOps_append, clearStageOps_toffoli, ih]
      rfl

theorem correctionNodeOps_toffoli (table : List Nat)
    (addressWidth outputWidth lowWidth row depth : Nat) : ∀ remaining,
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (correctionNodeOps table addressWidth outputWidth lowWidth row depth remaining) =
        Range.point (2 ^ remaining - 1) := by
  intro remaining
  induction remaining generalizing row depth with
  | zero =>
      simp [correctionNodeOps, correctionLeafOps_toffoli]
  | succ remaining ih =>
      rw [correctionNodeOps]
      have hpow := Nat.two_pow_pos remaining
      simp only [Program.weighOps_append, gateOps_toffoli, ih,
        Unary.andUncomputeClean_toffoli]
      simp [negativeAndGates, List.countP_cons, RGate.isCcx, Range.add, Range.point,
        Nat.pow_succ]
      omega

theorem correctionOps_toffoli (table : List Nat)
    (addressWidth outputWidth lowWidth remaining : Nat) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (correctionOps table addressWidth outputWidth lowWidth remaining) =
        Range.point (2 ^ remaining - 2) := by
  cases remaining with
  | zero =>
      simp [correctionOps, correctionLeafOps_toffoli]
  | succ remaining =>
      rw [correctionOps]
      simp only [Program.weighOps_append, gateOps_toffoli,
        correctionNodeOps_toffoli]
      simp [RGate.isCcx, Range.add, Range.point, Nat.pow_succ]
      omega

theorem measureOutputOps_toffoli (addressWidth : Nat) : ∀ bit count,
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (measureOutputOps addressWidth bit count) = Range.point 0 := by
  intro bit count
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      rw [measureOutputOps]
      rw [Program.weighOps_append]
      rw [ih (bit + 1)]
      rfl

theorem unaryHadamardOps_toffoli (addressWidth : Nat) : ∀ low count,
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (unaryHadamardOps addressWidth low count) = Range.point 0 := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      rw [unaryHadamardOps]
      rw [Program.weighOps]
      rw [ih (low + 1)]
      rfl

theorem program_toffoliCount (table : List Nat)
    (addressWidth outputWidth lowWidth : Nat) :
    (program table addressWidth outputWidth lowWidth).toffoliCount =
      Range.point (unlookupToffoliCount addressWidth lowWidth) := by
  simp only [program, Program.toffoliCount, unlookupOps,
    Program.weighOps_append, measureOutputOps_toffoli, prepareUnaryOps_toffoli,
    unaryHadamardOps_toffoli, correctionOps_toffoli, clearUnaryOps_toffoli]
  simp [unlookupToffoliCount, correctionToffoliCount, highWidth,
    Range.add, Range.point]

theorem prepareStageOps_measure (addressWidth stage : Nat) : ∀ low count,
    Program.tallyOps Lookup3.measurementCost
      (prepareStageOps addressWidth stage low count) = Range.point 0 := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      rw [prepareStageOps, Program.tallyOps_append, gateOps_measure, ih]
      rfl

theorem prepareUnaryOps_measure (addressWidth lowWidth : Nat) :
    Program.tallyOps Lookup3.measurementCost (prepareUnaryOps addressWidth lowWidth) =
      Range.point 0 := by
  induction lowWidth with
  | zero => rfl
  | succ lowWidth ih =>
      rw [prepareUnaryOps, Program.tallyOps_append, ih, prepareStageOps_measure]
      rfl

theorem clearStageOps_measure (addressWidth outputWidth stage : Nat) : ∀ low count,
    Program.tallyOps Lookup3.measurementCost
      (clearStageOps addressWidth outputWidth stage low count) = Range.point count := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      simp only [clearStageOps, Program.tallyOps_append,
        MeasuredUncompute.andUncomputeClean_measure, ih]
      simp [Program.tallyOps, Program.tallyOp, Lookup3.measurementCost,
        Range.add, Range.point]
      omega

theorem clearUnaryOps_measure (addressWidth outputWidth lowWidth : Nat) :
    Program.tallyOps Lookup3.measurementCost
      (clearUnaryOps addressWidth outputWidth lowWidth) =
        Range.point (batchSize lowWidth - 1) := by
  induction lowWidth with
  | zero => rfl
  | succ lowWidth ih =>
      rw [clearUnaryOps, Program.tallyOps_append, clearStageOps_measure, ih]
      simp [batchSize, Range.add, Range.point, Nat.pow_succ]
      omega

theorem correctionNodeOps_measure (table : List Nat)
    (addressWidth outputWidth lowWidth row depth : Nat) : ∀ remaining,
    Program.tallyOps Lookup3.measurementCost
      (correctionNodeOps table addressWidth outputWidth lowWidth row depth remaining) =
        Range.point (2 ^ remaining - 1) := by
  intro remaining
  induction remaining generalizing row depth with
  | zero => simp [correctionNodeOps, correctionLeafOps_measure]
  | succ remaining ih =>
      rw [correctionNodeOps]
      have hpow := Nat.two_pow_pos remaining
      simp only [Program.tallyOps_append, gateOps_measure, ih,
        MeasuredUncompute.andUncomputeClean_measure]
      simp [Range.add, Range.point, Nat.pow_succ]
      omega

theorem correctionOps_measure (table : List Nat)
    (addressWidth outputWidth lowWidth remaining : Nat) :
    Program.tallyOps Lookup3.measurementCost
      (correctionOps table addressWidth outputWidth lowWidth remaining) =
        Range.point (2 ^ remaining - 2) := by
  cases remaining with
  | zero => simp [correctionOps, correctionLeafOps_measure]
  | succ remaining =>
      rw [correctionOps]
      simp only [Program.tallyOps_append, gateOps_measure,
        correctionNodeOps_measure]
      simp [Range.add, Range.point, Nat.pow_succ]
      omega

theorem measureOutputOps_measure (addressWidth : Nat) : ∀ bit count,
    Program.tallyOps Lookup3.measurementCost
      (measureOutputOps addressWidth bit count) = Range.point count := by
  intro bit count
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      rw [measureOutputOps]
      simp [ih (bit + 1), Program.tallyOps, Program.tallyOp,
        Lookup3.measurementCost, Range.add, Range.choice, Range.point]
      omega

theorem unaryHadamardOps_measure (addressWidth : Nat) : ∀ low count,
    Program.tallyOps Lookup3.measurementCost
      (unaryHadamardOps addressWidth low count) = Range.point 0 := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      rw [unaryHadamardOps]
      simp [ih (low + 1), Program.tallyOps, Program.tallyOp,
        Lookup3.measurementCost, Range.add, Range.point]

theorem program_measureCount (table : List Nat)
    (addressWidth outputWidth lowWidth : Nat) :
    (program table addressWidth outputWidth lowWidth).measureCount =
      Range.point (unlookupMeasurementCount addressWidth outputWidth lowWidth) := by
  change Program.tallyOps Lookup3.measurementCost
    (unlookupOps table addressWidth outputWidth lowWidth) = _
  rw [unlookupOps, Program.tallyOps_append, Program.tallyOps_append,
    Program.tallyOps_append, Program.tallyOps_append, Program.tallyOps_append,
    measureOutputOps_measure, prepareUnaryOps_measure,
    unaryHadamardOps_measure, correctionOps_measure, clearUnaryOps_measure]
  simp [unlookupMeasurementCount, unlookupToffoliCount, correctionToffoliCount,
    highWidth, Range.add, Range.point]
  omega

theorem measureOutputOps_reset (addressWidth : Nat) : ∀ bit count,
    Program.tallyOps Lookup3.resetCost (measureOutputOps addressWidth bit count) =
      Range.point 0 := by
  intro bit count
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      rw [measureOutputOps]
      simp [ih (bit + 1), Program.tallyOps, Program.tallyOp,
        Lookup3.resetCost, Range.add, Range.choice, Range.point]

theorem unaryHadamardOps_reset (addressWidth : Nat) : ∀ low count,
    Program.tallyOps Lookup3.resetCost (unaryHadamardOps addressWidth low count) =
      Range.point 0 := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      rw [unaryHadamardOps]
      simp [ih (low + 1), Program.tallyOps, Program.tallyOp,
        Lookup3.resetCost, Range.add, Range.point]

theorem prepareStageOps_reset (addressWidth stage : Nat) : ∀ low count,
    Program.tallyOps Lookup3.resetCost (prepareStageOps addressWidth stage low count) =
      Range.point 0 := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      rw [prepareStageOps, Program.tallyOps_append, gateOps_reset, ih]
      rfl

theorem prepareUnaryOps_reset (addressWidth lowWidth : Nat) :
    Program.tallyOps Lookup3.resetCost (prepareUnaryOps addressWidth lowWidth) =
      Range.point 0 := by
  induction lowWidth with
  | zero => rfl
  | succ lowWidth ih =>
      rw [prepareUnaryOps, Program.tallyOps_append, ih, prepareStageOps_reset]
      rfl

theorem clearStageOps_reset (addressWidth outputWidth stage : Nat) : ∀ low count,
    Program.tallyOps Lookup3.resetCost
      (clearStageOps addressWidth outputWidth stage low count) = Range.point 0 := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      simp only [clearStageOps, Program.tallyOps_append,
        MeasuredUncompute.andUncomputeClean_reset, ih]
      rfl

theorem clearUnaryOps_reset (addressWidth outputWidth lowWidth : Nat) :
    Program.tallyOps Lookup3.resetCost (clearUnaryOps addressWidth outputWidth lowWidth) =
      Range.point 0 := by
  induction lowWidth with
  | zero => rfl
  | succ lowWidth ih =>
      rw [clearUnaryOps, Program.tallyOps_append, clearStageOps_reset, ih]
      rfl

theorem correctionNodeOps_reset (table : List Nat)
    (addressWidth outputWidth lowWidth row depth : Nat) : ∀ remaining,
    Program.tallyOps Lookup3.resetCost
      (correctionNodeOps table addressWidth outputWidth lowWidth row depth remaining) =
        Range.point 0 := by
  intro remaining
  induction remaining generalizing row depth with
  | zero => simp [correctionNodeOps, correctionLeafOps_reset]
  | succ remaining ih =>
      rw [correctionNodeOps]
      simp only [Program.tallyOps_append, gateOps_reset, ih,
        MeasuredUncompute.andUncomputeClean_reset]
      rfl

theorem correctionOps_reset (table : List Nat)
    (addressWidth outputWidth lowWidth remaining : Nat) :
    Program.tallyOps Lookup3.resetCost
      (correctionOps table addressWidth outputWidth lowWidth remaining) = Range.point 0 := by
  cases remaining with
  | zero => simp [correctionOps, correctionLeafOps_reset]
  | succ remaining =>
      rw [correctionOps]
      simp only [Program.tallyOps_append, gateOps_reset, correctionNodeOps_reset]
      rfl

theorem program_resetCount (table : List Nat)
    (addressWidth outputWidth lowWidth : Nat) :
    (program table addressWidth outputWidth lowWidth).resetCount = Range.point 0 := by
  change Program.tallyOps Lookup3.resetCost
    (unlookupOps table addressWidth outputWidth lowWidth) = _
  rw [unlookupOps, Program.tallyOps_append, Program.tallyOps_append,
    Program.tallyOps_append, Program.tallyOps_append, Program.tallyOps_append,
    measureOutputOps_reset, prepareUnaryOps_reset, unaryHadamardOps_reset,
    correctionOps_reset, clearUnaryOps_reset]
  rfl

theorem program_width (table : List Nat)
    (addressWidth outputWidth lowWidth : Nat) :
    (program table addressWidth outputWidth lowWidth).width =
      2 * addressWidth + outputWidth := rfl

theorem program_workspaceWidth (table : List Nat)
    (addressWidth outputWidth lowWidth : Nat) :
    (program table addressWidth outputWidth lowWidth).width -
      addressWidth - outputWidth = addressWidth := by
  rw [program_width]
  omega

theorem program_cbits (table : List Nat)
    (addressWidth outputWidth lowWidth : Nat) :
    (program table addressWidth outputWidth lowWidth).cbits = outputWidth + 1 := rfl

def selectorFits (addressWidth outputWidth : Nat) : Option Nat → Prop
  | none => True
  | some selector =>
      addressWidth + outputWidth ≤ selector ∧
        selector < width addressWidth outputWidth

private theorem correctionGate_wellFormed
    {addressWidth outputWidth lowWidth low : Nat} {control : Option Nat}
    (hlow : low < batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control) :
    (correctionGate addressWidth low control).wellFormed
      (width addressWidth outputWidth) = true := by
  cases control with
  | none =>
      dsimp +instances only [correctionGate, RGate.wellFormed, outputWire, width]
      simp only [decide_eq_true_eq]
      omega
  | some selector =>
      simp [selectorFits] at hcontrol
      have htarget : outputWire addressWidth low <
          addressWidth + outputWidth := by
        simp [outputWire]
        omega
      have htargetWidth : outputWire addressWidth low <
          width addressWidth outputWidth := by
        simp [outputWire, width]
        omega
      have hselectorTarget : selector ≠ outputWire addressWidth low :=
        (htarget.trans_le hcontrol.1).ne'
      simp [correctionGate, RGate.wellFormed, hcontrol.2,
        htargetWidth, hselectorTarget]

private theorem correctionGateOps_wellFormed
    {level addressWidth outputWidth lowWidth low : Nat} {control : Option Nat}
    (hlow : low < batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control) :
    Program.opsWellFormed level (width addressWidth outputWidth) 0 (outputWidth + 1)
      (gateOps [correctionGate addressWidth low control]) = true := by
  have hgate := correctionGate_wellFormed hlow hfit hcontrol
  cases control <;>
    simpa [gateOps, Unary.gateOps, correctionGate, compileGate,
      Program.opsWellFormed, Program.opWellFormed, Gate.wellFormedAt,
      RGate.wellFormed] using hgate

theorem gateOps_wellFormed {level totalWidth inputBits cbits : Nat}
    (hl : 3 ≤ level) {gates : List RGate}
    (hgates : gates.all (RGate.wellFormed totalWidth) = true) :
    Program.opsWellFormed level totalWidth inputBits cbits (gateOps gates) = true := by
  rw [gateOps, Unary.gateOps]
  have hcompiled : (gates.flatMap compileGate).all
      (Gate.wellFormedAt level totalWidth) = true := by
    change (compile ({ width := totalWidth, gates := gates } : RCircuit)).wellFormedAt
      level = true
    apply wellFormedAt_compile
    apply RCircuit.wellFormedAt_of_wellFormed hl
    simpa [RCircuit.wellFormed] using hgates
  have hall : ∀ compiled : List Gate,
      compiled.all (Gate.wellFormedAt level totalWidth) = true →
      Program.opsWellFormed level totalWidth inputBits cbits
        (compiled.map Op.gate) = true := by
    intro compiled hcompiled
    induction compiled with
    | nil => rfl
    | cons gate gates ih =>
        rw [List.all_cons, Bool.and_eq_true] at hcompiled
        simp [Program.opsWellFormed, Program.opWellFormed, hcompiled.1,
          ih hcompiled.2]
  exact hall _ hcompiled

theorem andUncomputeClean_wellFormed
    {level totalWidth inputBits cbits a b c scratch : Nat}
    (hl : 3 ≤ level) (ha : a < totalWidth) (hb : b < totalWidth)
    (hc : c < totalWidth) (hscratch : scratch < cbits) (hab : a ≠ b) :
    Program.opsWellFormed level totalWidth inputBits cbits
      (Semantics.andUncomputeClean a b c scratch) = true := by
  simp [Semantics.andUncomputeClean, andUncompute, Circuit.cz,
    Program.opsWellFormed, Program.opWellFormed, CRef.wellFormed,
    Gate.wellFormedAt, hl, ha, hb, hc, hscratch, hab]

theorem measureOutputOps_wellFormed {level addressWidth outputWidth bit count : Nat}
    (hl : 3 ≤ level) (hbound : bit + count ≤ outputWidth) :
    Program.opsWellFormed level (width addressWidth outputWidth) 0 (outputWidth + 1)
      (measureOutputOps addressWidth bit count) = true := by
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      have htail := ih (bit := bit + 1) (by omega)
      rw [measureOutputOps, Program.opsWellFormed_append, htail]
      dsimp +instances only [Program.opsWellFormed, Program.opWellFormed, CRef.wellFormed,
        Gate.wellFormedAt, width, outputWire]
      simp only [Bool.and_eq_true, Bool.and_true, decide_eq_true_eq]
      omega

theorem unaryHadamardOps_wellFormed
    {level addressWidth outputWidth low count lowWidth : Nat}
    (hl : 3 ≤ level) (hbound : low + count ≤ batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    Program.opsWellFormed level (width addressWidth outputWidth) 0 (outputWidth + 1)
      (unaryHadamardOps addressWidth low count) = true := by
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      have htail := ih (low := low + 1) (by omega)
      rw [unaryHadamardOps, Program.opsWellFormed, htail]
      dsimp +instances only [Program.opWellFormed, Gate.wellFormedAt, width, outputWire]
      simp only [Bool.and_eq_true, Bool.and_true, decide_eq_true_eq]
      omega

theorem prepareStageOps_wellFormed
    {level addressWidth outputWidth stage low count : Nat}
    (hl : 3 ≤ level) (hstage : stage < addressWidth)
    (hbound : low + count ≤ 2 ^ stage)
    (hfit : 2 ^ (stage + 1) ≤ outputWidth) :
    Program.opsWellFormed level (width addressWidth outputWidth) 0 (outputWidth + 1)
      (prepareStageOps addressWidth stage low count) = true := by
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      have htail := ih (low := low + 1) (by omega)
      have hfredkin : (fredkin stage
          (outputWire addressWidth low)
          (outputWire addressWidth (low + 2 ^ stage))).all
          (RGate.wellFormed (width addressWidth outputWidth)) = true := by
        apply fredkin_wellFormed <;>
          simp [width, outputWire] <;> omega
      have hhead := gateOps_wellFormed (inputBits := 0)
        (cbits := outputWidth + 1) hl hfredkin
      rw [prepareStageOps, Program.opsWellFormed_append, hhead, htail]
      rfl

theorem prepareUnaryOps_wellFormed
    {level addressWidth outputWidth lowWidth : Nat}
    (hl : 3 ≤ level) (haddress : lowWidth ≤ addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    Program.opsWellFormed level (width addressWidth outputWidth) 0 (outputWidth + 1)
      (prepareUnaryOps addressWidth lowWidth) = true := by
  induction lowWidth with
  | zero =>
      simp [prepareUnaryOps, Program.opsWellFormed, Program.opWellFormed,
        Gate.wellFormedAt, width, outputWire, batchSize] at hfit ⊢
      omega
  | succ lowWidth ih =>
      have hprevFit : batchSize lowWidth ≤ outputWidth := by
        simp [batchSize, Nat.pow_succ] at hfit ⊢
        omega
      have hprev := ih (by omega) hprevFit
      have hstage := prepareStageOps_wellFormed
        (level := level) (addressWidth := addressWidth) (outputWidth := outputWidth)
        (stage := lowWidth) (low := 0) (count := 2 ^ lowWidth)
        hl (by omega) (by omega) (by simpa [batchSize] using hfit)
      rw [prepareUnaryOps, Program.opsWellFormed_append, hprev, hstage]
      rfl

theorem clearStageOps_wellFormed
    {level addressWidth outputWidth stage low count : Nat}
    (hl : 3 ≤ level) (hstage : stage < addressWidth)
    (hbound : low + count ≤ 2 ^ stage)
    (hfit : 2 ^ (stage + 1) ≤ outputWidth) :
    Program.opsWellFormed level (width addressWidth outputWidth) 0 (outputWidth + 1)
      (clearStageOps addressWidth outputWidth stage low count) = true := by
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      let x := outputWire addressWidth low
      let y := outputWire addressWidth (low + 2 ^ stage)
      have hx : x < width addressWidth outputWidth := by
        simp [x, outputWire, width]
        omega
      have hy : y < width addressWidth outputWidth := by
        simp [y, outputWire, width]
        omega
      have hxy : y ≠ x := by
        simp [x, y, outputWire]
      have hcx : Program.opsWellFormed level (width addressWidth outputWidth) 0
          (outputWidth + 1) [.gate (.cx y x)] = true := by
        simp [Program.opsWellFormed, Program.opWellFormed, Gate.wellFormedAt,
          hx, hy, hxy]
      have herase := andUncomputeClean_wellFormed
        (level := level) (totalWidth := width addressWidth outputWidth)
        (inputBits := 0) (cbits := outputWidth + 1)
        (a := stage) (b := x) (c := y) (scratch := scratchBit outputWidth)
        hl (by simp [width]; omega) hx hy (by simp [scratchBit])
        (by simp [x, outputWire]; omega)
      have htail := ih (low := low + 1) (by omega)
      rw [clearStageOps, Program.opsWellFormed_append,
        Program.opsWellFormed_append, hcx, herase, htail]
      rfl

theorem clearUnaryOps_wellFormed
    {level addressWidth outputWidth lowWidth : Nat}
    (hl : 3 ≤ level) (haddress : lowWidth ≤ addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    Program.opsWellFormed level (width addressWidth outputWidth) 0 (outputWidth + 1)
      (clearUnaryOps addressWidth outputWidth lowWidth) = true := by
  induction lowWidth with
  | zero =>
      simp [clearUnaryOps, Program.opsWellFormed, Program.opWellFormed,
        Gate.wellFormedAt, width, outputWire, batchSize] at hfit ⊢
      omega
  | succ lowWidth ih =>
      have hprevFit : batchSize lowWidth ≤ outputWidth := by
        simp [batchSize, Nat.pow_succ] at hfit ⊢
        omega
      have hprev := ih (by omega) hprevFit
      have hstage := clearStageOps_wellFormed
        (level := level) (addressWidth := addressWidth) (outputWidth := outputWidth)
        (stage := lowWidth) (low := 0) (count := 2 ^ lowWidth)
        hl (by omega) (by omega) (by simpa [batchSize] using hfit)
      rw [clearUnaryOps, Program.opsWellFormed_append, hstage, hprev]
      rfl

theorem correctionBitOps_wellFormed
    {level : Nat} (table : List Nat)
    {addressWidth outputWidth lowWidth row low bit count : Nat}
    {control : Option Nat}
    (hlow : low < batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hbits : bit + count ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control) :
    Program.opsWellFormed level (width addressWidth outputWidth) 0 (outputWidth + 1)
      (correctionBitOps table addressWidth outputWidth lowWidth row low control bit count) =
        true := by
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      have htail := ih (bit := bit + 1) (by omega)
      have hcorrection := correctionGateOps_wellFormed
        (level := level) hlow hfit hcontrol
      rw [correctionBitOps.eq_def, Program.opsWellFormed_append, htail]
      split
      · simp [Program.opsWellFormed, Program.opWellFormed,
          CRef.wellFormed, hcorrection]
        omega
      · rfl

theorem correctionLeafOps_wellFormed
    {level : Nat} (table : List Nat)
    {addressWidth outputWidth lowWidth row low count : Nat}
    {control : Option Nat}
    (hbound : low + count ≤ batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control) :
    Program.opsWellFormed level (width addressWidth outputWidth) 0 (outputWidth + 1)
      (correctionLeafOps table addressWidth outputWidth lowWidth row control low count) =
        true := by
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      have hbit := correctionBitOps_wellFormed table
        (level := level) (row := row) (low := low) (bit := 0)
        (count := outputWidth) (control := control) (by omega) hfit (by omega) hcontrol
      have htail := ih (low := low + 1) (by omega)
      rw [correctionLeafOps, Program.opsWellFormed_append, hbit, htail]
      rfl

theorem correctionNodeOps_wellFormed
    {level : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high row depth remaining : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hselector : depth + remaining < high)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    Program.opsWellFormed level (width addressWidth outputWidth) 0 (outputWidth + 1)
      (correctionNodeOps table addressWidth outputWidth lowWidth row depth remaining) =
        true := by
  induction remaining generalizing row depth with
  | zero =>
      apply correctionLeafOps_wellFormed table (by simp [batchSize]) hfit
      simp [selectorFits, selectorWire, width]
      omega
  | succ remaining ih =>
      let address := lowWidth + remaining
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      have hnegative : (negativeAndGates address parent child).all
          (RGate.wellFormed (width addressWidth outputWidth)) = true := by
        simp [negativeAndGates, RGate.wellFormed, width, address, parent, child,
          selectorWire]
        omega
      have hnegative' := gateOps_wellFormed (inputBits := 0)
        (cbits := outputWidth + 1) hl hnegative
      have hleft := ih (row := row) (depth := depth + 1) (by omega)
      have hswitch : ([.cx parent child] : List RGate).all
          (RGate.wellFormed (width addressWidth outputWidth)) = true := by
        simp [RGate.wellFormed, width, parent, child, selectorWire]
        omega
      have hswitch' := gateOps_wellFormed (inputBits := 0)
        (cbits := outputWidth + 1) hl hswitch
      have hright := ih (row := row + 2 ^ remaining) (depth := depth + 1) (by omega)
      have herase := andUncomputeClean_wellFormed
        (level := level) (totalWidth := width addressWidth outputWidth)
        (inputBits := 0) (cbits := outputWidth + 1)
        (a := parent) (b := address) (c := child)
        (scratch := scratchBit outputWidth) hl
        (by simp [parent, selectorWire, width]; omega)
        (by simp [address, width]; omega)
        (by simp [child, selectorWire, width]; omega)
        (by simp [scratchBit])
        (by simp [parent, address, selectorWire]; omega)
      rw [correctionNodeOps, Program.opsWellFormed_append,
        Program.opsWellFormed_append, Program.opsWellFormed_append,
        Program.opsWellFormed_append, hnegative', hleft, hswitch', hright, herase]
      rfl

theorem correctionOps_wellFormed
    {level : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    Program.opsWellFormed level (width addressWidth outputWidth) 0 (outputWidth + 1)
      (correctionOps table addressWidth outputWidth lowWidth high) = true := by
  cases high with
  | zero =>
      apply correctionLeafOps_wellFormed table (by simp [batchSize]) hfit
      trivial
  | succ remaining =>
      let address := lowWidth + remaining
      let root := selectorWire addressWidth outputWidth 0
      have hroot : ([.x address, .cx address root, .x address] : List RGate).all
          (RGate.wellFormed (width addressWidth outputWidth)) = true := by
        simp [RGate.wellFormed, width, address, root, selectorWire]
        omega
      have hroot' := gateOps_wellFormed (inputBits := 0)
        (cbits := outputWidth + 1) hl hroot
      have hleft := correctionNodeOps_wellFormed hl table
        (high := remaining + 1) (row := 0) (depth := 0) (remaining := remaining)
        hsplit (by omega) hfit
      have hx : ([.x root] : List RGate).all
          (RGate.wellFormed (width addressWidth outputWidth)) = true := by
        simp [RGate.wellFormed, width, root, selectorWire]
        omega
      have hx' := gateOps_wellFormed (inputBits := 0)
        (cbits := outputWidth + 1) hl hx
      have hright := correctionNodeOps_wellFormed hl table
        (high := remaining + 1) (row := 2 ^ remaining) (depth := 0)
        (remaining := remaining) hsplit (by omega) hfit
      have hcx : ([.cx address root] : List RGate).all
          (RGate.wellFormed (width addressWidth outputWidth)) = true := by
        simp [RGate.wellFormed, width, address, root, selectorWire]
        omega
      have hcx' := gateOps_wellFormed (inputBits := 0)
        (cbits := outputWidth + 1) hl hcx
      rw [correctionOps, Program.opsWellFormed_append,
        Program.opsWellFormed_append, Program.opsWellFormed_append,
        Program.opsWellFormed_append, hroot', hleft, hx', hright, hcx']
      rfl

theorem program_wellFormed {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth lowWidth : Nat)
    (hlow : 0 < lowWidth) (hhigh : lowWidth + 2 ≤ addressWidth)
    (hfit : 2 ^ lowWidth ≤ outputWidth) :
    (program table addressWidth outputWidth lowWidth).wellFormed level = true := by
  have haddress : lowWidth ≤ addressWidth := by
    have _ := hlow
    omega
  have hmeasure := measureOutputOps_wellFormed
    (level := level) (addressWidth := addressWidth) (outputWidth := outputWidth)
    (bit := 0) (count := outputWidth) hl (by omega)
  have hprepare := prepareUnaryOps_wellFormed
    (level := level) (addressWidth := addressWidth) (lowWidth := lowWidth)
    hl haddress (by simpa [batchSize] using hfit)
  have hhadamard := unaryHadamardOps_wellFormed
    (level := level) (addressWidth := addressWidth) (outputWidth := outputWidth)
    (low := 0) (count := batchSize lowWidth) (lowWidth := lowWidth)
    hl (by omega) (by simpa [batchSize] using hfit)
  have hsplit : lowWidth + highWidth addressWidth lowWidth = addressWidth := by
    simp [highWidth]
    omega
  have hcorrection := correctionOps_wellFormed hl table hsplit
    (by simpa [batchSize] using hfit)
  have hclear := clearUnaryOps_wellFormed
    (level := level) (addressWidth := addressWidth) (lowWidth := lowWidth)
    hl haddress (by simpa [batchSize] using hfit)
  change Program.opsWellFormed level (width addressWidth outputWidth) 0
    (outputWidth + 1) (unlookupOps table addressWidth outputWidth lowWidth) = true
  rw [unlookupOps, Program.opsWellFormed_append, Program.opsWellFormed_append,
    Program.opsWellFormed_append, Program.opsWellFormed_append,
    Program.opsWellFormed_append, hmeasure, hprepare, hhadamard,
    hcorrection, hclear]
  rfl

/-! ## Independent semantic checkpoints -/

def measurementMask (addressWidth input : Nat) : Nat → Nat → Nat → Bool
  | _, 0, _ => false
  | bit, count + 1, creg =>
      Bool.xor
        (input.testBit (outputWire addressWidth bit) && creg.testBit bit)
        (measurementMask addressWidth input (bit + 1) count creg)

theorem phaseScalar_xor (d : Nat) (x y : Bool) :
    MeasuredUncompute.phaseScalar d (Bool.xor x y) =
      MeasuredUncompute.phaseScalar d x * MeasuredUncompute.phaseScalar d y := by
  cases x <;> cases y <;>
    simp [MeasuredUncompute.phaseScalar, Dy.mul_one, Dy.mul_neg, Dy.neg_neg]

theorem hVec_flipVec_hVec {d e q : Nat}
    (he : 4 * e = d) (h0 : 0 < e) (u : Vec d) :
    hVec q (flipVec q (hVec q u)) =
      fun i ↦ if i.testBit q then -u i else u i := by
  have hs := invSqrt2_sq_two he h0
  refine Vec.ext (fun i ↦ ?_)
  have hcancel : (i ^^^ (1 <<< q)) ^^^ (1 <<< q) = i :=
    Semantics.xor_cancel i q
  have htoggle : (i ^^^ (1 <<< q)).testBit q = !i.testBit q :=
    Semantics.testBit_xor_self i q
  cases hbit : i.testBit q <;>
    simp only [hVec, flipVec, hcancel, htoggle, hbit, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, if_false, if_true] <;>
    grind

theorem hadamardXHadamard_basis {level w q i : Nat}
    (hl : 3 ≤ level) (hq : q < w) :
    gateVec level w (.h q)
        (gateVec level w (.x q)
          (gateVec level w (.h q) (basis i : Vec (deg level)))) =
      MeasuredUncompute.phaseScalar (deg level) (i.testBit q) •
        (basis i : Vec (deg level)) := by
  have hh : (Gate.h q).wellFormedAt level w = true := by
    simp [Gate.wellFormedAt, hq, hl]
  have hx : (Gate.x q).wellFormedAt level w = true := by
    simp [Gate.wellFormedAt, hq]
  rw [gateVec_of_wf hh, gateVec_of_wf hx, gateVec_of_wf hh]
  change hVec q (flipVec q (hVec q (basis i))) = _
  rw [
    hVec_flipVec_hVec (four_dvd_deg hl) (Nat.two_pow_pos _)]
  refine Vec.ext (fun j ↦ ?_)
  by_cases hji : j = i
  · subst j
    rw [basis_self, Vec.smul_apply, basis_self]
    cases hbit : i.testBit q <;>
      simp [MeasuredUncompute.phaseScalar, Dy.mul_one]
  · rw [basis_of_ne hji, Vec.smul_apply, basis_of_ne hji]
    cases j.testBit q <;> simp [Dy.mul_zero, neg_zero]

def hadamardBlockVec {d : Nat} : Nat → Nat → Vec d → Vec d
  | _, 0, u => u
  | off, count + 1, u =>
      hadamardBlockVec (off + 1) count (hVec off u)

theorem hadamardBlockVec_smul {d off count : Nat}
    (c : Dy d) (u : Vec d) :
    hadamardBlockVec off count (c • u) =
      c • hadamardBlockVec off count u := by
  induction count generalizing off u with
  | zero => rfl
  | succ count ih =>
      rw [hadamardBlockVec, hadamardBlockVec, hVec_smul]
      exact ih (off := off + 1) (u := hVec off u)

def sameOutside (off count reference i : Nat) : Prop :=
  ∀ q, q < off ∨ off + count ≤ q →
    i.testBit q = reference.testBit q

theorem readField_eq_of_sameOutside
    {off count reference i field fieldWidth : Nat}
    (hsame : sameOutside off count reference i)
    (hdisjoint : field + fieldWidth ≤ off ∨ off + count ≤ field) :
    readField i field fieldWidth = readField reference field fieldWidth := by
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [testBit_readField, testBit_readField]
  by_cases hbit : bit < fieldWidth
  · simp only [hbit, decide_true, Bool.true_and]
    apply hsame
    rcases hdisjoint with hbefore | hafter
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · simp [hbit]

private theorem hVec_supportedOutside_succ
    {d off done reference : Nat} {u : Vec d}
    (hsupport : ∀ i, ¬sameOutside off done reference i →
      u i = Dy.zero d) :
    ∀ i, ¬sameOutside off (done + 1) reference i →
      hVec (off + done) u i = Dy.zero d := by
  intro i houtside
  have hi : ¬sameOutside off done reference i := by
    intro hsame
    apply houtside
    intro q hq
    apply hsame q
    rcases hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr (by omega)
  have hflip : ¬sameOutside off done reference
      (i ^^^ (1 <<< (off + done))) := by
    intro hsame
    apply houtside
    intro q hq
    have hne : q ≠ off + done := by
      rcases hq with hq | hq <;> omega
    rw [← Semantics.testBit_xor_of_ne hne i]
    apply hsame q
    rcases hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr (by omega)
  rw [hVec, hsupport i hi,
    hsupport (i ^^^ (1 <<< (off + done))) hflip]
  cases i.testBit (off + done) <;>
    simp [Dy.sub_eq_add_neg, Semantics.neg_zero, Dy.zero_add, Dy.mul_zero]

private theorem hadamardBlockVec_supportedOutside
    {d base reference : Nat} :
    ∀ done remaining (u : Vec d),
      (∀ i, ¬sameOutside base done reference i → u i = Dy.zero d) →
      ∀ i, ¬sameOutside base (done + remaining) reference i →
        hadamardBlockVec (base + done) remaining u i = Dy.zero d
  | done, 0, u, hsupport => by
      intro i houtside
      simpa [hadamardBlockVec] using
        hsupport i (by simpa using houtside)
  | done, remaining + 1, u, hsupport => by
      have hhead := hVec_supportedOutside_succ
        (off := base) (done := done) (reference := reference) hsupport
      have htail := hadamardBlockVec_supportedOutside
        (done + 1) remaining (hVec (base + done) u) hhead
      simpa [hadamardBlockVec, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using htail

theorem hadamardBlockVec_basis_sameOutside
    {d off count reference i : Nat}
    (hamp : hadamardBlockVec off count (basis reference : Vec d) i ≠
      Dy.zero d) :
    sameOutside off count reference i := by
  by_contra houtside
  apply hamp
  have hbase : ∀ j, ¬sameOutside off 0 reference j →
      (basis reference : Vec d) j = Dy.zero d := by
    intro j hj
    apply basis_of_ne
    intro hji
    subst j
    exact hj (fun _ _ ↦ rfl)
  have hzero := hadamardBlockVec_supportedOutside
    (base := off) (reference := reference) 0 count
      (basis reference : Vec d) hbase i (by simpa using houtside)
  simpa using hzero

theorem unaryHadamardOps_run
    {level w addressWidth low count : Nat}
    (hl : 3 ≤ level) (hfit : addressWidth + low + count ≤ w)
    (b : Branch (deg level)) :
    runOps level w (unaryHadamardOps addressWidth low count) b =
      [{ b with state :=
          hadamardBlockVec (outputWire addressWidth low) count b.state }] := by
  induction count generalizing low b with
  | zero => rfl
  | succ count ih =>
      have hq : outputWire addressWidth low < w := by
        simp [outputWire]
        omega
      have hwf : (Gate.h (outputWire addressWidth low)).wellFormedAt level w = true := by
        simp [Gate.wellFormedAt, hl, hq]
      rw [unaryHadamardOps, runOps_cons, runOp_gate,
        List.flatMap_singleton,
        ih (low := low + 1) (by omega),
        gateVec_of_wf hwf]
      rfl

theorem hadamardBlockVec_wf
    {level w off count : Nat} (hl : 3 ≤ level)
    (hfit : off + count ≤ w) {u : Vec (deg level)}
    (hu : WFVec (2 ^ w) u) :
    WFVec (2 ^ w) (hadamardBlockVec off count u) := by
  let start := Branch.mk [] 0 u 0
  let finish := Branch.mk [] 0 (hadamardBlockVec off count u) 0
  have hrun := unaryHadamardOps_run
    (addressWidth := off) (low := 0) (count := count) hl (by omega) start
  have hmem : finish ∈ runOps level w
      (unaryHadamardOps off 0 count) start := by
    rw [hrun]
    simp [start, finish, outputWire]
  exact wfVec_runOps level w _ hu hmem

def flipMaskBlockVec {d : Nat} : Nat → Nat → Nat → Nat → Vec d → Vec d
  | _, _, 0, _, u => u
  | off, bit, count + 1, mask, u =>
      flipMaskBlockVec (off + 1) (bit + 1) count mask
        (if mask.testBit bit then flipVec off u else u)

def walshParity : Nat → Nat → Nat → Nat → Nat → Bool
  | _, _, 0, _, _ => false
  | off, bit, count + 1, mask, i =>
      Bool.xor (i.testBit off && mask.testBit bit)
        (walshParity (off + 1) (bit + 1) count mask i)

def walshPhaseVec {d : Nat} (off bit count mask : Nat) (u : Vec d) : Vec d :=
  fun i ↦ MeasuredUncompute.phaseScalar d
    (walshParity off bit count mask i) * u i

theorem walshPhaseVec_basis {d off bit count mask i : Nat} :
    walshPhaseVec off bit count mask (basis i : Vec d) =
      MeasuredUncompute.phaseScalar d
          (walshParity off bit count mask i) •
        (basis i : Vec d) := by
  refine Vec.ext (fun j ↦ ?_)
  by_cases hji : j = i
  · subst j
    simp [walshPhaseVec, Vec.smul_apply, basis_self]
  · rw [walshPhaseVec, basis_of_ne hji, Dy.mul_zero,
      Vec.smul_apply, basis_of_ne hji, Dy.mul_zero]

private theorem hVec_hVec {d e q : Nat}
    (he : 4 * e = d) (h0 : 0 < e) (u : Vec d) :
    hVec q (hVec q u) = u := by
  have hs := invSqrt2_sq_two he h0
  refine Vec.ext (fun i ↦ ?_)
  have hcancel : (i ^^^ (1 <<< q)) ^^^ (1 <<< q) = i :=
    Semantics.xor_cancel i q
  have htoggle : (i ^^^ (1 <<< q)).testBit q = !i.testBit q :=
    Semantics.testBit_xor_self i q
  cases hbit : i.testBit q <;>
    simp only [hVec, hcancel, htoggle, hbit, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, if_false, if_true] <;>
    grind

private theorem hVec_comm {d q r : Nat} (hqr : q ≠ r) (u : Vec d) :
    hVec q (hVec r u) = hVec r (hVec q u) := by
  refine Vec.ext (fun i ↦ ?_)
  have hreadR : (i ^^^ (1 <<< q)).testBit r = i.testBit r :=
    Semantics.testBit_xor_of_ne hqr.symm i
  have hreadQ : (i ^^^ (1 <<< r)).testBit q = i.testBit q :=
    Semantics.testBit_xor_of_ne hqr i
  have hcross :
      (i ^^^ (1 <<< q)) ^^^ (1 <<< r) =
        (i ^^^ (1 <<< r)) ^^^ (1 <<< q) := by
    rw [Nat.xor_assoc, Nat.xor_assoc,
      Nat.xor_comm (1 <<< q) (1 <<< r)]
  cases hq : i.testBit q <;> cases hr : i.testBit r <;>
    simp only [hVec, hq, hr, hreadQ, hreadR, hcross,
      Bool.false_eq_true, if_false, if_true] <;>
    grind

private theorem hVec_flipVec_comm {d q r : Nat} (hqr : q ≠ r) (u : Vec d) :
    hVec q (flipVec r u) = flipVec r (hVec q u) := by
  refine Vec.ext (fun i ↦ ?_)
  have hreadQ : (i ^^^ (1 <<< r)).testBit q = i.testBit q :=
    Semantics.testBit_xor_of_ne hqr i
  have hcross :
      (i ^^^ (1 <<< q)) ^^^ (1 <<< r) =
        (i ^^^ (1 <<< r)) ^^^ (1 <<< q) := by
    rw [Nat.xor_assoc, Nat.xor_assoc,
      Nat.xor_comm (1 <<< q) (1 <<< r)]
  cases hq : i.testBit q <;>
    simp [hVec, flipVec, hq, hreadQ, hcross]

private theorem hadamardBlockVec_hVec_comm {d q off count : Nat}
    (hq : q < off) (u : Vec d) :
    hadamardBlockVec off count (hVec q u) =
      hVec q (hadamardBlockVec off count u) := by
  induction count generalizing off u with
  | zero => rfl
  | succ count ih =>
      rw [hadamardBlockVec, hadamardBlockVec,
        hVec_comm (show off ≠ q by omega)]
      exact ih (off := off + 1) (u := hVec off u) (by omega)

private theorem hadamardBlockVec_flipVec_comm {d q off count : Nat}
    (hq : q < off) (u : Vec d) :
    hadamardBlockVec off count (flipVec q u) =
      flipVec q (hadamardBlockVec off count u) := by
  induction count generalizing off u with
  | zero => rfl
  | succ count ih =>
      rw [hadamardBlockVec, hadamardBlockVec,
        hVec_flipVec_comm (show off ≠ q by omega)]
      exact ih (off := off + 1) (u := hVec off u) (by omega)

private theorem flipMaskBlockVec_hVec_comm
    {d q off bit count mask : Nat} (hq : q < off) (u : Vec d) :
    flipMaskBlockVec off bit count mask (hVec q u) =
      hVec q (flipMaskBlockVec off bit count mask u) := by
  induction count generalizing off bit u with
  | zero => rfl
  | succ count ih =>
      rw [flipMaskBlockVec, flipMaskBlockVec]
      have hhead :
          (if mask.testBit bit then flipVec off (hVec q u) else hVec q u) =
            hVec q (if mask.testBit bit then flipVec off u else u) := by
        by_cases hmask : mask.testBit bit
        · rw [if_pos hmask, if_pos hmask]
          exact (hVec_flipVec_comm (show q ≠ off by omega) u).symm
        · rw [if_neg hmask, if_neg hmask]
      rw [hhead]
      exact ih (off := off + 1) (bit := bit + 1)
        (u := if mask.testBit bit then flipVec off u else u) (by omega)

private theorem walshOne {d e q : Nat}
    (he : 4 * e = d) (h0 : 0 < e) (selected : Bool) (u : Vec d) :
    hVec q (if selected then flipVec q (hVec q u) else hVec q u) =
      fun i ↦ MeasuredUncompute.phaseScalar d (i.testBit q && selected) * u i := by
  cases selected with
  | false =>
      simp only [Bool.false_eq_true, if_false, Bool.and_false]
      rw [hVec_hVec he h0]
      refine Vec.ext (fun i ↦ ?_)
      simp [MeasuredUncompute.phaseScalar, Dy.one_mul]
  | true =>
      simp only [if_true, Bool.and_true]
      rw [hVec_flipVec_hVec he h0]
      refine Vec.ext (fun i ↦ ?_)
      cases hbit : i.testBit q with
      | false =>
          simp [MeasuredUncompute.phaseScalar, Dy.one_mul]
      | true =>
          simp only [if_true, MeasuredUncompute.phaseScalar]
          exact neg_eq_neg_one_mul _

theorem hadamardFlipMaskHadamard {d e : Nat}
    (he : 4 * e = d) (h0 : 0 < e) :
    ∀ off bit count mask (u : Vec d),
      hadamardBlockVec off count
          (flipMaskBlockVec off bit count mask
            (hadamardBlockVec off count u)) =
        fun i ↦ MeasuredUncompute.phaseScalar d
          (walshParity off bit count mask i) * u i := by
  intro off bit count
  induction count generalizing off bit with
  | zero =>
      intro mask u
      refine Vec.ext (fun i ↦ ?_)
      simp [hadamardBlockVec, flipMaskBlockVec, walshParity,
        MeasuredUncompute.phaseScalar, Dy.one_mul]
  | succ count ih =>
      intro mask u
      by_cases hmask : mask.testBit bit
      · have hmaskTrue : mask.testBit bit = true := hmask
        simp only [hadamardBlockVec, flipMaskBlockVec, hmaskTrue, if_true,
          walshParity, Bool.and_true]
        rw [← flipMaskBlockVec_hVec_comm (show off < off + 1 by omega)]
        rw [← hadamardBlockVec_flipVec_comm (show off < off + 1 by omega)]
        rw [← hadamardBlockVec_hVec_comm (show off < off + 1 by omega)]
        rw [ih (off := off + 1) (bit := bit + 1) mask
          (hVec off (flipVec off (hVec off u)))]
        rw [hVec_flipVec_hVec he h0]
        refine Vec.ext (fun i ↦ ?_)
        rw [phaseScalar_xor]
        let p := MeasuredUncompute.phaseScalar d
          (walshParity (off + 1) (bit + 1) count mask i)
        cases hi : i.testBit off with
        | false =>
            simp only [hi, Bool.false_eq_true, if_false]
            change p * u i = (Dy.one d * p) * u i
            rw [Dy.one_mul]
        | true =>
            simp only [hi, if_true]
            change p * (-u i) = ((-Dy.one d) * p) * u i
            calc
              p * (-u i) = -(p * u i) := Dy.mul_neg _ _
              _ = (-Dy.one d) * (p * u i) := neg_eq_neg_one_mul _
              _ = ((-Dy.one d) * p) * u i := (Dy.mul_assoc _ _ _).symm
      · have hmaskFalse : mask.testBit bit = false :=
          Bool.eq_false_of_not_eq_true hmask
        simp only [hadamardBlockVec, flipMaskBlockVec, hmaskFalse,
          Bool.false_eq_true, if_false, walshParity, Bool.and_false,
          Bool.false_xor]
        rw [← flipMaskBlockVec_hVec_comm (show off < off + 1 by omega)]
        rw [← hadamardBlockVec_hVec_comm (show off < off + 1 by omega)]
        rw [ih (off := off + 1) (bit := bit + 1) mask
          (hVec off (hVec off u))]
        rw [hVec_hVec he h0]

theorem measurementMask_writeBit_before
    (addressWidth input creg start count written : Nat) (value : Bool)
    (hwritten : written < start) :
    measurementMask addressWidth input start count
        (writeBit creg written value) =
      measurementMask addressWidth input start count creg := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      rw [measurementMask, measurementMask]
      rw [testBit_writeBit_of_ne (by omega), ih (start + 1) (by omega)]

theorem measurementMask_writeOutput_before
    (addressWidth input creg start count written : Nat) (value : Bool)
    (hwritten : written < start) :
    measurementMask addressWidth
        (writeBit input (outputWire addressWidth written) value)
        start count creg =
      measurementMask addressWidth input start count creg := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      rw [measurementMask, measurementMask]
      rw [testBit_writeBit_of_ne (by simp [outputWire]; omega),
        ih (start + 1) (by omega)]

theorem measurementScalar_eq_mul_phaseScalar {d : Nat}
    (c : Dy d) (b : Bool) :
    MeasuredUncompute.measurementScalar d c b =
      c * MeasuredUncompute.phaseScalar d b := by
  cases b <;>
    simp [MeasuredUncompute.measurementScalar,
      MeasuredUncompute.phaseScalar, Dy.mul_neg, Dy.mul_one]

theorem mul_four_reorder {d : Nat} (a b c e : Dy d) :
    (a * b) * (c * e) = (c * a) * (b * e) := by
  calc
    (a * b) * (c * e) = a * (b * (c * e)) := Dy.mul_assoc _ _ _
    _ = a * (c * (b * e)) := by
      rw [← Dy.mul_assoc b c e, Dy.mul_comm b c, Dy.mul_assoc c b e]
    _ = (a * c) * (b * e) := (Dy.mul_assoc _ _ _).symm
    _ = (c * a) * (b * e) := by rw [Dy.mul_comm a c]

theorem measureOutputOps_creg_before {level w addressWidth bit count : Nat}
    {rec : List Bool} {creg input : Nat} {u : Vec (deg level)}
    {b : Branch (deg level)} (hb :
      b ∈ runOps level w (measureOutputOps addressWidth bit count)
        (Branch.mk rec creg u input)) :
    ∀ c, c < bit → b.creg.testBit c = creg.testBit c := by
  induction count generalizing bit rec creg input u b with
  | zero =>
      rw [measureOutputOps, runOps_nil, List.mem_singleton] at hb
      subst b
      intro c _
      rfl
  | succ count ih =>
      intro c hc
      rw [measureOutputOps, runOps_append, List.mem_flatMap] at hb
      obtain ⟨x, hx, hxb⟩ := hb
      have htail := ih (bit := bit + 1) (rec := x.outcomes)
        (creg := x.creg) (u := x.state) (b := b) hxb c (by omega)
      have hxcreg : x.creg.testBit c = creg.testBit c := by
        simp [runOps_cons, runOp_gate, runOp_measure, runOp_branch,
          runOps_nil, CRef.read, testBit_writeBit] at hx
        rcases hx with rfl | rfl <;>
          rw [testBit_writeBit_of_ne (by omega)]
      exact htail.trans hxcreg

theorem measureOutputOps_outcomes_length
    {level w addressWidth bit count : Nat}
    {rec : List Bool} {creg input : Nat} {u : Vec (deg level)}
    {b : Branch (deg level)}
    (hb : b ∈ runOps level w (measureOutputOps addressWidth bit count)
      (Branch.mk rec creg u input)) :
    b.outcomes.length = rec.length + count := by
  induction count generalizing bit rec creg input u b with
  | zero =>
      rw [measureOutputOps, runOps_nil, List.mem_singleton] at hb
      subst b
      simp
  | succ count ih =>
      rw [measureOutputOps, runOps_append, List.mem_flatMap] at hb
      obtain ⟨x, hx, hxb⟩ := hb
      have hxlength : x.outcomes.length = rec.length + 1 := by
        simp [runOps_cons, runOp_gate, runOp_measure, runOp_branch,
          runOps_nil, CRef.read, testBit_writeBit] at hx
        rcases hx with rfl | rfl <;> simp
      have htail := ih hxb
      omega

theorem measureOutputOps_mask {level w addressWidth bit count i : Nat}
    (hl : 3 ≤ level) (hq : addressWidth + bit + count ≤ w)
    (rec : List Bool) (creg input : Nat) (b : Branch (deg level))
    (hb : b ∈ runOps level w (measureOutputOps addressWidth bit count)
      (Branch.mk rec creg (basis i) input)) :
    b.state = (Dy.invSqrt2 (deg level)) ^ count •
      (MeasuredUncompute.phaseScalar (deg level)
          (measurementMask addressWidth i bit count b.creg) •
        (basis (MeasuredUncompute.clearBits addressWidth bit count i) :
          Vec (deg level))) := by
  induction count generalizing bit i rec creg b with
  | zero =>
      rw [measureOutputOps, runOps_nil, List.mem_singleton] at hb
      subst b
      simp [measurementMask, MeasuredUncompute.clearBits, Dy.pow_zero_eq,
        MeasuredUncompute.phaseScalar, Vec.one_smul]
  | succ count ih =>
      let q := outputWire addressWidth bit
      let c := Dy.invSqrt2 (deg level)
      have hqw : q < w := by
        simp [q, outputWire]
        omega
      change b ∈ runOps level w
        ([.gate (.h q), .measure q bit] ++
          [.branch (.localBit bit) [.gate (.x q)] []] ++
          measureOutputOps addressWidth (bit + 1) count)
        (Branch.mk rec creg (basis i) input) at hb
      rw [runOps_append, List.mem_flatMap] at hb
      obtain ⟨x, hx, hxb⟩ := hb
      rw [runOps_append, Lookup3.xMeasure_basis hl hqw] at hx
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at hx
      simp only [runOps_singleton, runOp_branch, CRef.read,
        testBit_writeBit] at hx
      rcases hx with hx | hx
      · rw [if_neg (by simp)] at hx
        rw [runOps_nil, List.mem_singleton] at hx
        subst x
        let base := Branch.mk (false :: rec) (writeBit creg bit false)
          (basis (writeBit i q false) : Vec (deg level)) input
        change b ∈ runOps level w (measureOutputOps addressWidth (bit + 1) count)
          (smulBranch c base) at hxb
        rw [(runOps_smul level w).2, List.mem_map] at hxb
        obtain ⟨z, hz, rfl⟩ := hxb
        have hs := ih (bit := bit + 1)
          (i := writeBit i q false) (rec := false :: rec)
          (creg := writeBit creg bit false) (b := z) (by omega)
          (by simpa [base] using hz)
        have hmaskCreg := measureOutputOps_creg_before hz bit (by omega)
        simp only [smulBranch]
        rw [hs, measurementMask,
          measurementMask_writeOutput_before _ _ _ _ _ _ _ (by omega),
          hmaskCreg,
          testBit_writeBit, Bool.and_false, Bool.false_xor,
          MeasuredUncompute.clearBits]
        simp only [q, outputWire, MeasuredUncompute.outputWire,
          MeasuredUncompute.clearOutputBit, c, Dy.pow_succ, Vec.smul_smul]
        rw [← Dy.mul_assoc,
          Dy.mul_comm (Dy.invSqrt2 (deg level))
            (Dy.invSqrt2 (deg level) ^ count)]
      · rw [if_pos (by simp)] at hx
        rw [runOp_gate, List.mem_singleton] at hx
        subst x
        let s := MeasuredUncompute.measurementScalar (deg level) c (i.testBit q)
        let base := Branch.mk (true :: rec) (writeBit creg bit true)
          (basis (writeBit i q false) : Vec (deg level)) input
        have hflip : writeBit i q true ^^^ (1 <<< q) = writeBit i q false := by
          rw [MeasuredUncompute.xor_two_pow_eq_clear (testBit_writeBit _ _ _),
            writeBit_writeBit]
        have hhead : gateVec level w (.x q)
            (if i.testBit q then
              -(c • (basis (writeBit i q true) : Vec (deg level)))
            else c • basis (writeBit i q true)) =
            s • (basis (writeBit i q false) : Vec (deg level)) := by
          rw [MeasuredUncompute.measurementState, gateVec_smul,
            Semantics.apply_x hqw, hflip]
        rw [hhead] at hxb
        change b ∈ runOps level w (measureOutputOps addressWidth (bit + 1) count)
          (smulBranch s base) at hxb
        rw [(runOps_smul level w).2, List.mem_map] at hxb
        obtain ⟨z, hz, rfl⟩ := hxb
        have hs := ih (bit := bit + 1)
          (i := writeBit i q false) (rec := true :: rec)
          (creg := writeBit creg bit true) (b := z) (by omega)
          (by simpa [base] using hz)
        have hmaskCreg := measureOutputOps_creg_before
          (level := level) (w := w) hz bit (by omega)
        simp only [smulBranch]
        dsimp [s]
        rw [hs, measurementMask,
          measurementMask_writeOutput_before _ _ _ _ _ _ _ (by omega),
          hmaskCreg,
          testBit_writeBit, Bool.and_true, MeasuredUncompute.clearBits,
          phaseScalar_xor, measurementScalar_eq_mul_phaseScalar]
        simp only [q, outputWire, MeasuredUncompute.outputWire,
          MeasuredUncompute.clearOutputBit, c, Dy.pow_succ, Vec.smul_smul]
        rw [mul_four_reorder]

/-! ### Classical-register-aware uniform actions -/

/-- A basis action for one fixed classical input and register extends to a
finite superposition.  Fixing the classical data permits the output map to
depend on that data, as the correction evaluator does. -/
theorem runOps_superpose_fixed
    {level w input : Nat} {ops : List Op} {out : Nat → Nat}
    {amp : List Bool → Dy (deg level)} {dom : Nat → Prop}
    (rec : List Bool) (cr : Nat)
    (hcl : ∀ i, i < 2 ^ w → dom i →
      ∀ b ∈ runOps level w ops (Branch.mk rec cr (basis i) input),
        b.state = amp b.outcomes • (basis (out i) : Vec (deg level))) :
    ∀ (L : List Nat) (a : Nat → Dy (deg level)),
      (∀ i ∈ L, i < 2 ^ w ∧ dom i) →
        ∀ b ∈ runOps level w ops
          (Branch.mk rec cr (superpose id a L) input),
          b.state = amp b.outcomes • superpose out a L
  | [], a, _, b, hb => by
    rw [show superpose (d := deg level) id a [] = Vec.zero (deg level) from rfl] at hb
    rw [runOps_zero_state level w ops rec cr input hb,
      show superpose (d := deg level) out a [] = Vec.zero (deg level) from rfl,
      Vec.smul_zero]
  | i :: L, a, hmem, b, hb => by
    have hi := hmem i (List.mem_cons_self ..)
    have hsplit :
        runOps level w ops
            (Branch.mk rec cr (superpose id a (i :: L)) input) =
          List.zipWith addBranch
            ((runOps level w ops
              (Branch.mk rec cr (basis i) input)).map (smulBranch (a i)))
            (runOps level w ops
              (Branch.mk rec cr (superpose id a L) input)) := by
      show runOps level w ops
        (Branch.mk rec cr (a i • basis (id i) + superpose id a L) input) = _
      rw [(runOps_add level w).2 ops rec cr input
        (a i • basis (id i)) (superpose id a L)]
      congr 1
      exact (runOps_smul level w).2 ops (a i)
        (Branch.mk rec cr (basis (id i)) input)
    have hshape :
        shape ((runOps level w ops
          (Branch.mk rec cr (basis i) input)).map (smulBranch (a i))) =
        shape (runOps level w ops
          (Branch.mk rec cr (superpose id a L) input)) := by
      rw [shape_map_smulBranch, (shape_runOps level w).2,
        (shape_runOps level w).2]
    rw [hsplit] at hb
    have hX : ∀ x ∈ (runOps level w ops
        (Branch.mk rec cr (basis i) input)).map (smulBranch (a i)),
        x.state = a i •
          (amp x.outcomes • (basis (out i) : Vec (deg level))) := by
      intro x hx
      obtain ⟨x₀, hx₀, hxe⟩ := List.mem_map.mp hx
      rw [← hxe]
      show a i • x₀.state = _
      rw [hcl i hi.1 hi.2 x₀ hx₀]
      rfl
    have hY := runOps_superpose_fixed rec cr hcl L a
      (fun j hj ↦ hmem j (List.mem_cons_of_mem _ hj))
    have hsum := zipWith_addBranch_mem
      (g := fun s ↦ a i •
        (amp s • (basis (out i) : Vec (deg level))))
      (h := fun s ↦ amp s • superpose out a L)
      hshape hX hY b hb
    rw [hsum]
    refine Vec.ext (fun k ↦ ?_)
    show a i * (amp b.outcomes * (basis (out i) : Vec (deg level)) k)
        + amp b.outcomes * superpose out a L k =
      amp b.outcomes * (a i * (basis (out (id i)) : Vec (deg level)) k
        + superpose out a L k)
    rw [Dy.left_distrib, ← Dy.mul_assoc, ← Dy.mul_assoc,
      Dy.mul_comm (a i) (amp b.outcomes)]
    rfl

def retainedCreg (count creg : Nat) : Nat :=
  readField creg 0 count

def ImplementsRetainedU (level w input retained : Nat) (dom : Nat → Prop)
    (out : Nat → Nat → Nat) (c : Dy (deg level)) (ops : List Op) : Prop :=
  ∀ i, i < 2 ^ w → dom i → ∀ rec cr,
    ∀ b ∈ runOps level w ops (Branch.mk rec cr (basis i) input),
      retainedCreg retained b.creg = retainedCreg retained cr ∧
        b.state = c ^ (b.outcomes.length - rec.length) •
          (basis (out (retainedCreg retained cr) i) : Vec (deg level))

/-- A retained-register action extends to finite superpositions for a fixed
incoming classical register.  The result preserves cbits strictly below
`retained`.  Cbit `retained`, used as reusable scratch, remains unconstrained. -/
theorem ImplementsRetainedU.superpose {level w input retained : Nat}
    {dom : Nat → Prop} {out : Nat → Nat → Nat}
    {c : Dy (deg level)} {ops : List Op}
    (h : ImplementsRetainedU level w input retained dom out c ops)
    {reference : Nat} (hrefRange : reference < 2 ^ w)
    (hrefDom : dom reference) (rec : List Bool) (cr : Nat)
    (L : List Nat) (a : Nat → Dy (deg level))
    (hsupport : ∀ i ∈ L, i < 2 ^ w ∧ dom i) :
    ∀ b ∈ runOps level w ops
      (Branch.mk rec cr (Semantics.superpose id a L) input),
      retainedCreg retained b.creg = retainedCreg retained cr ∧
        b.state = c ^ (b.outcomes.length - rec.length) •
          Semantics.superpose (out (retainedCreg retained cr)) a L := by
  intro b hb
  constructor
  · have hbshape : (b.outcomes, b.creg, b.input) ∈
        shape (runOps level w ops
          (Branch.mk rec cr (Semantics.superpose id a L) input)) :=
      List.mem_map_of_mem hb
    rw [(shape_runOps level w).2 ops rec cr input
        (Semantics.superpose id a L),
      ← (shape_runOps level w).2 ops rec cr input
        (basis reference : Vec (deg level))] at hbshape
    obtain ⟨b₀, hb₀, hshape⟩ := List.mem_map.mp hbshape
    have hcreg : b₀.creg = b.creg :=
      congrArg (fun p : List Bool × Nat × Nat ↦ p.2.1) hshape
    rw [← hcreg]
    exact (h reference hrefRange hrefDom rec cr b₀ hb₀).1
  · apply runOps_superpose_fixed
      (out := out (retainedCreg retained cr))
      (amp := fun outcomes ↦ c ^ (outcomes.length - rec.length))
      (dom := dom) (rec := rec) (cr := cr)
    · intro i hi hdom b₀ hb₀
      exact (h i hi hdom rec cr b₀ hb₀).2
    · exact hsupport
    · exact hb

theorem ImplementsRetainedU.mono {level w input retained : Nat}
    {dom dom' : Nat → Prop} {out : Nat → Nat → Nat}
    {c : Dy (deg level)} {ops : List Op}
    (h : ImplementsRetainedU level w input retained dom out c ops)
    (hsub : ∀ i, dom' i → dom i) :
    ImplementsRetainedU level w input retained dom' out c ops :=
  fun i hi hd rec cr b hb ↦ h i hi (hsub i hd) rec cr b hb

theorem ImplementsRetainedU.append {level w input retained : Nat}
    {dom₁ dom₂ : Nat → Prop} {out₁ out₂ : Nat → Nat → Nat}
    {c : Dy (deg level)} {a b : List Op}
    (h₁ : ImplementsRetainedU level w input retained dom₁ out₁ c a)
    (h₂ : ImplementsRetainedU level w input retained dom₂ out₂ c b)
    (hrange : ∀ cr i, i < 2 ^ w → dom₁ i → out₁ cr i < 2 ^ w)
    (hdom : ∀ cr i, i < 2 ^ w → dom₁ i → dom₂ (out₁ cr i)) :
    ImplementsRetainedU level w input retained dom₁
      (fun cr i ↦ out₂ cr (out₁ cr i)) c (a ++ b) := by
  intro i hi hd rec cr br hbr
  rw [runOps_append, List.mem_flatMap] at hbr
  obtain ⟨x, hx, hxb⟩ := hbr
  have hxspec := h₁ i hi hd rec cr x hx
  have hxretain := hxspec.1
  have hxstate := hxspec.2
  have hxi : x.input = input := input_runOps level w a hx
  have hxe : x = smulBranch (c ^ (x.outcomes.length - rec.length))
      (Branch.mk x.outcomes x.creg
        (basis (out₁ (retainedCreg retained cr) i)) input) := by
    cases x with
    | mk outcomes creg state branchInput =>
        simp only [smulBranch] at hxi ⊢
        subst branchInput
        rw [← hxstate]
  rw [hxe, (runOps_smul level w).2 b _ _, List.mem_map] at hxb
  obtain ⟨y, hy, hyb⟩ := hxb
  have hyspec := h₂ (out₁ (retainedCreg retained cr) i)
    (hrange (retainedCreg retained cr) i hi hd)
    (hdom (retainedCreg retained cr) i hi hd)
    x.outcomes x.creg y hy
  have hyretain := hyspec.1
  have hystate := hyspec.2
  rw [hxretain] at hystate
  have hlo : rec.length ≤ x.outcomes.length :=
    runOps_record_le level w a rec cr input _ hx
  have hhi : x.outcomes.length ≤ y.outcomes.length :=
    runOps_record_le level w b x.outcomes x.creg input _ hy
  have hout : br.outcomes = y.outcomes := by rw [← hyb]; rfl
  have hcreg : br.creg = y.creg := by
    rw [← hyb]
    rfl
  have hstate : br.state =
      (c ^ (x.outcomes.length - rec.length)) • y.state := by
    rw [← hyb]
    rfl
  constructor
  · rw [hcreg]
    exact hyretain.trans hxretain
  · rw [hstate, hystate, Vec.smul_smul, ← Dy.pow_add, hout]
    congr 2
    omega

def ImplementsRetainedPhaseU
    (level w input retained : Nat) (dom : Nat → Prop)
    (out : Nat → Nat → Nat) (phase : Nat → Nat → Bool)
    (c : Dy (deg level)) (ops : List Op) : Prop :=
  ∀ i, i < 2 ^ w → dom i → ∀ rec cr,
    ∀ b ∈ runOps level w ops (Branch.mk rec cr (basis i) input),
      retainedCreg retained b.creg = retainedCreg retained cr ∧
        b.state = c ^ (b.outcomes.length - rec.length) •
          (MeasuredUncompute.phaseScalar (deg level)
              (phase (retainedCreg retained cr) i) •
            (basis (out (retainedCreg retained cr) i) : Vec (deg level)))

theorem ImplementsRetainedU.appendPhase
    {level w input retained : Nat} {dom₁ dom₂ : Nat → Prop}
    {out₁ out₂ : Nat → Nat → Nat}
    {phase : Nat → Nat → Bool} {c : Dy (deg level)} {a b : List Op}
    (h₁ : ImplementsRetainedU level w input retained dom₁ out₁ c a)
    (h₂ : ImplementsRetainedPhaseU level w input retained
      dom₂ out₂ phase c b)
    (hrange : ∀ cr i, i < 2 ^ w → dom₁ i → out₁ cr i < 2 ^ w)
    (hdom : ∀ cr i, i < 2 ^ w → dom₁ i → dom₂ (out₁ cr i)) :
    ImplementsRetainedPhaseU level w input retained dom₁
      (fun cr i ↦ out₂ cr (out₁ cr i))
      (fun cr i ↦ phase cr (out₁ cr i)) c (a ++ b) := by
  intro i hi hd rec cr br hbr
  rw [runOps_append, List.mem_flatMap] at hbr
  obtain ⟨x, hx, hxb⟩ := hbr
  have hxspec := h₁ i hi hd rec cr x hx
  have hxretain := hxspec.1
  have hxstate := hxspec.2
  have hxi : x.input = input := input_runOps level w a hx
  have hxe : x = smulBranch (c ^ (x.outcomes.length - rec.length))
      (Branch.mk x.outcomes x.creg
        (basis (out₁ (retainedCreg retained cr) i)) input) := by
    cases x with
    | mk outcomes creg state branchInput =>
        simp only [smulBranch] at hxi ⊢
        subst branchInput
        rw [← hxstate]
  rw [hxe, (runOps_smul level w).2 b _ _, List.mem_map] at hxb
  obtain ⟨y, hy, hyb⟩ := hxb
  have hyspec := h₂ (out₁ (retainedCreg retained cr) i)
    (hrange (retainedCreg retained cr) i hi hd)
    (hdom (retainedCreg retained cr) i hi hd)
    x.outcomes x.creg y hy
  have hyretain := hyspec.1
  have hystate := hyspec.2
  rw [hxretain] at hystate
  have hlo : rec.length ≤ x.outcomes.length :=
    runOps_record_le level w a rec cr input _ hx
  have hhi : x.outcomes.length ≤ y.outcomes.length :=
    runOps_record_le level w b x.outcomes x.creg input _ hy
  have hout : br.outcomes = y.outcomes := by rw [← hyb]; rfl
  have hcreg : br.creg = y.creg := by rw [← hyb]; rfl
  have hstate : br.state =
      (c ^ (x.outcomes.length - rec.length)) • y.state := by
    rw [← hyb]
    rfl
  constructor
  · rw [hcreg]
    exact hyretain.trans hxretain
  · rw [hstate, hystate, Vec.smul_smul, ← Dy.pow_add, hout]
    congr 2
    omega

theorem ImplementsRetainedPhaseU.append
    {level w input retained : Nat} {dom₁ dom₂ : Nat → Prop}
    {out₁ out₂ : Nat → Nat → Nat}
    {phase : Nat → Nat → Bool} {c : Dy (deg level)} {a b : List Op}
    (h₁ : ImplementsRetainedPhaseU level w input retained
      dom₁ out₁ phase c a)
    (h₂ : ImplementsRetainedU level w input retained dom₂ out₂ c b)
    (hrange : ∀ cr i, i < 2 ^ w → dom₁ i → out₁ cr i < 2 ^ w)
    (hdom : ∀ cr i, i < 2 ^ w → dom₁ i → dom₂ (out₁ cr i)) :
    ImplementsRetainedPhaseU level w input retained dom₁
      (fun cr i ↦ out₂ cr (out₁ cr i)) phase c (a ++ b) := by
  intro i hi hd rec cr br hbr
  rw [runOps_append, List.mem_flatMap] at hbr
  obtain ⟨x, hx, hxb⟩ := hbr
  have hxspec := h₁ i hi hd rec cr x hx
  have hxretain := hxspec.1
  have hxstate := hxspec.2
  have hxi : x.input = input := input_runOps level w a hx
  let s := MeasuredUncompute.phaseScalar (deg level)
    (phase (retainedCreg retained cr) i)
  let base := Branch.mk x.outcomes x.creg
    (basis (out₁ (retainedCreg retained cr) i) : Vec (deg level)) input
  have hxe : x = smulBranch (c ^ (x.outcomes.length - rec.length))
      (smulBranch s base) := by
    cases x with
    | mk outcomes creg state branchInput =>
        simp only [smulBranch, base] at hxi ⊢
        subst branchInput
        rw [← hxstate]
  rw [hxe, (runOps_smul level w).2 b _ _, List.mem_map] at hxb
  obtain ⟨y, hy, hyb⟩ := hxb
  change y ∈ runOps level w b (smulBranch s base) at hy
  rw [(runOps_smul level w).2 b s base, List.mem_map] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hzspec := h₂ (out₁ (retainedCreg retained cr) i)
    (hrange (retainedCreg retained cr) i hi hd)
    (hdom (retainedCreg retained cr) i hi hd)
    x.outcomes x.creg z hz
  have hzretain := hzspec.1
  have hzstate := hzspec.2
  rw [hxretain] at hzstate
  have hlo : rec.length ≤ x.outcomes.length :=
    runOps_record_le level w a rec cr input _ hx
  have hhi : x.outcomes.length ≤ z.outcomes.length :=
    runOps_record_le level w b x.outcomes x.creg input _ hz
  have hout : br.outcomes = z.outcomes := by
    rw [← hyb, ← hzy]
    rfl
  have hcreg : br.creg = z.creg := by
    rw [← hyb, ← hzy]
    rfl
  have hstate : br.state =
      (c ^ (x.outcomes.length - rec.length)) • (s • z.state) := by
    rw [← hyb, ← hzy]
    rfl
  constructor
  · rw [hcreg]
    exact hzretain.trans hxretain
  · rw [hstate, hzstate]
    simp only [Vec.smul_smul]
    have hmul : c ^ (x.outcomes.length - rec.length) *
        (s * c ^ (z.outcomes.length - x.outcomes.length)) =
        (c ^ (x.outcomes.length - rec.length) *
          c ^ (z.outcomes.length - x.outcomes.length)) * s := by
      calc
        _ = c ^ (x.outcomes.length - rec.length) *
            (c ^ (z.outcomes.length - x.outcomes.length) * s) := by
              rw [Dy.mul_comm s]
        _ = _ := (Dy.mul_assoc _ _ _).symm
    have hlength : (x.outcomes.length - rec.length) +
        (z.outcomes.length - x.outcomes.length) =
        z.outcomes.length - rec.length := by omega
    rw [hmul, ← Dy.pow_add, hlength, hout]

theorem retainedCreg_writeBit_of_le {retained cr scratch : Nat} (value : Bool)
    (hretain : retained ≤ scratch) :
    retainedCreg retained (writeBit cr scratch value) = retainedCreg retained cr := by
  apply Nat.eq_of_testBit_eq
  intro bit
  simp only [retainedCreg, testBit_readField, Nat.zero_add]
  by_cases hbit : bit < retained
  · simp only [hbit, decide_true, Bool.true_and]
    rw [testBit_writeBit_of_ne (by omega)]
  · simp [hbit]

theorem retainedCreg_testBit {count creg bit : Nat} (hbit : bit < count) :
    (retainedCreg count creg).testBit bit = creg.testBit bit := by
  simp [retainedCreg, testBit_readField, hbit]

theorem measurementMask_retainedCreg
    {addressWidth input start count retained creg : Nat}
    (hretain : start + count ≤ retained) :
    measurementMask addressWidth input start count
        (retainedCreg retained creg) =
      measurementMask addressWidth input start count creg := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      rw [measurementMask, measurementMask,
        retainedCreg_testBit (by omega), ih (by omega)]

def correctionBitEval (table : List Nat)
    (addressWidth outputWidth lowWidth row low : Nat) (control : Option Nat) :
    Nat → Nat → Nat → Nat → Nat
  | _, 0, _, i => i
  | bit, count + 1, mask, i =>
      let word := Lookup.value table outputWidth (row * batchSize lowWidth + low)
      let next := if word.testBit bit && mask.testBit bit then
        RGate.act (correctionGate addressWidth low control) i
      else i
      correctionBitEval table addressWidth outputWidth lowWidth row low control
        (bit + 1) count mask next

def correctionLeafEval (table : List Nat)
    (addressWidth outputWidth lowWidth row : Nat) (control : Option Nat) :
    Nat → Nat → Nat → Nat → Nat
  | _, 0, _, i => i
  | low, count + 1, mask, i =>
      correctionLeafEval table addressWidth outputWidth lowWidth row control
        (low + 1) count mask
        (correctionBitEval table addressWidth outputWidth lowWidth row low control
          0 outputWidth mask i)

def wordMaskParity (word : Nat) : Nat → Nat → Nat → Bool
  | _, 0, _ => false
  | bit, count + 1, mask =>
      Bool.xor (word.testBit bit && mask.testBit bit)
        (wordMaskParity word (bit + 1) count mask)

def correctionWordParity (table : List Nat)
    (outputWidth lowWidth row low mask : Nat) : Bool :=
  wordMaskParity
    (Lookup.value table outputWidth (row * batchSize lowWidth + low))
    0 outputWidth mask

def correctionMaskAux (table : List Nat)
    (outputWidth lowWidth row mask : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | low, count + 1 =>
      writeBit
        (correctionMaskAux table outputWidth lowWidth row mask (low + 1) count)
        low (correctionWordParity table outputWidth lowWidth row low mask)

def correctionMask (table : List Nat)
    (outputWidth lowWidth row mask : Nat) : Nat :=
  correctionMaskAux table outputWidth lowWidth row mask
    0 (batchSize lowWidth)

def correctionMaskEval (addressWidth : Nat) (control : Option Nat) :
    Nat → Nat → Nat → Nat → Nat
  | _, 0, _, i => i
  | low, count + 1, mask, i =>
      correctionMaskEval addressWidth control (low + 1) count mask
        (if mask.testBit low then
          RGate.act (correctionGate addressWidth low control) i
        else i)

private theorem correctionMaskAux_testBit_inside
    {table : List Nat} {outputWidth lowWidth row mask low count q : Nat}
    (hlow : low ≤ q) (hhigh : q < low + count) :
    (correctionMaskAux table outputWidth lowWidth row mask low count).testBit q =
      correctionWordParity table outputWidth lowWidth row q mask := by
  induction count generalizing low with
  | zero => omega
  | succ count ih =>
      rw [correctionMaskAux]
      by_cases hq : q = low
      · subst q
        rw [testBit_writeBit]
      · rw [testBit_writeBit_of_ne hq]
        exact ih (low := low + 1) (by omega) (by omega)

theorem correctionMask_testBit
    {table : List Nat} {outputWidth lowWidth row mask low : Nat}
    (hlow : low < batchSize lowWidth) :
    (correctionMask table outputWidth lowWidth row mask).testBit low =
      correctionWordParity table outputWidth lowWidth row low mask := by
  exact correctionMaskAux_testBit_inside (low := 0)
    (count := batchSize lowWidth) (by omega) (by omega)

private theorem correctionBitEval_eq_gateParity
    {table : List Nat}
    {addressWidth outputWidth lowWidth row low : Nat}
    {control : Option Nat}
    (hlow : low < batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control) :
    ∀ bit count mask i,
      correctionBitEval table addressWidth outputWidth lowWidth row low
          control bit count mask i =
        if wordMaskParity
            (Lookup.value table outputWidth
              (row * batchSize lowWidth + low)) bit count mask then
          RGate.act (correctionGate addressWidth low control) i
        else i := by
  intro bit count
  induction count generalizing bit with
  | zero =>
      intro mask i
      simp [correctionBitEval, wordMaskParity]
  | succ count ih =>
      intro mask i
      let word := Lookup.value table outputWidth
        (row * batchSize lowWidth + low)
      let gate := correctionGate addressWidth low control
      have hgate : gate.wellFormed (width addressWidth outputWidth) = true :=
        correctionGate_wellFormed hlow hfit hcontrol
      by_cases hhead : word.testBit bit && mask.testBit bit
      · rw [correctionBitEval, if_pos hhead, ih (bit + 1)]
        cases htail : wordMaskParity word (bit + 1) count mask <;>
          simp [wordMaskParity, word, gate, hhead, htail,
            RGate.act_act hgate]
      · rw [correctionBitEval, if_neg hhead, ih (bit + 1)]
        cases htail : wordMaskParity word (bit + 1) count mask <;>
          simp [wordMaskParity, word, hhead, htail]

theorem correctionLeafEval_eq_maskEval
    {table : List Nat}
    {addressWidth outputWidth lowWidth row low count mask i : Nat}
    {control : Option Nat}
    (hbound : low + count ≤ batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control) :
    correctionLeafEval table addressWidth outputWidth lowWidth row control
        low count mask i =
      correctionMaskEval addressWidth control low count
        (correctionMask table outputWidth lowWidth row mask) i := by
  induction count generalizing low i with
  | zero => rfl
  | succ count ih =>
      rw [correctionLeafEval, correctionMaskEval]
      rw [correctionBitEval_eq_gateParity (by omega) hfit hcontrol]
      rw [correctionMask_testBit (show low < batchSize lowWidth by omega)]
      exact ih (low := low + 1) (i :=
        if correctionWordParity table outputWidth lowWidth row low mask then
          RGate.act (correctionGate addressWidth low control) i
        else i) (by omega)

def correctionControlEnabled : Option Nat → Nat → Bool
  | none, _ => true
  | some control, i => i.testBit control

private theorem correctionGate_testBit_of_ne_target
    {addressWidth low q i : Nat} {control : Option Nat}
    (hne : q ≠ outputWire addressWidth low) :
    (RGate.act (correctionGate addressWidth low control) i).testBit q =
      i.testBit q := by
  cases control with
  | none =>
      rw [correctionGate, act_x_write,
        testBit_writeField_outside (by omega)]
  | some selector =>
      rw [correctionGate, act_cx_write,
        testBit_writeField_outside (by omega)]

private theorem correctionGate_testBit_target
    {addressWidth low i : Nat} {control : Option Nat} :
    (RGate.act (correctionGate addressWidth low control) i).testBit
        (outputWire addressWidth low) =
      Bool.xor (i.testBit (outputWire addressWidth low))
        (correctionControlEnabled control i) := by
  cases control with
  | none =>
      rw [correctionGate, RGate.act, Semantics.testBit_xor_self]
      cases i.testBit (outputWire addressWidth low) <;> rfl
  | some control =>
      cases hcontrol : i.testBit control with
      | false =>
          simp [correctionGate, correctionControlEnabled, RGate.act, hcontrol]
      | true =>
          simp only [correctionGate, correctionControlEnabled, RGate.act,
            hcontrol, if_true]
          rw [Semantics.testBit_xor_self]
          cases i.testBit (outputWire addressWidth low) <;> rfl

private theorem correctionGate_controlEnabled
    {addressWidth outputWidth lowWidth low i : Nat}
    {control : Option Nat}
    (hlow : low < batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control) :
    correctionControlEnabled control
        (RGate.act (correctionGate addressWidth low control) i) =
      correctionControlEnabled control i := by
  cases control with
  | none => rfl
  | some control =>
      apply correctionGate_testBit_of_ne_target
      simp only [selectorFits] at hcontrol
      simp [outputWire]
      omega

private theorem correctionMaskEval_testBit_of_outsideRange
    {addressWidth low count mask i q : Nat} {control : Option Nat}
    (hq : q < outputWire addressWidth low ∨
      outputWire addressWidth (low + count) ≤ q) :
    (correctionMaskEval addressWidth control low count mask i).testBit q =
      i.testBit q := by
  induction count generalizing low i with
  | zero => rfl
  | succ count ih =>
      rw [correctionMaskEval]
      have htail : q < outputWire addressWidth (low + 1) ∨
          outputWire addressWidth ((low + 1) + count) ≤ q := by
        simp only [outputWire] at hq ⊢
        omega
      rw [ih htail]
      by_cases hmask : mask.testBit low
      · rw [if_pos hmask,
          correctionGate_testBit_of_ne_target (control := control) (by
            simp only [outputWire] at hq ⊢
            omega)]
      · rw [if_neg hmask]

theorem correctionMaskEval_testBit_inside
    {addressWidth outputWidth lowWidth low count mask i q : Nat}
    {control : Option Nat}
    (hbound : low + count ≤ batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control)
    (hlow : low ≤ q) (hhigh : q < low + count) :
    (correctionMaskEval addressWidth control low count mask i).testBit
        (outputWire addressWidth q) =
      Bool.xor (i.testBit (outputWire addressWidth q))
        (mask.testBit q && correctionControlEnabled control i) := by
  induction count generalizing low i with
  | zero => omega
  | succ count ih =>
      rw [correctionMaskEval]
      by_cases hq : q = low
      · subst q
        by_cases hmask : mask.testBit low
        · rw [if_pos hmask]
          rw [correctionMaskEval_testBit_of_outsideRange (by
            left
            simp [outputWire])]
          rw [correctionGate_testBit_target]
          simp [hmask]
        · rw [if_neg hmask]
          rw [correctionMaskEval_testBit_of_outsideRange (by
            left
            simp [outputWire])]
          simp [hmask]
      · by_cases hmask : mask.testBit low
        · rw [if_pos hmask,
            ih (low := low + 1) (i :=
              RGate.act (correctionGate addressWidth low control) i)
              (by omega) (by omega) (by omega)]
          rw [correctionGate_testBit_of_ne_target (by
              simp only [outputWire]
              omega),
            correctionGate_controlEnabled (by omega) hfit hcontrol]
        · rw [if_neg hmask]
          exact ih (low := low + 1) (i := i)
            (by omega) (by omega) (by omega)

def correctionNodePre
    (addressWidth outputWidth depth remaining i : Nat) : Prop :=
  readField i (selectorWire addressWidth outputWidth (depth + 1)) remaining = 0

def correctionPre (addressWidth outputWidth high i : Nat) : Prop :=
  readField i (selectorWire addressWidth outputWidth 0) high = 0

def correctionNodeEval (table : List Nat)
    (addressWidth outputWidth lowWidth : Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat
  | row, depth, 0, mask, i =>
      correctionLeafEval table addressWidth outputWidth lowWidth row
        (some (selectorWire addressWidth outputWidth depth))
        0 (batchSize lowWidth) mask i
  | row, depth, remaining + 1, mask, i =>
      let address := lowWidth + remaining
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      let i₁ := Unary.negativeAndOut address parent child i
      let i₂ := correctionNodeEval table addressWidth outputWidth lowWidth
        row (depth + 1) remaining mask i₁
      let i₃ := RGate.act (.cx parent child) i₂
      let i₄ := correctionNodeEval table addressWidth outputWidth lowWidth
        (row + 2 ^ remaining) (depth + 1) remaining mask i₃
      writeBit i₄ child false

def correctionEval (table : List Nat)
    (addressWidth outputWidth lowWidth : Nat) : Nat → Nat → Nat → Nat
  | 0, mask, i =>
      correctionLeafEval table addressWidth outputWidth lowWidth 0 none
        0 (batchSize lowWidth) mask i
  | remaining + 1, mask, i =>
      let address := lowWidth + remaining
      let root := selectorWire addressWidth outputWidth 0
      let i₁ := actGates [.x address, .cx address root, .x address] i
      let i₂ := correctionNodeEval table addressWidth outputWidth lowWidth
        0 0 remaining mask i₁
      let i₃ := RGate.act (.x root) i₂
      let i₄ := correctionNodeEval table addressWidth outputWidth lowWidth
        (2 ^ remaining) 0 remaining mask i₃
      RGate.act (.cx address root) i₄

private theorem correctionNodePre_child_clear
    {addressWidth outputWidth depth remaining i : Nat}
    (hpre : correctionNodePre addressWidth outputWidth depth (remaining + 1) i) :
    bitValue i (selectorWire addressWidth outputWidth (depth + 1)) = 0 := by
  rw [← readField_one]
  exact readField_sub_zero (Nat.le_refl _) (by omega) hpre

private theorem correctionNodePre_tail
    {addressWidth outputWidth depth remaining i : Nat}
    (hpre : correctionNodePre addressWidth outputWidth depth (remaining + 1) i) :
    correctionNodePre addressWidth outputWidth (depth + 1) remaining i := by
  apply readField_sub_zero
    (off := selectorWire addressWidth outputWidth (depth + 1))
    (len := remaining + 1)
  · simp [selectorWire]
  · simp only [selectorWire]
    omega
  · exact hpre

private theorem correctionNodePre_negativeAndOut_tail
    {addressWidth outputWidth lowWidth depth remaining i : Nat}
    (hpre : correctionNodePre addressWidth outputWidth depth (remaining + 1) i) :
    correctionNodePre addressWidth outputWidth (depth + 1) remaining
      (Unary.negativeAndOut (lowWidth + remaining)
        (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1)) i) := by
  rw [correctionNodePre, Unary.negativeAndOut,
    readField_writeField_of_disjoint (Or.inl (by
      simp only [selectorWire]
      omega))]
  exact correctionNodePre_tail hpre

private theorem correctionPre_root_clear
    {addressWidth outputWidth high i : Nat}
    (hhigh : 0 < high) (hpre : correctionPre addressWidth outputWidth high i) :
    bitValue i (selectorWire addressWidth outputWidth 0) = 0 := by
  rw [← readField_one]
  exact readField_sub_zero (Nat.le_refl _) (by omega) hpre

private theorem correctionPre_tail
    {addressWidth outputWidth remaining i : Nat}
    (hpre : correctionPre addressWidth outputWidth (remaining + 1) i) :
    correctionNodePre addressWidth outputWidth 0 remaining i := by
  apply readField_sub_zero
    (off := selectorWire addressWidth outputWidth 0)
    (len := remaining + 1)
  · simp [selectorWire]
  · simp only [selectorWire]
    omega
  · exact hpre

private theorem nil_implementsRetainedU {level w input retained : Nat}
    (c : Dy (deg level)) :
    ImplementsRetainedU level w input retained (fun _ ↦ True)
      (fun _ i ↦ i) c [] := by
  intro i _ _ rec cr b hb
  rw [runOps_nil, List.mem_singleton] at hb
  subst b
  simp [Nat.sub_self, Dy.pow_zero_eq, Vec.one_smul]

private theorem branchLocal_implementsRetainedU
    {level w input retained bit : Nat} {dom : Nat → Prop}
    {outTrue outFalse : Nat → Nat → Nat}
    {c : Dy (deg level)} {ifTrue ifFalse : List Op}
    (hbit : bit < retained)
    (htrue : ImplementsRetainedU level w input retained dom outTrue c ifTrue)
    (hfalse : ImplementsRetainedU level w input retained dom outFalse c ifFalse) :
    ImplementsRetainedU level w input retained dom
      (fun mask i ↦ if mask.testBit bit then outTrue mask i else outFalse mask i)
      c [.branch (.localBit bit) ifTrue ifFalse] := by
  intro i hi hdom rec cr b hb
  rw [runOps_singleton, runOp_branch, CRef.read] at hb
  have hread := retainedCreg_testBit (creg := cr) hbit
  cases hc : cr.testBit bit with
  | false =>
      rw [if_neg (by simp [hc])] at hb
      have hs := hfalse i hi hdom rec cr b hb
      simpa [hread, hc] using hs
  | true =>
      rw [if_pos (by simp [hc])] at hb
      have hs := htrue i hi hdom rec cr b hb
      simpa [hread, hc] using hs

theorem readField_append (i off low high : Nat) :
    readField i off (low + high) =
      readField i off low + 2 ^ low * readField i (off + low) high := by
  show (i >>> off) % 2 ^ (low + high) =
    (i >>> off) % 2 ^ low +
      2 ^ low * ((i >>> (off + low)) % 2 ^ high)
  rw [Nat.pow_add, Nat.mod_mul, Nat.shiftRight_add]
  simp only [Nat.shiftRight_eq_div_pow]

theorem gateOps_append (left right : List RGate) :
    gateOps (left ++ right) = gateOps left ++ gateOps right := by
  simp [gateOps, Unary.gateOps, List.flatMap_append]

theorem gateOps_implementsU {level w input : Nat} (hl : 3 ≤ level)
    {gates : List RGate}
    (hwf : ({ width := w, gates := gates } : RCircuit).wellFormed = true)
    (c : Dy (deg level)) :
    ImplementsU level w input (fun _ => True) (actGates gates) c
      (gateOps gates) := by
  have h := implementsU_gates hl (input := input)
    (r := ({ width := w, gates := gates } : RCircuit)) rfl hwf c
  change ImplementsU level w input (fun _ => True) (actGates gates) c
    ((gates.flatMap compileGate).map Op.gate) at h
  exact h

theorem gateOps_implementsRetainedU {level w input retained : Nat}
    (hl : 3 ≤ level) {gates : List RGate}
    (hwf : ({ width := w, gates := gates } : RCircuit).wellFormed = true)
    (c : Dy (deg level)) :
    ImplementsRetainedU level w input retained (fun _ ↦ True)
      (fun _ i ↦ actGates gates i) c (gateOps gates) := by
  have hstate := gateOps_implementsU (input := input) hl hwf c
  intro i hi _ rec cr b hb
  have hs := hstate i hi trivial rec cr b hb
  have hcreg : b.creg = cr := by
    rw [gateOps, Unary.gateOps, runOps_gates, List.mem_singleton] at hb
    rw [hb]
  exact ⟨by rw [hcreg], hs⟩

theorem andUncomputeClean_implementsRetainedU
    {level w input retained a b c scratch : Nat}
    (hl : 3 ≤ level) (haw : a < w) (hbw : b < w) (hcw : c < w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hretain : retained ≤ scratch) :
    ImplementsRetainedU level w input retained
      (fun i ↦ i.testBit c = (i.testBit a && i.testBit b))
      (fun _ i ↦ writeBit i c false) (Dy.invSqrt2 (deg level))
      (Semantics.andUncomputeClean a b c scratch) := by
  have hstate := implementsU_andUncomputeClean (input := input)
    (m := scratch) hl haw hbw hcw hab hac hbc
  intro i hi hand rec cr br hbr
  have hs := hstate i hi hand rec cr br hbr
  have hbr' := hbr
  rw [Semantics.andUncomputeClean, runOps_append,
    runOps_andUncompute hl haw hbw hcw hab hac hbc
      (andAncilla_basis hand) rec cr input] at hbr'
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append, runOps_singleton, runOp_branch] at hbr'
  constructor
  · rcases hbr' with h | h
    · rw [if_neg (by simp [CRef.read, testBit_writeBit])] at h
      rw [runOps_nil, List.mem_singleton] at h
      rw [h]
      exact retainedCreg_writeBit_of_le false hretain
    · rw [if_pos (by simp [CRef.read, testBit_writeBit])] at h
      rw [runOp_gate, List.mem_singleton] at h
      rw [h]
      exact retainedCreg_writeBit_of_le true hretain
  · exact hs

private theorem correctionGate_implementsRetainedU
    {level input addressWidth outputWidth lowWidth low : Nat}
    {control : Option Nat} (hl : 3 ≤ level)
    (hlow : low < batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control)
    (c : Dy (deg level)) :
    ImplementsRetainedU level (width addressWidth outputWidth) input outputWidth
      (fun _ ↦ True)
      (fun _ i ↦ RGate.act (correctionGate addressWidth low control) i) c
      (gateOps [correctionGate addressWidth low control]) := by
  have hgate := correctionGate_wellFormed hlow hfit hcontrol
  have hwf : (RCircuit.mk (width addressWidth outputWidth)
      [correctionGate addressWidth low control]).wellFormed = true := by
    simp [RCircuit.wellFormed, hgate]
  have h := gateOps_implementsRetainedU (input := input) (retained := outputWidth)
    hl hwf c
  simpa [actGates_cons, actGates_nil] using h

private theorem correctionBitEval_lt
    {table : List Nat} {addressWidth outputWidth lowWidth row low : Nat}
    {control : Option Nat} (hlow : low < batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control) :
    ∀ bit count mask i, i < 2 ^ width addressWidth outputWidth →
      correctionBitEval table addressWidth outputWidth lowWidth row low control
        bit count mask i < 2 ^ width addressWidth outputWidth := by
  intro bit count
  induction count generalizing bit with
  | zero => exact fun _ _ hi ↦ hi
  | succ count ih =>
      intro mask i hi
      rw [correctionBitEval]
      split
      · exact ih (bit + 1) mask _
          (RGate.act_lt (correctionGate_wellFormed hlow hfit hcontrol) hi)
      · exact ih (bit + 1) mask i hi

theorem correctionBitOps_implementsRetainedU
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth row low bit count : Nat}
    {control : Option Nat}
    (hlow : low < batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hbits : bit + count ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control)
    (c : Dy (deg level)) :
    ImplementsRetainedU level (width addressWidth outputWidth) input outputWidth
      (fun _ ↦ True)
      (fun mask i ↦ correctionBitEval table addressWidth outputWidth lowWidth
        row low control bit count mask i) c
      (correctionBitOps table addressWidth outputWidth lowWidth row low control
        bit count) := by
  induction count generalizing bit with
  | zero =>
      simpa [correctionBitOps, correctionBitEval] using
        (nil_implementsRetainedU
          (level := level) (w := width addressWidth outputWidth)
          (input := input) (retained := outputWidth) c)
  | succ count ih =>
      let word := Lookup.value table outputWidth (row * batchSize lowWidth + low)
      have htail := ih (bit := bit + 1) (by omega)
      by_cases hword : word.testBit bit
      · have hgate := correctionGate_implementsRetainedU
          (input := input) hl hlow hfit hcontrol c
        have hnil := nil_implementsRetainedU
          (level := level) (w := width addressWidth outputWidth)
          (input := input) (retained := outputWidth) c
        have hhead := branchLocal_implementsRetainedU
          (dom := fun _ ↦ True) (bit := bit) (by omega) hgate hnil
        have hall := hhead.append htail
          (fun mask i hi _ ↦ by
            by_cases hmask : mask.testBit bit
            · simp [hmask]
              exact RGate.act_lt
                (correctionGate_wellFormed hlow hfit hcontrol) hi
            · simpa [hmask] using hi)
          (fun _ _ _ _ ↦ trivial)
        simpa [correctionBitOps, correctionBitEval, word, hword,
          Function.comp_def] using hall
      · simpa [correctionBitOps, correctionBitEval, word, hword] using htail

private theorem correctionLeafEval_lt
    {table : List Nat} {addressWidth outputWidth lowWidth row : Nat}
    {control : Option Nat} (hfit : batchSize lowWidth ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control) :
    ∀ low count mask i, low + count ≤ batchSize lowWidth →
      i < 2 ^ width addressWidth outputWidth →
      correctionLeafEval table addressWidth outputWidth lowWidth row control
        low count mask i < 2 ^ width addressWidth outputWidth := by
  intro low count
  induction count generalizing low with
  | zero => exact fun _ _ _ hi ↦ hi
  | succ count ih =>
      intro mask i hbound hi
      rw [correctionLeafEval]
      exact ih (low + 1) mask _ (by omega)
        (correctionBitEval_lt (show low < batchSize lowWidth by omega)
          hfit hcontrol 0 outputWidth mask i hi)

theorem correctionLeafOps_implementsRetainedU
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth row low count : Nat}
    {control : Option Nat}
    (hbound : low + count ≤ batchSize lowWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hcontrol : selectorFits addressWidth outputWidth control)
    (c : Dy (deg level)) :
    ImplementsRetainedU level (width addressWidth outputWidth) input outputWidth
      (fun _ ↦ True)
      (fun mask i ↦ correctionLeafEval table addressWidth outputWidth lowWidth
        row control low count mask i) c
      (correctionLeafOps table addressWidth outputWidth lowWidth row control
        low count) := by
  induction count generalizing low with
  | zero =>
      simpa [correctionLeafOps, correctionLeafEval] using
        (nil_implementsRetainedU
          (level := level) (w := width addressWidth outputWidth)
          (input := input) (retained := outputWidth) c)
  | succ count ih =>
      have hhead := correctionBitOps_implementsRetainedU hl table
        (input := input)
        (row := row) (low := low) (bit := 0) (count := outputWidth)
        (control := control) (by omega) hfit (by omega) hcontrol c
      have htail := ih (low := low + 1) (by omega)
      have hall := hhead.append htail
        (fun mask i hi _ ↦ correctionBitEval_lt (show low < batchSize lowWidth by omega)
          hfit hcontrol 0 outputWidth mask i hi)
        (fun _ _ _ _ ↦ trivial)
      simpa [correctionLeafOps, correctionLeafEval, Function.comp_def] using hall

private theorem correctionBitEval_testBit_of_ne_target
    {table : List Nat} {addressWidth outputWidth lowWidth row low q : Nat}
    {control : Option Nat} (hne : q ≠ outputWire addressWidth low) :
    ∀ bit count mask i,
      (correctionBitEval table addressWidth outputWidth lowWidth row low control
        bit count mask i).testBit q = i.testBit q := by
  intro bit count
  induction count generalizing bit with
  | zero => exact fun _ _ ↦ rfl
  | succ count ih =>
      intro mask i
      rw [correctionBitEval]
      split
      · rw [ih (bit + 1) mask,
          correctionGate_testBit_of_ne_target hne]
      · exact ih (bit + 1) mask i

private theorem correctionLeafEval_testBit_of_outside
    {table : List Nat} {addressWidth outputWidth lowWidth row q : Nat}
    {control : Option Nat}
    (hq : q < addressWidth ∨ addressWidth + outputWidth ≤ q) :
    ∀ low count mask i, low + count ≤ outputWidth →
      (correctionLeafEval table addressWidth outputWidth lowWidth row control
        low count mask i).testBit q = i.testBit q := by
  intro low count
  induction count generalizing low with
  | zero => exact fun _ _ _ ↦ rfl
  | succ count ih =>
      intro mask i hbound
      rw [correctionLeafEval,
        ih (low := low + 1) mask _ (by omega),
        correctionBitEval_testBit_of_ne_target (q := q) (by
          simp only [outputWire]
          rcases hq with hq | hq <;> omega)]

private theorem correctionNodeEval_testBit_of_outside
    {table : List Nat} {addressWidth outputWidth lowWidth : Nat}
    (hfit : batchSize lowWidth ≤ outputWidth) :
    ∀ row depth remaining mask i q,
      correctionNodePre addressWidth outputWidth depth remaining i →
      (q < addressWidth ∨ addressWidth + outputWidth ≤ q) →
      (correctionNodeEval table addressWidth outputWidth lowWidth
        row depth remaining mask i).testBit q = i.testBit q := by
  intro row depth remaining
  induction remaining generalizing row depth with
  | zero =>
      intro mask i q _ hq
      exact correctionLeafEval_testBit_of_outside hq 0
        (batchSize lowWidth) mask i (by omega)
  | succ remaining ih =>
      intro mask i q hpre hq
      let address := lowWidth + remaining
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      let i₁ := Unary.negativeAndOut address parent child i
      let i₂ := correctionNodeEval table addressWidth outputWidth lowWidth
        row (depth + 1) remaining mask i₁
      let i₃ := RGate.act (.cx parent child) i₂
      let i₄ := correctionNodeEval table addressWidth outputWidth lowWidth
        (row + 2 ^ remaining) (depth + 1) remaining mask i₃
      have hleftPre : correctionNodePre addressWidth outputWidth
          (depth + 1) remaining i₁ := by
        simpa [i₁, address, parent, child] using
          (correctionNodePre_negativeAndOut_tail
            (lowWidth := lowWidth) hpre)
      have hi₂Pre : correctionNodePre addressWidth outputWidth
          (depth + 1) remaining i₂ := by
        rw [correctionNodePre]
        calc
          readField i₂ (selectorWire addressWidth outputWidth (depth + 2)) remaining =
              readField i₁ (selectorWire addressWidth outputWidth (depth + 2))
                remaining := by
            apply Nat.eq_of_testBit_eq
            intro bit
            simp only [testBit_readField]
            by_cases hbit : bit < remaining
            · simp only [hbit, decide_true, Bool.true_and]
              exact ih row (depth + 1) mask i₁
                (selectorWire addressWidth outputWidth (depth + 2) + bit)
                hleftPre (Or.inr (by simp [selectorWire]; omega))
            · simp [hbit]
          _ = 0 := hleftPre
      have hrightPre : correctionNodePre addressWidth outputWidth
          (depth + 1) remaining i₃ := by
        rw [correctionNodePre]
        change readField i₃
          (selectorWire addressWidth outputWidth (depth + 2)) remaining = 0
        dsimp only [i₃]
        rw [act_cx_write,
          readField_writeField_of_disjoint (Or.inl (by
            simp only [child, selectorWire]
            omega))]
        exact hi₂Pre
      rw [correctionNodeEval]
      by_cases hqchild : q = child
      · subst q
        rw [testBit_writeBit]
        have hchildValue := correctionNodePre_child_clear hpre
        exact ((testBit_eq_false_iff_bitValue_eq_zero i child).mpr
          hchildValue).symm
      · rw [testBit_writeBit_of_ne hqchild false,
          ih (row + 2 ^ remaining) (depth + 1) mask i₃ q hrightPre hq]
        have hswitch : i₃.testBit q = i₂.testBit q := by
          dsimp only [i₃]
          rw [act_cx_write, testBit_writeField_outside (by omega)]
        rw [hswitch, ih row (depth + 1) mask i₁ q hleftPre hq]
        dsimp only [i₁]
        rw [Unary.negativeAndOut,
          testBit_writeField_outside (by omega)]

private theorem correctionNodeEval_preservesPre
    {table : List Nat} {addressWidth outputWidth lowWidth row depth remaining mask i : Nat}
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hpre : correctionNodePre addressWidth outputWidth depth remaining i) :
    correctionNodePre addressWidth outputWidth depth remaining
      (correctionNodeEval table addressWidth outputWidth lowWidth
        row depth remaining mask i) := by
  rw [correctionNodePre]
  calc
    readField
        (correctionNodeEval table addressWidth outputWidth lowWidth
          row depth remaining mask i)
        (selectorWire addressWidth outputWidth (depth + 1)) remaining =
        readField i (selectorWire addressWidth outputWidth (depth + 1)) remaining := by
      apply Nat.eq_of_testBit_eq
      intro bit
      simp only [testBit_readField]
      by_cases hbit : bit < remaining
      · simp only [hbit, decide_true, Bool.true_and]
        exact correctionNodeEval_testBit_of_outside hfit row depth remaining mask i
          (selectorWire addressWidth outputWidth (depth + 1) + bit)
          hpre (Or.inr (by simp [selectorWire]; omega))
      · simp [hbit]
    _ = 0 := hpre

private theorem correctionNodeBeforeUncompute_and
    {table : List Nat}
    {addressWidth outputWidth lowWidth row depth remaining mask i : Nat}
    (haddress : lowWidth + remaining < addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hpre : correctionNodePre addressWidth outputWidth depth (remaining + 1) i) :
    let address := lowWidth + remaining
    let parent := selectorWire addressWidth outputWidth depth
    let child := selectorWire addressWidth outputWidth (depth + 1)
    let i₁ := Unary.negativeAndOut address parent child i
    let i₂ := correctionNodeEval table addressWidth outputWidth lowWidth
      row (depth + 1) remaining mask i₁
    let i₃ := RGate.act (.cx parent child) i₂
    let i₄ := correctionNodeEval table addressWidth outputWidth lowWidth
      (row + 2 ^ remaining) (depth + 1) remaining mask i₃
    i₄.testBit child = (i₄.testBit parent && i₄.testBit address) := by
  dsimp only
  let address := lowWidth + remaining
  let parent := selectorWire addressWidth outputWidth depth
  let child := selectorWire addressWidth outputWidth (depth + 1)
  let i₁ := Unary.negativeAndOut address parent child i
  let i₂ := correctionNodeEval table addressWidth outputWidth lowWidth
    row (depth + 1) remaining mask i₁
  let i₃ := RGate.act (.cx parent child) i₂
  let i₄ := correctionNodeEval table addressWidth outputWidth lowWidth
    (row + 2 ^ remaining) (depth + 1) remaining mask i₃
  change i₄.testBit child = (i₄.testBit parent && i₄.testBit address)
  have hchildValue := correctionNodePre_child_clear hpre
  have hchild : i.testBit child = false :=
    (testBit_eq_false_iff_bitValue_eq_zero i child).mpr hchildValue
  have hleftPre : correctionNodePre addressWidth outputWidth
      (depth + 1) remaining i₁ := by
    simpa [i₁, address, parent, child] using
      (correctionNodePre_negativeAndOut_tail
        (lowWidth := lowWidth) hpre)
  have hi₂Pre : correctionNodePre addressWidth outputWidth
      (depth + 1) remaining i₂ :=
    correctionNodeEval_preservesPre hfit hleftPre
  have hrightPre : correctionNodePre addressWidth outputWidth
      (depth + 1) remaining i₃ := by
    rw [correctionNodePre]
    change readField i₃
      (selectorWire addressWidth outputWidth (depth + 2)) remaining = 0
    dsimp only [i₃]
    rw [act_cx_write,
      readField_writeField_of_disjoint (Or.inl (by
        simp only [child, selectorWire]
        omega))]
    exact hi₂Pre
  have hi₁Child : i₁.testBit child =
      (i.testBit parent && !i.testBit address) := by
    dsimp only [i₁]
    rw [Unary.negativeAndOut,
      testBit_writeField_inside (Nat.le_refl _) (by omega)]
    simp only [Nat.sub_self]
    cases hp : i.testBit parent <;> cases ha : i.testBit address <;>
      simp [bitValue, hchild, hp, ha]
  have hi₁Parent : i₁.testBit parent = i.testBit parent := by
    dsimp only [i₁]
    rw [Unary.negativeAndOut,
      testBit_writeField_outside (Or.inl (by
        simp [parent, child, selectorWire]))]
  have hi₁Address : i₁.testBit address = i.testBit address := by
    dsimp only [i₁]
    rw [Unary.negativeAndOut,
      testBit_writeField_outside (Or.inl (by
        simp [address, child, selectorWire]
        omega))]
  have hi₂Child : i₂.testBit child = i₁.testBit child :=
    correctionNodeEval_testBit_of_outside hfit row (depth + 1) remaining
      mask i₁ child hleftPre (Or.inr (by simp [child, selectorWire]))
  have hi₂Parent : i₂.testBit parent = i₁.testBit parent :=
    correctionNodeEval_testBit_of_outside hfit row (depth + 1) remaining
      mask i₁ parent hleftPre (Or.inr (by simp [parent, selectorWire]))
  have hi₂Address : i₂.testBit address = i₁.testBit address :=
    correctionNodeEval_testBit_of_outside hfit row (depth + 1) remaining
      mask i₁ address hleftPre (Or.inl (by simpa [address] using haddress))
  have hi₃Child : i₃.testBit child =
      (i.testBit parent && i.testBit address) := by
    dsimp only [i₃]
    cases hp : i.testBit parent <;> cases ha : i.testBit address <;>
      simp [RGate.act, hi₂Parent, hi₂Child, hi₁Parent, hi₁Child,
        hp, ha]
  have hi₃Parent : i₃.testBit parent = i.testBit parent := by
    dsimp only [i₃]
    rw [act_cx_write,
      testBit_writeField_outside (Or.inl (by
        simp [parent, child, selectorWire])), hi₂Parent, hi₁Parent]
  have hi₃Address : i₃.testBit address = i.testBit address := by
    dsimp only [i₃]
    rw [act_cx_write,
      testBit_writeField_outside (Or.inl (by
        simp [address, child, selectorWire]
        omega)), hi₂Address, hi₁Address]
  have hi₄Child : i₄.testBit child = i₃.testBit child :=
    correctionNodeEval_testBit_of_outside hfit (row + 2 ^ remaining)
      (depth + 1) remaining mask i₃ child hrightPre
      (Or.inr (by simp [child, selectorWire]))
  have hi₄Parent : i₄.testBit parent = i₃.testBit parent :=
    correctionNodeEval_testBit_of_outside hfit (row + 2 ^ remaining)
      (depth + 1) remaining mask i₃ parent hrightPre
      (Or.inr (by simp [parent, selectorWire]))
  have hi₄Address : i₄.testBit address = i₃.testBit address :=
    correctionNodeEval_testBit_of_outside hfit (row + 2 ^ remaining)
      (depth + 1) remaining mask i₃ address hrightPre
      (Or.inl (by simpa [address] using haddress))
  rw [hi₄Child, hi₄Parent, hi₄Address, hi₃Child, hi₃Parent, hi₃Address]

private theorem correctionNodeEval_readField_address
    {table : List Nat}
    {addressWidth outputWidth lowWidth row depth remaining mask i off count : Nat}
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hpre : correctionNodePre addressWidth outputWidth depth remaining i)
    (hfield : off + count ≤ addressWidth) :
    readField
        (correctionNodeEval table addressWidth outputWidth lowWidth
          row depth remaining mask i) off count =
      readField i off count := by
  apply Nat.eq_of_testBit_eq
  intro bit
  simp only [testBit_readField]
  by_cases hbit : bit < count
  · simp only [hbit, decide_true, Bool.true_and]
    exact correctionNodeEval_testBit_of_outside hfit row depth remaining mask i
      (off + bit) hpre (Or.inl (by omega))
  · simp [hbit]

theorem correctionNodeEval_outputBit
    {table : List Nat}
    {addressWidth outputWidth lowWidth high row depth remaining mask i low : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hselector : depth + remaining < high)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hpre : correctionNodePre addressWidth outputWidth depth remaining i)
    (hlow : low < batchSize lowWidth) :
    (correctionNodeEval table addressWidth outputWidth lowWidth
        row depth remaining mask i).testBit (outputWire addressWidth low) =
      Bool.xor (i.testBit (outputWire addressWidth low))
        (i.testBit (selectorWire addressWidth outputWidth depth) &&
          (correctionMask table outputWidth lowWidth
            (row + readField i lowWidth remaining) mask).testBit low) := by
  induction remaining generalizing row depth i with
  | zero =>
      have hcontrol : selectorFits addressWidth outputWidth
          (some (selectorWire addressWidth outputWidth depth)) := by
        simp [selectorFits, selectorWire, width]
        omega
      rw [correctionNodeEval,
        correctionLeafEval_eq_maskEval (by omega) hfit hcontrol,
        correctionMaskEval_testBit_inside (by omega) hfit hcontrol
          (show 0 ≤ low by omega) (by simpa using hlow)]
      simp [correctionControlEnabled, readField_size_zero, Bool.and_comm]
  | succ remaining ih =>
      let address := lowWidth + remaining
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      let target := outputWire addressWidth low
      let i₁ := Unary.negativeAndOut address parent child i
      let i₂ := correctionNodeEval table addressWidth outputWidth lowWidth
        row (depth + 1) remaining mask i₁
      let i₃ := RGate.act (.cx parent child) i₂
      let i₄ := correctionNodeEval table addressWidth outputWidth lowWidth
        (row + 2 ^ remaining) (depth + 1) remaining mask i₃
      have haddress : lowWidth + remaining < addressWidth := by
        omega
      have hchildValue := correctionNodePre_child_clear hpre
      have hchild : i.testBit child = false :=
        (testBit_eq_false_iff_bitValue_eq_zero i child).mpr hchildValue
      have hleftPre : correctionNodePre addressWidth outputWidth
          (depth + 1) remaining i₁ := by
        simpa [i₁, address, parent, child] using
          (correctionNodePre_negativeAndOut_tail
            (lowWidth := lowWidth) hpre)
      have hi₂Pre : correctionNodePre addressWidth outputWidth
          (depth + 1) remaining i₂ :=
        correctionNodeEval_preservesPre hfit hleftPre
      have hrightPre : correctionNodePre addressWidth outputWidth
          (depth + 1) remaining i₃ := by
        rw [correctionNodePre]
        change readField i₃
          (selectorWire addressWidth outputWidth (depth + 2)) remaining = 0
        dsimp only [i₃]
        rw [act_cx_write,
          readField_writeField_of_disjoint (Or.inl (by
            simp only [child, selectorWire]
            omega))]
        exact hi₂Pre
      have hi₁Child : i₁.testBit child =
          (i.testBit parent && !i.testBit address) := by
        dsimp only [i₁]
        rw [Unary.negativeAndOut,
          testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp only [Nat.sub_self]
        cases hp : i.testBit parent <;> cases ha : i.testBit address <;>
          simp [bitValue, hchild, hp, ha]
      have hi₁Parent : i₁.testBit parent = i.testBit parent := by
        dsimp only [i₁]
        rw [Unary.negativeAndOut,
          testBit_writeField_outside (Or.inl (by
            simp [parent, child, selectorWire]))]
      have hi₁Address : i₁.testBit address = i.testBit address := by
        dsimp only [i₁]
        rw [Unary.negativeAndOut,
          testBit_writeField_outside (Or.inl (by
            simp [address, child, selectorWire]
            omega))]
      have hi₁Target : i₁.testBit target = i.testBit target := by
        dsimp only [i₁]
        rw [Unary.negativeAndOut,
          testBit_writeField_outside (Or.inl (by
            simp [target, child, outputWire, selectorWire]
            omega))]
      have hi₁Read : readField i₁ lowWidth remaining =
          readField i lowWidth remaining := by
        dsimp only [i₁]
        rw [Unary.negativeAndOut,
          readField_writeField_of_disjoint
            (show child + 1 ≤ lowWidth ∨ lowWidth + remaining ≤ child from
              Or.inr (by
                simp [child, selectorWire]
                omega))]
      have hi₂Child : i₂.testBit child = i₁.testBit child :=
        correctionNodeEval_testBit_of_outside hfit row (depth + 1) remaining
          mask i₁ child hleftPre (Or.inr (by simp [child, selectorWire]))
      have hi₂Parent : i₂.testBit parent = i₁.testBit parent :=
        correctionNodeEval_testBit_of_outside hfit row (depth + 1) remaining
          mask i₁ parent hleftPre (Or.inr (by simp [parent, selectorWire]))
      have hi₂Address : i₂.testBit address = i₁.testBit address :=
        correctionNodeEval_testBit_of_outside hfit row (depth + 1) remaining
          mask i₁ address hleftPre (Or.inl (by
            simp [address]
            omega))
      have hi₂Read : readField i₂ lowWidth remaining =
          readField i₁ lowWidth remaining :=
        correctionNodeEval_readField_address hfit hleftPre (by omega)
      have hi₃Child : i₃.testBit child =
          (i.testBit parent && i.testBit address) := by
        dsimp only [i₃]
        cases hp : i.testBit parent <;> cases ha : i.testBit address <;>
          simp [RGate.act, hi₂Parent, hi₂Child, hi₁Parent, hi₁Child,
            hp, ha]
      have hi₃Target : i₃.testBit target = i₂.testBit target := by
        dsimp only [i₃]
        rw [act_cx_write,
          testBit_writeField_outside (Or.inl (by
            simp [target, child, outputWire, selectorWire]
            omega))]
      have hi₃Read : readField i₃ lowWidth remaining =
          readField i lowWidth remaining := by
        dsimp only [i₃]
        rw [act_cx_write,
          readField_writeField_of_disjoint
            (show child + 1 ≤ lowWidth ∨ lowWidth + remaining ≤ child from
              Or.inr (by
                simp [child, selectorWire]
                omega)),
          hi₂Read, hi₁Read]
      have hleft := ih (row := row) (depth := depth + 1) (i := i₁)
        (by omega) hleftPre
      have hright := ih (row := row + 2 ^ remaining)
        (depth := depth + 1) (i := i₃) (by omega) hrightPre
      rw [correctionNodeEval,
        testBit_writeBit_of_ne (by
          simp [outputWire, selectorWire]
          omega),
        hright, hi₃Target, hleft, hi₁Target,
        hi₃Child, hi₁Child, hi₃Read, hi₁Read]
      rw [readField_high]
      simp only [target]
      cases hp : i.testBit parent <;> cases ha : i.testBit address <;>
        simp [address, ha, bitValue, Nat.add_assoc, Nat.add_comm]

private theorem correctionNegativeGates_wellFormed
    {addressWidth outputWidth lowWidth high depth remaining : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hselector : depth + (remaining + 1) < high) :
    (RCircuit.mk (width addressWidth outputWidth)
      (negativeAndGates (lowWidth + remaining)
        (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1)))).wellFormed = true := by
  simp [RCircuit.wellFormed, negativeAndGates, RGate.wellFormed,
    width, selectorWire]
  omega

private theorem correctionSwitchGates_wellFormed
    {addressWidth outputWidth high depth remaining : Nat}
    (hselector : depth + (remaining + 1) < high)
    (hhigh : high ≤ addressWidth) :
    (RCircuit.mk (width addressWidth outputWidth)
      [.cx (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1))]).wellFormed = true := by
  simp [RCircuit.wellFormed, RGate.wellFormed, width, selectorWire]
  omega

private theorem correctionNegativeOut_lt
    {addressWidth outputWidth lowWidth high depth remaining i : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hselector : depth + (remaining + 1) < high)
    (hi : i < 2 ^ width addressWidth outputWidth) :
    Unary.negativeAndOut (lowWidth + remaining)
        (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1)) i <
      2 ^ width addressWidth outputWidth := by
  rw [← Unary.negativeAndGates_act
    (show lowWidth + remaining ≠ selectorWire addressWidth outputWidth depth by
      simp [selectorWire]; omega)
    (show lowWidth + remaining ≠
        selectorWire addressWidth outputWidth (depth + 1) by
      simp [selectorWire]; omega)
    (show selectorWire addressWidth outputWidth depth ≠
        selectorWire addressWidth outputWidth (depth + 1) by
      simp [selectorWire])]
  apply Reversible.act_lt
    (r := RCircuit.mk (width addressWidth outputWidth)
      (Unary.negativeAndGates (lowWidth + remaining)
        (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1))))
  · simpa [negativeAndGates, Unary.negativeAndGates] using
      (correctionNegativeGates_wellFormed hsplit hselector)
  · exact hi

private theorem correctionSwitchOut_lt
    {addressWidth outputWidth high depth remaining i : Nat}
    (hselector : depth + (remaining + 1) < high)
    (hhigh : high ≤ addressWidth)
    (hi : i < 2 ^ width addressWidth outputWidth) :
    RGate.act (.cx (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1))) i <
      2 ^ width addressWidth outputWidth := by
  change actGates
      [.cx (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1))] i <
    2 ^ width addressWidth outputWidth
  exact Reversible.act_lt
    (correctionSwitchGates_wellFormed hselector hhigh) hi

private theorem correctionNodeEval_lt
    {table : List Nat}
    {addressWidth outputWidth lowWidth high row depth remaining mask i : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hselector : depth + remaining < high)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hi : i < 2 ^ width addressWidth outputWidth)
    (hpre : correctionNodePre addressWidth outputWidth depth remaining i) :
    correctionNodeEval table addressWidth outputWidth lowWidth
        row depth remaining mask i < 2 ^ width addressWidth outputWidth := by
  induction remaining generalizing row depth i with
  | zero =>
      rw [correctionNodeEval]
      exact correctionLeafEval_lt hfit
        (by simp [selectorFits, selectorWire, width]; omega)
        0 (batchSize lowWidth) mask i (by omega) hi
  | succ remaining ih =>
      let address := lowWidth + remaining
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      let i₁ := Unary.negativeAndOut address parent child i
      let i₂ := correctionNodeEval table addressWidth outputWidth lowWidth
        row (depth + 1) remaining mask i₁
      let i₃ := RGate.act (.cx parent child) i₂
      let i₄ := correctionNodeEval table addressWidth outputWidth lowWidth
        (row + 2 ^ remaining) (depth + 1) remaining mask i₃
      have hi₁ : i₁ < 2 ^ width addressWidth outputWidth := by
        simpa [i₁, address, parent, child] using
          correctionNegativeOut_lt hsplit hselector hi
      have hleftPre : correctionNodePre addressWidth outputWidth
          (depth + 1) remaining i₁ := by
        simpa [i₁, address, parent, child] using
          (correctionNodePre_negativeAndOut_tail
            (lowWidth := lowWidth) hpre)
      have hi₂ : i₂ < 2 ^ width addressWidth outputWidth :=
        ih (row := row) (depth := depth + 1) (i := i₁)
          (by omega) hi₁ hleftPre
      have hi₃ : i₃ < 2 ^ width addressWidth outputWidth := by
        simpa [i₃, parent, child] using
          correctionSwitchOut_lt hselector (by omega : high ≤ addressWidth) hi₂
      have hi₂Pre : correctionNodePre addressWidth outputWidth
          (depth + 1) remaining i₂ :=
        correctionNodeEval_preservesPre hfit hleftPre
      have hrightPre : correctionNodePre addressWidth outputWidth
          (depth + 1) remaining i₃ := by
        rw [correctionNodePre]
        change readField i₃
          (selectorWire addressWidth outputWidth (depth + 2)) remaining = 0
        dsimp only [i₃]
        rw [act_cx_write,
          readField_writeField_of_disjoint (Or.inl (by
            simp only [child, selectorWire]
            omega))]
        exact hi₂Pre
      have hi₄ : i₄ < 2 ^ width addressWidth outputWidth :=
        ih (row := row + 2 ^ remaining) (depth := depth + 1) (i := i₃)
          (by omega) hi₃ hrightPre
      rw [correctionNodeEval, Unary.writeBit_false_eq_writeField]
      exact writeField_lt (by simp [selectorWire, width]; omega) hi₄

theorem correctionNodeOps_implementsRetainedU
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high row depth remaining : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hselector : depth + remaining < high)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    ImplementsRetainedU level (width addressWidth outputWidth) input outputWidth
      (correctionNodePre addressWidth outputWidth depth remaining)
      (fun mask i ↦ correctionNodeEval table addressWidth outputWidth lowWidth
        row depth remaining mask i)
      (Dy.invSqrt2 (deg level))
      (correctionNodeOps table addressWidth outputWidth lowWidth
        row depth remaining) := by
  let c := Dy.invSqrt2 (deg level)
  change ImplementsRetainedU level (width addressWidth outputWidth) input outputWidth
    (correctionNodePre addressWidth outputWidth depth remaining)
    (fun mask i ↦ correctionNodeEval table addressWidth outputWidth lowWidth
      row depth remaining mask i)
    c
    (correctionNodeOps table addressWidth outputWidth lowWidth
      row depth remaining)
  induction remaining generalizing row depth with
  | zero =>
      have hleaf := correctionLeafOps_implementsRetainedU hl table
        (input := input) (addressWidth := addressWidth)
        (outputWidth := outputWidth) (lowWidth := lowWidth)
        (row := row) (low := 0) (count := batchSize lowWidth)
        (control := some (selectorWire addressWidth outputWidth depth))
        (by omega) hfit
        (by simp [selectorFits, selectorWire, width]; omega) c
      simpa [correctionNodeOps, correctionNodeEval] using
        hleaf.mono (fun _ _ ↦ trivial)
  | succ remaining ih =>
      let address := lowWidth + remaining
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      let i₁ := fun i ↦ Unary.negativeAndOut address parent child i
      let i₂ := fun mask i ↦ correctionNodeEval table addressWidth outputWidth
        lowWidth row (depth + 1) remaining mask (i₁ i)
      let i₃ := fun mask i ↦ RGate.act (.cx parent child) (i₂ mask i)
      let i₄ := fun mask i ↦ correctionNodeEval table addressWidth outputWidth
        lowWidth (row + 2 ^ remaining) (depth + 1) remaining mask (i₃ mask i)
      have hnegAll := gateOps_implementsRetainedU
        (w := width addressWidth outputWidth) (input := input)
        (retained := outputWidth)
        (gates := negativeAndGates address parent child) hl
        (correctionNegativeGates_wellFormed
          (outputWidth := outputWidth) hsplit hselector) c
      have hneg : ImplementsRetainedU level
          (width addressWidth outputWidth) input outputWidth
          (correctionNodePre addressWidth outputWidth depth (remaining + 1))
          (fun _ i ↦ i₁ i) c
          (gateOps (negativeAndGates address parent child)) := by
        intro i hi _ rec cr br hbr
        have hs := hnegAll i hi trivial rec cr br hbr
        have hact : actGates (negativeAndGates address parent child) i = i₁ i := by
          simpa [i₁, address, parent, child, negativeAndGates,
            Unary.negativeAndGates] using
            (Unary.negativeAndGates_act
              (show address ≠ parent by
                simp [address, parent, selectorWire]; omega)
              (show address ≠ child by
                simp [address, child, selectorWire]; omega)
              (show parent ≠ child by
                simp [parent, child, selectorWire]) (i := i))
        constructor
        · exact hs.1
        · simpa only [hact] using hs.2
      have hleft := ih (row := row) (depth := depth + 1) (by omega)
      have hnegLeft := hneg.append hleft
        (fun _ i hi _ ↦ by
          simpa [i₁, address, parent, child] using
            correctionNegativeOut_lt hsplit hselector hi)
        (fun _ _ _ hpre ↦ by
          simpa [i₁, address, parent, child] using
            (correctionNodePre_negativeAndOut_tail
              (lowWidth := lowWidth) hpre))
      have hswitchAll := gateOps_implementsRetainedU
        (w := width addressWidth outputWidth) (input := input)
        (retained := outputWidth)
        (gates := [.cx parent child]) hl
        (correctionSwitchGates_wellFormed hselector
          (by omega : high ≤ addressWidth)) c
      have hswitch : ImplementsRetainedU level
          (width addressWidth outputWidth) input outputWidth
          (fun _ ↦ True)
          (fun _ i ↦ RGate.act (.cx parent child) i) c
          (gateOps [.cx parent child]) := by
        simpa [actGates_cons, actGates_nil] using hswitchAll
      have hthroughSwitch := hnegLeft.append hswitch
        (fun mask i hi hpre ↦ by
          have hi₁ : i₁ i < 2 ^ width addressWidth outputWidth := by
            simpa [i₁, address, parent, child] using
              correctionNegativeOut_lt hsplit hselector hi
          have hleftPre : correctionNodePre addressWidth outputWidth
              (depth + 1) remaining (i₁ i) := by
            simpa [i₁, address, parent, child] using
              (correctionNodePre_negativeAndOut_tail
                (lowWidth := lowWidth) hpre)
          simpa [i₂] using correctionNodeEval_lt hsplit (by omega) hfit hi₁ hleftPre)
        (fun _ _ _ _ ↦ trivial)
      have hright := ih (row := row + 2 ^ remaining)
        (depth := depth + 1) (by omega)
      have hthroughRight := hthroughSwitch.append hright
        (fun mask i hi hpre ↦ by
          have hi₁ : i₁ i < 2 ^ width addressWidth outputWidth := by
            simpa [i₁, address, parent, child] using
              correctionNegativeOut_lt hsplit hselector hi
          have hleftPre : correctionNodePre addressWidth outputWidth
              (depth + 1) remaining (i₁ i) := by
            simpa [i₁, address, parent, child] using
              (correctionNodePre_negativeAndOut_tail
                (lowWidth := lowWidth) hpre)
          have hi₂ : i₂ mask i < 2 ^ width addressWidth outputWidth := by
            simpa [i₂] using
              correctionNodeEval_lt hsplit (by omega) hfit hi₁ hleftPre
          simpa [i₃, parent, child, actGates] using
            correctionSwitchOut_lt hselector
              (by omega : high ≤ addressWidth) hi₂)
        (fun mask i _ hpre ↦ by
          have hleftPre : correctionNodePre addressWidth outputWidth
              (depth + 1) remaining (i₁ i) := by
            simpa [i₁, address, parent, child] using
              (correctionNodePre_negativeAndOut_tail
                (lowWidth := lowWidth) hpre)
          have hi₂Pre : correctionNodePre addressWidth outputWidth
              (depth + 1) remaining (i₂ mask i) := by
            simpa [i₂] using correctionNodeEval_preservesPre hfit hleftPre
          rw [correctionNodePre]
          change readField (i₃ mask i)
            (selectorWire addressWidth outputWidth (depth + 2)) remaining = 0
          dsimp only [i₃]
          rw [act_cx_write,
            readField_writeField_of_disjoint (Or.inl (by
              simp only [child, selectorWire]
              omega))]
          exact hi₂Pre)
      have herase : ImplementsRetainedU level
          (width addressWidth outputWidth) input outputWidth
          (fun i ↦ i.testBit child = (i.testBit parent && i.testBit address))
          (fun _ i ↦ writeBit i child false) c
          (Semantics.andUncomputeClean parent address child
            (scratchBit outputWidth)) := by
        simpa [c] using andUncomputeClean_implementsRetainedU
          (w := width addressWidth outputWidth)
          (input := input) (retained := outputWidth) hl
          (a := parent) (b := address) (c := child)
          (scratch := scratchBit outputWidth)
          (by simp [parent, selectorWire, width]; omega)
          (by simp [address, width]; omega)
          (by simp [child, selectorWire, width]; omega)
          (by simp [parent, address, selectorWire]; omega)
          (by simp [parent, child, selectorWire])
          (by simp [address, child, selectorWire]; omega)
          (by simp [scratchBit])
      have hall := hthroughRight.append herase
        (fun mask i hi hpre ↦ by
          have hi₁ : i₁ i < 2 ^ width addressWidth outputWidth := by
            simpa [i₁, address, parent, child] using
              correctionNegativeOut_lt hsplit hselector hi
          have hleftPre : correctionNodePre addressWidth outputWidth
              (depth + 1) remaining (i₁ i) := by
            simpa [i₁, address, parent, child] using
              (correctionNodePre_negativeAndOut_tail
                (lowWidth := lowWidth) hpre)
          have hi₂ : i₂ mask i < 2 ^ width addressWidth outputWidth := by
            simpa [i₂] using
              correctionNodeEval_lt hsplit (by omega) hfit hi₁ hleftPre
          have hi₃ : i₃ mask i < 2 ^ width addressWidth outputWidth := by
            simpa [i₃, parent, child, actGates] using
              correctionSwitchOut_lt hselector
                (by omega : high ≤ addressWidth) hi₂
          have hi₂Pre : correctionNodePre addressWidth outputWidth
              (depth + 1) remaining (i₂ mask i) := by
            simpa [i₂] using correctionNodeEval_preservesPre hfit hleftPre
          have hrightPre : correctionNodePre addressWidth outputWidth
              (depth + 1) remaining (i₃ mask i) := by
            rw [correctionNodePre]
            change readField (i₃ mask i)
              (selectorWire addressWidth outputWidth (depth + 2)) remaining = 0
            dsimp only [i₃]
            rw [act_cx_write,
              readField_writeField_of_disjoint (Or.inl (by
                simp only [child, selectorWire]
                omega))]
            exact hi₂Pre
          simpa [i₄] using correctionNodeEval_lt hsplit (by omega) hfit hi₃ hrightPre)
        (fun mask i _ hpre ↦ by
          simpa [i₁, i₂, i₃, i₄, address, parent, child] using
            (correctionNodeBeforeUncompute_and
              (table := table) (row := row) (mask := mask)
              (show lowWidth + remaining < addressWidth by omega)
              hfit hpre))
      simpa [correctionNodeOps, correctionNodeEval, i₁, i₂, i₃, i₄,
        address, parent, child, actGates, List.append_assoc,
        Function.comp_def] using hall

private theorem correctionRootInitGates_wellFormed
    {addressWidth outputWidth lowWidth remaining : Nat}
    (hsplit : lowWidth + (remaining + 1) = addressWidth) :
    (RCircuit.mk (width addressWidth outputWidth)
      [.x (lowWidth + remaining),
        .cx (lowWidth + remaining) (selectorWire addressWidth outputWidth 0),
        .x (lowWidth + remaining)]).wellFormed = true := by
  simp [RCircuit.wellFormed, RGate.wellFormed, width, selectorWire]
  omega

private theorem correctionRootXGates_wellFormed
    {addressWidth outputWidth lowWidth remaining : Nat}
    (hsplit : lowWidth + (remaining + 1) = addressWidth) :
    (RCircuit.mk (width addressWidth outputWidth)
      [.x (selectorWire addressWidth outputWidth 0)]).wellFormed = true := by
  simp [RCircuit.wellFormed, RGate.wellFormed, width, selectorWire]
  omega

private theorem correctionRootCxGates_wellFormed
    {addressWidth outputWidth lowWidth remaining : Nat}
    (hsplit : lowWidth + (remaining + 1) = addressWidth) :
    (RCircuit.mk (width addressWidth outputWidth)
      [.cx (lowWidth + remaining)
        (selectorWire addressWidth outputWidth 0)]).wellFormed = true := by
  simp [RCircuit.wellFormed, RGate.wellFormed, width, selectorWire]
  omega

private theorem correctionRootInit_nodePre
    {addressWidth outputWidth lowWidth remaining i : Nat}
    (hsplit : lowWidth + (remaining + 1) = addressWidth)
    (hpre : correctionPre addressWidth outputWidth (remaining + 1) i) :
    correctionNodePre addressWidth outputWidth 0 remaining
      (actGates [.x (lowWidth + remaining),
        .cx (lowWidth + remaining) (selectorWire addressWidth outputWidth 0),
        .x (lowWidth + remaining)] i) := by
  rw [correctionNodePre]
  calc
    readField
        (actGates [.x (lowWidth + remaining),
          .cx (lowWidth + remaining) (selectorWire addressWidth outputWidth 0),
          .x (lowWidth + remaining)] i)
        (selectorWire addressWidth outputWidth 1) remaining =
        readField i (selectorWire addressWidth outputWidth 1) remaining := by
      apply readField_actGates_of_outside
      intro gate hgate q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
      rcases hgate with rfl | rfl | rfl <;>
        simp [RGate.wires, selectorWire] at hq ⊢ <;> omega
    _ = 0 := correctionPre_tail hpre

private theorem correctionRootX_nodePre
    {table : List Nat}
    {addressWidth outputWidth lowWidth row remaining mask i : Nat}
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hpre : correctionNodePre addressWidth outputWidth 0 remaining i) :
    correctionNodePre addressWidth outputWidth 0 remaining
      (RGate.act (.x (selectorWire addressWidth outputWidth 0))
        (correctionNodeEval table addressWidth outputWidth lowWidth
          row 0 remaining mask i)) := by
  have hevalPre := correctionNodeEval_preservesPre
    (table := table) (row := row) (mask := mask) hfit hpre
  rw [correctionNodePre, act_x_write,
    readField_writeField_of_disjoint (Or.inl (by
      simp [selectorWire]))]
  exact hevalPre

private theorem correctionRootInit_lt
    {addressWidth outputWidth lowWidth remaining i : Nat}
    (hsplit : lowWidth + (remaining + 1) = addressWidth)
    (hi : i < 2 ^ width addressWidth outputWidth) :
    actGates [.x (lowWidth + remaining),
      .cx (lowWidth + remaining) (selectorWire addressWidth outputWidth 0),
      .x (lowWidth + remaining)] i <
        2 ^ width addressWidth outputWidth :=
  Reversible.act_lt (correctionRootInitGates_wellFormed hsplit) hi

private theorem correctionRootX_lt
    {addressWidth outputWidth lowWidth remaining i : Nat}
    (hsplit : lowWidth + (remaining + 1) = addressWidth)
    (hi : i < 2 ^ width addressWidth outputWidth) :
    RGate.act (.x (selectorWire addressWidth outputWidth 0)) i <
      2 ^ width addressWidth outputWidth := by
  change actGates [.x (selectorWire addressWidth outputWidth 0)] i <
    2 ^ width addressWidth outputWidth
  exact Reversible.act_lt (correctionRootXGates_wellFormed hsplit) hi

theorem correctionOps_implementsRetainedU
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    ImplementsRetainedU level (width addressWidth outputWidth) input outputWidth
      (correctionPre addressWidth outputWidth high)
      (fun mask i ↦ correctionEval table addressWidth outputWidth lowWidth
        high mask i)
      (Dy.invSqrt2 (deg level))
      (correctionOps table addressWidth outputWidth lowWidth high) := by
  let c := Dy.invSqrt2 (deg level)
  change ImplementsRetainedU level (width addressWidth outputWidth) input outputWidth
    (correctionPre addressWidth outputWidth high)
    (fun mask i ↦ correctionEval table addressWidth outputWidth lowWidth
      high mask i)
    c (correctionOps table addressWidth outputWidth lowWidth high)
  cases high with
  | zero =>
      have hleaf := correctionLeafOps_implementsRetainedU hl table
        (input := input) (addressWidth := addressWidth)
        (outputWidth := outputWidth) (lowWidth := lowWidth)
        (row := 0) (low := 0) (count := batchSize lowWidth)
        (control := none) (by omega) hfit (by simp [selectorFits]) c
      simpa [correctionOps, correctionEval] using
        hleaf.mono (fun _ _ ↦ trivial)
  | succ remaining =>
      let address := lowWidth + remaining
      let root := selectorWire addressWidth outputWidth 0
      let i₁ := fun i ↦ actGates [.x address, .cx address root, .x address] i
      let i₂ := fun mask i ↦ correctionNodeEval table addressWidth outputWidth
        lowWidth 0 0 remaining mask (i₁ i)
      let i₃ := fun mask i ↦ RGate.act (.x root) (i₂ mask i)
      let i₄ := fun mask i ↦ correctionNodeEval table addressWidth outputWidth
        lowWidth (2 ^ remaining) 0 remaining mask (i₃ mask i)
      have hinitAll := gateOps_implementsRetainedU
        (w := width addressWidth outputWidth) (input := input)
        (retained := outputWidth)
        (gates := [.x address, .cx address root, .x address]) hl
        (by simpa [address, root] using
          (correctionRootInitGates_wellFormed hsplit)) c
      have hinit := hinitAll.mono
        (dom' := correctionPre addressWidth outputWidth (remaining + 1))
        (fun _ _ ↦ trivial)
      have hleft := correctionNodeOps_implementsRetainedU hl table
        (input := input) (high := remaining + 1) (row := 0)
        (depth := 0) (remaining := remaining) hsplit (by omega) hfit
      have hthroughLeft := hinit.append hleft
        (fun _ i hi _ ↦ by
          simpa [i₁, address, root] using correctionRootInit_lt hsplit hi)
        (fun _ i _ hpre ↦ by
          simpa [i₁, address, root] using
            (correctionRootInit_nodePre (lowWidth := lowWidth) hsplit hpre))
      have hrootXAll := gateOps_implementsRetainedU
        (w := width addressWidth outputWidth) (input := input)
        (retained := outputWidth) (gates := [.x root]) hl
        (by simpa [root] using
          (correctionRootXGates_wellFormed hsplit)) c
      have hrootX : ImplementsRetainedU level
          (width addressWidth outputWidth) input outputWidth
          (fun _ ↦ True) (fun _ i ↦ RGate.act (.x root) i) c
          (gateOps [.x root]) := by
        simpa [actGates_cons, actGates_nil] using hrootXAll
      have hthroughRootX := hthroughLeft.append hrootX
        (fun mask i hi hpre ↦ by
          have hi₁ : i₁ i < 2 ^ width addressWidth outputWidth := by
            simpa [i₁, address, root] using correctionRootInit_lt hsplit hi
          have hleftPre : correctionNodePre addressWidth outputWidth
              0 remaining (i₁ i) := by
            simpa [i₁, address, root] using
              (correctionRootInit_nodePre (lowWidth := lowWidth) hsplit hpre)
          simpa [i₂] using correctionNodeEval_lt hsplit (by omega) hfit hi₁ hleftPre)
        (fun _ _ _ _ ↦ trivial)
      have hright := correctionNodeOps_implementsRetainedU hl table
        (input := input) (high := remaining + 1) (row := 2 ^ remaining)
        (depth := 0) (remaining := remaining) hsplit (by omega) hfit
      have hthroughRight := hthroughRootX.append hright
        (fun mask i hi hpre ↦ by
          have hi₁ : i₁ i < 2 ^ width addressWidth outputWidth := by
            simpa [i₁, address, root] using correctionRootInit_lt hsplit hi
          have hleftPre : correctionNodePre addressWidth outputWidth
              0 remaining (i₁ i) := by
            simpa [i₁, address, root] using
              (correctionRootInit_nodePre (lowWidth := lowWidth) hsplit hpre)
          have hi₂ : i₂ mask i < 2 ^ width addressWidth outputWidth := by
            simpa [i₂] using
              correctionNodeEval_lt hsplit (by omega) hfit hi₁ hleftPre
          simpa [i₃, root] using correctionRootX_lt hsplit hi₂)
        (fun mask i _ hpre ↦ by
          have hleftPre : correctionNodePre addressWidth outputWidth
              0 remaining (i₁ i) := by
            simpa [i₁, address, root] using
              (correctionRootInit_nodePre (lowWidth := lowWidth) hsplit hpre)
          simpa [i₂, i₃, root] using
            (correctionRootX_nodePre
              (table := table) (lowWidth := lowWidth) (row := 0)
              (mask := mask) hfit hleftPre))
      have hfinalAll := gateOps_implementsRetainedU
        (w := width addressWidth outputWidth) (input := input)
        (retained := outputWidth) (gates := [.cx address root]) hl
        (by simpa [address, root] using
          (correctionRootCxGates_wellFormed hsplit)) c
      have hfinal : ImplementsRetainedU level
          (width addressWidth outputWidth) input outputWidth
          (fun _ ↦ True) (fun _ i ↦ RGate.act (.cx address root) i) c
          (gateOps [.cx address root]) := by
        simpa [actGates_cons, actGates_nil] using hfinalAll
      have hall := hthroughRight.append hfinal
        (fun mask i hi hpre ↦ by
          have hi₁ : i₁ i < 2 ^ width addressWidth outputWidth := by
            simpa [i₁, address, root] using correctionRootInit_lt hsplit hi
          have hleftPre : correctionNodePre addressWidth outputWidth
              0 remaining (i₁ i) := by
            simpa [i₁, address, root] using
              (correctionRootInit_nodePre (lowWidth := lowWidth) hsplit hpre)
          have hi₂ : i₂ mask i < 2 ^ width addressWidth outputWidth := by
            simpa [i₂] using
              correctionNodeEval_lt hsplit (by omega) hfit hi₁ hleftPre
          have hi₃ : i₃ mask i < 2 ^ width addressWidth outputWidth := by
            simpa [i₃, root] using correctionRootX_lt hsplit hi₂
          have hrightPre : correctionNodePre addressWidth outputWidth
              0 remaining (i₃ mask i) := by
            simpa [i₂, i₃, root] using
              (correctionRootX_nodePre
                (table := table) (lowWidth := lowWidth) (row := 0)
                (mask := mask) hfit hleftPre)
          simpa [i₄] using correctionNodeEval_lt hsplit (by omega) hfit hi₃ hrightPre)
        (fun _ _ _ _ ↦ trivial)
      simpa [correctionOps, correctionEval, i₁, i₂, i₃, i₄,
        address, root, actGates, List.append_assoc, Function.comp_def] using hall

theorem correctionEval_selectorClear
    {table : List Nat}
    {addressWidth outputWidth lowWidth high mask i : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hpre : correctionPre addressWidth outputWidth high i) :
    correctionPre addressWidth outputWidth high
      (correctionEval table addressWidth outputWidth lowWidth high mask i) := by
  cases high with
  | zero => simp [correctionPre, readField_size_zero]
  | succ remaining =>
      let address := lowWidth + remaining
      let root := selectorWire addressWidth outputWidth 0
      let i₁ := actGates [.x address, .cx address root, .x address] i
      let i₂ := correctionNodeEval table addressWidth outputWidth
        lowWidth 0 0 remaining mask i₁
      let i₃ := RGate.act (.x root) i₂
      let i₄ := correctionNodeEval table addressWidth outputWidth
        lowWidth (2 ^ remaining) 0 remaining mask i₃
      have hrootClear : i.testBit root = false := by
        apply (testBit_eq_false_iff_bitValue_eq_zero i root).2
        simpa [root] using correctionPre_root_clear (by omega) hpre
      have haddressLt : address < addressWidth := by
        dsimp only [address]
        omega
      have haddressRoot : address ≠ root := by
        have hrootGe : addressWidth ≤ root := by
          simp [root, selectorWire]
        omega
      have hxRoot (j : Nat) :
          (RGate.act (.x address) j).testBit root = j.testBit root := by
        exact RGate.testBit_xor_of_ne (by
          simp [address, root, selectorWire]; omega) j
      have hxAddress (j : Nat) :
          (RGate.act (.x address) j).testBit address = !j.testBit address :=
        Semantics.testBit_xor_self j address
      have hcxRoot (j : Nat) :
          (RGate.act (.cx address root) j).testBit root =
            if j.testBit address then !j.testBit root else j.testBit root := by
        cases haddress : j.testBit address with
        | false => simp [RGate.act, haddress]
        | true =>
            simp only [RGate.act, haddress, if_true]
            exact Semantics.testBit_xor_self j root
      have hcxAddress (j : Nat) :
          (RGate.act (.cx address root) j).testBit address =
            j.testBit address := by
        cases haddress : j.testBit address with
        | false => simp [RGate.act, haddress]
        | true =>
            simp only [RGate.act, haddress, if_true]
            exact (RGate.testBit_xor_of_ne haddressRoot j).trans haddress
      have hleftPre : correctionNodePre addressWidth outputWidth
          0 remaining i₁ := by
        simpa [i₁, address, root] using
          (correctionRootInit_nodePre (lowWidth := lowWidth) hsplit hpre)
      have hi₁Root : i₁.testBit root = !i.testBit address := by
        change (RGate.act (.x address)
          (RGate.act (.cx address root) (RGate.act (.x address) i))).testBit root = _
        rw [hxRoot, hcxRoot, hxAddress, hxRoot, hrootClear]
        cases i.testBit address <;> rfl
      have hi₂Root : i₂.testBit root = i₁.testBit root := by
        exact correctionNodeEval_testBit_of_outside hfit 0 0 remaining mask i₁
          root hleftPre (Or.inr (by simp [root, selectorWire]))
      have hrightPre : correctionNodePre addressWidth outputWidth
          0 remaining i₃ := by
        simpa [i₃, root] using
          (correctionRootX_nodePre
            (table := table) (lowWidth := lowWidth) (row := 0)
            (mask := mask) hfit hleftPre)
      have hi₃Root : i₃.testBit root = i.testBit address := by
        dsimp only [i₃]
        rw [RGate.act]
        rw [Semantics.testBit_xor_self, hi₂Root, hi₁Root]
        cases i.testBit address <;> rfl
      have hi₄Root : i₄.testBit root = i₃.testBit root := by
        exact correctionNodeEval_testBit_of_outside hfit (2 ^ remaining) 0
          remaining mask i₃ root hrightPre
          (Or.inr (by simp [root, selectorWire]))
      have hi₁Address : i₁.testBit address = i.testBit address := by
        change (RGate.act (.x address)
          (RGate.act (.cx address root) (RGate.act (.x address) i))).testBit
            address = _
        rw [hxAddress, hcxAddress, hxAddress]
        cases i.testBit address <;> rfl
      have hi₂Address : i₂.testBit address = i₁.testBit address := by
        exact correctionNodeEval_testBit_of_outside hfit 0 0 remaining mask i₁
          address hleftPre (Or.inl (by simp [address]; omega))
      have hi₃Address : i₃.testBit address = i₂.testBit address := by
        dsimp only [i₃]
        rw [RGate.act, RGate.testBit_xor_of_ne (by
          simp [address, root, selectorWire]; omega)]
      have hi₄Address : i₄.testBit address = i₃.testBit address := by
        exact correctionNodeEval_testBit_of_outside hfit (2 ^ remaining) 0
          remaining mask i₃ address hrightPre
          (Or.inl (by simp [address]; omega))
      have hfinalRoot :
          (RGate.act (.cx address root) i₄).testBit root = false := by
        cases ha : i.testBit address <;>
          simp [RGate.act, hi₄Address, hi₃Address, hi₂Address,
            hi₁Address, hi₄Root, hi₃Root, ha]
      have hi₄Pre : correctionNodePre addressWidth outputWidth
          0 remaining i₄ := correctionNodeEval_preservesPre hfit hrightPre
      have hfinalTail :
          readField (RGate.act (.cx address root) i₄)
              (selectorWire addressWidth outputWidth 1) remaining = 0 := by
        rw [act_cx_write,
          readField_writeField_of_disjoint (Or.inl (by
            simp [root, selectorWire]))]
        exact hi₄Pre
      rw [correctionPre]
      change readField (RGate.act (.cx address root) i₄) root
        (remaining + 1) = 0
      rw [show remaining + 1 = 1 + remaining by omega,
        readField_append, readField_one]
      have hrootValue :
          bitValue (RGate.act (.cx address root) i₄) root = 0 :=
        (testBit_eq_false_iff_bitValue_eq_zero _ _).1 hfinalRoot
      have hfinalTail' :
          readField (RGate.act (.cx address root) i₄) (root + 1) remaining = 0 := by
        simpa [root, selectorWire] using hfinalTail
      rw [hrootValue, hfinalTail']

theorem correctionEval_outputBit
    {table : List Nat}
    {addressWidth outputWidth lowWidth high mask i low : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hpre : correctionPre addressWidth outputWidth high i)
    (hlow : low < batchSize lowWidth) :
    (correctionEval table addressWidth outputWidth lowWidth high mask i).testBit
        (outputWire addressWidth low) =
      Bool.xor (i.testBit (outputWire addressWidth low))
        ((correctionMask table outputWidth lowWidth
          (readField i lowWidth high) mask).testBit low) := by
  cases high with
  | zero =>
      rw [correctionEval,
        correctionLeafEval_eq_maskEval (by omega) hfit
          (by simp [selectorFits]),
        correctionMaskEval_testBit_inside (by omega) hfit
          (by simp [selectorFits]) (show 0 ≤ low by omega)
          (by simpa using hlow)]
      simp [correctionControlEnabled, readField_size_zero]
  | succ remaining =>
      let address := lowWidth + remaining
      let root := selectorWire addressWidth outputWidth 0
      let target := outputWire addressWidth low
      let i₁ := actGates [.x address, .cx address root, .x address] i
      let i₂ := correctionNodeEval table addressWidth outputWidth
        lowWidth 0 0 remaining mask i₁
      let i₃ := RGate.act (.x root) i₂
      let i₄ := correctionNodeEval table addressWidth outputWidth
        lowWidth (2 ^ remaining) 0 remaining mask i₃
      have hrootClear : i.testBit root = false := by
        apply (testBit_eq_false_iff_bitValue_eq_zero i root).2
        simpa [root] using correctionPre_root_clear (by omega) hpre
      have hleftPre : correctionNodePre addressWidth outputWidth
          0 remaining i₁ := by
        simpa [i₁, address, root] using
          (correctionRootInit_nodePre (lowWidth := lowWidth) hsplit hpre)
      have hrightPre : correctionNodePre addressWidth outputWidth
          0 remaining i₃ := by
        simpa [i₃, root] using
          (correctionRootX_nodePre
            (table := table) (lowWidth := lowWidth) (row := 0)
            (mask := mask) hfit hleftPre)
      have hxRoot (j : Nat) :
          (RGate.act (.x address) j).testBit root = j.testBit root := by
        exact RGate.testBit_xor_of_ne (by
          simp [address, root, selectorWire]
          omega) j
      have hxAddress (j : Nat) :
          (RGate.act (.x address) j).testBit address = !j.testBit address :=
        Semantics.testBit_xor_self j address
      have hcxRoot (j : Nat) :
          (RGate.act (.cx address root) j).testBit root =
            if j.testBit address then !j.testBit root else j.testBit root := by
        cases haddress : j.testBit address with
        | false => simp [RGate.act, haddress]
        | true =>
            simp only [RGate.act, haddress, if_true]
            exact Semantics.testBit_xor_self j root
      have hcxAddress (j : Nat) :
          (RGate.act (.cx address root) j).testBit address =
            j.testBit address := by
        cases haddress : j.testBit address with
        | false => simp [RGate.act, haddress]
        | true =>
            simp only [RGate.act, haddress, if_true]
            rw [RGate.testBit_xor_of_ne (by
              simp [address, root, selectorWire]
              omega)]
            exact haddress
      have hi₁Root : i₁.testBit root = !i.testBit address := by
        change (RGate.act (.x address)
          (RGate.act (.cx address root) (RGate.act (.x address) i))).testBit
            root = _
        rw [hxRoot, hcxRoot, hxAddress, hxRoot, hrootClear]
        cases i.testBit address <;> rfl
      have hi₁Address : i₁.testBit address = i.testBit address := by
        change (RGate.act (.x address)
          (RGate.act (.cx address root) (RGate.act (.x address) i))).testBit
            address = _
        rw [hxAddress, hcxAddress, hxAddress]
        cases i.testBit address <;> rfl
      have hi₁Target : i₁.testBit target = i.testBit target := by
        dsimp only [i₁]
        apply testBit_actGates_of_outside
        intro gate hgate hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
        rcases hgate with rfl | rfl | rfl <;>
          simp [RGate.wires, target, outputWire, address, root,
            selectorWire] at hmem <;> omega
      have hi₁Read : readField i₁ lowWidth remaining =
          readField i lowWidth remaining := by
        dsimp only [i₁]
        apply readField_actGates_of_outside
        intro gate hgate q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
        rcases hgate with rfl | rfl | rfl <;>
          simp [RGate.wires, address, root, selectorWire] at hq ⊢ <;> omega
      have hi₂Root : i₂.testBit root = i₁.testBit root :=
        correctionNodeEval_testBit_of_outside hfit 0 0 remaining mask i₁
          root hleftPre (Or.inr (by simp [root, selectorWire]))
      have hi₂Address : i₂.testBit address = i₁.testBit address :=
        correctionNodeEval_testBit_of_outside hfit 0 0 remaining mask i₁
          address hleftPre (Or.inl (by simp [address]; omega))
      have hi₂Target : i₂.testBit target =
          Bool.xor (i.testBit target)
            (!i.testBit address &&
              (correctionMask table outputWidth lowWidth
                (readField i lowWidth remaining) mask).testBit low) := by
        have hleft := correctionNodeEval_outputBit
          (table := table) (high := remaining + 1) (row := 0) (depth := 0)
          (mask := mask) hsplit (by omega) hfit hleftPre hlow
        change i₂.testBit target = Bool.xor (i₁.testBit target)
          (i₁.testBit root &&
            (correctionMask table outputWidth lowWidth
              (0 + readField i₁ lowWidth remaining) mask).testBit low) at hleft
        simpa [hi₁Target, hi₁Root, hi₁Read] using hleft
      have hi₃Root : i₃.testBit root = i.testBit address := by
        dsimp only [i₃]
        rw [RGate.act, Semantics.testBit_xor_self, hi₂Root, hi₁Root]
        cases i.testBit address <;> rfl
      have hi₃Address : i₃.testBit address = i.testBit address := by
        dsimp only [i₃]
        rw [RGate.act, RGate.testBit_xor_of_ne (by
          simp [address, root, selectorWire]
          omega), hi₂Address, hi₁Address]
      have hi₃Target : i₃.testBit target = i₂.testBit target := by
        dsimp only [i₃]
        rw [RGate.act, RGate.testBit_xor_of_ne (by
          simp [target, root, outputWire, selectorWire]
          omega)]
      have hi₃Read : readField i₃ lowWidth remaining =
          readField i lowWidth remaining := by
        dsimp only [i₃]
        rw [act_x_write,
          readField_writeField_of_disjoint (Or.inr (by
            simp [root, selectorWire]
            omega))]
        exact (correctionNodeEval_readField_address hfit hleftPre
          (by omega)).trans hi₁Read
      have hi₄Target : i₄.testBit target =
          Bool.xor (i₂.testBit target)
            (i.testBit address &&
              (correctionMask table outputWidth lowWidth
                (2 ^ remaining + readField i lowWidth remaining) mask).testBit
                  low) := by
        have hright := correctionNodeEval_outputBit
          (table := table) (high := remaining + 1) (row := 2 ^ remaining)
          (depth := 0) (mask := mask) hsplit (by omega) hfit hrightPre hlow
        change i₄.testBit target = Bool.xor (i₃.testBit target)
          (i₃.testBit root &&
            (correctionMask table outputWidth lowWidth
              (2 ^ remaining + readField i₃ lowWidth remaining) mask).testBit
                low) at hright
        simpa [hi₃Target, hi₃Root, hi₃Read] using hright
      have hfinalTarget :
          (RGate.act (.cx address root) i₄).testBit target =
            i₄.testBit target := by
        rw [act_cx_write,
          testBit_writeField_outside (Or.inl (by
            simp [target, root, outputWire, selectorWire]
            omega))]
      rw [correctionEval]
      change (RGate.act (.cx address root) i₄).testBit target = _
      rw [hfinalTarget, hi₄Target, hi₂Target, readField_high]
      cases haddress : i.testBit address <;>
        simp [target, address, haddress, bitValue, Nat.add_comm]

theorem correctionEval_testBit_of_outsideOutput
    {table : List Nat}
    {addressWidth outputWidth lowWidth high mask i q : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hpre : correctionPre addressWidth outputWidth high i)
    (hq : q < addressWidth ∨ addressWidth + outputWidth ≤ q) :
    (correctionEval table addressWidth outputWidth lowWidth high mask i).testBit q =
      i.testBit q := by
  cases high with
  | zero =>
      rw [correctionEval]
      exact correctionLeafEval_testBit_of_outside hq 0
        (batchSize lowWidth) mask i (by simpa using hfit)
  | succ remaining =>
      let address := lowWidth + remaining
      let root := selectorWire addressWidth outputWidth 0
      let i₁ := actGates [.x address, .cx address root, .x address] i
      let i₂ := correctionNodeEval table addressWidth outputWidth
        lowWidth 0 0 remaining mask i₁
      let i₃ := RGate.act (.x root) i₂
      let i₄ := correctionNodeEval table addressWidth outputWidth
        lowWidth (2 ^ remaining) 0 remaining mask i₃
      have hrootClear : i.testBit root = false := by
        apply (testBit_eq_false_iff_bitValue_eq_zero i root).2
        simpa [root] using correctionPre_root_clear (by omega) hpre
      have hleftPre : correctionNodePre addressWidth outputWidth
          0 remaining i₁ := by
        simpa [i₁, address, root] using
          (correctionRootInit_nodePre (lowWidth := lowWidth) hsplit hpre)
      have hxRoot (j : Nat) :
          (RGate.act (.x address) j).testBit root = j.testBit root :=
        RGate.testBit_xor_of_ne (by
          simp [address, root, selectorWire]
          omega) j
      have hxAddress (j : Nat) :
          (RGate.act (.x address) j).testBit address = !j.testBit address :=
        Semantics.testBit_xor_self j address
      have hcxRoot (j : Nat) :
          (RGate.act (.cx address root) j).testBit root =
            if j.testBit address then !j.testBit root else j.testBit root := by
        cases haddress : j.testBit address with
        | false => simp [RGate.act, haddress]
        | true =>
            simp only [RGate.act, haddress, if_true]
            exact Semantics.testBit_xor_self j root
      have hcxAddress (j : Nat) :
          (RGate.act (.cx address root) j).testBit address =
            j.testBit address := by
        cases haddress : j.testBit address with
        | false => simp [RGate.act, haddress]
        | true =>
            simp only [RGate.act, haddress, if_true]
            rw [RGate.testBit_xor_of_ne (by
              simp [address, root, selectorWire]
              omega)]
            exact haddress
      have hi₁Root : i₁.testBit root = !i.testBit address := by
        change (RGate.act (.x address)
          (RGate.act (.cx address root) (RGate.act (.x address) i))).testBit
            root = _
        rw [hxRoot, hcxRoot, hxAddress, hxRoot, hrootClear]
        cases i.testBit address <;> rfl
      have hi₁Address : i₁.testBit address = i.testBit address := by
        change (RGate.act (.x address)
          (RGate.act (.cx address root) (RGate.act (.x address) i))).testBit
            address = _
        rw [hxAddress, hcxAddress, hxAddress]
        cases i.testBit address <;> rfl
      have hi₂Root : i₂.testBit root = i₁.testBit root :=
        correctionNodeEval_testBit_of_outside hfit 0 0 remaining mask i₁
          root hleftPre (Or.inr (by simp [root, selectorWire]))
      have hrightPre : correctionNodePre addressWidth outputWidth
          0 remaining i₃ := by
        simpa [i₃, root] using
          (correctionRootX_nodePre
            (table := table) (lowWidth := lowWidth) (row := 0)
            (mask := mask) hfit hleftPre)
      have hi₃Root : i₃.testBit root = i.testBit address := by
        dsimp only [i₃]
        rw [RGate.act, Semantics.testBit_xor_self, hi₂Root, hi₁Root]
        cases i.testBit address <;> rfl
      have hi₄Root : i₄.testBit root = i₃.testBit root :=
        correctionNodeEval_testBit_of_outside hfit (2 ^ remaining) 0
          remaining mask i₃ root hrightPre
          (Or.inr (by simp [root, selectorWire]))
      rw [correctionEval]
      change (RGate.act (.cx address root) i₄).testBit q = i.testBit q
      by_cases hqa : q = address
      · subst q
        rw [act_cx_write, testBit_writeField_outside (by
          simp [address, root, selectorWire]
          omega)]
        rw [correctionNodeEval_testBit_of_outside hfit
          (2 ^ remaining) 0 remaining mask i₃ address hrightPre
          (Or.inl (by simp [address]; omega))]
        dsimp only [i₃]
        rw [RGate.act, RGate.testBit_xor_of_ne (by
          simp [address, root, selectorWire]
          omega)]
        rw [correctionNodeEval_testBit_of_outside hfit
          0 0 remaining mask i₁ address hleftPre
          (Or.inl (by simp [address]; omega))]
        exact hi₁Address
      · by_cases hqr : q = root
        · subst q
          rw [act_cx_write, testBit_writeField_inside (by omega) (by omega)]
          simp only [bitValue]
          rw [hi₄Root, hi₃Root]
          have hi₄Address := correctionNodeEval_testBit_of_outside
            (table := table) hfit
            (2 ^ remaining) 0 remaining mask i₃ address hrightPre
            (Or.inl (by simp [address]; omega))
          have hi₂Address := correctionNodeEval_testBit_of_outside
            (table := table) hfit
            0 0 remaining mask i₁ address hleftPre
            (Or.inl (by simp [address]; omega))
          have hi₃Address : i₃.testBit address = i₂.testBit address := by
            dsimp only [i₃]
            rw [RGate.act, RGate.testBit_xor_of_ne (by
              simp [address, root, selectorWire]
              omega)]
          rw [hi₄Address, hi₃Address, hi₂Address, hi₁Address]
          cases i.testBit address <;> simp [hrootClear]
        · rw [act_cx_write, testBit_writeField_outside (by omega)]
          rw [correctionNodeEval_testBit_of_outside hfit
            (2 ^ remaining) 0 remaining mask i₃ q hrightPre hq]
          dsimp only [i₃]
          rw [RGate.act, RGate.testBit_xor_of_ne hqr]
          rw [correctionNodeEval_testBit_of_outside hfit
            0 0 remaining mask i₁ q hleftPre hq]
          dsimp only [i₁]
          apply testBit_actGates_of_outside
          intro gate hgate hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
          rcases hgate with rfl | rfl | rfl <;>
            simp [RGate.wires] at hmem <;> omega

private theorem correctionLeafEval_testBit_outputTail
    {table : List Nat}
    {addressWidth outputWidth lowWidth row q : Nat}
    {control : Option Nat}
    (hq : addressWidth + batchSize lowWidth ≤ q) :
    ∀ low count mask i, low + count ≤ batchSize lowWidth →
      (correctionLeafEval table addressWidth outputWidth lowWidth row
        control low count mask i).testBit q = i.testBit q := by
  intro low count
  induction count generalizing low with
  | zero => exact fun _ _ _ ↦ rfl
  | succ count ih =>
      intro mask i hbound
      rw [correctionLeafEval,
        ih (low := low + 1) mask _ (by omega),
        correctionBitEval_testBit_of_ne_target (by
          simp [outputWire]
          omega)]

private theorem correctionNodeEval_testBit_outputTail
    {table : List Nat}
    {addressWidth outputWidth lowWidth q : Nat}
    (hlo : addressWidth + batchSize lowWidth ≤ q)
    (hhi : q < addressWidth + outputWidth) :
    ∀ row depth remaining mask i,
      (correctionNodeEval table addressWidth outputWidth lowWidth
        row depth remaining mask i).testBit q = i.testBit q := by
  intro row depth remaining
  induction remaining generalizing row depth with
  | zero =>
      intro mask i
      exact correctionLeafEval_testBit_outputTail hlo 0
        (batchSize lowWidth) mask i (by omega)
  | succ remaining ih =>
      intro mask i
      let address := lowWidth + remaining
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      have hqchild : q ≠ child := by
        dsimp [child, selectorWire]
        omega
      rw [correctionNodeEval,
        testBit_writeBit_of_ne hqchild,
        ih (row := row + 2 ^ remaining) (depth := depth + 1),
        act_cx_write,
        testBit_writeField_outside (Or.inl (by
          dsimp [child, selectorWire]
          omega)),
        ih (row := row) (depth := depth + 1)]
      simp only [Unary.negativeAndOut]
      rw [testBit_writeField_outside (Or.inl (by
        dsimp [child, selectorWire]
        omega))]

private theorem correctionEval_testBit_outputTail
    {table : List Nat}
    {addressWidth outputWidth lowWidth high mask i q : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hlo : addressWidth + batchSize lowWidth ≤ q)
    (hhi : q < addressWidth + outputWidth) :
    (correctionEval table addressWidth outputWidth lowWidth high mask i).testBit q =
      i.testBit q := by
  cases high with
  | zero =>
      rw [correctionEval]
      exact correctionLeafEval_testBit_outputTail hlo 0
        (batchSize lowWidth) mask i (by omega)
  | succ remaining =>
      let address := lowWidth + remaining
      let root := selectorWire addressWidth outputWidth 0
      let i₁ := actGates [.x address, .cx address root, .x address] i
      let i₂ := correctionNodeEval table addressWidth outputWidth
        lowWidth 0 0 remaining mask i₁
      let i₃ := RGate.act (.x root) i₂
      let i₄ := correctionNodeEval table addressWidth outputWidth
        lowWidth (2 ^ remaining) 0 remaining mask i₃
      rw [correctionEval]
      change (RGate.act (.cx address root) i₄).testBit q = i.testBit q
      rw [act_cx_write,
        testBit_writeField_outside (by simp [root, selectorWire]; omega),
        correctionNodeEval_testBit_outputTail hlo hhi]
      dsimp only [i₃]
      rw [act_x_write,
        testBit_writeField_outside (Or.inl (by
          dsimp [root, selectorWire]
          omega)),
        correctionNodeEval_testBit_outputTail hlo hhi]
      dsimp only [i₁]
      apply testBit_actGates_of_outside
      intro gate hgate hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
      rcases hgate with rfl | rfl | rfl <;>
        simp [RGate.wires, address, root, selectorWire] at hmem <;> omega

theorem correctionEval_eq_maskEval
    {table : List Nat}
    {addressWidth outputWidth lowWidth high mask i : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hpre : correctionPre addressWidth outputWidth high i) :
    correctionEval table addressWidth outputWidth lowWidth high mask i =
      correctionMaskEval addressWidth none 0 (batchSize lowWidth)
        (correctionMask table outputWidth lowWidth
          (readField i lowWidth high) mask) i := by
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases hqlo : q < addressWidth
  · rw [correctionEval_testBit_of_outsideOutput hsplit hfit hpre
      (Or.inl hqlo),
      correctionMaskEval_testBit_of_outsideRange (Or.inl (by
        simp [outputWire]
        omega))]
  · by_cases hqhi : addressWidth + outputWidth ≤ q
    · rw [correctionEval_testBit_of_outsideOutput hsplit hfit hpre
        (Or.inr hqhi),
        correctionMaskEval_testBit_of_outsideRange (Or.inr (by
          simp [outputWire]
          omega))]
    · let low := q - addressWidth
      have hq : q = outputWire addressWidth low := by
        simp [low, outputWire]
        omega
      have hlowOutput : low < outputWidth := by
        dsimp only [low]
        omega
      by_cases hlow : low < batchSize lowWidth
      · rw [hq, correctionEval_outputBit hsplit hfit hpre hlow,
          correctionMaskEval_testBit_inside (by omega) hfit
            (by simp [selectorFits]) (show 0 ≤ low by omega)
            (by simpa using hlow)]
        simp [correctionControlEnabled]
      · rw [hq, correctionEval_testBit_outputTail hsplit
            (by simp [outputWire, low]; omega)
            (by simpa [outputWire] using hlowOutput),
          correctionMaskEval_testBit_of_outsideRange (Or.inr (by
            simp [outputWire]
            omega))]

theorem flipMaskBlockVec_basis
    {d addressWidth low count mask i : Nat} :
    flipMaskBlockVec (outputWire addressWidth low) low count mask
        (basis i : Vec d) =
      basis (correctionMaskEval addressWidth none low count mask i) := by
  induction count generalizing low i with
  | zero => rfl
  | succ count ih =>
      rw [flipMaskBlockVec, correctionMaskEval]
      have hoff : outputWire addressWidth low + 1 =
          outputWire addressWidth (low + 1) := by
        simp only [outputWire]
        omega
      by_cases hmask : mask.testBit low
      · rw [if_pos hmask, if_pos hmask, Semantics.flipVec_basis]
        change flipMaskBlockVec (outputWire addressWidth low + 1)
            (low + 1) count mask
              (basis (i ^^^ (1 <<< outputWire addressWidth low))) =
          basis (correctionMaskEval addressWidth none (low + 1) count mask
            (RGate.act (.x (outputWire addressWidth low)) i))
        have hact : RGate.act (.x (outputWire addressWidth low)) i =
            i ^^^ (1 <<< outputWire addressWidth low) := rfl
        rw [hoff, hact]
        exact ih (low := low + 1)
          (i := i ^^^ (1 <<< outputWire addressWidth low))
      · rw [if_neg hmask, if_neg hmask]
        change flipMaskBlockVec (outputWire addressWidth low + 1)
            (low + 1) count mask (basis i) =
          basis (correctionMaskEval addressWidth none (low + 1) count mask i)
        rw [hoff]
        exact ih (low := low + 1) (i := i)

theorem flipMaskBlockVec_zero {d off bit count mask : Nat} :
    flipMaskBlockVec off bit count mask (Vec.zero d) = Vec.zero d := by
  induction count generalizing off bit with
  | zero => rfl
  | succ count ih =>
      rw [flipMaskBlockVec]
      have hhead :
          (if mask.testBit bit then flipVec off (Vec.zero d) else Vec.zero d) =
            Vec.zero d := by
        split
        · exact Vec.ext (fun _ ↦ rfl)
        · rfl
      rw [hhead]
      exact ih (off := off + 1) (bit := bit + 1)

theorem flipMaskBlockVec_add {d off bit count mask : Nat} (u v : Vec d) :
    flipMaskBlockVec off bit count mask (u + v) =
      flipMaskBlockVec off bit count mask u +
        flipMaskBlockVec off bit count mask v := by
  induction count generalizing off bit u v with
  | zero => rfl
  | succ count ih =>
      rw [flipMaskBlockVec, flipMaskBlockVec, flipMaskBlockVec]
      by_cases hmask : mask.testBit bit
      · rw [if_pos hmask, if_pos hmask, if_pos hmask,
          Semantics.flipVec_add]
        exact ih (off := off + 1) (bit := bit + 1)
          (u := flipVec off u) (v := flipVec off v)
      · rw [if_neg hmask, if_neg hmask, if_neg hmask]
        exact ih (off := off + 1) (bit := bit + 1) (u := u) (v := v)

theorem flipMaskBlockVec_smul {d off bit count mask : Nat}
    (c : Dy d) (u : Vec d) :
    flipMaskBlockVec off bit count mask (c • u) =
      c • flipMaskBlockVec off bit count mask u := by
  induction count generalizing off bit u with
  | zero => rfl
  | succ count ih =>
      rw [flipMaskBlockVec, flipMaskBlockVec]
      by_cases hmask : mask.testBit bit
      · rw [if_pos hmask, if_pos hmask, Semantics.flipVec_smul]
        exact ih (off := off + 1) (bit := bit + 1) (u := flipVec off u)
      · rw [if_neg hmask, if_neg hmask]
        exact ih (off := off + 1) (bit := bit + 1) (u := u)

theorem flipMaskBlockVec_superpose
    {d addressWidth low count mask : Nat}
    (L : List Nat) (a : Nat → Dy d) :
    flipMaskBlockVec (outputWire addressWidth low) low count mask
        (Semantics.superpose id a L) =
      Semantics.superpose
        (correctionMaskEval addressWidth none low count mask) a L := by
  induction L with
  | nil =>
      rw [show Semantics.superpose (d := d) id a [] = Vec.zero d from rfl,
        flipMaskBlockVec_zero]
      rfl
  | cons i L ih =>
      rw [Semantics.superpose, flipMaskBlockVec_add,
        flipMaskBlockVec_smul, flipMaskBlockVec_basis, ih]
      rfl

private theorem superpose_congr_map
    {d : Nat} {f g : Nat → Nat} {a : Nat → Dy d} {L : List Nat}
    (h : ∀ i ∈ L, f i = g i) :
    Semantics.superpose f a L = Semantics.superpose g a L := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      rw [Semantics.superpose, Semantics.superpose, h i (List.mem_cons_self ..),
        ih (fun j hj ↦ h j (List.mem_cons_of_mem _ hj))]

theorem correctionOps_superpose
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high row : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (rec : List Bool) (cr : Nat) (L : List Nat)
    (a : Nat → Dy (deg level))
    (hsupport : ∀ i ∈ L,
      i < 2 ^ width addressWidth outputWidth ∧
        correctionPre addressWidth outputWidth high i)
    (hrow : ∀ i ∈ L, readField i lowWidth high = row) :
    ∀ b ∈ runOps level (width addressWidth outputWidth)
      (correctionOps table addressWidth outputWidth lowWidth high)
      (Branch.mk rec cr (Semantics.superpose id a L) input),
      retainedCreg outputWidth b.creg = retainedCreg outputWidth cr ∧
        b.state =
          (Dy.invSqrt2 (deg level)) ^
              (b.outcomes.length - rec.length) •
            flipMaskBlockVec (outputWire addressWidth 0) 0
              (batchSize lowWidth)
              (correctionMask table outputWidth lowWidth row
                (retainedCreg outputWidth cr))
              (Semantics.superpose id a L) := by
  intro b hb
  have hsem := (correctionOps_implementsRetainedU hl table hsplit hfit).superpose
    (reference := 0) (Nat.two_pow_pos _)
    (by simp [correctionPre, readField]) rec cr L a hsupport b hb
  constructor
  · exact hsem.1
  · rw [hsem.2]
    congr 1
    rw [flipMaskBlockVec_superpose]
    apply superpose_congr_map
    intro i hi
    rw [correctionEval_eq_maskEval hsplit hfit (hsupport i hi).2,
      hrow i hi]

theorem walshSandwich_basis_of_superpose
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high row unaryState : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (rec : List Bool) (cr : Nat) (L : List Nat)
    (a : Nat → Dy (deg level))
    (hdecomp :
      hadamardBlockVec (outputWire addressWidth 0) (batchSize lowWidth)
          (basis unaryState : Vec (deg level)) =
        Semantics.superpose id a L)
    (hsupport : ∀ i ∈ L,
      i < 2 ^ width addressWidth outputWidth ∧
        correctionPre addressWidth outputWidth high i)
    (hrow : ∀ i ∈ L, readField i lowWidth high = row) :
    ∀ b ∈ runOps level (width addressWidth outputWidth)
      (unaryHadamardOps addressWidth 0 (batchSize lowWidth) ++
        correctionOps table addressWidth outputWidth lowWidth high ++
        unaryHadamardOps addressWidth 0 (batchSize lowWidth))
      (Branch.mk rec cr (basis unaryState) input),
      retainedCreg outputWidth b.creg = retainedCreg outputWidth cr ∧
        b.state =
          (Dy.invSqrt2 (deg level)) ^
              (b.outcomes.length - rec.length) •
            walshPhaseVec (outputWire addressWidth 0) 0
                (batchSize lowWidth)
                (correctionMask table outputWidth lowWidth row
                  (retainedCreg outputWidth cr))
              (basis unaryState : Vec (deg level)) := by
  intro b hb
  rw [runOps_append, List.mem_flatMap] at hb
  obtain ⟨x, hx, hxb⟩ := hb
  rw [runOps_append, List.mem_flatMap] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  rw [unaryHadamardOps_run hl (by simp [width]; omega),
    List.mem_singleton] at hz
  subst z
  rw [hdecomp] at hzx
  have hcorr := correctionOps_superpose
    (input := input) hl table hsplit hfit rec cr L a hsupport hrow x hzx
  rw [unaryHadamardOps_run hl (by simp [width]; omega),
    List.mem_singleton] at hxb
  subst b
  constructor
  · exact hcorr.1
  · rw [hcorr.2, hadamardBlockVec_smul, ← hdecomp,
      hadamardFlipMaskHadamard (Semantics.four_dvd_deg hl)
        (Nat.two_pow_pos _)]
    rfl

def WalshDecomposition
    (level addressWidth outputWidth lowWidth high unaryState : Nat) : Prop :=
  ∃ (L : List Nat) (a : Nat → Dy (deg level)),
    hadamardBlockVec (outputWire addressWidth 0) (batchSize lowWidth)
        (basis unaryState : Vec (deg level)) =
      Semantics.superpose id a L ∧
    (∀ i ∈ L,
      i < 2 ^ width addressWidth outputWidth ∧
        correctionPre addressWidth outputWidth high i) ∧
    (∀ i ∈ L,
      readField i lowWidth high = readField unaryState lowWidth high)

private theorem superpose_append_eq
    {d : Nat} (f : Nat → Nat) (a : Nat → Dy d) :
    ∀ left right,
      Semantics.superpose f a (left ++ right) =
        Semantics.superpose f a left + Semantics.superpose f a right
  | [], right => by
      apply Vec.ext
      intro i
      exact (Dy.zero_add _).symm
  | i :: left, right => by
      rw [List.cons_append, Semantics.superpose, Semantics.superpose,
        superpose_append_eq f a left right]
      apply Vec.ext
      intro j
      exact (Dy.add_assoc _ _ _).symm

private theorem superpose_filter_eq
    {d : Nat} {P : Nat → Bool}
    (f : Nat → Nat) (a : Nat → Dy d) :
    ∀ L, (∀ i ∈ L, P i = false → a i = Dy.zero d) →
      Semantics.superpose f a (L.filter P) =
        Semantics.superpose f a L
  | [], _ => rfl
  | i :: L, hzero => by
      by_cases hi : P i = true
      · rw [List.filter_cons_of_pos hi, Semantics.superpose,
          Semantics.superpose,
          superpose_filter_eq f a L
            (fun j hj ↦ hzero j (List.mem_cons_of_mem i hj))]
      · rw [List.filter_cons_of_neg hi, Semantics.superpose,
          superpose_filter_eq f a L
            (fun j hj ↦ hzero j (List.mem_cons_of_mem i hj)),
          hzero i (List.mem_cons_self ..)
            (Bool.eq_false_of_not_eq_true hi)]
        apply Vec.ext
        intro j
        simp [Vec.add_apply, Vec.smul_apply, Dy.zero_mul, Dy.zero_add]

private theorem superpose_range_eq_vsum
    {d : Nat} (u : Vec d) : ∀ n,
    Semantics.superpose id (fun i ↦ u i) (List.range n) =
      vsum n (fun i ↦ u i • (basis i : Vec d))
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, superpose_append_eq,
        superpose_range_eq_vsum u n, vsum_succ]
      apply Vec.ext
      intro j
      simp [Semantics.superpose, Vec.add_apply, Vec.smul_apply, Dy.add_zero]

private theorem superpose_filter_range_eq
    {d n : Nat} (u : Vec d) (P : Nat → Bool)
    (hu : WFVec n u)
    (hzero : ∀ i, i < n → P i = false → u i = Dy.zero d) :
    Semantics.superpose id (fun i ↦ u i) ((List.range n).filter P) = u := by
  calc
    Semantics.superpose id (fun i ↦ u i) ((List.range n).filter P) =
        Semantics.superpose id (fun i ↦ u i) (List.range n) :=
      superpose_filter_eq id (fun i ↦ u i) (List.range n)
        (fun i hi ↦ hzero i (List.mem_range.mp hi))
    _ = vsum n (fun i ↦ u i • (basis i : Vec d)) :=
      superpose_range_eq_vsum u n
    _ = u := (eq_vsum_basis hu).symm

theorem walshDecomposition_generated
    {level addressWidth outputWidth lowWidth high unaryState : Nat}
    (hl : 3 ≤ level) (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hi : unaryState < 2 ^ width addressWidth outputWidth)
    (hpre : correctionPre addressWidth outputWidth high unaryState) :
    WalshDecomposition level addressWidth outputWidth lowWidth high unaryState := by
  classical
  let u : Vec (deg level) :=
    hadamardBlockVec (outputWire addressWidth 0) (batchSize lowWidth)
      (basis unaryState : Vec (deg level))
  let P : Nat → Bool := fun i ↦ decide
    (correctionPre addressWidth outputWidth high i ∧
      readField i lowWidth high = readField unaryState lowWidth high)
  have hu : WFVec (2 ^ width addressWidth outputWidth) u := by
    apply hadamardBlockVec_wf hl (by simp [outputWire, width]; omega)
    exact wfVec_basis hi
  have hzero : ∀ i, i < 2 ^ width addressWidth outputWidth →
      P i = false → u i = Dy.zero (deg level) := by
    intro i _ hfalse
    have houtside : ¬(correctionPre addressWidth outputWidth high i ∧
        readField i lowWidth high = readField unaryState lowWidth high) := by
      simpa [P] using hfalse
    by_contra hamp
    apply houtside
    have hsame : sameOutside (outputWire addressWidth 0)
        (batchSize lowWidth) unaryState i :=
      hadamardBlockVec_basis_sameOutside (by simpa [u] using hamp)
    constructor
    · rw [correctionPre,
        readField_eq_of_sameOutside hsame (Or.inr (by
          simp [outputWire, selectorWire]
          omega))]
      exact hpre
    · exact readField_eq_of_sameOutside hsame (Or.inl (by
        simp [outputWire]
        omega))
  let L := (List.range (2 ^ width addressWidth outputWidth)).filter P
  refine ⟨L, (fun i ↦ u i), ?_, ?_, ?_⟩
  · exact (superpose_filter_range_eq u P hu hzero).symm
  · intro i hiL
    have hmem := List.mem_filter.mp hiL
    have hP : correctionPre addressWidth outputWidth high i ∧
        readField i lowWidth high = readField unaryState lowWidth high := by
      simpa [P] using hmem.2
    exact ⟨List.mem_range.mp hmem.1, hP.1⟩
  · intro i hiL
    have hP : correctionPre addressWidth outputWidth high i ∧
        readField i lowWidth high = readField unaryState lowWidth high := by
      simpa [P] using (List.mem_filter.mp hiL).2
    exact hP.2

theorem walshSandwich_basis
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high unaryState : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hdecomp : WalshDecomposition level addressWidth outputWidth
      lowWidth high unaryState) (rec : List Bool) (cr : Nat) :
    ∀ b ∈ runOps level (width addressWidth outputWidth)
      (unaryHadamardOps addressWidth 0 (batchSize lowWidth) ++
        correctionOps table addressWidth outputWidth lowWidth high ++
        unaryHadamardOps addressWidth 0 (batchSize lowWidth))
      (Branch.mk rec cr (basis unaryState) input),
      retainedCreg outputWidth b.creg = retainedCreg outputWidth cr ∧
        b.state =
          (Dy.invSqrt2 (deg level)) ^
              (b.outcomes.length - rec.length) •
            (MeasuredUncompute.phaseScalar (deg level)
                (walshParity (outputWire addressWidth 0) 0
                  (batchSize lowWidth)
                  (correctionMask table outputWidth lowWidth
                    (readField unaryState lowWidth high)
                    (retainedCreg outputWidth cr)) unaryState) •
              (basis unaryState : Vec (deg level))) := by
  obtain ⟨L, a, hvec, hsupport, hrow⟩ := hdecomp
  intro b hb
  have hsem := walshSandwich_basis_of_superpose
    (input := input) hl table hsplit hfit rec cr L a hvec hsupport hrow b hb
  constructor
  · exact hsem.1
  · rw [hsem.2, walshPhaseVec_basis]

theorem walshSandwich_basis_generated
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high unaryState : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hi : unaryState < 2 ^ width addressWidth outputWidth)
    (hpre : correctionPre addressWidth outputWidth high unaryState)
    (rec : List Bool) (cr : Nat) :
    ∀ b ∈ runOps level (width addressWidth outputWidth)
      (unaryHadamardOps addressWidth 0 (batchSize lowWidth) ++
        correctionOps table addressWidth outputWidth lowWidth high ++
        unaryHadamardOps addressWidth 0 (batchSize lowWidth))
      (Branch.mk rec cr (basis unaryState) input),
      retainedCreg outputWidth b.creg = retainedCreg outputWidth cr ∧
        b.state =
          (Dy.invSqrt2 (deg level)) ^
              (b.outcomes.length - rec.length) •
            (MeasuredUncompute.phaseScalar (deg level)
                (walshParity (outputWire addressWidth 0) 0
                  (batchSize lowWidth)
                  (correctionMask table outputWidth lowWidth
                    (readField unaryState lowWidth high)
                    (retainedCreg outputWidth cr)) unaryState) •
              (basis unaryState : Vec (deg level))) :=
  walshSandwich_basis hl table hsplit hfit
    (walshDecomposition_generated hl hsplit hfit hi hpre) rec cr

theorem walshSandwich_implementsRetainedPhaseU
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    ImplementsRetainedPhaseU level (width addressWidth outputWidth)
      input outputWidth
      (WalshDecomposition level addressWidth outputWidth lowWidth high)
      (fun _ i ↦ i)
      (fun cr i ↦ walshParity (outputWire addressWidth 0) 0
        (batchSize lowWidth)
        (correctionMask table outputWidth lowWidth
          (readField i lowWidth high) cr) i)
      (Dy.invSqrt2 (deg level))
      (unaryHadamardOps addressWidth 0 (batchSize lowWidth) ++
        correctionOps table addressWidth outputWidth lowWidth high ++
        unaryHadamardOps addressWidth 0 (batchSize lowWidth)) := by
  intro i hi hdecomp rec cr b hb
  exact walshSandwich_basis hl table hsplit hfit hdecomp rec cr b hb

theorem prepareStageOps_eq_gateOps (addressWidth stage : Nat) : ∀ low count,
    prepareStageOps addressWidth stage low count =
      gateOps (swapFieldsControlled stage
        (outputWire addressWidth low)
        (outputWire addressWidth (low + 2 ^ stage)) count) := by
  intro low count
  induction count generalizing low with
  | zero => rfl
  | succ count ih =>
      rw [prepareStageOps, swapFieldsControlled, gateOps_append, ih]
      simp [outputWire, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

def prepareUnaryGates (addressWidth : Nat) : Nat → List RGate
  | 0 => [.x (outputWire addressWidth 0)]
  | lowWidth + 1 =>
      prepareUnaryGates addressWidth lowWidth ++
        swapFieldsControlled lowWidth (outputWire addressWidth 0)
          (outputWire addressWidth (2 ^ lowWidth)) (2 ^ lowWidth)

def prepareUnaryOut (addressWidth lowWidth i : Nat) : Nat :=
  actGates (prepareUnaryGates addressWidth lowWidth) i

def unaryValue (lowWidth i : Nat) : Nat :=
  2 ^ readField i 0 lowWidth

def unaryClear (addressWidth lowWidth i : Nat) : Prop :=
  readField i (outputWire addressWidth 0) (batchSize lowWidth) = 0

def unaryReady (addressWidth lowWidth i : Nat) : Prop :=
  readField i (outputWire addressWidth 0) (batchSize lowWidth) =
    unaryValue lowWidth i

theorem prepareUnaryOps_eq_gateOps (addressWidth lowWidth : Nat) :
    prepareUnaryOps addressWidth lowWidth =
      gateOps (prepareUnaryGates addressWidth lowWidth) := by
  induction lowWidth with
  | zero => rfl
  | succ lowWidth ih =>
      rw [prepareUnaryOps, prepareUnaryGates, gateOps_append, ← ih,
        prepareStageOps_eq_gateOps]
      simp

theorem prepareUnaryGates_wellFormed
    {addressWidth outputWidth lowWidth : Nat}
    (haddress : lowWidth ≤ addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    (prepareUnaryGates addressWidth lowWidth).all
      (RGate.wellFormed (width addressWidth outputWidth)) = true := by
  induction lowWidth with
  | zero =>
      simp [batchSize] at hfit
      simp [prepareUnaryGates, RGate.wellFormed, width, outputWire]
      omega
  | succ lowWidth ih =>
      have hpow : 0 < 2 ^ lowWidth := Nat.two_pow_pos lowWidth
      have hstageFit : 2 * 2 ^ lowWidth ≤ outputWidth := by
        simpa [batchSize, Nat.pow_succ, Nat.mul_comm] using hfit
      have hprevFit : batchSize lowWidth ≤ outputWidth := by
        simp [batchSize]
        omega
      have hprev := ih (by omega) hprevFit
      have hstage :
          (swapFieldsControlled lowWidth (outputWire addressWidth 0)
            (outputWire addressWidth (2 ^ lowWidth)) (2 ^ lowWidth)).all
            (RGate.wellFormed (width addressWidth outputWidth)) = true := by
        apply swapFieldsControlled_wellFormed
        · left
          simp [outputWire]
        · left
          simp [outputWire]
          omega
        · left
          simp [outputWire]
          omega
        · simp [width]
          omega
        · simp [width, outputWire]
          omega
        · simp [width, outputWire]
          omega
      rw [prepareUnaryGates, List.all_append, hprev, hstage, Bool.true_and]

theorem prepareUnaryOps_implements
    {level input addressWidth outputWidth lowWidth : Nat}
    (hl : 3 ≤ level) (haddress : lowWidth ≤ addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    ImplementsU level (width addressWidth outputWidth) input (fun _ => True)
      (prepareUnaryOut addressWidth lowWidth) (Dy.invSqrt2 (deg level))
      (prepareUnaryOps addressWidth lowWidth) := by
  have hgates := prepareUnaryGates_wellFormed haddress hfit
  have hwf : ({ width := width addressWidth outputWidth, gates := prepareUnaryGates addressWidth lowWidth } : RCircuit).wellFormed = true := by
    simpa [RCircuit.wellFormed] using hgates
  rw [prepareUnaryOps_eq_gateOps]
  exact gateOps_implementsU hl hwf (Dy.invSqrt2 (deg level))

theorem prepareUnaryOps_implementsRetainedU
    {level input addressWidth outputWidth lowWidth : Nat}
    (hl : 3 ≤ level) (haddress : lowWidth ≤ addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    ImplementsRetainedU level (width addressWidth outputWidth) input outputWidth
      (fun _ ↦ True) (fun _ i ↦ prepareUnaryOut addressWidth lowWidth i)
      (Dy.invSqrt2 (deg level)) (prepareUnaryOps addressWidth lowWidth) := by
  have hgates := prepareUnaryGates_wellFormed haddress hfit
  have hwf : (RCircuit.mk (width addressWidth outputWidth)
      (prepareUnaryGates addressWidth lowWidth)).wellFormed = true := by
    simpa [RCircuit.wellFormed] using hgates
  rw [prepareUnaryOps_eq_gateOps]
  exact gateOps_implementsRetainedU hl hwf (Dy.invSqrt2 (deg level))

theorem unaryValue_lt (lowWidth i : Nat) :
    unaryValue lowWidth i < 2 ^ batchSize lowWidth := by
  apply Nat.pow_lt_pow_right (by omega)
  simpa [batchSize] using readField_lt i 0 lowWidth

theorem prepareUnaryOut_eq_write
    {addressWidth lowWidth i : Nat}
    (haddress : lowWidth ≤ addressWidth)
    (hclear : unaryClear addressWidth lowWidth i) :
    prepareUnaryOut addressWidth lowWidth i =
      writeField i (outputWire addressWidth 0) (batchSize lowWidth)
        (unaryValue lowWidth i) := by
  induction lowWidth with
  | zero =>
      have hbit : bitValue i (outputWire addressWidth 0) = 0 := by
        simpa [unaryClear, batchSize, readField_one] using hclear
      simp [prepareUnaryOut, prepareUnaryGates, actGates_cons, actGates_nil,
        act_x_write, hbit, unaryValue, batchSize, readField, Nat.mod_one]
  | succ lowWidth ih =>
      let k := 2 ^ lowWidth
      let off := outputWire addressWidth 0
      let upper := outputWire addressWidth k
      let value := unaryValue lowWidth i
      have hk : 0 < k := Nat.two_pow_pos lowWidth
      have hsplit : readField i off k = 0 ∧ readField i upper k = 0 := by
        have := (readField_split (i := i) (off := off) (a := k) (b := k)).mp ?_
        · simpa [upper, off, outputWire] using this
        · simpa [unaryClear, batchSize, Nat.pow_succ, Nat.mul_two, k, off] using hclear
      have hprevClear : unaryClear addressWidth lowWidth i := by
        simpa [unaryClear, batchSize, off] using hsplit.1
      have hprev := ih (by omega) hprevClear
      change prepareUnaryOut addressWidth lowWidth i =
        writeField i off k value at hprev
      have hvalueFit : value < 2 ^ k := by
        simpa [value, k, batchSize] using unaryValue_lt lowWidth i
      have hcontrol : bitValue
          (writeField i off k value) lowWidth = bitValue i lowWidth := by
        rw [bitValue_write_out (Or.inl (by
          simp [off, outputWire]
          omega))]
      rw [prepareUnaryOut, prepareUnaryGates, actGates_append]
      change actGates
        (swapFieldsControlled lowWidth off upper k)
          (prepareUnaryOut addressWidth lowWidth i) = _
      rw [hprev]
      rw [show batchSize (lowWidth + 1) = k + k by
        simp [batchSize, Nat.pow_succ, Nat.mul_two, k]]
      change actGates (swapFieldsControlled lowWidth off upper k)
          (writeField i off k value) =
        writeField i off (k + k) (unaryValue (lowWidth + 1) i)
      cases hc : bitValue i lowWidth with
      | zero =>
          have hcontrolZero : bitValue
              (writeField i off k value) lowWidth = 0 := hcontrol.trans hc
          rw [swapFieldsControlled_off k off upper
            (writeField i off k value) (by simp [off, upper, outputWire])
            (by left; simp [off, outputWire]; omega) hcontrolZero]
          have hwideValue : unaryValue (lowWidth + 1) i = value := by
            rw [unaryValue, readField_high]
            simp only [Nat.zero_add]
            rw [hc]
            simp [value, unaryValue]
          rw [hwideValue]
          change writeField i off k value = writeField i off (k + k) value
          have hvalueWideFit : value < 2 ^ (k + k) :=
            hvalueFit.trans (Nat.pow_lt_pow_right (by omega) (by omega))
          rw [← Reversible.xor_shiftedField_eq_writeField_of_clear
              (i := i) (value := value) (wire := off) (width := k)
              hsplit.1 hvalueFit,
            ← Reversible.xor_shiftedField_eq_writeField_of_clear
              (i := i) (value := value) (wire := off) (width := k + k)
              (by simpa [unaryClear, batchSize, Nat.pow_succ, Nat.mul_two, k, off]
                using hclear)
              hvalueWideFit]
      | succ control =>
          have hcOne : bitValue i lowWidth = 1 := by
            have := bitValue_lt i lowWidth
            omega
          have hcontrolOne : bitValue
              (writeField i off k value) lowWidth = 1 := hcontrol.trans hcOne
          rw [swapFieldsControlled_on k off upper
            (writeField i off k value) (by simp [off, upper, outputWire])
            (by left; simp [off, outputWire]; omega)
            (by left; simp [upper, outputWire]; omega)
            hcontrolOne]
          rw [readField_writeField_of_disjoint (Or.inl (by
                simp [off, upper, outputWire])),
            readField_writeField_self hvalueFit,
            hsplit.2,
            writeField_writeField,
            show writeField i off k 0 = i by simpa [hsplit.1] using
              (writeField_read i off k)]
          have hwideValue : unaryValue (lowWidth + 1) i = 2 ^ k * value := by
            rw [unaryValue, readField_high]
            simp only [Nat.zero_add]
            rw [hcOne]
            simp [value, unaryValue, k, Nat.pow_add, Nat.mul_comm]
          rw [hwideValue]
          change writeField i upper k value =
            writeField i off (k + k) (2 ^ k * value)
          have hwideFit : 2 ^ k * value < 2 ^ (k + k) := by
            rw [Nat.pow_add]
            exact (Nat.mul_lt_mul_left (Nat.two_pow_pos k)).2 hvalueFit
          rw [← Reversible.xor_shiftedField_eq_writeField_of_clear
              (i := i) (value := value) (wire := upper) (width := k)
              hsplit.2 hvalueFit,
            ← Reversible.xor_shiftedField_eq_writeField_of_clear
              (i := i) (value := 2 ^ k * value) (wire := off) (width := k + k)
              (by simpa [unaryClear, batchSize, Nat.pow_succ, Nat.mul_two, k, off]
                using hclear)
              hwideFit]
          simp [upper, off, outputWire, Nat.shiftLeft_eq, Nat.pow_add,
            Nat.mul_assoc, Nat.mul_comm]

theorem prepareUnaryOut_ready
    {addressWidth lowWidth i : Nat}
    (haddress : lowWidth ≤ addressWidth)
    (hclear : unaryClear addressWidth lowWidth i) :
    unaryReady addressWidth lowWidth
      (prepareUnaryOut addressWidth lowWidth i) := by
  rw [prepareUnaryOut_eq_write haddress hclear]
  rw [unaryReady, readField_writeField_self (unaryValue_lt lowWidth i)]
  unfold unaryValue
  rw [readField_writeField_of_disjoint (Or.inr (by
    simp [outputWire]
    omega))]

theorem prepareUnaryOut_lt
    {addressWidth outputWidth lowWidth i : Nat}
    (haddress : lowWidth ≤ addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hi : i < 2 ^ width addressWidth outputWidth) :
    prepareUnaryOut addressWidth lowWidth i <
      2 ^ width addressWidth outputWidth := by
  apply actGates_lt
  · intro g hg
    exact (List.all_eq_true.mp
      (prepareUnaryGates_wellFormed haddress hfit)) g hg
  · exact hi

theorem prepareUnaryOut_readField_before
    {addressWidth lowWidth i field fieldWidth : Nat}
    (haddress : lowWidth ≤ addressWidth)
    (hclear : unaryClear addressWidth lowWidth i)
    (hbefore : field + fieldWidth ≤ addressWidth) :
    readField (prepareUnaryOut addressWidth lowWidth i) field fieldWidth =
      readField i field fieldWidth := by
  rw [prepareUnaryOut_eq_write haddress hclear,
    readField_writeField_of_disjoint]
  exact Or.inr (by simp [outputWire]; omega)

theorem prepareUnaryOut_correctionPre
    {addressWidth outputWidth lowWidth high i : Nat}
    (haddress : lowWidth ≤ addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hclear : unaryClear addressWidth lowWidth i)
    (hpre : correctionPre addressWidth outputWidth high i) :
    correctionPre addressWidth outputWidth high
      (prepareUnaryOut addressWidth lowWidth i) := by
  rw [correctionPre, prepareUnaryOut_eq_write haddress hclear,
    readField_writeField_of_disjoint]
  · exact hpre
  · exact Or.inl (by simp [outputWire, selectorWire]; omega)

theorem clearBits_unaryClear
    {addressWidth outputWidth lowWidth i : Nat}
    (hfit : batchSize lowWidth ≤ outputWidth) :
    unaryClear addressWidth lowWidth
      (MeasuredUncompute.clearBits addressWidth 0 outputWidth i) := by
  unfold unaryClear
  rw [MeasuredUncompute.clearBits_zero addressWidth outputWidth addressWidth]
  change readField (writeField i addressWidth outputWidth 0)
    (outputWire addressWidth 0) (batchSize lowWidth) = 0
  have hread := readField_writeField_subfield
    (i := i) (off := addressWidth) (width := outputWidth)
    (v := 0) (inner := 0) (len := batchSize lowWidth) (by omega)
  simpa [outputWire, readField] using hread

theorem clearBits_readField_before
    {addressWidth outputWidth i field fieldWidth : Nat}
    (hbefore : field + fieldWidth ≤ addressWidth) :
    readField (MeasuredUncompute.clearBits addressWidth 0 outputWidth i)
        field fieldWidth =
      readField i field fieldWidth := by
  rw [MeasuredUncompute.clearBits_zero addressWidth outputWidth addressWidth]
  change readField (writeField i addressWidth outputWidth 0)
      field fieldWidth = readField i field fieldWidth
  rw [readField_writeField_of_disjoint]
  exact Or.inr (by omega)

theorem clearBits_correctionPre
    {addressWidth outputWidth high i : Nat}
    (hhigh : high ≤ addressWidth)
    (hworkspace : Lookup.workspace addressWidth outputWidth addressWidth i = 0) :
    correctionPre addressWidth outputWidth high
      (MeasuredUncompute.clearBits addressWidth 0 outputWidth i) := by
  rw [correctionPre,
    MeasuredUncompute.clearBits_zero addressWidth outputWidth addressWidth]
  change readField (writeField i addressWidth outputWidth 0)
      (selectorWire addressWidth outputWidth 0) high = 0
  rw [readField_writeField_of_disjoint]
  · simpa [Lookup.workspace, Lookup.layout, Layout.read, Layout.offset,
      Layout.size, selectorWire] using
      readField_sub_zero (i := i) (off := addressWidth + outputWidth)
        (len := addressWidth) (o := selectorWire addressWidth outputWidth 0)
        (l := high) (by simp [selectorWire]) (by simp [selectorWire]; omega)
        hworkspace
  · exact Or.inl (by simp [selectorWire])

def clearPairReady (addressWidth stage low i : Nat) : Prop :=
  let x := outputWire addressWidth low
  let y := outputWire addressWidth (low + 2 ^ stage)
  i.testBit y =
    (i.testBit stage && Bool.xor (i.testBit x) (i.testBit y))

def clearPairOut (addressWidth stage low i : Nat) : Nat :=
  let x := outputWire addressWidth low
  let y := outputWire addressWidth (low + 2 ^ stage)
  writeBit (RGate.act (.cx y x) i) y false

def clearStageReady (addressWidth stage low count i : Nat) : Prop :=
  ∀ offset, offset < count → clearPairReady addressWidth stage (low + offset) i

def clearStageOut (addressWidth stage : Nat) : Nat → Nat → Nat → Nat
  | _, 0, i => i
  | low, count + 1, i =>
      clearStageOut addressWidth stage (low + 1) count
        (clearPairOut addressWidth stage low i)

def clearUnaryOut (addressWidth : Nat) : Nat → Nat → Nat
  | 0, i => RGate.act (.x (outputWire addressWidth 0)) i
  | lowWidth + 1, i =>
      clearUnaryOut addressWidth lowWidth
        (clearStageOut addressWidth lowWidth 0 (2 ^ lowWidth) i)

theorem clearPairReady_afterCnot
    {addressWidth stage low i : Nat} (hstage : stage < addressWidth)
    (hready : clearPairReady addressWidth stage low i) :
    let x := outputWire addressWidth low
    let y := outputWire addressWidth (low + 2 ^ stage)
    let j := RGate.act (.cx y x) i
    j.testBit y = (j.testBit stage && j.testBit x) := by
  let x := outputWire addressWidth low
  let y := outputWire addressWidth (low + 2 ^ stage)
  have hyx : y ≠ x := by simp [x, y, outputWire]
  have hsx : stage ≠ x := by simp [x, outputWire]; omega
  change (RGate.act (.cx y x) i).testBit y =
    ((RGate.act (.cx y x) i).testBit stage &&
      (RGate.act (.cx y x) i).testBit x)
  cases hs : i.testBit stage <;>
    cases hx : i.testBit x <;>
    cases hy : i.testBit y <;>
    simp [clearPairReady, x, y, hs, hx, hy, RGate.act,
      RGate.testBit_xor_of_ne hyx, RGate.testBit_xor_of_ne hsx] at hready ⊢

theorem clearPairOut_testBit_of_ne
    {addressWidth stage low i q : Nat}
    (hqx : q ≠ outputWire addressWidth low)
    (hqy : q ≠ outputWire addressWidth (low + 2 ^ stage)) :
    (clearPairOut addressWidth stage low i).testBit q = i.testBit q := by
  rw [clearPairOut, testBit_writeBit_of_ne hqy]
  simp only [RGate.act]
  split
  · exact RGate.testBit_xor_of_ne hqx i
  · rfl

theorem clearPairOut_testBit_lower
    (addressWidth stage low i : Nat) :
    (clearPairOut addressWidth stage low i).testBit
        (outputWire addressWidth low) =
      Bool.xor (i.testBit (outputWire addressWidth low))
        (i.testBit (outputWire addressWidth (low + 2 ^ stage))) := by
  have hxy : outputWire addressWidth low ≠
      outputWire addressWidth (low + 2 ^ stage) := by
    simp [outputWire]
  cases hy : i.testBit (outputWire addressWidth (low + 2 ^ stage)) <;>
    simp [clearPairOut, testBit_writeBit_of_ne hxy, RGate.act, hy]

theorem clearPairOut_testBit_upper
    (addressWidth stage low i : Nat) :
    (clearPairOut addressWidth stage low i).testBit
        (outputWire addressWidth (low + 2 ^ stage)) = false := by
  rw [clearPairOut, testBit_writeBit]

theorem clearStageOut_testBit_of_ne
    {addressWidth stage q : Nat} : ∀ {low count i : Nat},
    (∀ offset, offset < count →
      q ≠ outputWire addressWidth (low + offset) ∧
      q ≠ outputWire addressWidth (low + offset + 2 ^ stage)) →
    (clearStageOut addressWidth stage low count i).testBit q = i.testBit q := by
  intro low count
  induction count generalizing low with
  | zero => intro i _; rfl
  | succ count ih =>
      intro i hne
      rw [clearStageOut]
      have htail : ∀ offset, offset < count →
          q ≠ outputWire addressWidth (low + 1 + offset) ∧
          q ≠ outputWire addressWidth (low + 1 + offset + 2 ^ stage) := by
        intro offset hoffset
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hne (offset + 1) (by omega)
      rw [ih htail]
      exact clearPairOut_testBit_of_ne
        (by simpa using (hne 0 (by omega)).1)
        (by simpa using (hne 0 (by omega)).2)

theorem clearStageOut_testBit_lower
    {addressWidth stage low count i offset : Nat}
    (hbound : low + count ≤ 2 ^ stage) (hoffset : offset < count) :
    (clearStageOut addressWidth stage low count i).testBit
        (outputWire addressWidth (low + offset)) =
      Bool.xor (i.testBit (outputWire addressWidth (low + offset)))
        (i.testBit (outputWire addressWidth (low + offset + 2 ^ stage))) := by
  induction count generalizing low i offset with
  | zero => omega
  | succ count ih =>
      rw [clearStageOut]
      cases offset with
      | zero =>
          have htail := clearStageOut_testBit_of_ne
            (addressWidth := addressWidth) (stage := stage)
            (q := outputWire addressWidth low)
            (low := low + 1) (count := count)
            (i := clearPairOut addressWidth stage low i) (by
              intro offset hoffset
              constructor <;> simp [outputWire] <;> omega)
          simpa only [Nat.add_zero] using htail.trans
            (clearPairOut_testBit_lower addressWidth stage low i)
      | succ offset =>
          have hnext := ih (low := low + 1)
            (i := clearPairOut addressWidth stage low i)
            (offset := offset) (by omega) (by omega)
          have hnext' :
              (clearStageOut addressWidth stage (low + 1) count
                (clearPairOut addressWidth stage low i)).testBit
                  (outputWire addressWidth (low + (offset + 1))) =
                Bool.xor
                  ((clearPairOut addressWidth stage low i).testBit
                    (outputWire addressWidth (low + (offset + 1))))
                  ((clearPairOut addressWidth stage low i).testBit
                    (outputWire addressWidth
                      (low + (offset + 1) + 2 ^ stage))) := by
            simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext
          have hnextX : outputWire addressWidth (low + (offset + 1)) ≠
              outputWire addressWidth low := by simp [outputWire]
          have hnextY : outputWire addressWidth (low + (offset + 1)) ≠
              outputWire addressWidth (low + 2 ^ stage) := by
            simp [outputWire]
            omega
          have hupperX : outputWire addressWidth
                (low + (offset + 1) + 2 ^ stage) ≠
              outputWire addressWidth low := by simp [outputWire]; omega
          have hupperY : outputWire addressWidth
                (low + (offset + 1) + 2 ^ stage) ≠
              outputWire addressWidth (low + 2 ^ stage) := by
            simp [outputWire]
          rw [clearPairOut_testBit_of_ne hnextX hnextY,
            clearPairOut_testBit_of_ne hupperX hupperY] at hnext'
          exact hnext'

theorem clearStageOut_testBit_upper
    {addressWidth stage low count i offset : Nat}
    (hbound : low + count ≤ 2 ^ stage) (hoffset : offset < count) :
    (clearStageOut addressWidth stage low count i).testBit
        (outputWire addressWidth (low + offset + 2 ^ stage)) = false := by
  induction count generalizing low i offset with
  | zero => omega
  | succ count ih =>
      rw [clearStageOut]
      cases offset with
      | zero =>
          have htail := clearStageOut_testBit_of_ne
            (addressWidth := addressWidth) (stage := stage)
            (q := outputWire addressWidth (low + 2 ^ stage))
            (low := low + 1) (count := count)
            (i := clearPairOut addressWidth stage low i) (by
              intro offset hoffset
              constructor <;> simp [outputWire] <;> omega)
          simpa only [Nat.add_zero] using htail.trans
            (clearPairOut_testBit_upper addressWidth stage low i)
      | succ offset =>
          have hnext := ih (low := low + 1)
            (i := clearPairOut addressWidth stage low i)
            (offset := offset) (by omega) (by omega)
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext

theorem clearStageOut_testBit_address
    {addressWidth stage low count i q : Nat} (hq : q < addressWidth) :
    (clearStageOut addressWidth stage low count i).testBit q = i.testBit q := by
  apply clearStageOut_testBit_of_ne
  intro offset hoffset
  have hlower : q < outputWire addressWidth (low + offset) := by
    exact hq.trans_le (by simp [outputWire])
  have hupper : q < outputWire addressWidth (low + offset + 2 ^ stage) := by
    exact hq.trans_le (by simp [outputWire])
  exact ⟨Nat.ne_of_lt hlower, Nat.ne_of_lt hupper⟩

theorem clearStageOut_readField_address
    {addressWidth stage low count i : Nat} (hstage : stage ≤ addressWidth) :
    readField (clearStageOut addressWidth stage low count i) 0 stage =
      readField i 0 stage := by
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [testBit_readField, testBit_readField]
  by_cases hbit : bit < stage
  · simp only [hbit, decide_true, Bool.true_and]
    exact clearStageOut_testBit_address (by omega)
  · simp [hbit]

theorem clearStageReady_tail
    {addressWidth stage low count i : Nat}
    (hstage : stage < addressWidth)
    (hbound : low + (count + 1) ≤ 2 ^ stage)
    (hready : clearStageReady addressWidth stage low (count + 1) i) :
    clearStageReady addressWidth stage (low + 1) count
      (clearPairOut addressWidth stage low i) := by
  intro offset hoffset
  have hnext := hready (offset + 1) (by omega)
  let currentX := outputWire addressWidth low
  let currentY := outputWire addressWidth (low + 2 ^ stage)
  let nextX := outputWire addressWidth (low + 1 + offset)
  let nextY := outputWire addressWidth (low + 1 + offset + 2 ^ stage)
  have hstageX : stage ≠ currentX := by
    simp [currentX, outputWire]
    omega
  have hstageY : stage ≠ currentY := by
    simp [currentY, outputWire]
    omega
  have hnextXCurrentX : nextX ≠ currentX := by
    simp [nextX, currentX, outputWire]
    omega
  have hnextXCurrentY : nextX ≠ currentY := by
    simp [nextX, currentY, outputWire]
    omega
  have hnextYCurrentX : nextY ≠ currentX := by
    simp [nextY, currentX, outputWire]
    omega
  have hnextYCurrentY : nextY ≠ currentY := by
    simp [nextY, currentY, outputWire]
    omega
  change clearPairReady addressWidth stage (low + 1 + offset)
    (clearPairOut addressWidth stage low i)
  have hnext' : clearPairReady addressWidth stage (low + 1 + offset) i := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext
  simpa only [clearPairReady, nextX, nextY,
      clearPairOut_testBit_of_ne hstageX hstageY,
      clearPairOut_testBit_of_ne hnextXCurrentX hnextXCurrentY,
      clearPairOut_testBit_of_ne hnextYCurrentX hnextYCurrentY] using hnext'

theorem clearPairOut_lt
    {addressWidth outputWidth stage low i : Nat}
    (hlow : low < 2 ^ stage) (hfit : 2 ^ (stage + 1) ≤ outputWidth)
    (hi : i < 2 ^ width addressWidth outputWidth) :
    clearPairOut addressWidth stage low i <
      2 ^ width addressWidth outputWidth := by
  let x := outputWire addressWidth low
  let y := outputWire addressWidth (low + 2 ^ stage)
  have hx : x < width addressWidth outputWidth := by
    simp [x, outputWire, width]
    omega
  have hy : y < width addressWidth outputWidth := by
    simp [y, outputWire, width]
    omega
  have hxy : x ≠ y := by simp [x, y, outputWire]
  have hcx : (RGate.cx y x).wellFormed (width addressWidth outputWidth) = true := by
    simp [RGate.wellFormed, hx, hy, Ne.symm hxy]
  exact Lookup3.writeBit_lt hy (RGate.act_lt hcx hi)

theorem clearStageOut_lt
    {addressWidth outputWidth stage low count i : Nat}
    (hbound : low + count ≤ 2 ^ stage)
    (hfit : 2 ^ (stage + 1) ≤ outputWidth)
    (hi : i < 2 ^ width addressWidth outputWidth) :
    clearStageOut addressWidth stage low count i <
      2 ^ width addressWidth outputWidth := by
  induction count generalizing low i with
  | zero => exact hi
  | succ count ih =>
      rw [clearStageOut]
      exact ih (by omega)
        (clearPairOut_lt (show low < 2 ^ stage by omega) hfit hi)

theorem clearPairOps_implements
    {level input addressWidth outputWidth stage low : Nat}
    (hl : 3 ≤ level) (hstage : stage < addressWidth)
    (hlow : low < 2 ^ stage) (hfit : 2 ^ (stage + 1) ≤ outputWidth) :
    ImplementsU level (width addressWidth outputWidth) input
      (clearPairReady addressWidth stage low)
      (clearPairOut addressWidth stage low)
      (Dy.invSqrt2 (deg level))
      ([.gate (.cx (outputWire addressWidth (low + 2 ^ stage))
          (outputWire addressWidth low))] ++
        Semantics.andUncomputeClean stage (outputWire addressWidth low)
          (outputWire addressWidth (low + 2 ^ stage)) (scratchBit outputWidth)) := by
  let w := width addressWidth outputWidth
  let x := outputWire addressWidth low
  let y := outputWire addressWidth (low + 2 ^ stage)
  have hx : x < w := by simp [x, w, width, outputWire]; omega
  have hy : y < w := by simp [y, w, width, outputWire]; omega
  have hs : stage < w := by simp [w, width]; omega
  have hxy : x ≠ y := by simp [x, y, outputWire]
  have hsx : stage ≠ x := by simp [x, outputWire]; omega
  have hsy : stage ≠ y := by simp [y, outputWire]; omega
  have hcxwf : (RGate.cx y x).wellFormed w = true := by
    simp [RGate.wellFormed, hx, hy, Ne.symm hxy]
  have hcxCircuit : ({ width := w, gates := [.cx y x] } : RCircuit).wellFormed = true := by
    simp [RCircuit.wellFormed, hcxwf]
  have hcxAll := gateOps_implementsU (input := input) hl hcxCircuit
    (Dy.invSqrt2 (deg level))
  have hcx := hcxAll.mono (dom' := clearPairReady addressWidth stage low)
    (fun _ _ => trivial)
  have hand := implementsU_andUncomputeClean (input := input)
    (w := w) (a := stage) (b := x) (c := y) (m := scratchBit outputWidth)
    hl hs hx hy hsx hsy hxy
  have hall := hcx.append hand
    (fun i hi _ => RGate.act_lt hcxwf hi)
    (fun _ _ hready => by
      simpa [x, y, actGates_cons, actGates_nil] using
        clearPairReady_afterCnot hstage hready)
  have hout : (fun i => writeBit (actGates [.cx y x] i) y false) =
      clearPairOut addressWidth stage low := by
    funext i
    rfl
  rw [hout] at hall
  simpa [clearPairOut, x, y, gateOps, Unary.gateOps, compileGate,
    Function.comp_def] using hall

theorem clearPairOps_implementsRetainedU
    {level input addressWidth outputWidth stage low : Nat}
    (hl : 3 ≤ level) (hstage : stage < addressWidth)
    (hlow : low < 2 ^ stage) (hfit : 2 ^ (stage + 1) ≤ outputWidth) :
    ImplementsRetainedU level (width addressWidth outputWidth) input outputWidth
      (clearPairReady addressWidth stage low)
      (fun _ i ↦ clearPairOut addressWidth stage low i)
      (Dy.invSqrt2 (deg level))
      ([.gate (.cx (outputWire addressWidth (low + 2 ^ stage))
          (outputWire addressWidth low))] ++
        Semantics.andUncomputeClean stage (outputWire addressWidth low)
          (outputWire addressWidth (low + 2 ^ stage))
          (scratchBit outputWidth)) := by
  let w := width addressWidth outputWidth
  let x := outputWire addressWidth low
  let y := outputWire addressWidth (low + 2 ^ stage)
  have hx : x < w := by simp [x, w, width, outputWire]; omega
  have hy : y < w := by simp [y, w, width, outputWire]; omega
  have hs : stage < w := by simp [w, width]; omega
  have hxy : x ≠ y := by simp [x, y, outputWire]
  have hsx : stage ≠ x := by simp [x, outputWire]; omega
  have hsy : stage ≠ y := by simp [y, outputWire]; omega
  have hcxwf : (RGate.cx y x).wellFormed w = true := by
    simp [RGate.wellFormed, hx, hy, Ne.symm hxy]
  have hcxCircuit :
      ({ width := w, gates := [.cx y x] } : RCircuit).wellFormed = true := by
    simp [RCircuit.wellFormed, hcxwf]
  have hcxAll := gateOps_implementsRetainedU
    (input := input) (retained := outputWidth) hl hcxCircuit
    (Dy.invSqrt2 (deg level))
  have hcx := hcxAll.mono
    (dom' := clearPairReady addressWidth stage low) (fun _ _ ↦ trivial)
  have hand := andUncomputeClean_implementsRetainedU
    (input := input) (w := w) (retained := outputWidth)
    (a := stage) (b := x) (c := y) (scratch := scratchBit outputWidth)
    hl hs hx hy hsx hsy hxy (by simp [scratchBit])
  have hall := hcx.append hand
    (fun _ i hi _ ↦ RGate.act_lt hcxwf hi)
    (fun _ _ _ hready ↦ by
      simpa [x, y, actGates_cons, actGates_nil] using
        clearPairReady_afterCnot hstage hready)
  have hout : (fun (_ : Nat) i ↦ writeBit (actGates [.cx y x] i) y false) =
      (fun (_ : Nat) i ↦ clearPairOut addressWidth stage low i) := by
    funext _ i
    rfl
  rw [hout] at hall
  simpa [clearPairOut, x, y, gateOps, Unary.gateOps, compileGate,
    Function.comp_def] using hall

theorem clearStageOps_implements
    {level input addressWidth outputWidth stage low count : Nat}
    (hl : 3 ≤ level) (hstage : stage < addressWidth)
    (hbound : low + count ≤ 2 ^ stage)
    (hfit : 2 ^ (stage + 1) ≤ outputWidth) :
    ImplementsU level (width addressWidth outputWidth) input
      (clearStageReady addressWidth stage low count)
      (clearStageOut addressWidth stage low count)
      (Dy.invSqrt2 (deg level))
      (clearStageOps addressWidth outputWidth stage low count) := by
  induction count generalizing low with
  | zero =>
      intro i _ _ rec _ b hb
      rw [clearStageOps, runOps_nil, List.mem_singleton] at hb
      subst b
      simp only [clearStageOut, Nat.sub_self, Dy.pow_zero_eq, Vec.one_smul]
  | succ count ih =>
      have hhead := clearPairOps_implements (input := input) hl hstage
        (show low < 2 ^ stage by omega) hfit
      have hheadReady := hhead.mono
        (dom' := clearStageReady addressWidth stage low (count + 1))
        (fun _ hready => hready 0 (by omega))
      have htail := ih (low := low + 1) (by omega)
      have hall := hheadReady.append htail
        (fun i hi _ => clearPairOut_lt (by omega) hfit hi)
        (fun _ _ hready => clearStageReady_tail hstage hbound hready)
      simpa [clearStageOps, clearStageOut, clearPairOut,
        Function.comp_def, List.append_assoc] using hall

theorem clearStageOps_implementsRetainedU
    {level input addressWidth outputWidth stage low count : Nat}
    (hl : 3 ≤ level) (hstage : stage < addressWidth)
    (hbound : low + count ≤ 2 ^ stage)
    (hfit : 2 ^ (stage + 1) ≤ outputWidth) :
    ImplementsRetainedU level (width addressWidth outputWidth) input outputWidth
      (clearStageReady addressWidth stage low count)
      (fun _ i ↦ clearStageOut addressWidth stage low count i)
      (Dy.invSqrt2 (deg level))
      (clearStageOps addressWidth outputWidth stage low count) := by
  induction count generalizing low with
  | zero =>
      intro i _ _ rec cr b hb
      rw [clearStageOps, runOps_nil, List.mem_singleton] at hb
      subst b
      simp only [retainedCreg, clearStageOut, Nat.sub_self,
        Dy.pow_zero_eq, Vec.one_smul, and_self]
  | succ count ih =>
      have hhead := clearPairOps_implementsRetainedU
        (input := input) hl hstage (show low < 2 ^ stage by omega) hfit
      have hheadReady := hhead.mono
        (dom' := clearStageReady addressWidth stage low (count + 1))
        (fun _ hready ↦ hready 0 (by omega))
      have htail := ih (low := low + 1) (by omega)
      have hall := hheadReady.append htail
        (fun _ i hi _ ↦ clearPairOut_lt (by omega) hfit hi)
        (fun _ _ _ hready ↦ clearStageReady_tail hstage hbound hready)
      simpa [clearStageOps, clearStageOut, clearPairOut,
        Function.comp_def, List.append_assoc] using hall

theorem unaryReady_testBit
    {addressWidth lowWidth i index : Nat}
    (hindex : index < batchSize lowWidth)
    (hready : unaryReady addressWidth lowWidth i) :
    i.testBit (outputWire addressWidth index) =
      decide (readField i 0 lowWidth = index) := by
  unfold unaryReady unaryValue at hready
  have h := congrArg (fun value => value.testBit index) hready
  rw [testBit_readField, Nat.testBit_two_pow] at h
  simpa [hindex, outputWire] using h

private theorem walshParity_of_all_false
    {off bit count mask i : Nat}
    (hfalse : ∀ index, index < count →
      i.testBit (off + index) = false) :
    walshParity off bit count mask i = false := by
  induction count generalizing off bit with
  | zero => rfl
  | succ count ih =>
      have hhead := hfalse 0 (by omega)
      simp only [Nat.add_zero] at hhead
      rw [walshParity, hhead]
      simp only [Bool.false_and, Bool.false_xor]
      apply ih
      intro index hindex
      have hnext := hfalse (index + 1) (by omega)
      have hindexEq : (off + 1) + index = off + (index + 1) := by omega
      rw [hindexEq]
      exact hnext

theorem walshParity_single
    {off bit count selected mask i : Nat}
    (hselected : selected < count)
    (hone : ∀ index, index < count →
      i.testBit (off + index) = decide (selected = index)) :
    walshParity off bit count mask i = mask.testBit (bit + selected) := by
  induction count generalizing off bit selected with
  | zero => omega
  | succ count ih =>
      cases selected with
      | zero =>
          have hhead := hone 0 (by omega)
          simp only [Nat.add_zero] at hhead
          rw [walshParity, hhead]
          simp only [decide_true, Bool.true_and]
          rw [walshParity_of_all_false]
          · simp
          · intro index hindex
            have hnext := hone (index + 1) (by omega)
            have hindexEq : (off + 1) + index = off + (index + 1) := by omega
            rw [hindexEq]
            have hdecide : decide ((0 : Nat) = index + 1) = false := by simp
            exact hnext.trans hdecide
      | succ selected =>
          have hhead := hone 0 (by omega)
          simp only [Nat.add_zero] at hhead
          rw [walshParity, hhead]
          simp only [Nat.succ_ne_zero, decide_false, Bool.false_and,
            Bool.false_xor]
          have htail := ih (off := off + 1) (bit := bit + 1)
            (selected := selected) (by omega) (by
              intro index hindex
              have hnext := hone (index + 1) (by omega)
              have hindexEq : (off + 1) + index =
                  off + (index + 1) := by omega
              rw [hindexEq]
              by_cases heq : selected = index
              · subst index
                simpa using hnext
              · have hneq : selected + 1 ≠ index + 1 := by omega
                simpa [heq, hneq] using hnext)
          have hindexEq : (bit + 1) + selected =
              bit + (selected + 1) := by omega
          rw [hindexEq] at htail
          exact htail

theorem unaryReady_walshParity
    {addressWidth lowWidth mask i : Nat}
    (hready : unaryReady addressWidth lowWidth i) :
    walshParity (outputWire addressWidth 0) 0 (batchSize lowWidth) mask i =
      mask.testBit (readField i 0 lowWidth) := by
  have hselected : readField i 0 lowWidth < batchSize lowWidth := by
    simpa [batchSize] using readField_lt i 0 lowWidth
  have hone : ∀ index, index < batchSize lowWidth →
      i.testBit (outputWire addressWidth 0 + index) =
        decide (readField i 0 lowWidth = index) := by
    intro index hindex
    simpa [outputWire] using
      (unaryReady_testBit (addressWidth := addressWidth)
        (lowWidth := lowWidth) (index := index) hindex hready)
  have h := walshParity_single
    (off := outputWire addressWidth 0) (bit := 0)
    (count := batchSize lowWidth) (selected := readField i 0 lowWidth)
    (mask := mask) (i := i) hselected hone
  simpa using h

theorem unaryReady_correctionWalshParity
    {table : List Nat}
    {addressWidth outputWidth lowWidth row creg i : Nat}
    (hready : unaryReady addressWidth lowWidth i) :
    walshParity (outputWire addressWidth 0) 0 (batchSize lowWidth)
        (correctionMask table outputWidth lowWidth row creg) i =
      correctionWordParity table outputWidth lowWidth row
        (readField i 0 lowWidth) creg := by
  rw [unaryReady_walshParity hready, correctionMask_testBit]
  simpa [batchSize] using readField_lt i 0 lowWidth

theorem measurementMask_eq_wordMaskParity
    {addressWidth input word bit count creg : Nat}
    (hbits : ∀ index, index < count →
      input.testBit (outputWire addressWidth (bit + index)) =
        word.testBit (bit + index)) :
    measurementMask addressWidth input bit count creg =
      wordMaskParity word bit count creg := by
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      have hhead := hbits 0 (by omega)
      simp only [Nat.add_zero] at hhead
      rw [measurementMask, wordMaskParity, hhead]
      rw [ih]
      intro index hindex
      have hnext := hbits (index + 1) (by omega)
      have hindexEq : (bit + 1) + index = bit + (index + 1) := by omega
      rw [hindexEq]
      exact hnext

theorem batchAddress_eq (i lowWidth high : Nat) :
    readField i lowWidth high * batchSize lowWidth +
        readField i 0 lowWidth =
      readField i 0 (lowWidth + high) := by
  rw [readField_append]
  simp [batchSize, Nat.mul_comm, Nat.add_comm]

theorem measurementMask_eq_lookupWordParity
    {table : List Nat}
    {addressWidth outputWidth input creg : Nat}
    (hready : MeasuredUncompute.rangeReady table addressWidth outputWidth
      addressWidth 0 outputWidth input) :
    measurementMask addressWidth input 0 outputWidth creg =
      wordMaskParity
        (Lookup.value table outputWidth (readField input 0 addressWidth))
        0 outputWidth creg := by
  apply measurementMask_eq_wordMaskParity
  intro index hindex
  have hbit := hready.2 index (by omega) (by omega)
  simpa [outputWire, MeasuredUncompute.outputWire, Lookup.address,
    Lookup.layout, Layout.read, Layout.offset, Layout.size] using hbit

theorem correctionWalshParity_eq_measurementMask
    {table : List Nat}
    {addressWidth outputWidth lowWidth high input unaryState creg : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hloaded : MeasuredUncompute.rangeReady table addressWidth outputWidth
      addressWidth 0 outputWidth input)
    (hunary : unaryReady addressWidth lowWidth unaryState)
    (hlow : readField unaryState 0 lowWidth =
      readField input 0 lowWidth)
    (hhigh : readField unaryState lowWidth high =
      readField input lowWidth high) :
    walshParity (outputWire addressWidth 0) 0 (batchSize lowWidth)
        (correctionMask table outputWidth lowWidth
          (readField unaryState lowWidth high) creg) unaryState =
      measurementMask addressWidth input 0 outputWidth creg := by
  rw [unaryReady_correctionWalshParity hunary,
    measurementMask_eq_lookupWordParity hloaded]
  unfold correctionWordParity
  rw [hlow, hhigh, batchAddress_eq, hsplit]

theorem phaseScalar_mul_self (d : Nat) (phase : Bool) :
    MeasuredUncompute.phaseScalar d phase *
        MeasuredUncompute.phaseScalar d phase = Dy.one d := by
  cases phase <;>
    simp [MeasuredUncompute.phaseScalar, Dy.mul_one, Dy.mul_neg, Dy.neg_neg]

theorem measurementCorrectionPhase_cancel
    {d : Nat} {table : List Nat}
    {addressWidth outputWidth lowWidth high input unaryState creg : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hloaded : MeasuredUncompute.rangeReady table addressWidth outputWidth
      addressWidth 0 outputWidth input)
    (hunary : unaryReady addressWidth lowWidth unaryState)
    (hlow : readField unaryState 0 lowWidth =
      readField input 0 lowWidth)
    (hhigh : readField unaryState lowWidth high =
      readField input lowWidth high) :
    MeasuredUncompute.phaseScalar d
        (measurementMask addressWidth input 0 outputWidth creg) *
      MeasuredUncompute.phaseScalar d
        (walshParity (outputWire addressWidth 0) 0 (batchSize lowWidth)
          (correctionMask table outputWidth lowWidth
            (readField unaryState lowWidth high) creg) unaryState) =
      Dy.one d := by
  rw [correctionWalshParity_eq_measurementMask hsplit hloaded hunary hlow hhigh]
  exact phaseScalar_mul_self d _

theorem unaryReady_pair
    {addressWidth stage low i : Nat} (hlow : low < 2 ^ stage)
    (hready : unaryReady addressWidth (stage + 1) i) :
    clearPairReady addressWidth stage low i ∧
      Bool.xor (i.testBit (outputWire addressWidth low))
        (i.testBit (outputWire addressWidth (low + 2 ^ stage))) =
          decide (readField i 0 stage = low) := by
  have hlower := unaryReady_testBit
    (addressWidth := addressWidth) (lowWidth := stage + 1)
    (index := low) (by
      simp [batchSize, Nat.pow_succ]
      omega) hready
  have hupper := unaryReady_testBit
    (addressWidth := addressWidth) (lowWidth := stage + 1)
    (index := low + 2 ^ stage) (by
      simp [batchSize, Nat.pow_succ]
      omega) hready
  have hsplit := readField_high i 0 stage
  simp only [Nat.zero_add] at hsplit
  cases hbit : i.testBit stage with
  | false =>
      have hvalue : bitValue i stage = 0 := by simp [bitValue, hbit]
      rw [hvalue, Nat.mul_zero, Nat.add_zero] at hsplit
      have hupperNe : readField i 0 stage ≠ low + 2 ^ stage := by
        have hlt := readField_lt i 0 stage
        omega
      constructor
      · simp [clearPairReady, hlower, hupper, hbit, hsplit, hupperNe]
      · simp [hlower, hupper, hsplit, hupperNe]
  | true =>
      have hvalue : bitValue i stage = 1 := by simp [bitValue, hbit]
      rw [hvalue, Nat.mul_one] at hsplit
      have hlowerNe : readField i 0 stage + 2 ^ stage ≠ low := by
        have hlt := readField_lt i 0 stage
        omega
      constructor
      · simp [clearPairReady, hlower, hupper, hbit, hsplit, hlowerNe]
      · simp [hlower, hupper, hsplit, hlowerNe]

theorem unaryReady_clearStageReady
    {addressWidth stage i : Nat}
    (hready : unaryReady addressWidth (stage + 1) i) :
    clearStageReady addressWidth stage 0 (2 ^ stage) i := by
  intro offset hoffset
  simpa using (unaryReady_pair (addressWidth := addressWidth)
    (stage := stage) (low := offset) hoffset hready).1

theorem clearStageOut_unaryReady
    {addressWidth stage i : Nat} (hstage : stage < addressWidth)
    (hready : unaryReady addressWidth (stage + 1) i) :
    unaryReady addressWidth stage
      (clearStageOut addressWidth stage 0 (2 ^ stage) i) := by
  unfold unaryReady unaryValue batchSize
  rw [clearStageOut_readField_address (show stage ≤ addressWidth by omega)]
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [testBit_readField, Nat.testBit_two_pow]
  by_cases hbit : bit < 2 ^ stage
  · simp only [hbit, decide_true, Bool.true_and]
    rw [show outputWire addressWidth 0 + bit =
      outputWire addressWidth (0 + bit) by simp [outputWire]]
    rw [clearStageOut_testBit_lower (addressWidth := addressWidth)
      (stage := stage) (low := 0) (count := 2 ^ stage) (i := i)
      (offset := bit) (by omega) hbit]
    simpa using (unaryReady_pair (addressWidth := addressWidth)
      (stage := stage) (low := bit) hbit hready).2
  · have hne : readField i 0 stage ≠ bit := by
      have hlt := readField_lt i 0 stage
      omega
    simp [hbit, hne]

theorem clearStageOut_then_clear
    {addressWidth stage i : Nat} :
    writeField (clearStageOut addressWidth stage 0 (2 ^ stage) i)
        (outputWire addressWidth 0) (2 ^ stage) 0 =
      writeField i (outputWire addressWidth 0) (2 ^ (stage + 1)) 0 := by
  let off := outputWire addressWidth 0
  let k := 2 ^ stage
  have hwide : 2 ^ (stage + 1) = k + k := by
    simp [k, Nat.pow_succ, Nat.mul_two]
  rw [hwide]
  apply Nat.eq_of_testBit_eq
  intro bit
  change (writeField (clearStageOut addressWidth stage 0 k i) off k 0).testBit bit =
    (writeField i off (k + k) 0).testBit bit
  by_cases hbelow : bit < off
  · rw [testBit_writeField_outside (Or.inl hbelow),
      testBit_writeField_outside (Or.inl hbelow)]
    apply clearStageOut_testBit_of_ne
    intro offset hoffset
    constructor <;> simp [off, outputWire] at hbelow ⊢ <;> omega
  · by_cases hlower : bit < off + k
    · rw [testBit_writeField_inside (by omega) hlower,
        testBit_writeField_inside (by omega) (by omega)]
    · by_cases hupper : bit < off + k + k
      · have hupper' : bit < off + (k + k) := by omega
        rw [testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_inside (i := i) (off := off) (n := k + k)
            (v := 0) (by omega) hupper']
        have hoffset : bit - (off + k) < k := by omega
        have hclear := clearStageOut_testBit_upper
          (addressWidth := addressWidth) (stage := stage) (low := 0)
          (count := k) (i := i) (offset := bit - (off + k))
          (by simp [k]) hoffset
        have hwire : outputWire addressWidth
            (0 + (bit - (off + k)) + 2 ^ stage) = bit := by
          have hlower' : off + k ≤ bit := by omega
          dsimp [off, k, outputWire] at hlower' ⊢
          omega
        rw [hwire] at hclear
        simpa only [Nat.zero_testBit] using hclear
      · rw [testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_outside (Or.inr (by omega))]
        apply clearStageOut_testBit_of_ne
        intro offset hoffset
        constructor <;> simp [off, k, outputWire] at hupper ⊢ <;> omega

theorem clearUnaryOps_implements
    {level input addressWidth outputWidth lowWidth : Nat}
    (hl : 3 ≤ level) (haddress : lowWidth ≤ addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    ImplementsU level (width addressWidth outputWidth) input
      (unaryReady addressWidth lowWidth)
      (clearUnaryOut addressWidth lowWidth)
      (Dy.invSqrt2 (deg level))
      (clearUnaryOps addressWidth outputWidth lowWidth) := by
  induction lowWidth with
  | zero =>
      have hq : outputWire addressWidth 0 < width addressWidth outputWidth := by
        simp [batchSize] at hfit
        simp [outputWire, width]
        omega
      have hx := MeasuredUncompute.x_implementsU (input := input) hq
        (Dy.invSqrt2 (deg level))
      have hout : (fun i => i ^^^ (1 <<< outputWire addressWidth 0)) =
          clearUnaryOut addressWidth 0 := by
        funext i
        rfl
      rw [hout] at hx
      simpa [clearUnaryOps] using hx.mono
        (dom' := unaryReady addressWidth 0) (fun _ _ => trivial)
  | succ lowWidth ih =>
      have hstage : lowWidth < addressWidth := by omega
      have hprevFit : batchSize lowWidth ≤ outputWidth := by
        simp [batchSize, Nat.pow_succ] at hfit
        simp [batchSize]
        omega
      have hstageAll := clearStageOps_implements
        (input := input) hl hstage (low := 0) (count := 2 ^ lowWidth)
        (by omega) (by simpa [batchSize] using hfit)
      have hstageReady := hstageAll.mono
        (dom' := unaryReady addressWidth (lowWidth + 1))
        (fun _ hready => unaryReady_clearStageReady hready)
      have htail := ih (by omega) hprevFit
      have hall := hstageReady.append htail
        (fun i hi _ => clearStageOut_lt (by omega)
          (by simpa [batchSize] using hfit) hi)
        (fun _ _ hready => clearStageOut_unaryReady hstage hready)
      simpa [clearUnaryOps, clearUnaryOut, Function.comp_def] using hall

theorem clearUnaryOps_implementsRetainedU
    {level input addressWidth outputWidth lowWidth : Nat}
    (hl : 3 ≤ level) (haddress : lowWidth ≤ addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    ImplementsRetainedU level (width addressWidth outputWidth) input outputWidth
      (unaryReady addressWidth lowWidth)
      (fun _ i ↦ clearUnaryOut addressWidth lowWidth i)
      (Dy.invSqrt2 (deg level))
      (clearUnaryOps addressWidth outputWidth lowWidth) := by
  induction lowWidth with
  | zero =>
      have hq : outputWire addressWidth 0 <
          width addressWidth outputWidth := by
        simp [batchSize] at hfit
        simp [outputWire, width]
        omega
      have hwf : (RCircuit.mk (width addressWidth outputWidth)
          [.x (outputWire addressWidth 0)]).wellFormed = true := by
        simp [RCircuit.wellFormed, RGate.wellFormed, hq]
      have hx := gateOps_implementsRetainedU
        (input := input) (retained := outputWidth) hl hwf
        (Dy.invSqrt2 (deg level))
      have hout : (fun (_ : Nat) i ↦
          actGates [.x (outputWire addressWidth 0)] i) =
          (fun (_ : Nat) i ↦ clearUnaryOut addressWidth 0 i) := by
        funext _ i
        rfl
      rw [hout] at hx
      simpa [clearUnaryOps, gateOps, Unary.gateOps, compileGate] using
        hx.mono (dom' := unaryReady addressWidth 0) (fun _ _ ↦ trivial)
  | succ lowWidth ih =>
      have hstage : lowWidth < addressWidth := by omega
      have hprevFit : batchSize lowWidth ≤ outputWidth := by
        simp [batchSize, Nat.pow_succ] at hfit
        simp [batchSize]
        omega
      have hstageAll := clearStageOps_implementsRetainedU
        (input := input) hl hstage (low := 0) (count := 2 ^ lowWidth)
        (by omega) (by simpa [batchSize] using hfit)
      have hstageReady := hstageAll.mono
        (dom' := unaryReady addressWidth (lowWidth + 1))
        (fun _ hready ↦ unaryReady_clearStageReady hready)
      have htail := ih (by omega) hprevFit
      have hall := hstageReady.append htail
        (fun _ i hi _ ↦ clearStageOut_lt (by omega)
          (by simpa [batchSize] using hfit) hi)
        (fun _ _ _ hready ↦ clearStageOut_unaryReady hstage hready)
      simpa [clearUnaryOps, clearUnaryOut, Function.comp_def] using hall

theorem clearUnaryOut_eq_clear
    {addressWidth lowWidth i : Nat} (haddress : lowWidth ≤ addressWidth)
    (hready : unaryReady addressWidth lowWidth i) :
    clearUnaryOut addressWidth lowWidth i =
      writeField i (outputWire addressWidth 0) (batchSize lowWidth) 0 := by
  induction lowWidth generalizing i with
  | zero =>
      have hset := unaryReady_testBit
        (addressWidth := addressWidth) (lowWidth := 0) (index := 0)
        (by simp [batchSize]) hready
      rw [clearUnaryOut]
      change i ^^^ (1 <<< outputWire addressWidth 0) = _
      rw [MeasuredUncompute.xor_two_pow_eq_clear (by
            simpa [readField, Nat.mod_one] using hset),
        Unary.writeBit_false_eq_writeField]
      simp [batchSize]
  | succ lowWidth ih =>
      rw [clearUnaryOut]
      rw [ih (by omega) (clearStageOut_unaryReady (by omega) hready)]
      simpa [batchSize] using
        (clearStageOut_then_clear
          (addressWidth := addressWidth) (stage := lowWidth) (i := i))

theorem clearUnaryOut_prepareUnaryOut
    {addressWidth lowWidth i : Nat}
    (haddress : lowWidth ≤ addressWidth)
    (hclear : unaryClear addressWidth lowWidth i) :
    clearUnaryOut addressWidth lowWidth
        (prepareUnaryOut addressWidth lowWidth i) = i := by
  rw [clearUnaryOut_eq_clear haddress
      (prepareUnaryOut_ready haddress hclear),
    prepareUnaryOut_eq_write haddress hclear, writeField_writeField]
  have hzero : writeField i (outputWire addressWidth 0)
      (batchSize lowWidth) 0 = i := by
    calc
      writeField i (outputWire addressWidth 0) (batchSize lowWidth) 0 =
          writeField i (outputWire addressWidth 0) (batchSize lowWidth)
            (readField i (outputWire addressWidth 0) (batchSize lowWidth)) :=
        congrArg
          (fun v ↦ writeField i (outputWire addressWidth 0)
            (batchSize lowWidth) v) hclear.symm
      _ = i := writeField_read i (outputWire addressWidth 0)
        (batchSize lowWidth)
  exact hzero

/-!
The paper supplies no circuit-level interface between output measurement,
unary preparation, Walsh-basis correction, and unary cleanup.  It also omits
the retained-measurement-register invariant needed to use one measurement mask
after selector cleanup.  `prepareWalshClear_implementsRetainedPhaseU` supplies
that composition and leaves scratch cbit `outputWidth` unconstrained.
-/

theorem prepareWalshClear_implementsRetainedPhaseU
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    ImplementsRetainedPhaseU level (width addressWidth outputWidth)
      input outputWidth
      (fun i ↦ unaryClear addressWidth lowWidth i ∧
        correctionPre addressWidth outputWidth high i)
      (fun _ i ↦ i)
      (fun cr i ↦
        let unaryState := prepareUnaryOut addressWidth lowWidth i
        walshParity (outputWire addressWidth 0) 0 (batchSize lowWidth)
          (correctionMask table outputWidth lowWidth
            (readField unaryState lowWidth high) cr) unaryState)
      (Dy.invSqrt2 (deg level))
      (prepareUnaryOps addressWidth lowWidth ++
        unaryHadamardOps addressWidth 0 (batchSize lowWidth) ++
        correctionOps table addressWidth outputWidth lowWidth high ++
        unaryHadamardOps addressWidth 0 (batchSize lowWidth) ++
        clearUnaryOps addressWidth outputWidth lowWidth) := by
  have haddress : lowWidth ≤ addressWidth := by omega
  have hprepAll := prepareUnaryOps_implementsRetainedU
    (input := input) hl haddress hfit
  have hprep := hprepAll.mono
    (dom' := fun i ↦ unaryClear addressWidth lowWidth i ∧
      correctionPre addressWidth outputWidth high i)
    (fun _ _ ↦ trivial)
  have hwalsh := walshSandwich_implementsRetainedPhaseU
    (input := input) hl table hsplit hfit
  have hprepared := hprep.appendPhase hwalsh
    (fun _ i hi _ ↦ prepareUnaryOut_lt haddress hfit hi)
    (fun _ i hi hdom ↦ walshDecomposition_generated hl hsplit hfit
      (prepareUnaryOut_lt haddress hfit hi)
      (prepareUnaryOut_correctionPre haddress hfit hdom.1 hdom.2))
  have hclear := clearUnaryOps_implementsRetainedU
    (input := input) hl haddress hfit
  have hall := hprepared.append hclear
    (fun _ i hi _ ↦ prepareUnaryOut_lt haddress hfit hi)
    (fun _ _ _ hdom ↦ prepareUnaryOut_ready haddress hdom.1)
  intro i hi hdom rec cr b hb
  have hspec := hall i hi hdom rec cr b (by
    simpa [List.append_assoc] using hb)
  simpa [Function.comp_def,
    clearUnaryOut_prepareUnaryOut haddress hdom.1] using hspec

/-!
Schrottenloher's Algorithm 1 treats QROM unlookup as a named operation and
does not state the measurement-conditioned branch semantics proved here.  The
theorem composes VQ's output measurement, unary reuse, Walsh correction, and
cleanup circuits on a loaded basis state.  It identifies the retained
measurement register at the suffix boundary, while making no claim about
scratch cbit `outputWidth`, whole-program probability, or the 3460-wire
specialization.
-/

theorem unlookupOps_basis
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high i : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth)
    (hi : i < 2 ^ width addressWidth outputWidth)
    (hloaded : MeasuredUncompute.rangeReady table addressWidth outputWidth
      addressWidth 0 outputWidth i)
    (rec : List Bool) (cr : Nat) :
    ∀ b ∈ runOps level (width addressWidth outputWidth)
      (unlookupOps table addressWidth outputWidth lowWidth)
      (Branch.mk rec cr (basis i) input),
      ∃ measured,
        measured ∈ runOps level (width addressWidth outputWidth)
          (measureOutputOps addressWidth 0 outputWidth)
          (Branch.mk rec cr (basis i) input) ∧
        retainedCreg outputWidth b.creg =
          retainedCreg outputWidth measured.creg ∧
        b.state = (Dy.invSqrt2 (deg level)) ^
            (b.outcomes.length - rec.length) •
          (basis (MeasuredUncompute.clearBits addressWidth 0 outputWidth i) :
            Vec (deg level)) := by
  intro b hb
  let c := Dy.invSqrt2 (deg level)
  let cleared := MeasuredUncompute.clearBits addressWidth 0 outputWidth i
  let unaryState := prepareUnaryOut addressWidth lowWidth cleared
  let tailOps :=
    prepareUnaryOps addressWidth lowWidth ++
      unaryHadamardOps addressWidth 0 (batchSize lowWidth) ++
      correctionOps table addressWidth outputWidth lowWidth high ++
      unaryHadamardOps addressWidth 0 (batchSize lowWidth) ++
      clearUnaryOps addressWidth outputWidth lowWidth
  have hhighWidth : highWidth addressWidth lowWidth = high := by
    simp [highWidth]
    omega
  have hb' : b ∈ runOps level (width addressWidth outputWidth)
      (measureOutputOps addressWidth 0 outputWidth ++ tailOps)
      (Branch.mk rec cr (basis i) input) := by
    simpa [unlookupOps, tailOps, hhighWidth, List.append_assoc] using hb
  rw [runOps_append, List.mem_flatMap] at hb'
  obtain ⟨x, hx, hxb⟩ := hb'
  have hmeasure := measureOutputOps_mask (i := i) hl
    (show addressWidth + 0 + outputWidth ≤
      width addressWidth outputWidth by simp [width]; omega)
    rec cr input x hx
  have hmeasureLength := measureOutputOps_outcomes_length hx
  have hclearedRange : cleared < 2 ^ width addressWidth outputWidth := by
    have hwidth : (Lookup.layout addressWidth outputWidth addressWidth).width =
        width addressWidth outputWidth := by
      simp [Lookup.layout, Layout.width, width]
      omega
    have hiLayout : i <
        2 ^ (Lookup.layout addressWidth outputWidth addressWidth).width := by
      rw [hwidth]
      exact hi
    have hclear := MeasuredUncompute.clearBits_lt
      (addressWidth := addressWidth) (outputWidth := outputWidth)
      (workspaceWidth := addressWidth) hiLayout
    rw [hwidth] at hclear
    exact hclear
  have hclearedUnary : unaryClear addressWidth lowWidth cleared := by
    exact clearBits_unaryClear hfit
  have hclearedPre : correctionPre addressWidth outputWidth high cleared := by
    exact clearBits_correctionPre (by omega) hloaded.1
  have hunary : unaryReady addressWidth lowWidth unaryState := by
    exact prepareUnaryOut_ready (by omega) hclearedUnary
  have hlow : readField unaryState 0 lowWidth = readField i 0 lowWidth := by
    calc
      readField unaryState 0 lowWidth = readField cleared 0 lowWidth :=
        prepareUnaryOut_readField_before (by omega) hclearedUnary (by omega)
      _ = readField i 0 lowWidth := clearBits_readField_before (by omega)
  have hhigh : readField unaryState lowWidth high =
      readField i lowWidth high := by
    calc
      readField unaryState lowWidth high =
          readField cleared lowWidth high :=
        prepareUnaryOut_readField_before (by omega) hclearedUnary (by omega)
      _ = readField i lowWidth high := clearBits_readField_before (by omega)
  let measurementPhase := MeasuredUncompute.phaseScalar (deg level)
    (measurementMask addressWidth i 0 outputWidth x.creg)
  let correctionPhase := MeasuredUncompute.phaseScalar (deg level)
    (walshParity (outputWire addressWidth 0) 0 (batchSize lowWidth)
      (correctionMask table outputWidth lowWidth
        (readField unaryState lowWidth high)
        (retainedCreg outputWidth x.creg)) unaryState)
  have hphase : measurementPhase * correctionPhase = Dy.one (deg level) := by
    have hcancel := measurementCorrectionPhase_cancel
      (d := deg level) (table := table) (addressWidth := addressWidth)
      (outputWidth := outputWidth) (lowWidth := lowWidth) (high := high)
      (input := i) (unaryState := unaryState)
      (creg := retainedCreg outputWidth x.creg)
      hsplit hloaded hunary hlow hhigh
    rw [measurementMask_retainedCreg (by omega)] at hcancel
    exact hcancel
  let base := Branch.mk x.outcomes x.creg
    (basis cleared : Vec (deg level)) input
  have hxinput : x.input = input :=
    input_runOps level (width addressWidth outputWidth)
      (measureOutputOps addressWidth 0 outputWidth) hx
  have hxe : x = smulBranch (c ^ outputWidth)
      (smulBranch measurementPhase base) := by
    cases x with
    | mk outcomes creg state branchInput =>
        simp only [smulBranch, base] at hxinput ⊢
        subst branchInput
        rw [← hmeasure]
  rw [hxe, (runOps_smul level (width addressWidth outputWidth)).2
      tailOps _ _, List.mem_map] at hxb
  obtain ⟨z, hz, hzb⟩ := hxb
  change z ∈ runOps level (width addressWidth outputWidth) tailOps
    (smulBranch measurementPhase base) at hz
  rw [(runOps_smul level (width addressWidth outputWidth)).2
      tailOps measurementPhase base, List.mem_map] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  have hsuffix := prepareWalshClear_implementsRetainedPhaseU
    (input := input) hl table hsplit hfit
  have hyspec := hsuffix cleared hclearedRange
    ⟨hclearedUnary, hclearedPre⟩ x.outcomes x.creg y (by
      simpa [tailOps, List.append_assoc] using hy)
  have hbOutcomes : b.outcomes = y.outcomes := by
    rw [← hzb, ← hyz]
    rfl
  have hbCreg : b.creg = y.creg := by
    rw [← hzb, ← hyz]
    rfl
  have hbState : b.state =
      (c ^ outputWidth) • (measurementPhase • y.state) := by
    rw [← hzb, ← hyz]
    rfl
  have htailLength : x.outcomes.length ≤ y.outcomes.length :=
    runOps_record_le level (width addressWidth outputWidth) tailOps
      x.outcomes x.creg input _ hy
  have hlength : outputWidth +
      (y.outcomes.length - x.outcomes.length) =
      b.outcomes.length - rec.length := by
    rw [hbOutcomes, hmeasureLength]
    omega
  refine ⟨x, hx, ?_, ?_⟩
  · rw [hbCreg]
    exact hyspec.1
  · rw [hbState, hyspec.2]
    apply Vec.ext
    intro k
    simp only [Vec.smul_apply]
    calc
      c ^ outputWidth *
          (measurementPhase *
            (c ^ (y.outcomes.length - x.outcomes.length) *
              (correctionPhase * (basis cleared : Vec (deg level)) k))) =
          (c ^ outputWidth *
            c ^ (y.outcomes.length - x.outcomes.length)) *
            ((measurementPhase * correctionPhase) *
              (basis cleared : Vec (deg level)) k) := by
        rw [← Dy.mul_assoc (c ^ outputWidth) measurementPhase,
          mul_four_reorder,
          Dy.mul_comm (c ^ (y.outcomes.length - x.outcomes.length)),
          ← Dy.mul_assoc measurementPhase correctionPhase]
      _ = (c ^ outputWidth *
            c ^ (y.outcomes.length - x.outcomes.length)) *
          (basis cleared : Vec (deg level)) k := by
        rw [hphase, Dy.one_mul]
      _ = c ^ (outputWidth +
            (y.outcomes.length - x.outcomes.length)) *
          (basis cleared : Vec (deg level)) k := by
        rw [Dy.pow_add]
      _ = c ^ (b.outcomes.length - rec.length) *
          (basis cleared : Vec (deg level)) k := by rw [hlength]

theorem unlookupOps_implementsU
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    ImplementsU level (width addressWidth outputWidth) input
      (MeasuredUncompute.rangeReady table addressWidth outputWidth
        addressWidth 0 outputWidth)
      (MeasuredUncompute.clearBits addressWidth 0 outputWidth)
      (Dy.invSqrt2 (deg level))
      (unlookupOps table addressWidth outputWidth lowWidth) := by
  intro i hi hloaded rec cr b hb
  obtain ⟨_, _, _, hstate⟩ :=
    unlookupOps_basis (input := input) hl table hsplit hfit
      hi hloaded rec cr b hb
  exact hstate

theorem program_realisesAt
    {level : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hlow : 0 < lowWidth) (hdeep : lowWidth + 2 ≤ addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    RealisesAt level 0 (spec table addressWidth outputWidth)
      (program table addressWidth outputWidth lowWidth) := by
  have hwf := program_wellFormed hl table addressWidth outputWidth lowWidth
    hlow hdeep (by simpa [batchSize] using hfit)
  refine realisesAt_of_implementsU rfl hwf (Nat.two_pow_pos 0)
    (out := MeasuredUncompute.clearBits addressWidth 0 outputWidth)
    (c := Dy.invSqrt2 (deg level)) ?_ ?_ ?_
  · simpa [program, spec] using
      (unlookupOps_implementsU (input := 0) hl table hsplit hfit)
  · intro i hi _
    refine ⟨rfl, ?_⟩
    have hwidth :
        (Lookup.layout addressWidth outputWidth addressWidth).width =
          width addressWidth outputWidth := by
      simp [Lookup.layout, Layout.width, width]
      omega
    change MeasuredUncompute.clearBits addressWidth 0 outputWidth i <
      2 ^ width addressWidth outputWidth
    rw [← hwidth]
    apply MeasuredUncompute.clearBits_lt (workspaceWidth := addressWidth)
    rw [hwidth]
    change i < 2 ^ width addressWidth outputWidth at hi
    exact hi
  · intro i hi _
    exact totalProb_basis level
      (program table addressWidth outputWidth lowWidth) hwf 0
      (by simpa [program, spec] using hi)

/-!
Schrottenloher does not define a batching parameter, identify `K = 256` with
an eight-bit low-address split, or give a wire map for batched unlookup in the
3,460-wire circuit.  `programK256_realisesAt_3460` treats those choices as VQ
contribution data and requires an injective map into the ambient register.
Relabelling preserves the checked Program semantics, while scratch cbit
`outputWidth` remains unconstrained.
-/

theorem programK256_realisesAt_3460
    {level : Nat} (hl : 3 ≤ level) (table : List Nat)
    {outputWidth : Nat} (houtput : 256 ≤ outputWidth)
    (f : Nat → Nat)
    (hlt : ∀ q, q < (spec table 16 outputWidth).width → f q < 3460)
    (hinj : ∀ x y, x < (spec table 16 outputWidth).width →
      y < (spec table 16 outputWidth).width → f x = f y → x = y) :
    RealisesAt level 0 ((spec table 16 outputWidth).place f 3460)
      (Program.relabel f 3460 (program table 16 outputWidth 8)) := by
  have hlocal : RealisesAt level 0 (spec table 16 outputWidth)
      (program table 16 outputWidth 8) :=
    program_realisesAt (addressWidth := 16) (outputWidth := outputWidth)
      (lowWidth := 8) (high := 8) hl table (by omega) (by omega) (by omega)
      (by simpa [batchSize] using houtput)
  exact hlocal.relabel hlt hinj

/-!
The round-trip theorem composes VQ's rootless lookup with the batched measured
unlookup under an explicit clear-output and clear-selector precondition.  The
paper does not supply this composition theorem or its register placement
obligations.  The result constrains the quantum output and branch amplitude,
while leaving scratch cbit `outputWidth` unconstrained.
-/

theorem roundTripOps_implementsU
    {level input : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    ImplementsU level (width addressWidth outputWidth) input
      (fun i ↦ Lookup.workspace addressWidth outputWidth addressWidth i = 0 ∧
        Lookup.output addressWidth outputWidth addressWidth i = 0)
      id (Dy.invSqrt2 (deg level))
      (roundTripOps table addressWidth outputWidth lowWidth) := by
  have hlookup : ImplementsU level (width addressWidth outputWidth) input
      (fun i ↦ Lookup.workspace addressWidth outputWidth addressWidth i = 0)
      (Lookup.xorOutput table addressWidth outputWidth addressWidth)
      (Dy.invSqrt2 (deg level))
      (Unary.Rootless.lookupOps table addressWidth outputWidth) := by
    simpa [Unary.Rootless.width_eq, Unary.Rootless.selectorWidth, width] using
      (Unary.Rootless.lookup_implements (input := input) hl table
        addressWidth outputWidth)
  have hfirst := hlookup.mono
    (dom' := fun i ↦
      Lookup.workspace addressWidth outputWidth addressWidth i = 0 ∧
        Lookup.output addressWidth outputWidth addressWidth i = 0)
    (fun _ h ↦ h.1)
  have hsecond := unlookupOps_implementsU (input := input) hl table hsplit hfit
  have hall := hfirst.append hsecond
    (fun i hi _ ↦ by
      have hiRootless :
          i < 2 ^ Unary.Rootless.width addressWidth outputWidth := by
        simpa [Unary.Rootless.width_eq, width] using hi
      have hout := Unary.Rootless.xorOutput_lt
        (table := table) hiRootless
      simpa [Unary.Rootless.width_eq, Unary.Rootless.selectorWidth, width] using
        hout)
    (fun _ _ h ↦ MeasuredUncompute.xorOutput_ready h.1 h.2)
  intro i hi hready rec cr b hb
  have hstate := hall i hi hready rec cr b (by
    simpa [roundTripOps] using hb)
  simp only [id_eq] at hstate ⊢
  rw [MeasuredUncompute.clearBits_xorOutput hready.2] at hstate
  exact hstate

theorem roundTripProgram_wellFormed
    {level : Nat} (hl : 3 ≤ level) (table : List Nat)
    (addressWidth outputWidth lowWidth : Nat)
    (hlow : 0 < lowWidth) (hdeep : lowWidth + 2 ≤ addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    (roundTripProgram table addressWidth outputWidth lowWidth).wellFormed level =
      true := by
  have hlookupProgram := Unary.Rootless.lookupProgram_wellFormed hl table
    addressWidth outputWidth
  have hlookupOps : Program.opsWellFormed level
      (Unary.Rootless.width addressWidth outputWidth) 0
      (if addressWidth ≤ 1 then 0 else 1)
      (Unary.Rootless.lookupOps table addressWidth outputWidth) = true := by
    simpa [Unary.Rootless.lookupProgram, Program.wellFormed] using hlookupProgram
  have hlookupWide : Program.opsWellFormed level
      (width addressWidth outputWidth) 0 (outputWidth + 1)
      (Unary.Rootless.lookupOps table addressWidth outputWidth) = true := by
    have hmono := MeasuredUncompute.opsWellFormed_cbits_mono
      (cbits' := outputWidth + 1) (by split <;> omega)
      (Unary.Rootless.lookupOps table addressWidth outputWidth) hlookupOps
    simpa [Unary.Rootless.width_eq, width] using hmono
  have hunlookupProgram := program_wellFormed hl table addressWidth outputWidth
    lowWidth hlow hdeep (by simpa [batchSize] using hfit)
  have hunlookupOps : Program.opsWellFormed level
      (width addressWidth outputWidth) 0 (outputWidth + 1)
      (unlookupOps table addressWidth outputWidth lowWidth) = true := by
    simpa [program, Program.wellFormed] using hunlookupProgram
  change Program.opsWellFormed level (width addressWidth outputWidth) 0
    (outputWidth + 1) (roundTripOps table addressWidth outputWidth lowWidth) = true
  rw [roundTripOps, Program.opsWellFormed_append, hlookupWide, hunlookupOps]
  rfl

theorem roundTripProgram_realisesAt
    {level : Nat} (hl : 3 ≤ level) (table : List Nat)
    {addressWidth outputWidth lowWidth high : Nat}
    (hsplit : lowWidth + high = addressWidth)
    (hlow : 0 < lowWidth) (hdeep : lowWidth + 2 ≤ addressWidth)
    (hfit : batchSize lowWidth ≤ outputWidth) :
    RealisesAt level 0 (roundTripSpec addressWidth outputWidth)
      (roundTripProgram table addressWidth outputWidth lowWidth) := by
  have hwf := roundTripProgram_wellFormed hl table addressWidth outputWidth
    lowWidth hlow hdeep hfit
  have hwidth : (roundTripProgram table addressWidth outputWidth lowWidth).width =
      (roundTripSpec addressWidth outputWidth).width := by
    simp [roundTripProgram, roundTripSpec, MeasuredUncompute.roundTripSpec,
      Lookup.layout, Layout.width, width]
    omega
  refine realisesAt_of_implementsU hwidth hwf (Nat.two_pow_pos 0)
    (out := id) (c := Dy.invSqrt2 (deg level)) ?_ ?_ ?_
  · simpa [roundTripProgram, roundTripSpec, MeasuredUncompute.roundTripSpec] using
      (roundTripOps_implementsU (input := 0) hl table hsplit hfit)
  · intro i hi _
    exact ⟨rfl, hi⟩
  · intro i hi _
    exact totalProb_basis level
      (roundTripProgram table addressWidth outputWidth lowWidth) hwf 0
      (by rw [hwidth]; exact hi)

def unaryTwoClear (addressWidth i : Nat) : Prop :=
  i.testBit (outputWire addressWidth 0) = false ∧
    i.testBit (outputWire addressWidth 1) = false

def unaryTwoReady (addressWidth i : Nat) : Prop :=
  i.testBit (outputWire addressWidth 0) = !i.testBit 0 ∧
    i.testBit (outputWire addressWidth 1) = i.testBit 0

def prepareUnaryOneOut (addressWidth i : Nat) : Nat :=
  actGates
    ([.x (outputWire addressWidth 0)] ++
      fredkin 0 (outputWire addressWidth 0) (outputWire addressWidth 1)) i

def clearUnaryOneOut (addressWidth i : Nat) : Nat :=
  let x := outputWire addressWidth 0
  let y := outputWire addressWidth 1
  RGate.act (.x x) (writeBit (RGate.act (.cx y x) i) y false)

theorem prepareUnaryOps_one_implements {level input addressWidth outputWidth : Nat}
    (hl : 3 ≤ level) (haddress : 2 ≤ addressWidth)
    (houtput : 2 ≤ outputWidth) :
    ImplementsU level (width addressWidth outputWidth) input (fun _ => True)
      (prepareUnaryOneOut addressWidth) (Dy.invSqrt2 (deg level))
      (prepareUnaryOps addressWidth 1) := by
  let gates : List RGate := [.x (outputWire addressWidth 0)] ++
    fredkin 0 (outputWire addressWidth 0) (outputWire addressWidth 1)
  have hxw : outputWire addressWidth 0 < width addressWidth outputWidth := by
    simp [width, outputWire]
    omega
  have hyw : outputWire addressWidth 1 < width addressWidth outputWidth := by
    simp [width, outputWire]
    omega
  have h0x : 0 ≠ outputWire addressWidth 0 := by
    simp [outputWire]
    omega
  have h0y : 0 ≠ outputWire addressWidth 1 := by simp [outputWire]
  have hxy : outputWire addressWidth 0 ≠ outputWire addressWidth 1 := by
    simp [outputWire]
  have hfredkin := fredkin_wellFormed
    (control := 0) (x := outputWire addressWidth 0)
    (y := outputWire addressWidth 1)
    (width := width addressWidth outputWidth)
    (by simp [width]; omega) hxw hyw h0x h0y hxy
  have hwf : ({ width := width addressWidth outputWidth, gates := gates } :
      RCircuit).wellFormed = true := by
    simp only [gates, RCircuit.wellFormed, List.all_append, Bool.and_eq_true]
    constructor
    · simpa [RGate.wellFormed] using hxw
    · exact hfredkin
  have h := gateOps_implementsU (input := input) (gates := gates) hl hwf
    (Dy.invSqrt2 (deg level))
  have hout : actGates gates = prepareUnaryOneOut addressWidth := by
    funext i
    rfl
  rw [hout] at h
  simpa [prepareUnaryOps, prepareStageOps, prepareUnaryOneOut,
    gateOps, Unary.gateOps, List.flatMap_append, compileGate, gates] using h

theorem prepareUnaryOneOut_ready {addressWidth i : Nat}
    (haddress : 2 ≤ addressWidth) (hclear : unaryTwoClear addressWidth i) :
    unaryTwoReady addressWidth (prepareUnaryOneOut addressWidth i) := by
  let x := outputWire addressWidth 0
  let y := outputWire addressWidth 1
  let j := RGate.act (.x x) i
  have hxy : x ≠ y := by simp [x, y, outputWire]
  have h0x : 0 ≠ x := by simp [x, outputWire]; omega
  have h0y : 0 ≠ y := by simp [y, outputWire]
  have hj0 : j.testBit 0 = i.testBit 0 := by
    simpa [j, RGate.act] using RGate.testBit_xor_of_ne h0x i
  have hjx : j.testBit x = true := by
    dsimp [j]
    rw [RGate.act, Semantics.testBit_xor_self, hclear.1]
    rfl
  have hjy : j.testBit y = false := by
    dsimp [j]
    rw [RGate.act, RGate.testBit_xor_of_ne (Ne.symm hxy), hclear.2]
  have hready :
      (actGates (fredkin 0 x y) j).testBit x = !i.testBit 0 ∧
        (actGates (fredkin 0 x y) j).testBit y = i.testBit 0 ∧
        (actGates (fredkin 0 x y) j).testBit 0 = i.testBit 0 := by
    cases h0 : i.testBit 0 with
    | false =>
        have hcontrol : bitValue j 0 = 0 := by simp [bitValue, hj0, h0]
        rw [fredkin_off hxy h0x hcontrol]
        exact ⟨by simpa [h0] using hjx,
          by simpa [h0] using hjy, by simpa [h0] using hj0⟩
    | true =>
        have hcontrol : bitValue j 0 = 1 := by simp [bitValue, hj0, h0]
        rw [fredkin_on hxy h0x h0y hcontrol]
        constructor
        · rw [testBit_writeField_outside (Or.inl (by
              simp [x, y, outputWire])),
            testBit_writeField_inside (by omega) (by omega)]
          simp [bitValue, hjy]
        · constructor
          · rw [testBit_writeField_inside (by omega) (by omega)]
            simp [bitValue, hjx]
          · rw [testBit_writeField_outside (Or.inl (by
                simp [y, outputWire])),
              testBit_writeField_outside (Or.inl (by
                simp [x, outputWire]
                omega))]
            simpa [h0] using hj0
  have hout0 := hready.2.2
  have hxyReady :
      (actGates (fredkin 0 x y) j).testBit x =
          !(actGates (fredkin 0 x y) j).testBit 0 ∧
        (actGates (fredkin 0 x y) j).testBit y =
          (actGates (fredkin 0 x y) j).testBit 0 := by
    rw [hout0]
    exact ⟨hready.1, hready.2.1⟩
  simpa [unaryTwoReady, prepareUnaryOneOut, actGates_append,
    actGates_cons, actGates_nil, x, y, j] using hxyReady

theorem afterUnaryCnot_and {addressWidth i : Nat}
    (haddress : 2 ≤ addressWidth) (hready : unaryTwoReady addressWidth i) :
    let x := outputWire addressWidth 0
    let y := outputWire addressWidth 1
    let j := RGate.act (.cx y x) i
    j.testBit y = (j.testBit 0 && j.testBit x) := by
  let x := outputWire addressWidth 0
  let y := outputWire addressWidth 1
  let j := RGate.act (.cx y x) i
  change j.testBit y = (j.testBit 0 && j.testBit x)
  have h0x : 0 ≠ x := by simp [x, outputWire]; omega
  have hyx : y ≠ x := by simp [x, y, outputWire]
  cases h0 : i.testBit 0 with
  | false =>
      have hx : i.testBit x = true := by simpa [x, unaryTwoReady, h0] using hready.1
      have hy : i.testBit y = false := by simpa [y, unaryTwoReady, h0] using hready.2
      simp [j, RGate.act, hx, hy, h0]
  | true =>
      have hx : i.testBit x = false := by simpa [x, unaryTwoReady, h0] using hready.1
      have hy : i.testBit y = true := by simpa [y, unaryTwoReady, h0] using hready.2
      have hjy : j.testBit y = true := by
        dsimp [j]
        rw [RGate.act, if_pos hy, RGate.testBit_xor_of_ne hyx, hy]
      have hj0 : j.testBit 0 = true := by
        dsimp [j]
        rw [RGate.act, if_pos hy, RGate.testBit_xor_of_ne h0x, h0]
      have hjx : j.testBit x = true := by
        dsimp [j]
        rw [RGate.act, if_pos hy, Semantics.testBit_xor_self, hx]
        rfl
      rw [hjy, hj0, hjx]
      rfl

theorem clearUnaryOneOut_eq_clear {addressWidth i : Nat}
    (hready : unaryTwoReady addressWidth i) :
    clearUnaryOneOut addressWidth i =
      writeBit (writeBit i (outputWire addressWidth 1) false)
        (outputWire addressWidth 0) false := by
  let x := outputWire addressWidth 0
  let y := outputWire addressWidth 1
  let j := RGate.act (.cx y x) i
  let k := writeBit j y false
  have hxy : x ≠ y := by simp [x, y, outputWire]
  have hkx : k.testBit x = true := by
    rw [testBit_writeBit_of_ne hxy]
    cases h0 : i.testBit 0 with
    | false =>
        have hx : i.testBit x = true := by
          simpa [x, unaryTwoReady, h0] using hready.1
        have hy : i.testBit y = false := by
          simpa [y, unaryTwoReady, h0] using hready.2
        simp [j, RGate.act, hx, hy]
    | true =>
        have hx : i.testBit x = false := by
          simpa [x, unaryTwoReady, h0] using hready.1
        have hy : i.testBit y = true := by
          simpa [y, unaryTwoReady, h0] using hready.2
        simp [j, RGate.act, hx, hy]
  change RGate.act (.x x) k = writeBit (writeBit i y false) x false
  change k ^^^ (1 <<< x) = _
  rw [MeasuredUncompute.xor_two_pow_eq_clear hkx]
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hrx : r = x
  · subst r
    rw [testBit_writeBit, testBit_writeBit]
  · by_cases hry : r = y
    · subst r
      rw [testBit_writeBit_of_ne (Ne.symm hxy), testBit_writeBit,
        testBit_writeBit_of_ne (Ne.symm hxy), testBit_writeBit]
    · rw [testBit_writeBit_of_ne hrx, testBit_writeBit_of_ne hry,
        testBit_writeBit_of_ne hrx, testBit_writeBit_of_ne hry]
      simp only [j, RGate.act]
      split
      · rw [RGate.testBit_xor_of_ne hrx]
      · rfl

theorem clearUnaryOps_one_implements {level input addressWidth outputWidth : Nat}
    (hl : 3 ≤ level) (haddress : 2 ≤ addressWidth)
    (houtput : 2 ≤ outputWidth) :
    ImplementsU level (width addressWidth outputWidth) input
      (unaryTwoReady addressWidth) (clearUnaryOneOut addressWidth)
      (Dy.invSqrt2 (deg level))
      (clearUnaryOps addressWidth outputWidth 1) := by
  let w := width addressWidth outputWidth
  let x := outputWire addressWidth 0
  let y := outputWire addressWidth 1
  have hxw : x < w := by simp [x, w, width, outputWire]; omega
  have hyw : y < w := by simp [y, w, width, outputWire]; omega
  have h0w : 0 < w := by simp [w, width]; omega
  have h0x : 0 ≠ x := by simp [x, outputWire]; omega
  have h0y : 0 ≠ y := by simp [y, outputWire]
  have hxy : x ≠ y := by simp [x, y, outputWire]
  have hcxwf : (RGate.cx y x).wellFormed w = true := by
    simp [RGate.wellFormed, hxw, hyw, Ne.symm hxy]
  have hcxCircuit : ({ width := w, gates := [.cx y x] } : RCircuit).wellFormed =
      true := by simp [RCircuit.wellFormed, hcxwf]
  have hcxAll := gateOps_implementsU (w := w) (input := input) hl
    (gates := [.cx y x]) hcxCircuit (Dy.invSqrt2 (deg level))
  have hcx := hcxAll.mono (dom' := unaryTwoReady addressWidth)
    (fun _ _ => trivial)
  have hand := implementsU_andUncomputeClean (input := input) (m := outputWidth)
    hl h0w hxw hyw h0x h0y hxy
  have hthrough := hcx.append hand
    (fun i hi _ => RGate.act_lt hcxwf hi)
    (fun i _ hready => by
      simpa [x, y, actGates_cons, actGates_nil] using
        afterUnaryCnot_and haddress hready)
  have hxAll := MeasuredUncompute.x_implementsU (input := input) hxw
    (Dy.invSqrt2 (deg level))
  have hall := hthrough.append hxAll
    (fun i hi _ => Lookup3.writeBit_lt hyw
      (RGate.act_lt hcxwf hi))
    (fun _ _ _ => trivial)
  have hout :
      (fun i => writeBit (actGates [.cx y x] i) y false ^^^ (1 <<< x)) =
        clearUnaryOneOut addressWidth := by
    funext i
    rfl
  rw [hout] at hall
  simpa [clearUnaryOps, clearStageOps, clearUnaryOneOut, w, x, y,
    gateOps, Unary.gateOps, Function.comp_def, List.append_assoc,
    compileGate, scratchBit] using hall

end VQ.Lookup.BatchedUncompute
