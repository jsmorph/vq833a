import VQ.Euclid.InverterCallerProgram
import VQ.Program.ExactCliffordCCZ
import VQ.Program.ResourceReport

namespace VQ.Euclid.InverterCallerProgram

open Reversible Semantics

def report (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    Program.ResourceReport :=
  Program.resourceReport
    (program prep rounds n lengthWidth shiftWidth)

theorem program_usesOnlyExactCliffordCCZ (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    Program.ExactCliffordCCZ.UsesOnly
      (program prep rounds n lengthWidth shiftWidth) := by
  exact Program.ExactCliffordCCZ.ofCircuit_compile_usesOnly _

@[simp] theorem report_qubits (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).qubits =
      (InverterCaller.layout n lengthWidth shiftWidth).width := rfl

@[simp] theorem report_inputBits (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).inputBits = 0 := rfl

@[simp] theorem report_localBits (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).localBits = 0 := rfl

theorem report_usedQubits_le
    {prep : List RGate} {p rounds n lengthWidth shiftWidth : Nat}
    (hprep : InverterTotalCaller.PreprocessorSpec
      prep p n lengthWidth shiftWidth)
    (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    (report prep rounds n lengthWidth shiftWidth).usedQubits ≤
      (InverterCaller.layout n lengthWidth shiftWidth).width := by
  exact usedWires_le hprep hlength hwidths

theorem report_gates_hi_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).gates.hi ≤
      compiledGateBound prep rounds n lengthWidth shiftWidth := by
  exact gateCount_hi_le prep rounds n lengthWidth shiftWidth

theorem report_clifford_hi_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).clifford.hi ≤
      compiledCliffordBound prep rounds n lengthWidth shiftWidth := by
  exact cliffordCount_hi_le prep rounds n lengthWidth shiftWidth

theorem report_cnot_hi_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).cnot.hi ≤
      reversibleCxBound prep rounds n lengthWidth shiftWidth := by
  exact cnotCount_hi_le prep rounds n lengthWidth shiftWidth

theorem report_toffoli_hi_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).toffoli.hi ≤
      reversibleCcxBound prep rounds n lengthWidth shiftWidth := by
  exact toffoliCount_hi_le prep rounds n lengthWidth shiftWidth

theorem report_totalDepth_hi_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).totalDepth.hi ≤
      compiledGateBound prep rounds n lengthWidth shiftWidth := by
  exact depthRange_hi_le prep rounds n lengthWidth shiftWidth

theorem report_toffoliDepth_hi_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).toffoliDepth.hi ≤
      reversibleCcxBound prep rounds n lengthWidth shiftWidth := by
  exact toffoliDepthRange_hi_le prep rounds n lengthWidth shiftWidth

@[simp] theorem report_measurements (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).measurements =
      Range.point 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_resets (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).resets = Range.point 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_measurementResets (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).measurementResets =
      Range.point 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_measurementDepth_hi (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).measurementDepth.hi = 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_feedForwardDepth_hi (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).feedForwardDepth.hi = 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_classicalOps (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).classicalOps =
      Range.point 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_classicalDepth_hi (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).classicalDepth.hi = 0 := by
  simp [report, Program.resourceReport]

theorem report_cczToTUpper_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (report prep rounds n lengthWidth shiftWidth).cczToTUpper ≤
      7 * reversibleCcxBound prep rounds n lengthWidth shiftWidth := by
  exact Nat.mul_le_mul_left 7
    (toffoliCount_hi_le prep rounds n lengthWidth shiftWidth)

end VQ.Euclid.InverterCallerProgram
