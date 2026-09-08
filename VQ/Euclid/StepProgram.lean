import VQ.Euclid.Program
import VQ.Program.ExactCliffordCCZ
import VQ.Program.ResourceReport

namespace VQ
namespace Euclid
namespace StepProgram

open Reversible Semantics

def report (rounds n lengthWidth shiftWidth : Nat) :
    Program.ResourceReport :=
  Program.resourceReport (program rounds n lengthWidth shiftWidth)

theorem program_usesOnlyExactCliffordCCZ
    (rounds n lengthWidth shiftWidth : Nat) :
    Program.ExactCliffordCCZ.UsesOnly
      (program rounds n lengthWidth shiftWidth) := by
  exact Program.ExactCliffordCCZ.ofCircuit_compile_usesOnly _

@[simp] theorem report_qubits (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).qubits =
      (StepLayout.layout n lengthWidth shiftWidth).width := rfl

@[simp] theorem report_inputBits (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).inputBits = 0 := rfl

@[simp] theorem report_localBits (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).localBits = 0 := rfl

@[simp] theorem report_usedInputBits
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).usedInputBits = 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_usedLocalBits
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).usedLocalBits = 0 := by
  simp [report, Program.resourceReport]

theorem report_usedQubits_le
    {rounds n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (report rounds n lengthWidth shiftWidth).usedQubits ≤
      (StepLayout.layout n lengthWidth shiftWidth).width := by
  exact usedWires_le hlength hwidths

theorem report_gates_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).gates.hi ≤
      rounds * StepResources.compiledGateBound n lengthWidth shiftWidth := by
  exact gateCount_hi_le rounds n lengthWidth shiftWidth

theorem report_clifford_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).clifford.hi ≤
      rounds * StepResources.compiledCliffordBound n lengthWidth shiftWidth := by
  exact cliffordCount_hi_le rounds n lengthWidth shiftWidth

theorem report_cnot_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).cnot.hi ≤
      rounds * StepResources.cxBound n lengthWidth shiftWidth := by
  exact cnotCount_hi_le rounds n lengthWidth shiftWidth

theorem report_toffoli_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).toffoli.hi ≤
      rounds * StepResources.ccxBound n lengthWidth shiftWidth := by
  exact toffoliCount_hi_le rounds n lengthWidth shiftWidth

theorem report_totalDepth_hi_le
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).totalDepth.hi ≤
      rounds * StepResources.compiledGateBound n lengthWidth shiftWidth := by
  exact depthRange_hi_le rounds n lengthWidth shiftWidth

theorem report_toffoliDepth_hi_le
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).toffoliDepth.hi ≤
      rounds * StepResources.ccxBound n lengthWidth shiftWidth := by
  exact toffoliDepthRange_hi_le rounds n lengthWidth shiftWidth

@[simp] theorem report_measurements
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).measurements = Range.point 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_resets (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).resets = Range.point 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_measurementResets
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).measurementResets =
      Range.point 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_measurementDepth_hi
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).measurementDepth.hi = 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_feedForwardDepth_hi
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).feedForwardDepth.hi = 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_classicalOps
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).classicalOps = Range.point 0 := by
  simp [report, Program.resourceReport]

@[simp] theorem report_classicalDepth_hi
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).classicalDepth.hi = 0 := by
  simp [report, Program.resourceReport]

theorem report_cczToTUpper_le
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).cczToTUpper ≤
      7 * (rounds * StepResources.ccxBound n lengthWidth shiftWidth) := by
  exact Nat.mul_le_mul_left 7
    (toffoliCount_hi_le rounds n lengthWidth shiftWidth)

end StepProgram
end Euclid
end VQ
