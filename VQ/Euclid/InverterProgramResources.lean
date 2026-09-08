import VQ.Euclid.InverterProgram
import VQ.Program.ExactCliffordCCZ
import VQ.Program.ResourceReport

namespace VQ.Euclid.InverterProgram

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
      (Inverter.layout n lengthWidth shiftWidth).width := rfl

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
      (Inverter.layout n lengthWidth shiftWidth).width := by
  exact usedWires_le hlength hwidths

theorem report_gates_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).gates.hi ≤
      compiledGateBound rounds n lengthWidth shiftWidth := by
  exact gateCount_hi_le rounds n lengthWidth shiftWidth

theorem report_clifford_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).clifford.hi ≤
      compiledCliffordBound rounds n lengthWidth shiftWidth := by
  exact cliffordCount_hi_le rounds n lengthWidth shiftWidth

theorem report_cnot_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).cnot.hi ≤
      reversibleCxBound rounds n lengthWidth shiftWidth := by
  exact cnotCount_hi_le rounds n lengthWidth shiftWidth

theorem report_toffoli_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).toffoli.hi ≤
      reversibleCcxBound rounds n lengthWidth shiftWidth := by
  exact toffoliCount_hi_le rounds n lengthWidth shiftWidth

theorem report_totalDepth_hi_le
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).totalDepth.hi ≤
      compiledGateBound rounds n lengthWidth shiftWidth := by
  exact depthRange_hi_le rounds n lengthWidth shiftWidth

theorem report_toffoliDepth_hi_le
    (rounds n lengthWidth shiftWidth : Nat) :
    (report rounds n lengthWidth shiftWidth).toffoliDepth.hi ≤
      reversibleCcxBound rounds n lengthWidth shiftWidth := by
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
      7 * reversibleCcxBound rounds n lengthWidth shiftWidth := by
  exact Nat.mul_le_mul_left 7
    (toffoliCount_hi_le rounds n lengthWidth shiftWidth)

theorem secp256k1_report_qubits :
    (report 3072 256 9 12).qubits = 860 := by
  rw [report_qubits, Inverter.layout, TerminalCircuit.layout,
    ExtractionPlaced.layout_width, ExtractionPlaced.baseWidth,
    StepLayout.layout_width]
  norm_num [StepLayout.auxOffset, StepLayout.phase1Wire,
    StepLayout.shiftOffset, StepLayout.auxWidth,
    StepLayout.selectorWidth, workWidth]

theorem secp256k1_coefficientAdjustmentConstant :
    EndpointPrep.coefficientAdjustmentConstant 256 = 257 := by
  decide

theorem secp256k1_reversibleGateBound :
    reversibleGateBound 3072 256 9 12 = 4190064084 := by
  norm_num [reversibleGateBound, StepResources.gateBound,
    StepResources.remainderPrepareGateBound,
    StepResources.swapPrepareGateBound,
    StepResources.coefficientPrepareGateBound,
    StepResources.coefficientAdjustmentXorLength,
    StepResources.phaseGateBound, SwapLength.gateBound,
    LengthWriter.gateBound, LengthWriter.zeroGateBound,
    workWidth, Increment.lengthCost, Increment.conjunctionLength,
    controlledXorGates, EndpointPrep.controlWire,
    EndpointPrep.rightOffset, secp256k1_coefficientAdjustmentConstant,
    PrunedSelectSwap.width259_gateBound]

theorem secp256k1_reversibleCcxBound :
    reversibleCcxBound 3072 256 9 12 = 2162690874 := by
  norm_num [reversibleCcxBound, StepResources.ccxBound,
    StepResources.remainderPrepareCcxBound,
    StepResources.swapPrepareCcxBound,
    StepResources.coefficientPrepareCcxBound,
    StepResources.phaseCcxBound, SwapLength.ccxBound,
    LengthWriter.ccxBound, LengthWriter.zeroCcxBound,
    workWidth, Increment.ccxCost, Increment.conjunctionCcx,
    PrunedSelectSwap.width259_ccxBound]

theorem secp256k1_reversibleCxBound :
    reversibleCxBound 3072 256 9 12 = 4144713876 := by
  norm_num [reversibleCxBound, StepResources.cxBound,
    StepResources.coefficientPrepareCxBound,
    StepResources.coefficientAdjustmentXorLength,
    StepResources.phaseCxBound, SwapLength.gateBound,
    LengthWriter.gateBound, LengthWriter.zeroGateBound,
    workWidth, Increment.cxCost, Increment.conjunctionCx,
    controlledXorGates, EndpointPrep.controlWire,
    EndpointPrep.rightOffset, secp256k1_coefficientAdjustmentConstant,
    PrunedSelectSwap.width259_cxBound]

theorem secp256k1_compiledGateBound :
    compiledGateBound 3072 256 9 12 = 8515445832 := by
  rw [compiledGateBound, secp256k1_reversibleGateBound,
    secp256k1_reversibleCcxBound]

theorem secp256k1_compiledCliffordBound :
    compiledCliffordBound 3072 256 9 12 = 6352754958 := by
  rw [compiledCliffordBound, secp256k1_reversibleGateBound,
    secp256k1_reversibleCcxBound]

theorem secp256k1_report_gates_hi_le :
    (report 3072 256 9 12).gates.hi ≤ 8515445832 := by
  calc
    (report 3072 256 9 12).gates.hi ≤
        compiledGateBound 3072 256 9 12 :=
      report_gates_hi_le 3072 256 9 12
    _ = 8515445832 := secp256k1_compiledGateBound

theorem secp256k1_report_clifford_hi_le :
    (report 3072 256 9 12).clifford.hi ≤ 6352754958 := by
  calc
    (report 3072 256 9 12).clifford.hi ≤
        compiledCliffordBound 3072 256 9 12 :=
      report_clifford_hi_le 3072 256 9 12
    _ = 6352754958 := secp256k1_compiledCliffordBound

theorem secp256k1_report_cnot_hi_le :
    (report 3072 256 9 12).cnot.hi ≤ 4144713876 := by
  calc
    (report 3072 256 9 12).cnot.hi ≤
        reversibleCxBound 3072 256 9 12 :=
      report_cnot_hi_le 3072 256 9 12
    _ = 4144713876 := secp256k1_reversibleCxBound

theorem secp256k1_report_toffoli_hi_le :
    (report 3072 256 9 12).toffoli.hi ≤ 2162690874 := by
  calc
    (report 3072 256 9 12).toffoli.hi ≤
        reversibleCcxBound 3072 256 9 12 :=
      report_toffoli_hi_le 3072 256 9 12
    _ = 2162690874 := secp256k1_reversibleCcxBound

theorem secp256k1_report_totalDepth_hi_le :
    (report 3072 256 9 12).totalDepth.hi ≤ 8515445832 := by
  calc
    (report 3072 256 9 12).totalDepth.hi ≤
        compiledGateBound 3072 256 9 12 :=
      report_totalDepth_hi_le 3072 256 9 12
    _ = 8515445832 := secp256k1_compiledGateBound

theorem secp256k1_report_toffoliDepth_hi_le :
    (report 3072 256 9 12).toffoliDepth.hi ≤ 2162690874 := by
  calc
    (report 3072 256 9 12).toffoliDepth.hi ≤
        reversibleCcxBound 3072 256 9 12 :=
      report_toffoliDepth_hi_le 3072 256 9 12
    _ = 2162690874 := secp256k1_reversibleCcxBound

end VQ.Euclid.InverterProgram
