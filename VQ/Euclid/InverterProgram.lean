import VQ.Program.OfCircuit
import VQ.Program.Realise
import VQ.Euclid.Inverter

namespace VQ.Euclid.InverterProgram

open Reversible Semantics

def program (rounds n lengthWidth shiftWidth : Nat) : Program :=
  Program.ofCircuit
    (compile (Inverter.circuit rounds n lengthWidth shiftWidth))

def reversibleGateBound
    (rounds n lengthWidth shiftWidth : Nat) : Nat :=
  2 * (rounds * StepResources.gateBound n lengthWidth shiftWidth) +
    (2 * (Increment.lengthCost shiftWidth + 2 +
      3 * workWidth n * shiftWidth) + n + (11 * n + 4))

def reversibleCcxBound
    (rounds n lengthWidth shiftWidth : Nat) : Nat :=
  2 * (rounds * StepResources.ccxBound n lengthWidth shiftWidth) +
    (2 * (Increment.ccxCost shiftWidth + workWidth n * shiftWidth) +
      10 * n)

def reversibleCxBound
    (rounds n lengthWidth shiftWidth : Nat) : Nat :=
  2 * (rounds * StepResources.cxBound n lengthWidth shiftWidth) +
    (2 * (Increment.cxCost shiftWidth + 2 * workWidth n * shiftWidth) + n +
      (7 * n + 2))

def compiledGateBound
    (rounds n lengthWidth shiftWidth : Nat) : Nat :=
  reversibleGateBound rounds n lengthWidth shiftWidth +
    2 * reversibleCcxBound rounds n lengthWidth shiftWidth

def compiledCliffordBound
    (rounds n lengthWidth shiftWidth : Nat) : Nat :=
  reversibleGateBound rounds n lengthWidth shiftWidth +
    reversibleCcxBound rounds n lengthWidth shiftWidth

@[simp] theorem program_width (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).width =
      (Inverter.layout n lengthWidth shiftWidth).width := rfl

@[simp] theorem program_inputBits (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).inputBits = 0 := rfl

@[simp] theorem program_cbits (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).cbits = 0 := rfl

@[simp] theorem program_usedInputBits
    (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).usedInputBits = 0 := by
  simp [program]

@[simp] theorem program_usedCbits
    (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).usedCbits = 0 := by
  simp [program]

@[simp] theorem program_isUnitary
    (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).isUnitary = true := by
  simp [program]

theorem program_wellFormed
    {level rounds n lengthWidth shiftWidth : Nat}
    (hlevel : 3 ≤ level) (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    (program rounds n lengthWidth shiftWidth).wellFormed level = true := by
  exact wellFormed_ofCircuit_compile hlevel
    (Inverter.circuit_wellFormed hlength hwidths)

theorem runProgram_preprocessed_linear_schedule
    {level p a n lengthWidth shiftWidth : Nat}
    (hlevel : 3 ≤ level)
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n < 2 ^ shiftWidth)
    (ha0 : 0 < a)
    (ha : a < p) :
    let final := run lengthWidth shiftWidth (12 * n)
      (preprocessedState p a)
    runProgram level (program (12 * n) n lengthWidth shiftWidth) 0
        (basis (StepState.encoded n lengthWidth shiftWidth
          (preprocessedState p a)) : Vec (deg level)) =
      [{ outcomes := [], creg := 0,
         state := basis
           (writeField
             (StepState.encoded n lengthWidth shiftWidth
               (preprocessedState p a))
             (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n
             (decodedInverse p final)),
         input := 0 }] ∧
      decodedInverse p final < p ∧
      a * decodedInverse p final ≡ 1 [MOD p] := by
  dsimp only
  have hlength : 0 < lengthWidth := by
    by_contra hnot
    have hzero : lengthWidth = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hwork
    simp [workWidth] at hwork
  have hspec := Inverter.circuit_spec_preprocessed_linear_schedule
    hpPrime hpFit hwork hwidths hscheduleFit ha0 ha
  constructor
  · rw [program, runProgram_ofCircuit,
      run_compile_basis hlevel
        (Inverter.circuit_wellFormed hlength hwidths), hspec.1]
  · exact hspec.2

theorem gates_length_le (rounds n lengthWidth shiftWidth : Nat) :
    (Inverter.circuit rounds n lengthWidth shiftWidth).gates.length ≤
      reversibleGateBound rounds n lengthWidth shiftWidth := by
  simpa [Inverter.circuit, reversibleGateBound] using
    Inverter.gates_length_le rounds n lengthWidth shiftWidth

theorem gates_ccx_le (rounds n lengthWidth shiftWidth : Nat) :
    (Inverter.circuit rounds n lengthWidth shiftWidth).gates.countP
        RGate.isCcx ≤
      reversibleCcxBound rounds n lengthWidth shiftWidth := by
  simpa [Inverter.circuit, reversibleCcxBound] using
    Inverter.gates_ccx_le rounds n lengthWidth shiftWidth

theorem gates_cx_le (rounds n lengthWidth shiftWidth : Nat) :
    (Inverter.circuit rounds n lengthWidth shiftWidth).gates.countP
        RGate.isCx ≤
      reversibleCxBound rounds n lengthWidth shiftWidth := by
  simpa [Inverter.circuit, reversibleCxBound] using
    Inverter.gates_cx_le rounds n lengthWidth shiftWidth

theorem compiled_gateCount_le (rounds n lengthWidth shiftWidth : Nat) :
    Circuit.gateCount
        (compile (Inverter.circuit rounds n lengthWidth shiftWidth)) ≤
      compiledGateBound rounds n lengthWidth shiftWidth := by
  rw [gateCount_compile, compiledGateBound]
  exact Nat.add_le_add (gates_length_le rounds n lengthWidth shiftWidth)
    (Nat.mul_le_mul_left 2
      (gates_ccx_le rounds n lengthWidth shiftWidth))

theorem compiled_cliffordCount_le
    (rounds n lengthWidth shiftWidth : Nat) :
    Circuit.cliffordCount
        (compile (Inverter.circuit rounds n lengthWidth shiftWidth)) ≤
      compiledCliffordBound rounds n lengthWidth shiftWidth := by
  rw [cliffordCount_compile, compiledCliffordBound]
  exact Nat.add_le_add (gates_length_le rounds n lengthWidth shiftWidth)
    (gates_ccx_le rounds n lengthWidth shiftWidth)

theorem compiled_cnotCount_le (rounds n lengthWidth shiftWidth : Nat) :
    Circuit.cnotCount
        (compile (Inverter.circuit rounds n lengthWidth shiftWidth)) ≤
      reversibleCxBound rounds n lengthWidth shiftWidth := by
  rw [cnotCount_compile]
  exact gates_cx_le rounds n lengthWidth shiftWidth

theorem compiled_toffoliCount_le
    (rounds n lengthWidth shiftWidth : Nat) :
    Circuit.toffoliCount
        (compile (Inverter.circuit rounds n lengthWidth shiftWidth)) ≤
      reversibleCcxBound rounds n lengthWidth shiftWidth := by
  rw [toffoliCount_compile]
  exact gates_ccx_le rounds n lengthWidth shiftWidth

theorem gateCount_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).gateCount.hi ≤
      compiledGateBound rounds n lengthWidth shiftWidth := by
  simpa [program, Range.point] using
    compiled_gateCount_le rounds n lengthWidth shiftWidth

theorem cliffordCount_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).cliffordCount.hi ≤
      compiledCliffordBound rounds n lengthWidth shiftWidth := by
  simpa [program, Range.point] using
    compiled_cliffordCount_le rounds n lengthWidth shiftWidth

theorem cnotCount_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).cnotCount.hi ≤
      reversibleCxBound rounds n lengthWidth shiftWidth := by
  simpa [program, Range.point] using
    compiled_cnotCount_le rounds n lengthWidth shiftWidth

theorem toffoliCount_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).toffoliCount.hi ≤
      reversibleCcxBound rounds n lengthWidth shiftWidth := by
  simpa [program, Range.point] using
    compiled_toffoliCount_le rounds n lengthWidth shiftWidth

theorem depthRange_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).depthRange.hi ≤
      compiledGateBound rounds n lengthWidth shiftWidth := by
  exact (Program.depthRange_ofCircuit_hi_le_gateCount _).trans
    (compiled_gateCount_le rounds n lengthWidth shiftWidth)

theorem toffoliDepthRange_hi_le
    (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).toffoliDepthRange.hi ≤
      reversibleCcxBound rounds n lengthWidth shiftWidth := by
  exact (Program.toffoliDepthRange_ofCircuit_hi_le_toffoliCount _).trans
    (compiled_toffoliCount_le rounds n lengthWidth shiftWidth)

theorem usedWires_le
    {rounds n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (program rounds n lengthWidth shiftWidth).usedWires ≤
      (Inverter.layout n lengthWidth shiftWidth).width := by
  simpa [program, Inverter.circuit] using usedWires_compile_le_width
    (Inverter.circuit_wellFormed
      (rounds := rounds) hlength hwidths)

@[simp] theorem measureCount_exact
    (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).measureCount = Range.point 0 := by
  simp [program]

@[simp] theorem resetCount_exact
    (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).resetCount = Range.point 0 := by
  simp [program]

@[simp] theorem measureResetCount_exact
    (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).measureResetCount =
      Range.point 0 := by
  simp [program]

@[simp] theorem classicalOpCount_exact
    (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).classicalOpCount =
      Range.point 0 := by
  simp [program]

@[simp] theorem measurementDepthRange_hi
    (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).measurementDepthRange.hi = 0 := by
  simp [program]

@[simp] theorem feedForwardDepthRange_hi
    (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).feedForwardDepthRange.hi = 0 := by
  simp [program]

@[simp] theorem classicalDepthRange_hi
    (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).classicalDepthRange.hi = 0 := by
  simp [program]

end VQ.Euclid.InverterProgram
