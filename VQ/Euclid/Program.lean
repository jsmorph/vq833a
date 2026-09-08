/-
Program embedding, execution, and resources for fixed Euclidean-step repetition.
-/
import VQ.Program.OfCircuit
import VQ.Program.Realise
import VQ.Euclid.StepResources

namespace VQ
namespace Euclid
namespace StepProgram

open Reversible Semantics

def program (rounds n lengthWidth shiftWidth : Nat) : Program :=
  Program.ofCircuit
    (compile
      (StepResources.fixedRoundCircuit rounds n lengthWidth shiftWidth))


@[simp] theorem program_width (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).width =
      (StepLayout.layout n lengthWidth shiftWidth).width := rfl

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
    (StepResources.fixedRoundCircuit_wellFormed hlength hwidths)


theorem runProgram_encoded_of_trace
    {level rounds n lengthWidth shiftWidth : Nat} {s : State}
    (hlevel : 3 ≤ level) (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (htrace : Iteration.TraceAction n lengthWidth shiftWidth rounds s) :
    runProgram level (program rounds n lengthWidth shiftWidth) 0
        (basis (StepState.encoded n lengthWidth shiftWidth s) :
          Vec (deg level)) =
      [{ outcomes := [], creg := 0,
         state := basis
          (StepState.encoded n lengthWidth shiftWidth
            (run lengthWidth shiftWidth rounds s)),
         input := 0 }] := by
  rw [program, runProgram_ofCircuit,
    run_compile_basis hlevel
      (StepResources.fixedRoundCircuit_wellFormed hlength hwidths)]
  have hact := Iteration.act_circuit_encoded_of_trace htrace
  rw [show act
      (StepResources.fixedRoundCircuit rounds n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      StepState.encoded n lengthWidth shiftWidth
        (run lengthWidth shiftWidth rounds s) by
    simpa [StepResources.fixedRoundCircuit] using hact]

theorem gateCount_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).gateCount.hi ≤
      rounds * StepResources.compiledGateBound n lengthWidth shiftWidth := by
  simpa [program, Range.point] using
    StepResources.compiledFixed_gateCount_le
      rounds n lengthWidth shiftWidth

theorem cliffordCount_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).cliffordCount.hi ≤
      rounds * StepResources.compiledCliffordBound n lengthWidth shiftWidth := by
  simpa [program, Range.point] using
    StepResources.compiledFixed_clifford_le
      rounds n lengthWidth shiftWidth

theorem cnotCount_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).cnotCount.hi ≤
      rounds * StepResources.cxBound n lengthWidth shiftWidth := by
  simpa [program, Range.point] using
    StepResources.compiledFixed_cnot_le rounds n lengthWidth shiftWidth

theorem toffoliCount_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).toffoliCount.hi ≤
      rounds * StepResources.ccxBound n lengthWidth shiftWidth := by
  simpa [program, Range.point] using
    StepResources.compiledFixed_toffoli_le rounds n lengthWidth shiftWidth

theorem depthRange_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).depthRange.hi ≤
      rounds * StepResources.compiledGateBound n lengthWidth shiftWidth := by
  calc
    (program rounds n lengthWidth shiftWidth).depthRange.hi ≤
        Circuit.gateCount
          (compile
            (StepResources.fixedRoundCircuit rounds n lengthWidth shiftWidth)) := by
      simpa [program] using
        Program.depthRange_ofCircuit_hi_le_gateCount
          (compile
            (StepResources.fixedRoundCircuit rounds n lengthWidth shiftWidth))
    _ ≤ rounds * StepResources.compiledGateBound n lengthWidth shiftWidth :=
      StepResources.compiledFixed_gateCount_le
        rounds n lengthWidth shiftWidth

theorem toffoliDepthRange_hi_le
    (rounds n lengthWidth shiftWidth : Nat) :
    (program rounds n lengthWidth shiftWidth).toffoliDepthRange.hi ≤
      rounds * StepResources.ccxBound n lengthWidth shiftWidth := by
  calc
    (program rounds n lengthWidth shiftWidth).toffoliDepthRange.hi ≤
        Circuit.toffoliCount
          (compile
            (StepResources.fixedRoundCircuit rounds n lengthWidth shiftWidth)) := by
      simpa [program] using
        Program.toffoliDepthRange_ofCircuit_hi_le_toffoliCount
          (compile
            (StepResources.fixedRoundCircuit rounds n lengthWidth shiftWidth))
    _ ≤ rounds * StepResources.ccxBound n lengthWidth shiftWidth :=
      StepResources.compiledFixed_toffoli_le
        rounds n lengthWidth shiftWidth

theorem usedWires_le
    {rounds n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (program rounds n lengthWidth shiftWidth).usedWires ≤
      (StepLayout.layout n lengthWidth shiftWidth).width := by
  simpa [program] using
    StepResources.compiledFixed_usedWires_le
      (rounds := rounds) hlength hwidths

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

end StepProgram
end Euclid
end VQ
