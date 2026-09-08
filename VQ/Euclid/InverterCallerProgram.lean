import VQ.Program.OfCircuit
import VQ.Program.Realise
import VQ.Euclid.InverterProgram
import VQ.Euclid.InverterTotalCaller

namespace VQ.Euclid.InverterCallerProgram

open Reversible Semantics

def program (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) : Program :=
  Program.ofCircuit
    (compile
      (InverterCaller.circuit prep rounds n lengthWidth shiftWidth))

def reversibleGateBound (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) : Nat :=
  2 * prep.length +
    InverterProgram.reversibleGateBound rounds n lengthWidth shiftWidth

def reversibleCcxBound (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) : Nat :=
  2 * prep.countP RGate.isCcx +
    InverterProgram.reversibleCcxBound rounds n lengthWidth shiftWidth

def reversibleCxBound (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) : Nat :=
  2 * prep.countP RGate.isCx +
    InverterProgram.reversibleCxBound rounds n lengthWidth shiftWidth

def compiledGateBound (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) : Nat :=
  reversibleGateBound prep rounds n lengthWidth shiftWidth +
    2 * reversibleCcxBound prep rounds n lengthWidth shiftWidth

def compiledCliffordBound (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) : Nat :=
  reversibleGateBound prep rounds n lengthWidth shiftWidth +
    reversibleCcxBound prep rounds n lengthWidth shiftWidth

@[simp] theorem program_width (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).width =
      (InverterCaller.layout n lengthWidth shiftWidth).width := rfl

@[simp] theorem program_inputBits (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).inputBits = 0 := rfl

@[simp] theorem program_cbits (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).cbits = 0 := rfl

@[simp] theorem program_isUnitary (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).isUnitary = true := by
  simp [program]

theorem program_wellFormed
    {level rounds n lengthWidth shiftWidth : Nat} {prep : List RGate}
    {p : Nat}
    (hlevel : 3 ≤ level)
    (hprep : InverterTotalCaller.PreprocessorSpec
      prep p n lengthWidth shiftWidth)
    (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    (program prep rounds n lengthWidth shiftWidth).wellFormed level = true := by
  exact wellFormed_ofCircuit_compile hlevel
    (InverterCaller.circuit_wellFormed
      hprep.positive hlength hwidths)

theorem runProgram
    {level p a n lengthWidth shiftWidth : Nat} {prep : List RGate}
    (hlevel : 3 ≤ level)
    (hprep : InverterTotalCaller.PreprocessorSpec
      prep p n lengthWidth shiftWidth)
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n + 1 < 2 ^ shiftWidth)
    (ha : a < p) :
    runProgram level
        (program prep (12 * n) n lengthWidth shiftWidth) 0
        (basis (InverterCaller.rawInput n lengthWidth shiftWidth a) :
          Vec (deg level)) =
      [{ outcomes := [], creg := 0,
         state := basis
           ((InverterCaller.layout n lengthWidth shiftWidth).write
             (InverterCaller.rawInput n lengthWidth shiftWidth a) 1
             (InverterTotalCaller.result
               p n lengthWidth shiftWidth a)),
         input := 0 }] := by
  have hlength : 0 < lengthWidth := by
    by_contra hnot
    have hzero : lengthWidth = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hwork
    simp [workWidth] at hwork
  have haction := InverterTotalCaller.gates_act
    hprep hpPrime hpFit hwork hwidths hscheduleFit ha
  have haction' :
      act (InverterCaller.circuit prep (12 * n) n lengthWidth shiftWidth)
          (InverterCaller.rawInput n lengthWidth shiftWidth a) =
        (InverterCaller.layout n lengthWidth shiftWidth).write
          (InverterCaller.rawInput n lengthWidth shiftWidth a) 1
          (InverterTotalCaller.result p n lengthWidth shiftWidth a) := by
    simpa [InverterCaller.circuit, Reversible.act] using haction
  rw [program, runProgram_ofCircuit,
    run_compile_basis hlevel
      (InverterCaller.circuit_wellFormed
        hprep.positive hlength hwidths), haction']

theorem gates_length_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (InverterCaller.circuit prep rounds n lengthWidth shiftWidth).gates.length ≤
      reversibleGateBound prep rounds n lengthWidth shiftWidth := by
  simpa [InverterCaller.circuit, reversibleGateBound,
    InverterProgram.reversibleGateBound] using
    InverterCaller.gates_length_le
      prep rounds n lengthWidth shiftWidth

theorem gates_ccx_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (InverterCaller.circuit prep rounds n lengthWidth shiftWidth).gates.countP
        RGate.isCcx ≤
      reversibleCcxBound prep rounds n lengthWidth shiftWidth := by
  simpa [InverterCaller.circuit, reversibleCcxBound,
    InverterProgram.reversibleCcxBound] using
    InverterCaller.gates_ccx_le prep rounds n lengthWidth shiftWidth

theorem gates_cx_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (InverterCaller.circuit prep rounds n lengthWidth shiftWidth).gates.countP
        RGate.isCx ≤
      reversibleCxBound prep rounds n lengthWidth shiftWidth := by
  simpa [InverterCaller.circuit, reversibleCxBound,
    InverterProgram.reversibleCxBound] using
    InverterCaller.gates_cx_le prep rounds n lengthWidth shiftWidth

theorem compiled_gateCount_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    Circuit.gateCount
        (compile
          (InverterCaller.circuit prep rounds n lengthWidth shiftWidth)) ≤
      compiledGateBound prep rounds n lengthWidth shiftWidth := by
  rw [gateCount_compile, compiledGateBound]
  exact Nat.add_le_add
    (gates_length_le prep rounds n lengthWidth shiftWidth)
    (Nat.mul_le_mul_left 2
      (gates_ccx_le prep rounds n lengthWidth shiftWidth))

theorem compiled_cliffordCount_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    Circuit.cliffordCount
        (compile
          (InverterCaller.circuit prep rounds n lengthWidth shiftWidth)) ≤
      compiledCliffordBound prep rounds n lengthWidth shiftWidth := by
  rw [cliffordCount_compile, compiledCliffordBound]
  exact Nat.add_le_add
    (gates_length_le prep rounds n lengthWidth shiftWidth)
    (gates_ccx_le prep rounds n lengthWidth shiftWidth)

theorem compiled_cnotCount_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    Circuit.cnotCount
        (compile
          (InverterCaller.circuit prep rounds n lengthWidth shiftWidth)) ≤
      reversibleCxBound prep rounds n lengthWidth shiftWidth := by
  rw [cnotCount_compile]
  exact gates_cx_le prep rounds n lengthWidth shiftWidth

theorem compiled_toffoliCount_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    Circuit.toffoliCount
        (compile
          (InverterCaller.circuit prep rounds n lengthWidth shiftWidth)) ≤
      reversibleCcxBound prep rounds n lengthWidth shiftWidth := by
  rw [toffoliCount_compile]
  exact gates_ccx_le prep rounds n lengthWidth shiftWidth

theorem gateCount_hi_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).gateCount.hi ≤
      compiledGateBound prep rounds n lengthWidth shiftWidth := by
  simpa [program, Range.point] using
    compiled_gateCount_le prep rounds n lengthWidth shiftWidth

theorem cliffordCount_hi_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).cliffordCount.hi ≤
      compiledCliffordBound prep rounds n lengthWidth shiftWidth := by
  simpa [program, Range.point] using
    compiled_cliffordCount_le prep rounds n lengthWidth shiftWidth

theorem cnotCount_hi_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).cnotCount.hi ≤
      reversibleCxBound prep rounds n lengthWidth shiftWidth := by
  simpa [program, Range.point] using
    compiled_cnotCount_le prep rounds n lengthWidth shiftWidth

theorem toffoliCount_hi_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).toffoliCount.hi ≤
      reversibleCcxBound prep rounds n lengthWidth shiftWidth := by
  simpa [program, Range.point] using
    compiled_toffoliCount_le prep rounds n lengthWidth shiftWidth

theorem depthRange_hi_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).depthRange.hi ≤
      compiledGateBound prep rounds n lengthWidth shiftWidth := by
  exact (Program.depthRange_ofCircuit_hi_le_gateCount _).trans
    (compiled_gateCount_le prep rounds n lengthWidth shiftWidth)

theorem toffoliDepthRange_hi_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).toffoliDepthRange.hi ≤
      reversibleCcxBound prep rounds n lengthWidth shiftWidth := by
  exact (Program.toffoliDepthRange_ofCircuit_hi_le_toffoliCount _).trans
    (compiled_toffoliCount_le prep rounds n lengthWidth shiftWidth)

theorem usedWires_le
    {prep : List RGate} {p rounds n lengthWidth shiftWidth : Nat}
    (hprep : InverterTotalCaller.PreprocessorSpec
      prep p n lengthWidth shiftWidth)
    (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    (program prep rounds n lengthWidth shiftWidth).usedWires ≤
      (InverterCaller.layout n lengthWidth shiftWidth).width := by
  simpa [program, InverterCaller.circuit] using usedWires_compile_le_width
    (InverterCaller.circuit_wellFormed
      hprep.positive hlength hwidths)

@[simp] theorem measureCount_exact (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).measureCount =
      Range.point 0 := by
  simp [program]

@[simp] theorem resetCount_exact (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).resetCount =
      Range.point 0 := by
  simp [program]

@[simp] theorem measureResetCount_exact (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).measureResetCount =
      Range.point 0 := by
  simp [program]

@[simp] theorem classicalOpCount_exact (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).classicalOpCount =
      Range.point 0 := by
  simp [program]

@[simp] theorem measurementDepthRange_hi (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).measurementDepthRange.hi =
      0 := by
  simp [program]

@[simp] theorem feedForwardDepthRange_hi (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).feedForwardDepthRange.hi =
      0 := by
  simp [program]

@[simp] theorem classicalDepthRange_hi (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (program prep rounds n lengthWidth shiftWidth).classicalDepthRange.hi =
      0 := by
  simp [program]

end VQ.Euclid.InverterCallerProgram
