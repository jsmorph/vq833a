/-
Resource-certificate derivation for the clean fixed-schedule inverter.  The
certificate composes one-step repetition, terminal extraction, and reversed
fixed rounds.  Its final equalities recover the existing InverterProgram bounds.
-/
import VQ.Resource.Certificate
import VQ.Euclid.InverterProgram

namespace VQ.Euclid.InverterCertificate

open Reversible Resource

def stepBound (n lengthWidth shiftWidth : Nat) : ReversibleBounds :=
  { gates := StepResources.gateBound n lengthWidth shiftWidth,
    ccx := StepResources.ccxBound n lengthWidth shiftWidth,
    cx := StepResources.cxBound n lengthWidth shiftWidth }

def terminalBound (n shiftWidth : Nat) : ReversibleBounds :=
  { gates := 2 * (Increment.lengthCost shiftWidth + 2 +
        3 * workWidth n * shiftWidth) + n + (11 * n + 4),
    ccx := 2 * (Increment.ccxCost shiftWidth + workWidth n * shiftWidth) +
      10 * n,
    cx := 2 * (Increment.cxCost shiftWidth + 2 * workWidth n * shiftWidth) + n +
      (7 * n + 2) }

def fixedBound (rounds n lengthWidth shiftWidth : Nat) : ReversibleBounds :=
  (stepBound n lengthWidth shiftWidth).scale rounds

def inverterBound (rounds n lengthWidth shiftWidth : Nat) : ReversibleBounds :=
  ((fixedBound rounds n lengthWidth shiftWidth).add
    (terminalBound n shiftWidth)).add
      (fixedBound rounds n lengthWidth shiftWidth)

theorem stepCertificate (n lengthWidth shiftWidth : Nat) :
    ReversibleCertificate (Step.gates n lengthWidth shiftWidth)
      (stepBound n lengthWidth shiftWidth) :=
  ⟨StepResources.gates_length_le n lengthWidth shiftWidth,
    StepResources.gates_ccx_le n lengthWidth shiftWidth,
    StepResources.gates_cx_le n lengthWidth shiftWidth⟩

theorem fixedRoundGates_eq_fixedRepeat
    (rounds n lengthWidth shiftWidth : Nat) :
    StepResources.fixedRoundGates rounds n lengthWidth shiftWidth =
      ReversibleCertificate.fixedRepeat
        (Step.gates n lengthWidth shiftWidth) rounds := by
  change Iteration.gates n lengthWidth shiftWidth rounds = _
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      simp [Iteration.gates, ReversibleCertificate.fixedRepeat, ih]

theorem fixedCertificate (rounds n lengthWidth shiftWidth : Nat) :
    ReversibleCertificate
      (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth)
      (fixedBound rounds n lengthWidth shiftWidth) := by
  rw [fixedRoundGates_eq_fixedRepeat]
  exact (stepCertificate n lengthWidth shiftWidth).fixed rounds

theorem terminalCertificate (n lengthWidth shiftWidth : Nat) :
    ReversibleCertificate (TerminalCircuit.gates n lengthWidth shiftWidth)
      (terminalBound n shiftWidth) :=
  ⟨TerminalCircuit.gates_length_le n lengthWidth shiftWidth,
    TerminalCircuit.gates_ccx_le n lengthWidth shiftWidth,
    TerminalCircuit.gates_cx_le n lengthWidth shiftWidth⟩

theorem certificate (rounds n lengthWidth shiftWidth : Nat) :
    ReversibleCertificate (Inverter.gates rounds n lengthWidth shiftWidth)
      (inverterBound rounds n lengthWidth shiftWidth) := by
  simpa [Inverter.gates, Inverter.forwardGates, inverterBound] using
    (((fixedCertificate rounds n lengthWidth shiftWidth).append
      (terminalCertificate n lengthWidth shiftWidth)).append
        (fixedCertificate rounds n lengthWidth shiftWidth).reverse)

theorem compiledCertificate (rounds n lengthWidth shiftWidth : Nat) :
    CircuitCertificate
      (Reversible.compile (Inverter.circuit rounds n lengthWidth shiftWidth))
      (inverterBound rounds n lengthWidth shiftWidth).compiled := by
  simpa [Inverter.circuit] using
    (certificate rounds n lengthWidth shiftWidth).compile
      (Inverter.layout n lengthWidth shiftWidth).width

theorem programCertificate (rounds n lengthWidth shiftWidth : Nat) :
    ProgramCertificate (InverterProgram.program rounds n lengthWidth shiftWidth)
      (inverterBound rounds n lengthWidth shiftWidth).compiled.inProgram := by
  simpa [InverterProgram.program] using
    (compiledCertificate rounds n lengthWidth shiftWidth).ofCircuit

theorem inverterBound_gates (rounds n lengthWidth shiftWidth : Nat) :
    (inverterBound rounds n lengthWidth shiftWidth).gates =
      InverterProgram.reversibleGateBound rounds n lengthWidth shiftWidth := by
  simp only [inverterBound, fixedBound, stepBound, terminalBound,
    ReversibleBounds.add, ReversibleBounds.scale,
    InverterProgram.reversibleGateBound]
  omega

theorem inverterBound_ccx (rounds n lengthWidth shiftWidth : Nat) :
    (inverterBound rounds n lengthWidth shiftWidth).ccx =
      InverterProgram.reversibleCcxBound rounds n lengthWidth shiftWidth := by
  simp only [inverterBound, fixedBound, stepBound, terminalBound,
    ReversibleBounds.add, ReversibleBounds.scale,
    InverterProgram.reversibleCcxBound]
  omega

theorem inverterBound_cx (rounds n lengthWidth shiftWidth : Nat) :
    (inverterBound rounds n lengthWidth shiftWidth).cx =
      InverterProgram.reversibleCxBound rounds n lengthWidth shiftWidth := by
  simp only [inverterBound, fixedBound, stepBound, terminalBound,
    ReversibleBounds.add, ReversibleBounds.scale,
    InverterProgram.reversibleCxBound]
  omega

theorem compiledBound_gates (rounds n lengthWidth shiftWidth : Nat) :
    (inverterBound rounds n lengthWidth shiftWidth).compiled.gates =
      InverterProgram.compiledGateBound rounds n lengthWidth shiftWidth := by
  simp only [ReversibleBounds.compiled, InverterProgram.compiledGateBound]
  rw [inverterBound_gates, inverterBound_ccx]

theorem compiledBound_clifford (rounds n lengthWidth shiftWidth : Nat) :
    (inverterBound rounds n lengthWidth shiftWidth).compiled.clifford =
      InverterProgram.compiledCliffordBound rounds n lengthWidth shiftWidth := by
  simp only [ReversibleBounds.compiled, InverterProgram.compiledCliffordBound]
  rw [inverterBound_gates, inverterBound_ccx]

theorem gateCount_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (InverterProgram.program rounds n lengthWidth shiftWidth).gateCount.hi ≤
      InverterProgram.compiledGateBound rounds n lengthWidth shiftWidth := by
  calc
    _ ≤ (inverterBound rounds n lengthWidth shiftWidth).compiled.inProgram.gates :=
      (programCertificate rounds n lengthWidth shiftWidth).gates_le
    _ = _ := compiledBound_gates rounds n lengthWidth shiftWidth

theorem cliffordCount_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (InverterProgram.program rounds n lengthWidth shiftWidth).cliffordCount.hi ≤
      InverterProgram.compiledCliffordBound rounds n lengthWidth shiftWidth := by
  calc
    _ ≤ (inverterBound rounds n lengthWidth shiftWidth).compiled.inProgram.clifford :=
      (programCertificate rounds n lengthWidth shiftWidth).clifford_le
    _ = _ := compiledBound_clifford rounds n lengthWidth shiftWidth

theorem cnotCount_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (InverterProgram.program rounds n lengthWidth shiftWidth).cnotCount.hi ≤
      InverterProgram.reversibleCxBound rounds n lengthWidth shiftWidth := by
  calc
    _ ≤ (inverterBound rounds n lengthWidth shiftWidth).compiled.inProgram.cnot :=
      (programCertificate rounds n lengthWidth shiftWidth).cnot_le
    _ = _ := inverterBound_cx rounds n lengthWidth shiftWidth

theorem toffoliCount_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (InverterProgram.program rounds n lengthWidth shiftWidth).toffoliCount.hi ≤
      InverterProgram.reversibleCcxBound rounds n lengthWidth shiftWidth := by
  calc
    _ ≤ (inverterBound rounds n lengthWidth shiftWidth).compiled.inProgram.toffoli :=
      (programCertificate rounds n lengthWidth shiftWidth).toffoli_le
    _ = _ := inverterBound_ccx rounds n lengthWidth shiftWidth

theorem depthRange_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (InverterProgram.program rounds n lengthWidth shiftWidth).depthRange.hi ≤
      InverterProgram.compiledGateBound rounds n lengthWidth shiftWidth := by
  calc
    _ ≤ (inverterBound rounds n lengthWidth shiftWidth).compiled.inProgram.depth :=
      (programCertificate rounds n lengthWidth shiftWidth).depth_le
    _ = _ := compiledBound_gates rounds n lengthWidth shiftWidth

theorem toffoliDepthRange_hi_le (rounds n lengthWidth shiftWidth : Nat) :
    (InverterProgram.program rounds n lengthWidth shiftWidth).toffoliDepthRange.hi ≤
      InverterProgram.reversibleCcxBound rounds n lengthWidth shiftWidth := by
  calc
    _ ≤ (inverterBound rounds n lengthWidth shiftWidth).compiled.inProgram.toffoliDepth :=
      (programCertificate rounds n lengthWidth shiftWidth).toffoliDepth_le
    _ = _ := inverterBound_ccx rounds n lengthWidth shiftWidth

end VQ.Euclid.InverterCertificate
