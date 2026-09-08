import VQ.Curve.NarrowPackedRetainedMultiplication

namespace VQ.Curve.NarrowPackedArithmeticBounds

open Reversible

private theorem widen {w : Nat} {gs : List RGate} (h : w ≤ 826)
    (hw : gs.all (RGate.wellFormed w) = true) : gs.all (RGate.wellFormed 826) = true :=
  List.all_eq_true.mpr (fun g hg => RGate.wellFormed_mono h (List.all_eq_true.mp hw g hg))

theorem schedule : NarrowPackedRetainedDivision.scheduleGates.all (RGate.wellFormed 826) = true :=
  widen (by decide) NarrowPackedRetainedDivision.schedule_wellFormed

theorem numeratorMove : NarrowPackedRetainedDivision.numeratorMoveGates.all (RGate.wellFormed 826) = true :=
  RemoveBorrowedBit.gates_wellFormed (by decide)
    PackedAffineRetainedDivision.numeratorMoveGates_wellFormed_core
    NarrowPackedRetainedDivision.numeratorMove_avoids

theorem quotientMove : NarrowPackedRetainedDivision.quotientMoveGates.all (RGate.wellFormed 826) = true :=
  RemoveBorrowedBit.gates_wellFormed (by decide)
    PackedAffineRetainedDivision.quotientMoveGates_wellFormed_core
    NarrowPackedRetainedDivision.quotientMove_avoids

theorem preQuotient : NarrowPackedRetainedDivision.preQuotientGates.all (RGate.wellFormed 826) = true := by
  simp only [NarrowPackedRetainedDivision.preQuotientGates, List.all_append,
    widen (by decide) NarrowPackedRetainedDivision.terminal_wellFormed,
    widen (by decide) NarrowPackedRetainedDivision.modulus_below, Bool.and_self]

theorem cleanup : NarrowPackedRetainedDivision.cleanupGates.all (RGate.wellFormed 826) = true := by
  have ho : PackedAffineRetainedDivision.relocationGates.all (RGate.wellFormed 827) = true := by
    simp only [PackedAffineRetainedDivision.relocationGates, List.all_append, Bool.and_eq_true]
    exact ⟨copyFieldBlock_wf (Or.inl (by decide)) (by decide) (by decide),
      copyFieldBlock_wf (Or.inr (by decide)) (by decide) (by decide)⟩
  have hr : (NarrowPackedRetainedDivision.lowerGates PackedAffineRetainedDivision.relocationGates).all
      (RGate.wellFormed 826) = true := RemoveBorrowedBit.gates_wellFormed (by decide) ho
        NarrowPackedRetainedDivision.relocation_avoids
  simp only [NarrowPackedRetainedDivision.cleanupGates, List.all_append, List.all_reverse, hr,
    widen (by decide) NarrowPackedRetainedDivision.terminal_wellFormed,
    widen (by decide) NarrowPackedRetainedDivision.modulus_below, Bool.and_self]

def divisionRepairCircuit : RCircuit :=
  { width := 826, gates := NarrowPackedRetainedDivision.lowerGates PackedAffineProduct.gates }

theorem divisionRepairCircuit_wellFormed : divisionRepairCircuit.wellFormed = true := by
  simp only [divisionRepairCircuit, RCircuit.wellFormed, NarrowPackedRetainedDivision.lowerGates]
  exact RemoveBorrowedBit.gates_wellFormed (by decide) PackedAffineProduct.gates_wellFormed_core
    NarrowPackedOperands.product

theorem divisionRepair {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level 826 0 256 NarrowPackedRetainedDivision.phaseRepairOps = true := by
  have h := Lookup.BatchedReconstruction.repairAtOps_wellFormed hl divisionRepairCircuit_wellFormed
    (by decide : 259 + 256 ≤ divisionRepairCircuit.width)
  simpa only [divisionRepairCircuit, NarrowPackedRetainedDivision.phaseRepairOps,
    NarrowPackedRetainedDivision.productCircuit, Lookup.BatchedReconstruction.repairAtOps,
    Lookup.MeasuredUncompute.circuitOps, RCircuit.reverse] using h

def multiplicationRepairCircuit : RCircuit :=
  { width := 826, gates := NarrowPackedTerminalProduct.terminalGates }

theorem multiplicationRepairCircuit_wellFormed : multiplicationRepairCircuit.wellFormed = true :=
  NarrowPackedTerminalProduct.terminalGates_wellFormed

theorem multiplicationRepair {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level 826 0 256 NarrowPackedRetainedMultiplication.phaseRepairOps = true := by
  have h := Lookup.BatchedReconstruction.repairAtOps_wellFormed hl multiplicationRepairCircuit_wellFormed
    (by decide : 0 + 256 ≤ multiplicationRepairCircuit.width)
  simpa only [multiplicationRepairCircuit, NarrowPackedRetainedMultiplication.phaseRepairOps,
    NarrowPackedRetainedMultiplication.phaseRepairCircuit, Lookup.BatchedReconstruction.repairAtOps,
    Lookup.MeasuredUncompute.circuitOps, RCircuit.reverse] using h

theorem selectedDivision {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level 826 0 256 NarrowPackedRetainedDivision.selectedDivisionOps = true := by
  have hsr : NarrowPackedRetainedDivision.scheduleGates.reverse.all (RGate.wellFormed 826) = true := by
    simpa only [List.all_reverse] using schedule
  have hm := Lookup.BatchedReconstruction.measureOps_wellFormed
    (w := 826) (outputOffset := 570) (outputWidth := 256) (bit := 0) (count := 256)
    hl (by decide) (by decide)
  simp only [NarrowPackedRetainedDivision.selectedDivisionOps, NarrowPackedRetainedDivision.postForwardOps,
    NarrowPackedRetainedDivision.terminalOps, NarrowPackedRetainedDivision.gateOps,
    Program.opsWellFormed_append, Lookup3.gateOps_wellFormed hl schedule,
    Lookup3.gateOps_wellFormed hl preQuotient,
    Lookup3.gateOps_wellFormed hl NarrowPackedTerminalProduct.terminalGates_wellFormed,
    hm, Lookup3.gateOps_wellFormed hl cleanup, Lookup3.gateOps_wellFormed hl hsr,
    divisionRepair hl, Bool.and_self]

theorem selectedMultiplication {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level 826 0 256 NarrowPackedRetainedMultiplication.selectedMultiplicationOps = true := by
  have hnr : NarrowPackedRetainedDivision.numeratorMoveGates.reverse.all (RGate.wellFormed 826) = true := by
    simpa only [List.all_reverse] using numeratorMove
  have hsr : NarrowPackedRetainedDivision.scheduleGates.reverse.all (RGate.wellFormed 826) = true := by
    simpa only [List.all_reverse] using schedule
  have htr : NarrowPackedRetainedDivision.preQuotientGates.reverse.all (RGate.wellFormed 826) = true := by
    simpa only [List.all_reverse] using preQuotient
  have hm := Lookup.BatchedReconstruction.measureOps_wellFormed
    (w := 826) (outputOffset := 259) (outputWidth := 256) (bit := 0) (count := 256)
    hl (by decide) (by decide)
  simp only [NarrowPackedRetainedMultiplication.selectedMultiplicationOps,
    NarrowPackedRetainedMultiplication.postMeasurementOps, NarrowPackedRetainedMultiplication.reconstructionOps,
    NarrowPackedRetainedMultiplication.productMeasurementOps, NarrowPackedRetainedDivision.gateOps,
    Program.opsWellFormed_append, Lookup3.gateOps_wellFormed hl hnr,
    Lookup3.gateOps_wellFormed hl NarrowPackedInputProduct.gates_wellFormed,
    hm, Lookup3.gateOps_wellFormed hl schedule, Lookup3.gateOps_wellFormed hl preQuotient,
    multiplicationRepair hl, Lookup3.gateOps_wellFormed hl htr,
    Lookup3.gateOps_wellFormed hl hsr, Bool.and_self]

end VQ.Curve.NarrowPackedArithmeticBounds
