import VQ.Curve.PackedAffineInputProduct
import VQ.Curve.PackedAffineRetainedDivision

namespace VQ.Curve.PackedAffineRetainedMultiplication

open Reversible Semantics

def gateOps (gates : List RGate) : List Op := Lookup3.gateOps gates

def productMeasurementOps : List Op :=
  Lookup.BatchedReconstruction.measureOps
    Euclid.PackedStepLayout.workTwoOffset 0 256

def phaseRepairOps : List Op :=
  Lookup.BatchedReconstruction.repairAtOps
    PackedAffineTerminalProduct.terminalCircuit
    PackedAffineTerminalProduct.targetOffset 256

def reconstructionOps : List Op :=
  gateOps PackedAffineRetainedDivision.preQuotientGates ++
    phaseRepairOps ++
    gateOps PackedAffineRetainedDivision.preQuotientGates.reverse

def postMeasurementOps : List Op :=
  gateOps PackedAffineRetainedDivision.scheduleGates ++
    reconstructionOps ++
    gateOps PackedAffineRetainedDivision.scheduleGates.reverse

def selectedMultiplicationOps : List Op :=
  gateOps PackedAffineRetainedDivision.numeratorMoveGates.reverse ++
    gateOps PackedAffineInputProduct.gates ++
    productMeasurementOps ++
    postMeasurementOps

def totalMultiplicationOps : List Op :=
  gateOps PackedAffineRetainedDivision.numeratorMoveGates ++
    gateOps PackedFieldInversion.prepareGates ++
    selectedMultiplicationOps ++
    gateOps PackedFieldInversion.restoreGates ++
    gateOps PackedAffineRetainedDivision.quotientMoveGates

def totalMultiplicationProgram : Program :=
  { width := PackedAffineLayout.width
    cbits := 256
    ops := totalMultiplicationOps }

def phaseRepairCoreCircuit : RCircuit :=
  { width := PackedAffineLayout.auxiliaryOffset
    gates := PackedAffineTerminalProduct.terminalGates }

theorem phaseRepairCoreCircuit_wellFormed :
    phaseRepairCoreCircuit.wellFormed = true := by
  simpa only [phaseRepairCoreCircuit, RCircuit.wellFormed] using
    PackedAffineTerminalProduct.terminalGates_wellFormed_core

private theorem preQuotientGates_wellFormed_core :
    PackedAffineRetainedDivision.preQuotientGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  simp only [PackedAffineRetainedDivision.preQuotientGates,
    List.all_append, Bool.and_eq_true]
  exact ⟨PackedAffineTerminal.gates_wellFormed_core,
    constantXorGates_wellFormed (by decide)⟩

private theorem phaseRepairOps_wellFormed_core
    {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level PackedAffineLayout.auxiliaryOffset 0 256
      phaseRepairOps = true := by
  have hcore := Lookup.BatchedReconstruction.repairAtOps_wellFormed
    (level := level) (r := phaseRepairCoreCircuit)
    (phaseOffset := PackedAffineTerminalProduct.targetOffset)
    (outputWidth := 256) hl phaseRepairCoreCircuit_wellFormed (by decide)
  simpa [phaseRepairOps, phaseRepairCoreCircuit,
    PackedAffineTerminalProduct.terminalCircuit,
    Lookup.BatchedReconstruction.repairAtOps,
    Lookup.MeasuredUncompute.circuitOps] using hcore

private theorem reconstructionOps_wellFormed_core
    {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level PackedAffineLayout.auxiliaryOffset 0 256
      reconstructionOps = true := by
  simp only [reconstructionOps, gateOps, Program.opsWellFormed_append]
  rw [Lookup3.gateOps_wellFormed hl preQuotientGates_wellFormed_core,
    phaseRepairOps_wellFormed_core hl,
    Lookup3.gateOps_wellFormed hl (by
      simpa only [List.all_reverse] using
        preQuotientGates_wellFormed_core)]
  decide

private theorem postMeasurementOps_wellFormed_core
    {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level PackedAffineLayout.auxiliaryOffset 0 256
      postMeasurementOps = true := by
  simp only [postMeasurementOps, gateOps, Program.opsWellFormed_append]
  rw [Lookup3.gateOps_wellFormed hl
      PackedAffineRetainedDivision.scheduleGates_wellFormed_core,
    reconstructionOps_wellFormed_core hl,
    Lookup3.gateOps_wellFormed hl (by
      simpa only [List.all_reverse] using
        PackedAffineRetainedDivision.scheduleGates_wellFormed_core)]
  decide

theorem selectedMultiplicationOps_wellFormed_core
    {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level PackedAffineLayout.auxiliaryOffset 0 256
      selectedMultiplicationOps = true := by
  simp only [selectedMultiplicationOps, gateOps, productMeasurementOps,
    Program.opsWellFormed_append]
  rw [Lookup3.gateOps_wellFormed hl (by
      simpa only [List.all_reverse] using
        PackedAffineRetainedDivision.numeratorMoveGates_wellFormed_core),
    Lookup3.gateOps_wellFormed hl
      PackedAffineInputProduct.gates_wellFormed_core,
    Lookup.BatchedReconstruction.measureOps_wellFormed
      (outputWidth := 256) hl (by decide) (by omega),
    postMeasurementOps_wellFormed_core hl]
  decide

theorem totalMultiplicationProgram_wellFormed
    {level : Nat} (hl : 3 ≤ level) :
    totalMultiplicationProgram.wellFormed level = true := by
  have hselected := Program.opsWellFormed_relabel
    (f := id) (totalWidth := PackedAffineLayout.width)
    (fun _ hq => hq.trans (by decide))
    (fun _ _ _ _ hxy => hxy)
    (selectedMultiplicationOps_wellFormed_core hl)
  simp only [Op.relabelAll_id] at hselected
  simp only [Program.wellFormed, totalMultiplicationProgram,
    totalMultiplicationOps, gateOps, Program.opsWellFormed_append]
  rw [Lookup3.gateOps_wellFormed hl
      PackedAffineRetainedDivision.numeratorMoveGates_wellFormed,
    Lookup3.gateOps_wellFormed hl PackedFieldInversion.prepareGates_wellFormed,
    hselected,
    Lookup3.gateOps_wellFormed hl PackedFieldInversion.restoreGates_wellFormed,
    Lookup3.gateOps_wellFormed hl
      PackedAffineRetainedDivision.quotientMoveGates_wellFormed]
  decide

end VQ.Curve.PackedAffineRetainedMultiplication
