import VQ.Curve.NarrowPackedInputProduct
import VQ.Curve.NarrowPackedRetainedDivision

namespace VQ.Curve.NarrowPackedRetainedMultiplication

open Reversible
open NarrowPackedRetainedDivision (gateOps lowerGates)

def productMeasurementOps : List Op := Lookup.BatchedReconstruction.measureOps 259 0 256

def phaseRepairCircuit : RCircuit :=
  { width := 832, gates := NarrowPackedTerminalProduct.terminalGates }

def phaseRepairOps : List Op :=
  Lookup.BatchedReconstruction.repairAtOps phaseRepairCircuit 0 256

def reconstructionOps : List Op :=
  gateOps NarrowPackedRetainedDivision.preQuotientGates ++ phaseRepairOps ++
    gateOps NarrowPackedRetainedDivision.preQuotientGates.reverse

def postMeasurementOps : List Op :=
  gateOps NarrowPackedRetainedDivision.scheduleGates ++ reconstructionOps ++
    gateOps NarrowPackedRetainedDivision.scheduleGates.reverse

def selectedMultiplicationOps : List Op :=
  gateOps NarrowPackedRetainedDivision.numeratorMoveGates.reverse ++
    gateOps NarrowPackedInputProduct.gates ++ productMeasurementOps ++ postMeasurementOps

def totalMultiplicationOps : List Op :=
  gateOps NarrowPackedRetainedDivision.numeratorMoveGates ++
    gateOps (lowerGates PackedFieldInversion.prepareGates) ++ selectedMultiplicationOps ++
    gateOps (lowerGates PackedFieldInversion.restoreGates) ++
    gateOps NarrowPackedRetainedDivision.quotientMoveGates

def program : Program := { width := 832, cbits := 256, ops := totalMultiplicationOps }

theorem phaseRepair_wellFormed : phaseRepairCircuit.wellFormed = true :=
  NarrowPackedRetainedDivision.widen (by decide)
    NarrowPackedTerminalProduct.terminalGates_wellFormed

theorem selectedMultiplication_wellFormed {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level 832 0 256 selectedMultiplicationOps = true := by
  have hm := Lookup.BatchedReconstruction.measureOps_wellFormed
    (w := 832) (outputOffset := 259) (outputWidth := 256) (bit := 0) (count := 256)
    hl (by decide) (by decide)
  have hp := Lookup.BatchedReconstruction.repairAtOps_wellFormed hl phaseRepair_wellFormed
    (by decide : 0 + 256 ≤ phaseRepairCircuit.width)
  change Program.opsWellFormed level 832 0 256 phaseRepairOps = true at hp
  have hn := NarrowPackedRetainedDivision.numeratorMove_wellFormed
  have hi := NarrowPackedRetainedDivision.widen (by decide) NarrowPackedInputProduct.gates_wellFormed
  have hs := NarrowPackedRetainedDivision.widen (by decide) NarrowPackedRetainedDivision.schedule_wellFormed
  have ht := NarrowPackedRetainedDivision.preQuotient_wellFormed
  have hnr : NarrowPackedRetainedDivision.numeratorMoveGates.reverse.all (RGate.wellFormed 832) = true := by
    simpa only [List.all_reverse] using hn
  have hsr : NarrowPackedRetainedDivision.scheduleGates.reverse.all (RGate.wellFormed 832) = true := by
    simpa only [List.all_reverse] using hs
  have htr : NarrowPackedRetainedDivision.preQuotientGates.reverse.all (RGate.wellFormed 832) = true := by
    simpa only [List.all_reverse] using ht
  simp only [selectedMultiplicationOps, postMeasurementOps, reconstructionOps, productMeasurementOps,
    Program.opsWellFormed_append, gateOps,
    Lookup3.gateOps_wellFormed hl hnr,
    Lookup3.gateOps_wellFormed hl hi,
    Lookup3.gateOps_wellFormed hl hs,
    Lookup3.gateOps_wellFormed hl hsr,
    Lookup3.gateOps_wellFormed hl ht,
    Lookup3.gateOps_wellFormed hl htr,
    hm, hp, Bool.and_self]

end VQ.Curve.NarrowPackedRetainedMultiplication
