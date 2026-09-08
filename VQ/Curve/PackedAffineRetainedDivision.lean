import VQ.Curve.PackedAffineProduct
import VQ.Curve.PackedAffineTerminal
import VQ.Curve.PackedAffineTerminalProduct
import VQ.Curve.PackedFieldInversion
import VQ.Euclid.PackedInputPreparation
import VQ.Lookup.BatchedReconstruction
import VQ.Reversible.Constant

namespace VQ.Curve.PackedAffineRetainedDivision

open Reversible Semantics

def modulusGates : List RGate :=
  constantXorGates Curve.p Euclid.PackedStepLayout.workOneOffset 256

def relocationGates : List RGate :=
  copyField Euclid.PackedStepLayout.workOneOffset
      PackedAffineLayout.inverseOffset 256 ++
    copyField PackedAffineLayout.inverseOffset
      Euclid.PackedStepLayout.workOneOffset 256

def gateOps (gates : List RGate) : List Op := Lookup3.gateOps gates

def preQuotientGates : List RGate :=
  PackedAffineTerminal.gates ++ modulusGates

def cleanupGates : List RGate :=
  relocationGates ++ modulusGates ++ PackedAffineTerminal.gates.reverse

def terminalOps : List Op :=
  gateOps preQuotientGates ++
    gateOps PackedAffineTerminalProduct.terminalGates ++
    Lookup.BatchedReconstruction.measureOps
      PackedAffineLayout.inverseOffset 0 256 ++
    gateOps cleanupGates

def terminalProgram : Program :=
  { width := PackedAffineLayout.width
    cbits := 256
    ops := terminalOps }

def reversalGates : List RGate :=
  (Euclid.LuoWindowedOwnership.roundsGates 1620).reverse ++
    (Euclid.PackedInputPreparation.gates Curve.p).reverse

def phaseRepairOps : List Op :=
  Lookup.BatchedReconstruction.repairAtOps
    PackedAffineProduct.circuit PackedAffineProduct.targetOffset 256

def postForwardOps : List Op :=
  terminalOps ++
    (gateOps reversalGates ++ phaseRepairOps)

def numeratorMoveGates : List RGate :=
  copyField Euclid.PackedStepLayout.workTwoOffset
      PackedAffineLayout.inverseOffset 256 ++
    copyField PackedAffineLayout.inverseOffset
      Euclid.PackedStepLayout.workTwoOffset 256

def quotientMoveGates : List RGate :=
  copyField PackedAffineLayout.inverseOffset
      Euclid.PackedStepLayout.workTwoOffset 256 ++
    copyField Euclid.PackedStepLayout.workTwoOffset
      PackedAffineLayout.inverseOffset 256

def scheduleGates : List RGate :=
  Euclid.PackedInputPreparation.gates Curve.p ++
    Euclid.LuoWindowedOwnership.roundsGates 1620

def selectedDivisionOps : List Op :=
  gateOps scheduleGates ++ postForwardOps

def forwardGates : List RGate :=
  numeratorMoveGates ++ scheduleGates

def positiveDivisionOps : List Op :=
  gateOps forwardGates ++
    postForwardOps ++
    gateOps quotientMoveGates

def positiveDivisionProgram : Program :=
  { width := PackedAffineLayout.width
    cbits := 256
    ops := positiveDivisionOps }

def totalDivisionOps : List Op :=
  gateOps numeratorMoveGates ++
    gateOps PackedFieldInversion.prepareGates ++
    selectedDivisionOps ++
    gateOps PackedFieldInversion.restoreGates ++
    gateOps quotientMoveGates

def totalDivisionProgram : Program :=
  { width := PackedAffineLayout.width
    cbits := 256
    ops := totalDivisionOps }

theorem modulusGates_wellFormed :
    modulusGates.all (RGate.wellFormed PackedAffineLayout.width) = true := by
  exact constantXorGates_wellFormed (by decide)

theorem relocationGates_wellFormed :
    relocationGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp only [relocationGates, List.all_append, Bool.and_eq_true]
  exact ⟨copyFieldBlock_wf (Or.inl (by decide)) (by decide) (by decide),
    copyFieldBlock_wf (Or.inr (by decide)) (by decide) (by decide)⟩

theorem preQuotientGates_wellFormed :
    preQuotientGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  rw [preQuotientGates, List.all_append,
    PackedAffineTerminal.gates_wellFormed, modulusGates_wellFormed]
  rfl

theorem cleanupGates_wellFormed :
    cleanupGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  rw [cleanupGates, List.all_append, List.all_append,
    relocationGates_wellFormed, modulusGates_wellFormed,
    PackedAffineTerminal.reverseGates_wellFormed]
  rfl

theorem reversalGates_wellFormed :
    reversalGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  apply List.all_eq_true.mpr
  intro gate hgate
  rw [reversalGates, List.mem_append] at hgate
  rcases hgate with hround | hpreparation
  · apply RGate.wellFormed_mono
      (w := Euclid.PackedStepLayout.width) (by decide)
    exact List.all_eq_true.mp
      (Euclid.LuoWindowedOwnership.roundsGates_wellFormed (by decide : 1620 ≤ 1620)) gate
        (List.mem_reverse.mp hround)
  · apply RGate.wellFormed_mono
      (w := Euclid.PackedStepLayout.width) (by decide)
    exact List.all_eq_true.mp
      (Euclid.PackedInputPreparation.gates_wellFormed Curve.p) gate
        (List.mem_reverse.mp hpreparation)

theorem numeratorMoveGates_wellFormed :
    numeratorMoveGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp only [numeratorMoveGates, List.all_append, Bool.and_eq_true]
  exact ⟨copyFieldBlock_wf (Or.inl (by decide)) (by decide) (by decide),
    copyFieldBlock_wf (Or.inr (by decide)) (by decide) (by decide)⟩

theorem quotientMoveGates_wellFormed :
    quotientMoveGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp only [quotientMoveGates, List.all_append, Bool.and_eq_true]
  exact ⟨copyFieldBlock_wf (Or.inr (by decide)) (by decide) (by decide),
    copyFieldBlock_wf (Or.inl (by decide)) (by decide) (by decide)⟩

theorem numeratorMoveGates_wellFormed_core :
    numeratorMoveGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  simp only [numeratorMoveGates, List.all_append, Bool.and_eq_true]
  exact ⟨copyFieldBlock_wf (Or.inl (by decide)) (by decide) (by decide),
    copyFieldBlock_wf (Or.inr (by decide)) (by decide) (by decide)⟩

theorem quotientMoveGates_wellFormed_core :
    quotientMoveGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  simp only [quotientMoveGates, List.all_append, Bool.and_eq_true]
  exact ⟨copyFieldBlock_wf (Or.inr (by decide)) (by decide) (by decide),
    copyFieldBlock_wf (Or.inl (by decide)) (by decide) (by decide)⟩

private theorem allWellFormed_mono
    {gates : List RGate} {width largerWidth : Nat}
    (hwidth : width ≤ largerWidth)
    (hwellFormed : gates.all (RGate.wellFormed width) = true) :
    gates.all (RGate.wellFormed largerWidth) = true := by
  apply List.all_eq_true.mpr
  intro gate hgate
  exact RGate.wellFormed_mono hwidth
    (List.all_eq_true.mp hwellFormed gate hgate)

theorem forwardGates_wellFormed :
    forwardGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true := by
  simp only [forwardGates, scheduleGates, List.all_append, Bool.and_eq_true]
  exact ⟨numeratorMoveGates_wellFormed,
    ⟨allWellFormed_mono (by decide)
      (Euclid.PackedInputPreparation.gates_wellFormed Curve.p),
      allWellFormed_mono (by decide)
        (Euclid.LuoWindowedOwnership.roundsGates_wellFormed (by decide : 1620 ≤ 1620))⟩⟩

theorem scheduleGates_wellFormed_core :
    scheduleGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  simp only [scheduleGates, List.all_append, Bool.and_eq_true]
  exact ⟨allWellFormed_mono (by decide)
      (Euclid.PackedInputPreparation.gates_wellFormed Curve.p),
    allWellFormed_mono (by decide)
      (Euclid.LuoWindowedOwnership.roundsGates_wellFormed (by decide : 1620 ≤ 1620))⟩

theorem scheduleGates_wellFormed :
    scheduleGates.all
      (RGate.wellFormed PackedAffineLayout.width) = true :=
  allWellFormed_mono (by decide) scheduleGates_wellFormed_core

private theorem modulusGates_wellFormed_core :
    modulusGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  exact constantXorGates_wellFormed (by decide)

private theorem relocationGates_wellFormed_core :
    relocationGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  simp only [relocationGates, List.all_append, Bool.and_eq_true]
  exact ⟨copyFieldBlock_wf (Or.inl (by decide)) (by decide) (by decide),
    copyFieldBlock_wf (Or.inr (by decide)) (by decide) (by decide)⟩

private theorem preQuotientGates_wellFormed_core :
    preQuotientGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  rw [preQuotientGates, List.all_append,
    PackedAffineTerminal.gates_wellFormed_core,
    modulusGates_wellFormed_core]
  rfl

private theorem cleanupGates_wellFormed_core :
    cleanupGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  rw [cleanupGates, List.all_append, List.all_append,
    relocationGates_wellFormed_core, modulusGates_wellFormed_core,
    PackedAffineTerminal.reverseGates_wellFormed_core]
  rfl

private theorem reversalGates_wellFormed_core :
    reversalGates.all
      (RGate.wellFormed PackedAffineLayout.auxiliaryOffset) = true := by
  apply List.all_eq_true.mpr
  intro gate hgate
  rw [reversalGates, List.mem_append] at hgate
  rcases hgate with hround | hpreparation
  · apply RGate.wellFormed_mono
      (w := Euclid.PackedStepLayout.width) (by decide)
    exact List.all_eq_true.mp
      (Euclid.LuoWindowedOwnership.roundsGates_wellFormed (by decide : 1620 ≤ 1620)) gate
        (List.mem_reverse.mp hround)
  · apply RGate.wellFormed_mono
      (w := Euclid.PackedStepLayout.width) (by decide)
    exact List.all_eq_true.mp
      (Euclid.PackedInputPreparation.gates_wellFormed Curve.p) gate
        (List.mem_reverse.mp hpreparation)

private theorem phaseRepairOps_wellFormed_core
    {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level PackedAffineLayout.auxiliaryOffset 0 256
      phaseRepairOps = true := by
  have hcore := Lookup.BatchedReconstruction.repairAtOps_wellFormed
    (level := level) (r := PackedAffineProduct.coreCircuit)
    (phaseOffset := PackedAffineProduct.targetOffset) (outputWidth := 256)
    hl PackedAffineProduct.coreCircuit_wellFormed (by decide)
  simpa [phaseRepairOps, PackedAffineProduct.coreCircuit,
    PackedAffineProduct.circuit,
    Lookup.BatchedReconstruction.repairAtOps,
    Lookup.MeasuredUncompute.circuitOps] using hcore

theorem selectedDivisionOps_wellFormed_core
    {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level PackedAffineLayout.auxiliaryOffset 0 256
      selectedDivisionOps = true := by
  simp only [selectedDivisionOps, postForwardOps, terminalOps, gateOps,
    Program.opsWellFormed_append]
  rw [Lookup3.gateOps_wellFormed hl scheduleGates_wellFormed_core,
    Lookup3.gateOps_wellFormed hl preQuotientGates_wellFormed_core,
    Lookup3.gateOps_wellFormed hl
      PackedAffineTerminalProduct.terminalGates_wellFormed_core,
    Lookup.BatchedReconstruction.measureOps_wellFormed
      (outputWidth := 256) hl (by decide) (by omega),
    Lookup3.gateOps_wellFormed hl cleanupGates_wellFormed_core,
    Lookup3.gateOps_wellFormed hl reversalGates_wellFormed_core,
    phaseRepairOps_wellFormed_core hl]
  decide

theorem totalDivisionProgram_wellFormed
    {level : Nat} (hl : 3 ≤ level) :
    totalDivisionProgram.wellFormed level = true := by
  have hselected := Program.opsWellFormed_relabel
    (f := id) (totalWidth := PackedAffineLayout.width)
    (fun _ hq => hq.trans (by decide))
    (fun _ _ _ _ hxy => hxy)
    (selectedDivisionOps_wellFormed_core hl)
  simp only [Op.relabelAll_id] at hselected
  simp only [Program.wellFormed, totalDivisionProgram, totalDivisionOps,
    gateOps,
    Program.opsWellFormed_append]
  rw [Lookup3.gateOps_wellFormed hl numeratorMoveGates_wellFormed,
    Lookup3.gateOps_wellFormed hl
      PackedFieldInversion.prepareGates_wellFormed,
    hselected,
    Lookup3.gateOps_wellFormed hl
      PackedFieldInversion.restoreGates_wellFormed,
    Lookup3.gateOps_wellFormed hl quotientMoveGates_wellFormed]
  decide

end VQ.Curve.PackedAffineRetainedDivision
