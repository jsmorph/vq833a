import VQ.Curve.PackedAffineRetainedDivision
import VQ.Curve.NarrowPackedTerminalProduct
import VQ.Curve.NarrowPackedOperands
import VQ.Euclid.BorrowedPreparedSchedule
import VQ.Euclid.NarrowPackedTerminal

namespace VQ.Curve.NarrowPackedRetainedDivision

open Reversible

def lowerGates (gs : List RGate) : List RGate :=
  gs.map (RGate.map (RemoveBorrowedBit.lower 570))

def scheduleGates : List RGate := Euclid.BorrowedPreparedSchedule.gates

def terminalGates : List RGate :=
  Euclid.NarrowPackedTerminal.preparationGates ++ PackedAffineTerminal.signGates

def preQuotientGates : List RGate := terminalGates ++ PackedAffineRetainedDivision.modulusGates

def cleanupGates : List RGate :=
  lowerGates PackedAffineRetainedDivision.relocationGates ++
    PackedAffineRetainedDivision.modulusGates ++ terminalGates.reverse

def numeratorMoveGates : List RGate := lowerGates PackedAffineRetainedDivision.numeratorMoveGates

def quotientMoveGates : List RGate := lowerGates PackedAffineRetainedDivision.quotientMoveGates

def productCircuit : RCircuit := { width := 832, gates := lowerGates PackedAffineProduct.gates }

def gateOps (gs : List RGate) : List Op := Lookup3.gateOps gs

def terminalOps : List Op :=
  gateOps preQuotientGates ++ gateOps NarrowPackedTerminalProduct.terminalGates ++
    Lookup.BatchedReconstruction.measureOps 570 0 256 ++ gateOps cleanupGates

def phaseRepairOps : List Op := Lookup.BatchedReconstruction.repairAtOps productCircuit 259 256

def postForwardOps : List Op := terminalOps ++ (gateOps scheduleGates.reverse ++ phaseRepairOps)

def selectedDivisionOps : List Op := gateOps scheduleGates ++ postForwardOps

def totalDivisionOps : List Op :=
  gateOps numeratorMoveGates ++ gateOps (lowerGates PackedFieldInversion.prepareGates) ++
    selectedDivisionOps ++ gateOps (lowerGates PackedFieldInversion.restoreGates) ++
    gateOps quotientMoveGates

def program : Program := { width := 832, cbits := 256, ops := totalDivisionOps }

theorem oldSchedule_wellFormed :
    PackedAffineRetainedDivision.scheduleGates.all (RGate.wellFormed 571) = true := by
  have hp : (Euclid.PackedInputPreparation.gates p).all (RGate.wellFormed 571) = true :=
    Euclid.PackedInputPreparation.gates_wellFormed p
  have hr : (Euclid.LuoWindowedOwnership.roundsGates 1620).all (RGate.wellFormed 571) = true :=
    Euclid.LuoWindowedOwnership.roundsGates_wellFormed (by decide)
  simp only [PackedAffineRetainedDivision.scheduleGates, List.all_append,
    hp, hr, Bool.and_self]

theorem schedule_wellFormed : scheduleGates.all (RGate.wellFormed 571) = true :=
  Euclid.BorrowedPreparedSchedule.gates_wellFormed

theorem schedule_equiv :
    RemoveBorrowedBit.Equivalent 570 PackedAffineRetainedDivision.scheduleGates scheduleGates :=
  RemoveBorrowedBit.borrowed_core Euclid.BorrowedPreparedSchedule.gates_equiv
    oldSchedule_wellFormed schedule_wellFormed

theorem schedule_reverse_equiv :
    RemoveBorrowedBit.Equivalent 570 PackedAffineRetainedDivision.reversalGates scheduleGates.reverse := by
  simpa only [PackedAffineRetainedDivision.scheduleGates, List.reverse_append,
    PackedAffineRetainedDivision.reversalGates] using
    RemoveBorrowedBit.reverse schedule_equiv oldSchedule_wellFormed schedule_wellFormed

theorem sign_below : PackedAffineTerminal.signGates.all (RGate.wellFormed 570) = true := by
  native_decide

theorem terminal_wellFormed : terminalGates.all (RGate.wellFormed 571) = true := by
  have hs : PackedAffineTerminal.signGates.all (RGate.wellFormed 571) = true :=
    List.all_eq_true.mpr (fun g hg => RGate.wellFormed_mono (by decide)
      (List.all_eq_true.mp sign_below g hg))
  simp only [terminalGates, List.all_append, Euclid.NarrowPackedTerminal.preparationGates_below,
    hs, Bool.and_self]

theorem oldTerminal_wellFormed : PackedAffineTerminal.gates.all (RGate.wellFormed 571) = true := by
  have hs : PackedAffineTerminal.signGates.all (RGate.wellFormed 571) = true :=
    List.all_eq_true.mpr (fun g hg => RGate.wellFormed_mono (by decide)
      (List.all_eq_true.mp sign_below g hg))
  have hp : PackedAffineTerminal.preparationGates.all (RGate.wellFormed 571) = true :=
    Euclid.NarrowPackedTerminal.oldPreparation_below
  simp only [PackedAffineTerminal.gates, List.all_append, hp, hs, Bool.and_self]

theorem terminal_equiv :
    RemoveBorrowedBit.Equivalent 570 PackedAffineTerminal.gates terminalGates :=
  RemoveBorrowedBit.borrowed_core
    (Euclid.NarrowPackedTerminal.preparationGates_borrowed.append
      (BorrowedEquivalent.of_below (fun g hg _ hk =>
        wire_lt_of_wellFormed (List.all_eq_true.mp sign_below g hg) hk)))
    oldTerminal_wellFormed terminal_wellFormed

theorem modulus_below :
    PackedAffineRetainedDivision.modulusGates.all (RGate.wellFormed 570) = true :=
  constantXorGates_wellFormed (by decide)

theorem modulus_equiv : RemoveBorrowedBit.Equivalent 570
    PackedAffineRetainedDivision.modulusGates PackedAffineRetainedDivision.modulusGates := by
  have hw : PackedAffineRetainedDivision.modulusGates.all (RGate.wellFormed 571) = true :=
    List.all_eq_true.mpr (fun g hg => RGate.wellFormed_mono (by decide)
      (List.all_eq_true.mp modulus_below g hg))
  exact RemoveBorrowedBit.borrowed_core
    (BorrowedEquivalent.of_below (fun g hg _ hk =>
      wire_lt_of_wellFormed (List.all_eq_true.mp modulus_below g hg) hk)) hw hw

theorem preQuotient_equiv : RemoveBorrowedBit.Equivalent 570
    PackedAffineRetainedDivision.preQuotientGates preQuotientGates :=
  RemoveBorrowedBit.append terminal_equiv modulus_equiv

theorem relocation_avoids : NarrowPackedOperands.Avoids PackedAffineRetainedDivision.relocationGates := by
  have h : PackedAffineRetainedDivision.relocationGates.all
      (fun g => decide (570 ∉ g.wires)) = true := by native_decide
  exact fun g hg => of_decide_eq_true (List.all_eq_true.mp h g hg)

theorem cleanup_equiv : RemoveBorrowedBit.Equivalent 570
    PackedAffineRetainedDivision.cleanupGates cleanupGates :=
  RemoveBorrowedBit.append
    (RemoveBorrowedBit.append (NarrowPackedOperands.equivalent relocation_avoids) modulus_equiv)
    (RemoveBorrowedBit.reverse terminal_equiv oldTerminal_wellFormed terminal_wellFormed)

theorem numeratorMove_avoids : NarrowPackedOperands.Avoids PackedAffineRetainedDivision.numeratorMoveGates := by
  have h : PackedAffineRetainedDivision.numeratorMoveGates.all
      (fun g => decide (570 ∉ g.wires)) = true := by native_decide
  exact fun g hg => of_decide_eq_true (List.all_eq_true.mp h g hg)

theorem quotientMove_avoids : NarrowPackedOperands.Avoids PackedAffineRetainedDivision.quotientMoveGates := by
  have h : PackedAffineRetainedDivision.quotientMoveGates.all
      (fun g => decide (570 ∉ g.wires)) = true := by native_decide
  exact fun g hg => of_decide_eq_true (List.all_eq_true.mp h g hg)

theorem widen {w : Nat} {gs : List RGate} (h : w ≤ 832)
    (hw : gs.all (RGate.wellFormed w) = true) : gs.all (RGate.wellFormed 832) = true :=
  List.all_eq_true.mpr (fun g hg => RGate.wellFormed_mono h (List.all_eq_true.mp hw g hg))

theorem preQuotient_wellFormed : preQuotientGates.all (RGate.wellFormed 832) = true := by
  simp only [preQuotientGates, List.all_append,
    widen (by decide) terminal_wellFormed, widen (by decide) modulus_below, Bool.and_self]

theorem cleanup_wellFormed : cleanupGates.all (RGate.wellFormed 832) = true := by
  have hr : (lowerGates PackedAffineRetainedDivision.relocationGates).all
      (RGate.wellFormed 832) = true := NarrowPackedOperands.wellFormed relocation_avoids
        PackedAffineRetainedDivision.relocationGates_wellFormed
  simp only [cleanupGates, List.all_append, List.all_reverse, hr,
    widen (by decide) terminal_wellFormed, widen (by decide) modulus_below, Bool.and_self]

theorem numeratorMove_wellFormed : numeratorMoveGates.all (RGate.wellFormed 832) = true :=
  NarrowPackedOperands.wellFormed numeratorMove_avoids PackedAffineRetainedDivision.numeratorMoveGates_wellFormed

theorem quotientMove_wellFormed : quotientMoveGates.all (RGate.wellFormed 832) = true :=
  NarrowPackedOperands.wellFormed quotientMove_avoids PackedAffineRetainedDivision.quotientMoveGates_wellFormed

theorem product_wellFormed : productCircuit.wellFormed = true := by
  simp only [RCircuit.wellFormed, productCircuit, lowerGates]
  exact NarrowPackedOperands.wellFormed NarrowPackedOperands.product PackedAffineProduct.gates_wellFormed

theorem terminalOps_wellFormed {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level 832 0 256 terminalOps = true := by
  have hm := Lookup.BatchedReconstruction.measureOps_wellFormed
    (w := 832) (outputOffset := 570) (outputWidth := 256) (bit := 0) (count := 256)
    hl (by decide) (by decide)
  simp only [terminalOps, Program.opsWellFormed_append, gateOps,
    Lookup3.gateOps_wellFormed hl preQuotient_wellFormed,
    Lookup3.gateOps_wellFormed hl (widen (by decide) NarrowPackedTerminalProduct.terminalGates_wellFormed),
    hm, Lookup3.gateOps_wellFormed hl cleanup_wellFormed, Bool.and_self]

theorem program_wellFormed {level : Nat} (hl : 3 ≤ level) : program.wellFormed level = true := by
  have hs := widen (by decide) schedule_wellFormed
  have hsr : scheduleGates.reverse.all (RGate.wellFormed 832) = true := by
    simpa only [List.all_reverse] using hs
  have hp : (lowerGates PackedFieldInversion.prepareGates).all (RGate.wellFormed 832) = true :=
    NarrowPackedOperands.wellFormed NarrowPackedOperands.prepare PackedFieldInversion.prepareGates_wellFormed
  have hr : (lowerGates PackedFieldInversion.restoreGates).all (RGate.wellFormed 832) = true :=
    NarrowPackedOperands.wellFormed NarrowPackedOperands.restore PackedFieldInversion.restoreGates_wellFormed
  have hphase := Lookup.BatchedReconstruction.repairAtOps_wellFormed hl product_wellFormed
    (by decide : 259 + 256 ≤ productCircuit.width)
  change Program.opsWellFormed level 832 0 256
    (Lookup.BatchedReconstruction.repairAtOps productCircuit 259 256) = true at hphase
  change Program.opsWellFormed level 832 0 256 totalDivisionOps = true
  simp only [totalDivisionOps, selectedDivisionOps, postForwardOps,
    Program.opsWellFormed_append, gateOps,
    Lookup3.gateOps_wellFormed hl numeratorMove_wellFormed,
    Lookup3.gateOps_wellFormed hl quotientMove_wellFormed,
    Lookup3.gateOps_wellFormed hl hs, Lookup3.gateOps_wellFormed hl hsr,
    Lookup3.gateOps_wellFormed hl hp, Lookup3.gateOps_wellFormed hl hr,
    terminalOps_wellFormed hl, phaseRepairOps, hphase, Bool.and_self]

end VQ.Curve.NarrowPackedRetainedDivision
