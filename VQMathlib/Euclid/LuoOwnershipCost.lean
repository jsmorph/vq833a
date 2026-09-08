import VQ.Euclid.LuoOwnershipWindows
import VQ.Euclid.PackedTerminalEpoch
import VQMathlib.Euclid.PackedOwnershipCounts
import VQMathlib.Euclid.LuoOwnershipWriterCounts

namespace VQMathlib.LuoSchedule

open VQ.Euclid.LuoWindowedOwnership
open VQ
open VQ.Euclid
open VQ.Reversible

def ownershipUpperWriterToffoli (step : Nat) : Nat :=
  (LengthWriter.upperGates 1 (ownershipUpperWorkWidth step) 9).countP
    RGate.isCcx

def ownershipLowerWriterToffoli (step : Nat) : Nat :=
  (LengthWriter.lowerGates 256 (ownershipLowerSource step + 1)
      (ownershipLowerWorkWidth step) 9).countP RGate.isCcx

def ownershipWritersToffoli (step : Nat) : Nat :=
  2 * ownershipUpperWriterToffoli step +
    2 * ownershipLowerWriterToffoli step

def fullOwnershipWritersToffoli : Nat :=
  2 * (LengthWriter.upperGates 1 259 9).countP RGate.isCcx +
    2 * (LengthWriter.lowerGates 256 1 259 9).countP RGate.isCcx

def packedOwnershipToffoli : Nat :=
  VQ.Euclid.PackedTerminalEpoch.ownershipGates.countP RGate.isCcx

private def fixedOwnershipCount (upper lower whole : Nat) : Nat :=
  whole - (2 * upper + 2 * lower)

def fixedOwnershipToffoli : Nat :=
  fixedOwnershipCount
    ((LengthWriter.upperGates 1 259 9).countP RGate.isCcx)
    ((LengthWriter.lowerGates 256 1 259 9).countP RGate.isCcx)
    (PackedTerminalEpoch.ownershipGates.countP RGate.isCcx)

def windowedOwnershipToffoli (step : Nat) : Nat :=
  fixedOwnershipToffoli + ownershipWritersToffoli step

def windowedOwnershipScheduleToffoli : Nat :=
  ((List.range 1620).map (fun index =>
    windowedOwnershipToffoli (index + 1))).sum

theorem fullOwnershipWritersToffoli_eq :
    fullOwnershipWritersToffoli = 145048 := by
  native_decide

theorem packedOwnershipToffoli_eq : packedOwnershipToffoli = 145560 := by
  native_decide

private theorem fixedOwnershipCount_eq (upper lower whole : Nat)
    (h : whole - (2 * upper + 2 * lower) = 512) :
    fixedOwnershipCount upper lower whole = 512 := h

theorem fixedOwnershipToffoli_eq : fixedOwnershipToffoli = 512 :=
  fixedOwnershipCount_eq _ _ _
    VQMathlib.Euclid.PackedOwnershipCounts.ownershipGates_fixedDifference

theorem fullOwnership_reconstruction :
    fixedOwnershipToffoli + fullOwnershipWritersToffoli =
      packedOwnershipToffoli := by
  rw [fixedOwnershipToffoli_eq, fullOwnershipWritersToffoli_eq,
    packedOwnershipToffoli_eq]

theorem windowedOwnershipScheduleToffoli_eq :
    windowedOwnershipScheduleToffoli = 141696120 := by
  have hentry : (fun index => windowedOwnershipToffoli (index + 1)) =
      (fun index => 512 +
        (2 * OwnershipWriterCounts.upperCount (index + 1) +
          2 * OwnershipWriterCounts.lowerCount (index + 1))) := by
    funext index
    simp only [windowedOwnershipToffoli, fixedOwnershipToffoli_eq,
      ownershipWritersToffoli, ownershipUpperWriterToffoli,
      ownershipLowerWriterToffoli, OwnershipWriterCounts.upperCount_eq,
      OwnershipWriterCounts.lowerCount_eq]
  exact (congrArg (fun f => ((List.range 1620).map f).sum) hentry).trans
    OwnershipWriterCounts.schedule_eq

theorem windowedOwnershipSchedule_saving :
    1620 * packedOwnershipToffoli - windowedOwnershipScheduleToffoli =
      94111080 := by
  rw [packedOwnershipToffoli_eq, windowedOwnershipScheduleToffoli_eq]

theorem ownershipWindowProjectedScheduleToffoli_eq :
    361238504 - 94111080 = 267127424 := by
  decide

theorem ownershipAndCoefficientProjectedScheduleToffoli_eq :
    267127424 - 2866710 = 264260714 := by
  decide

end VQMathlib.LuoSchedule
