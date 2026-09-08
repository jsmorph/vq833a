/-
Coefficient endpoint preparation with an eight-bit remainder-length register.
-/
import VQ.Euclid.LuoCoefficientBoundary

namespace VQ
namespace Euclid
namespace CompactCoefficientBoundary

open Reversible

def n : Nat := 256
def width : Nat := 9

def lengthTOffset : Nat := 0
def lengthRPrimeOffset : Nat := 9
def lengthRPrimeWidth : Nat := 8
def extensionWire : Nat := 17
def shiftOffset : Nat := 18
def phaseTwoWire : Nat := 27
def scratchOffset : Nat := 28
def scratchWidth : Nat := 9
def carryWire : Nat := 37

def layout : Layout := [9, 8, 1, 9, 1, 9, 1]

def prepareGates : List RGate :=
  LuoCoefficientBoundary.prepareGates n width

def restoreGates : List RGate :=
  LuoCoefficientBoundary.restoreGates n width

def circuit : RCircuit :=
  { width := layout.width, gates := prepareGates ++ restoreGates }

theorem layout_width : layout.width = 38 := by
  decide

theorem old_wire_alignment :
    LuoCoefficientBoundary.lengthTOffset = lengthTOffset ∧
    LuoCoefficientBoundary.lengthRPrimeOffset width = lengthRPrimeOffset ∧
    LuoCoefficientBoundary.shiftOffset width = shiftOffset ∧
    LuoCoefficientBoundary.phaseTwoWire width = phaseTwoWire ∧
    LuoCoefficientBoundary.scratchOffset width = scratchOffset ∧
    LuoCoefficientBoundary.carryWire width = carryWire := by
  decide

theorem fullRPrime_of_extension_clear {i : Nat}
    (hextension : bitValue i extensionWire = 0) :
    readField i lengthRPrimeOffset width =
      readField i lengthRPrimeOffset lengthRPrimeWidth := by
  rw [show width = lengthRPrimeWidth + 1 by decide, readField_high]
  rw [show lengthRPrimeOffset + lengthRPrimeWidth = extensionWire by decide,
    hextension]
  simp

theorem prepare_lengthT_phaseTwoClear
    {i : Nat}
    (hscratch : readField i scratchOffset scratchWidth = 0)
    (hcarry : bitValue i carryWire = 0)
    (hphase : bitValue i phaseTwoWire = 0)
    (htfit : readField i lengthTOffset width + 2 < 2 ^ width) :
    readField (actGates prepareGates i) lengthTOffset width =
      readField i lengthTOffset width + 2 := by
  exact LuoCoefficientBoundary.prepareGates_lengthT_phaseTwoClear
    (by decide) hscratch hcarry hphase htfit

theorem prepare_lengthT_phaseTwoSet
    {i : Nat}
    (hextension : bitValue i extensionWire = 0)
    (hscratch : readField i scratchOffset scratchWidth = 0)
    (hcarry : bitValue i carryWire = 0)
    (hphase : bitValue i phaseTwoWire = 1)
    (hsum : readField i lengthRPrimeOffset lengthRPrimeWidth +
      readField i shiftOffset width ≤ n + 1) :
    readField (actGates prepareGates i) lengthTOffset width =
      n + 1 - readField i lengthRPrimeOffset lengthRPrimeWidth -
        readField i shiftOffset width := by
  have hsum' :
      readField i (LuoCoefficientBoundary.lengthRPrimeOffset width) width +
        readField i (LuoCoefficientBoundary.shiftOffset width) width ≤ n + 1 := by
    change readField i 9 9 + readField i 18 9 ≤ 257
    have hfull := fullRPrime_of_extension_clear hextension
    change readField i 9 9 = readField i 9 8 at hfull
    rw [hfull]
    change readField i 9 8 + readField i 18 9 ≤ 257 at hsum
    exact hsum
  have h := LuoCoefficientBoundary.prepareGates_lengthT_phaseTwoSet
    (n := n) (width := width) (I := i)
    (by decide) hscratch hcarry hphase hsum'
  change readField (actGates prepareGates i) lengthTOffset width =
    n + 1 - readField i lengthRPrimeOffset width -
      readField i shiftOffset width at h
  rw [fullRPrime_of_extension_clear hextension] at h
  exact h

theorem prepareRestore_act_phaseTwoClear
    {i : Nat}
    (hextension : bitValue i extensionWire = 0)
    (hscratch : readField i scratchOffset scratchWidth = 0)
    (hcarry : bitValue i carryWire = 0)
    (hphase : bitValue i phaseTwoWire = 0)
    (htfit : readField i lengthTOffset width + 2 < 2 ^ width)
    (hsum : readField i lengthRPrimeOffset lengthRPrimeWidth +
      readField i shiftOffset width ≤ n + 1) :
    actGates (prepareGates ++ restoreGates) i = i := by
  have hsum' : readField i lengthRPrimeOffset width +
      readField i shiftOffset width ≤ n + 1 := by
    rw [fullRPrime_of_extension_clear hextension]
    exact hsum
  exact LuoCoefficientBoundary.prepareRestoreGates_act_phaseTwoClear
    (by decide) hscratch hcarry hphase htfit hsum'

theorem prepareRestore_act_phaseTwoSet
    {i : Nat}
    (hextension : bitValue i extensionWire = 0)
    (hscratch : readField i scratchOffset scratchWidth = 0)
    (hcarry : bitValue i carryWire = 0)
    (hphase : bitValue i phaseTwoWire = 1)
    (htfit : readField i lengthTOffset width + 2 < 2 ^ width)
    (hsum : readField i lengthRPrimeOffset lengthRPrimeWidth +
      readField i shiftOffset width ≤ n + 1) :
    actGates (prepareGates ++ restoreGates) i = i := by
  have hsum' : readField i lengthRPrimeOffset width +
      readField i shiftOffset width ≤ n + 1 := by
    rw [fullRPrime_of_extension_clear hextension]
    exact hsum
  exact LuoCoefficientBoundary.prepareRestoreGates_act_phaseTwoSet
    (by decide) hscratch hcarry hphase htfit hsum'

theorem circuit_wellFormed : circuit.wellFormed = true := by
  have hp := LuoCoefficientBoundary.prepareGates_wellFormed n width
  have hr := LuoCoefficientBoundary.restoreGates_wellFormed n width
  rw [LuoCoefficientBoundary.layout_width] at hp hr
  change (LuoCoefficientBoundary.prepareGates n width).all
      (RGate.wellFormed 38) = true at hp
  change (LuoCoefficientBoundary.restoreGates n width).all
      (RGate.wellFormed 38) = true at hr
  simpa [circuit, RCircuit.wellFormed, prepareGates, restoreGates,
    layout_width, List.all_append] using And.intro hp hr

theorem circuit_width : circuit.width = 38 := by
  simp [circuit, layout_width]

theorem gates_length_le : circuit.gates.length ≤ 468 := by
  simpa [circuit, prepareGates, restoreGates, width] using
    LuoCoefficientBoundary.prepareRestoreGates_length_le n width

theorem gates_ccx : circuit.gates.countP RGate.isCcx = 126 := by
  simpa [circuit, prepareGates, restoreGates, width] using
    LuoCoefficientBoundary.prepareRestoreGates_ccx n width

end CompactCoefficientBoundary
end Euclid
end VQ
