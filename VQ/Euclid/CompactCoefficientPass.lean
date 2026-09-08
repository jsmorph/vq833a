/-
The secp256k1 coefficient pass with an eight-bit remainder-length register.
-/
import VQ.Euclid.LuoCoefficientPass

namespace VQ
namespace Euclid
namespace CompactCoefficientPass

open Reversible

def count : Nat := 257
def lengthRPrimeWidth : Nat := 8

def layout : Layout := LuoCoefficientPass.layout count
def gates : List RGate := LuoCoefficientPass.gates count
def circuit : RCircuit := { width := layout.width, gates := gates }

def phaseOneWire : Nat := LuoCoefficientPass.phaseOneWire
def phaseTwoWire : Nat := LuoCoefficientPass.phaseTwoWire
def signWire : Nat := LuoCoefficientPass.signWire
def workOneOffset : Nat := LuoCoefficientPass.workOneOffset
def workTwoOffset : Nat := LuoCoefficientPass.workTwoOffset count
def lengthTOffset : Nat := LuoCoefficientPass.lengthTOffset count
def lengthRPrimeOffset : Nat := LuoCoefficientPass.lengthRPrimeOffset count
def extensionWire : Nat := lengthRPrimeOffset + lengthRPrimeWidth
def shiftOffset : Nat := LuoCoefficientPass.shiftOffset count
def controlWire : Nat := LuoCoefficientPass.controlWire count
def temporaryWire : Nat := LuoCoefficientPass.temporaryWire count
def scratchOffset : Nat := LuoCoefficientPass.scratchOffset count
def carryWire : Nat := LuoCoefficientPass.carryWire count
def accumulatorWire : Nat := LuoCoefficientPass.accumulatorWire count
def cellScratchWire : Nat := LuoCoefficientPass.cellScratchWire count

def preparedT (i : Nat) : Nat :=
  LuoCoefficientPass.preparedLengthT count i

def preparedRPrime (i : Nat) : Nat :=
  LuoCoefficientPass.preparedLengthRPrime count i

theorem layout_width : layout.width = 558 := by
  simp [layout, count, LuoCoefficientPass.layout_width]

theorem fullRPrime_of_extension_clear {i : Nat}
    (hextension : bitValue i extensionWire = 0) :
    readField i lengthRPrimeOffset 9 =
      readField i lengthRPrimeOffset lengthRPrimeWidth := by
  rw [show 9 = lengthRPrimeWidth + 1 by decide, readField_high]
  rw [show lengthRPrimeOffset + lengthRPrimeWidth = extensionWire by rfl,
    hextension]
  simp

theorem full_sum
    {i : Nat}
    (hextension : bitValue i extensionWire = 0)
    (hsum : readField i lengthRPrimeOffset lengthRPrimeWidth +
      readField i shiftOffset 9 ≤ 257) :
    readField i lengthRPrimeOffset 9 + readField i shiftOffset 9 ≤ 257 := by
  rw [fullRPrime_of_extension_clear hextension]
  exact hsum

theorem phaseOneClear_phaseTwoClear_act
    {i : Nat}
    (hboundaryRange : 1 ≤ preparedT i ∧ preparedT i < 258)
    (hextension : bitValue i extensionWire = 0)
    (hphaseOne : bitValue i phaseOneWire = 0)
    (hphaseTwo : bitValue i phaseTwoWire = 0)
    (hcontrol : bitValue i controlWire = 0)
    (hscratch : readField i scratchOffset 9 = 0)
    (hcarry : bitValue i carryWire = 0)
    (haccumulator : bitValue i accumulatorWire = 0)
    (hcellScratch : bitValue i cellScratchWire = 0)
    (htfit : readField i lengthTOffset 9 + 2 < 512)
    (hsum : readField i lengthRPrimeOffset lengthRPrimeWidth +
      readField i shiftOffset 9 ≤ 257) :
    actGates gates i = i := by
  exact LuoCoefficientPass.gates_phaseOneClear_phaseTwoClear_act
    (by decide) (by decide) hboundaryRange hphaseOne hphaseTwo hcontrol
    hscratch hcarry haccumulator hcellScratch htfit
    (full_sum hextension hsum)

theorem phaseOneClear_phaseTwoSet_act
    {i : Nat}
    (hboundaryRange : 1 ≤ preparedRPrime i ∧ preparedRPrime i < 258)
    (hextension : bitValue i extensionWire = 0)
    (hphaseOne : bitValue i phaseOneWire = 0)
    (hphaseTwo : bitValue i phaseTwoWire = 1)
    (hcontrol : bitValue i controlWire = 0)
    (hscratch : readField i scratchOffset 9 = 0)
    (hcarry : bitValue i carryWire = 0)
    (haccumulator : bitValue i accumulatorWire = 0)
    (hcellScratch : bitValue i cellScratchWire = 0)
    (htfit : readField i lengthTOffset 9 + 2 < 512)
    (hsum : readField i lengthRPrimeOffset lengthRPrimeWidth +
      readField i shiftOffset 9 ≤ 257) :
    actGates gates i = i := by
  exact LuoCoefficientPass.gates_phaseOneClear_phaseTwoSet_act
    (by decide) (by decide) hboundaryRange hphaseOne hphaseTwo hcontrol
    hscratch hcarry haccumulator hcellScratch htfit
    (full_sum hextension hsum)

theorem phaseOneSet_phaseTwoClear_signSet_act
    {i : Nat}
    (hboundaryRange : 1 ≤ preparedT i ∧ preparedT i < 258)
    (hextension : bitValue i extensionWire = 0)
    (hphaseOne : bitValue i phaseOneWire = 1)
    (hphaseTwo : bitValue i phaseTwoWire = 0)
    (hsign : bitValue i signWire = 1)
    (hcontrol : bitValue i controlWire = 0)
    (htemporary : bitValue i temporaryWire = 0)
    (hscratch : readField i scratchOffset 9 = 0)
    (hcarry : bitValue i carryWire = 0)
    (haccumulator : bitValue i accumulatorWire = 0)
    (hcellScratch : bitValue i cellScratchWire = 0)
    (htfit : readField i lengthTOffset 9 + 2 < 512)
    (hsum : readField i lengthRPrimeOffset lengthRPrimeWidth +
      readField i shiftOffset 9 ≤ 257) :
    let boundary := preparedT i
    let total := readField i workTwoOffset boundary +
      readField i workOneOffset boundary
    actGates gates i =
      writeField
        (writeField i workTwoOffset boundary (total % 2 ^ boundary))
        signWire 1 ((total / 2 ^ boundary) % 2) := by
  exact LuoCoefficientPass.gates_phaseOneSet_phaseTwoClear_signSet_act
    (by decide) (by decide) hboundaryRange hphaseOne hphaseTwo hsign
    hcontrol htemporary hscratch hcarry haccumulator hcellScratch htfit
    (full_sum hextension hsum)

theorem phaseOneSet_phaseTwoClear_signClear_act
    {i : Nat}
    (hboundaryRange : 1 ≤ preparedT i ∧ preparedT i < 258)
    (hextension : bitValue i extensionWire = 0)
    (hphaseOne : bitValue i phaseOneWire = 1)
    (hphaseTwo : bitValue i phaseTwoWire = 0)
    (hsign : bitValue i signWire = 0)
    (hcontrol : bitValue i controlWire = 0)
    (htemporary : bitValue i temporaryWire = 0)
    (hscratch : readField i scratchOffset 9 = 0)
    (hcarry : bitValue i carryWire = 0)
    (haccumulator : bitValue i accumulatorWire = 0)
    (hcellScratch : bitValue i cellScratchWire = 0)
    (htfit : readField i lengthTOffset 9 + 2 < 512)
    (hsum : readField i lengthRPrimeOffset lengthRPrimeWidth +
      readField i shiftOffset 9 ≤ 257) :
    let boundary := preparedT i
    let difference := Adder.difference boundary
      (readField i workOneOffset boundary)
      (readField i workTwoOffset boundary)
    let total := difference + readField i workOneOffset boundary
    actGates gates i =
      writeField
        (writeField i workTwoOffset boundary (total % 2 ^ boundary))
        signWire 1 ((1 + total / 2 ^ boundary) % 2) := by
  exact LuoCoefficientPass.gates_phaseOneSet_phaseTwoClear_signClear_act
    (by decide) (by decide) hboundaryRange hphaseOne hphaseTwo hsign
    hcontrol htemporary hscratch hcarry haccumulator hcellScratch htfit
    (full_sum hextension hsum)

theorem phaseOneSet_phaseTwoSet_act
    {i : Nat}
    (hboundaryRange : 1 ≤ preparedRPrime i ∧ preparedRPrime i < 258)
    (hextension : bitValue i extensionWire = 0)
    (hphaseOne : bitValue i phaseOneWire = 1)
    (hphaseTwo : bitValue i phaseTwoWire = 1)
    (hcontrol : bitValue i controlWire = 0)
    (htemporary : bitValue i temporaryWire = 0)
    (hscratch : readField i scratchOffset 9 = 0)
    (hcarry : bitValue i carryWire = 0)
    (haccumulator : bitValue i accumulatorWire = 0)
    (hcellScratch : bitValue i cellScratchWire = 0)
    (htfit : readField i lengthTOffset 9 + 2 < 512)
    (hsum : readField i lengthRPrimeOffset lengthRPrimeWidth +
      readField i shiftOffset 9 ≤ 257) :
    let boundary := preparedRPrime i
    let difference := Adder.difference boundary
      (readField i workOneOffset boundary)
      (readField i workTwoOffset boundary)
    let total := difference + readField i workOneOffset boundary
    let signBeforeAdd := bitValue (i ^^^ (1 <<< signWire)) signWire
    actGates gates i =
      writeField
        (writeField i workTwoOffset boundary (total % 2 ^ boundary))
        signWire 1 ((signBeforeAdd + total / 2 ^ boundary) % 2) := by
  exact LuoCoefficientPass.gates_phaseOneSet_phaseTwoSet_act
    (by decide) (by decide) hboundaryRange hphaseOne hphaseTwo hcontrol
    htemporary hscratch hcarry haccumulator hcellScratch htfit
    (full_sum hextension hsum)

theorem circuit_wellFormed : circuit.wellFormed = true := by
  change gates.all (RGate.wellFormed layout.width) = true
  simpa [gates, layout] using
    LuoCoefficientPass.gates_wellFormed (count := count)
      (by decide) (by decide)

theorem circuit_width : circuit.width = 558 := by
  simp [circuit, layout_width]

theorem circuit_resources :
    circuit.gates.length ≤ 15368 ∧
    circuit.gates.countP RGate.isCcx = 5778 ∧
    circuit.gates.countP RGate.isCx = 5392 ∧
    circuit.width = 558 := by
  simpa [circuit, gates, layout, count] using
    LuoCoefficientPass.gates_resources (count := count)
      (by decide) (by decide)

end CompactCoefficientPass
end Euclid
end VQ
