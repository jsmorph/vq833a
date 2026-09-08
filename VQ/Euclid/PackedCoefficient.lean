/-
State transformation of the compact coefficient circuit in the 571-wire layout.
-/
import VQ.Euclid.PackedState

namespace VQ
namespace Euclid
namespace PackedCoefficient

open Reversible

def localLayout : Layout := PackedStepLayout.coefficientLayout
def wiring : Wiring := PackedStepLayout.coefficientWiring

def input (I : Nat) : Nat :=
  gatherBits (place localLayout wiring) localLayout.width I

def boundary (I : Nat) : Nat :=
  CompactCoefficientDirty.preparedRPrime (input I)

def difference (I : Nat) : Nat :=
  Adder.difference (boundary I)
    (readField (input I) CompactCoefficientDirty.workOneOffset (boundary I))
    (readField (input I) CompactCoefficientDirty.workTwoOffset (boundary I))

def total (I : Nat) : Nat :=
  difference I +
    readField (input I) CompactCoefficientDirty.workOneOffset (boundary I)

def signBeforeAdd (I : Nat) : Nat :=
  bitValue (input I ^^^ (1 <<< CompactCoefficientDirty.signWire))
    CompactCoefficientDirty.signWire

def targetValue (I : Nat) : Nat := total I % 2 ^ boundary I

def workValue (I : Nat) : Nat :=
  writeField
    (readField I PackedStepLayout.workTwoOffset 257)
    0 (boundary I) (targetValue I)

def signValue (I : Nat) : Nat :=
  (signBeforeAdd I + total I / 2 ^ boundary I) % 2

theorem input_field (j I : Nat) (hj : j < wiring.length) :
    localLayout.read (input I) j =
      readField I (wiring.getD j 0) (localLayout.size j) := by
  exact read_gatherBits localLayout wiring j I hj

private theorem lift_local_write
    {I localBoundary localTarget localSign : Nat}
    (hfit : localBoundary ≤ 257)
    (hlocal : actGates CompactCoefficientDirty.gates (input I) =
      writeField
        (writeField (input I) CompactCoefficientDirty.workTwoOffset
          localBoundary localTarget)
        CompactCoefficientDirty.signWire 1 localSign) :
    actGates PackedStepLayout.coefficientGates I =
      writeField
        (writeField I PackedStepLayout.workTwoOffset localBoundary localTarget)
        PackedStepLayout.signWire 1 localSign := by
  let physicalWorkValue := writeField
    (readField I PackedStepLayout.workTwoOffset 257)
    0 localBoundary localTarget
  have hinputWork :
      readField (input I) CompactCoefficientDirty.workTwoOffset 257 =
        readField I PackedStepLayout.workTwoOffset 257 := by
    have h := input_field 4 I (by decide)
    rw [Layout.read] at h
    have hoff : localLayout.offset 4 =
        CompactCoefficientDirty.workTwoOffset := by decide
    have hsize : localLayout.size 4 = 257 := by decide
    have hwire : wiring.getD 4 0 = PackedStepLayout.workTwoOffset := by decide
    rw [hoff, hsize, hwire] at h
    exact h
  have hsubLocal :
      writeField (input I) CompactCoefficientDirty.workTwoOffset
          localBoundary localTarget =
        writeField (input I) CompactCoefficientDirty.workTwoOffset 257
          physicalWorkValue := by
    simpa only [Nat.add_zero, physicalWorkValue, hinputWork] using
      (writeField_subfield
        (i := input I)
        (outerOffset := CompactCoefficientDirty.workTwoOffset)
        (outerWidth := 257) (innerOffset := 0)
        (innerWidth := localBoundary) (value := localTarget)
        (by simpa using hfit))
  rw [hsubLocal] at hlocal
  have hlocal' : actGates CompactCoefficientDirty.gates (input I) =
      localLayout.write
        (localLayout.write (input I) 4 physicalWorkValue) 2 localSign := by
    have hoffWork : localLayout.offset 4 =
        CompactCoefficientDirty.workTwoOffset := by decide
    have hsizeWork : localLayout.size 4 = 257 := by decide
    have hoffSign : localLayout.offset 2 =
        CompactCoefficientDirty.signWire := by decide
    have hsizeSign : localLayout.size 2 = 1 := by decide
    rw [← hoffWork, ← hsizeWork, ← hoffSign, ← hsizeSign] at hlocal
    simpa only [Layout.write] using hlocal
  have hplaced := actGates_placed_write₂
    (gs := CompactCoefficientDirty.gates)
    (L := localLayout) (W := wiring)
    (k₁ := 4) (k₂ := 2)
    (v₁ := physicalWorkValue) (v₂ := localSign)
    PackedStepLayout.coefficient_disjoint (by decide)
    (by decide) (by decide) (by decide)
    (fun g hg => RCircuit.wellFormed_mem
      CompactCoefficientDirty.circuit_wellFormed hg)
    hlocal'
  have hwireWork : wiring.getD 4 0 = PackedStepLayout.workTwoOffset := by
    decide
  have hsizeWork : localLayout.size 4 = 257 := by decide
  have hwireSign : wiring.getD 2 0 = PackedStepLayout.signWire := by decide
  have hsizeSign : localLayout.size 2 = 1 := by decide
  rw [hwireWork, hsizeWork, hwireSign, hsizeSign] at hplaced
  have hsubPhysical :
      writeField I PackedStepLayout.workTwoOffset localBoundary localTarget =
        writeField I PackedStepLayout.workTwoOffset 257 physicalWorkValue := by
    simpa only [Nat.add_zero, physicalWorkValue] using
      (writeField_subfield
        (i := I) (outerOffset := PackedStepLayout.workTwoOffset)
        (outerWidth := 257) (innerOffset := 0)
        (innerWidth := localBoundary) (value := localTarget)
        (by simpa using hfit))
  rw [← hsubPhysical] at hplaced
  rw [PackedStepLayout.coefficientGates, PackedStepLayout.placed]
  simpa only [localLayout, wiring] using hplaced

private theorem lift_local_identity
    {I : Nat}
    (hlocal : actGates CompactCoefficientDirty.gates (input I) = input I) :
    actGates PackedStepLayout.coefficientGates I = I := by
  have hlocal' : actGates CompactCoefficientDirty.gates (input I) =
      actGates [] (input I) := by
    simpa only [actGates_nil] using hlocal
  have hplaced := actGates_placed_congr
    (gs := CompactCoefficientDirty.gates) (hs := [])
    PackedStepLayout.coefficient_disjoint (by decide)
    (fun g hg => RCircuit.wellFormed_mem
      CompactCoefficientDirty.circuit_wellFormed hg)
    (by intro g hg; simp at hg) I
    (by simpa [input, localLayout, wiring] using hlocal')
  change actGates
      (CompactCoefficientDirty.gates.map
        (RGate.map (place localLayout wiring))) I = I at hplaced
  simpa [PackedStepLayout.coefficientGates, PackedStepLayout.placed,
    localLayout, wiring] using hplaced

theorem gates_act
    {I : Nat}
    (hboundaryRange :
      1 ≤ boundary I ∧ boundary I < 1 + CompactCoefficientDirty.count)
    (hphaseOne : bitValue (input I) CompactCoefficientDirty.phaseOneWire = 1)
    (hphaseTwo : bitValue (input I) CompactCoefficientDirty.phaseTwoWire = 1)
    (hcontrol : bitValue (input I) CompactCoefficientDirty.controlWire = 0)
    (hscratch : readField (input I) CompactCoefficientDirty.scratchOffset 9 = 0)
    (hcarry : bitValue (input I) CompactCoefficientDirty.carryWire = 0)
    (haccumulator :
      bitValue (input I) CompactCoefficientDirty.accumulatorWire = 0)
    (hcellScratch :
      bitValue (input I) CompactCoefficientDirty.cellScratchWire = 0)
    (htfit : readField (input I) CompactCoefficientDirty.lengthTOffset 9 +
      2 < 2 ^ 9)
    (hsum : readField (input I)
        CompactCoefficientDirty.lengthRPrimeOffset 9 +
      readField (input I) CompactCoefficientDirty.shiftOffset 9 ≤ 257) :
    actGates PackedStepLayout.coefficientGates I =
      writeField
        (writeField I PackedStepLayout.workTwoOffset (boundary I)
          (targetValue I))
        PackedStepLayout.signWire 1 (signValue I) := by
  have hlocal := CompactCoefficientDirty.phaseFour_act
    hboundaryRange hphaseOne hphaseTwo hcontrol hscratch hcarry haccumulator
    hcellScratch htfit hsum
  dsimp only at hlocal
  change actGates CompactCoefficientDirty.gates (input I) =
    writeField
      (writeField (input I) CompactCoefficientDirty.workTwoOffset
        (boundary I) (targetValue I))
      CompactCoefficientDirty.signWire 1 (signValue I) at hlocal
  have hfit : boundary I ≤ 257 := by
    have hcount : CompactCoefficientDirty.count = 257 := rfl
    omega
  exact lift_local_write hfit hlocal

theorem gates_act_phaseTwo
    {I selected : Nat}
    (hboundaryRange :
      1 ≤ CompactCoefficientDirty.preparedT (input I) ∧
        CompactCoefficientDirty.preparedT (input I) <
          1 + CompactCoefficientDirty.count)
    (hphaseOne : bitValue (input I) CompactCoefficientDirty.phaseOneWire = 1)
    (hphaseTwo : bitValue (input I) CompactCoefficientDirty.phaseTwoWire = 0)
    (hselected :
      bitValue (input I) CompactCoefficientDirty.signWire = selected)
    (hcontrol : bitValue (input I) CompactCoefficientDirty.controlWire = 0)
    (hscratch : readField (input I) CompactCoefficientDirty.scratchOffset 9 = 0)
    (hcarry : bitValue (input I) CompactCoefficientDirty.carryWire = 0)
    (haccumulator :
      bitValue (input I) CompactCoefficientDirty.accumulatorWire = 0)
    (hcellScratch :
      bitValue (input I) CompactCoefficientDirty.cellScratchWire = 0)
    (htfit : readField (input I) CompactCoefficientDirty.lengthTOffset 9 +
      2 < 2 ^ 9) :
    let localBoundary := CompactCoefficientDirty.preparedT (input I)
    let localDifference := Adder.difference localBoundary
      (readField (input I) CompactCoefficientDirty.workOneOffset
        localBoundary)
      (readField (input I) CompactCoefficientDirty.workTwoOffset
        localBoundary)
    let localCoefficient := if selected = 0 then localDifference else
      readField (input I) CompactCoefficientDirty.workTwoOffset localBoundary
    let localTotal := localCoefficient +
      readField (input I) CompactCoefficientDirty.workOneOffset localBoundary
    let localSignBeforeAdd := bitValue
      (input I ^^^ (1 <<< CompactCoefficientDirty.signWire))
      CompactCoefficientDirty.signWire
    actGates PackedStepLayout.coefficientGates I =
      writeField
        (writeField I PackedStepLayout.workTwoOffset localBoundary
          (localTotal % 2 ^ localBoundary))
        PackedStepLayout.signWire 1
          ((localSignBeforeAdd + localTotal / 2 ^ localBoundary) % 2) := by
  have hlocal := CompactCoefficientDirty.phaseTwo_act hboundaryRange hphaseOne
    hphaseTwo hcontrol hscratch hcarry haccumulator hcellScratch htfit
  dsimp only at hlocal
  rw [hselected] at hlocal
  have hfit : CompactCoefficientDirty.preparedT (input I) ≤ 257 := by
    have hcount : CompactCoefficientDirty.count = 257 := rfl
    omega
  exact lift_local_write hfit hlocal

theorem gates_identity_phaseZero
    {I : Nat}
    (hphaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphaseTwo : bitValue I PackedStepLayout.phaseTwoWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0)
    (hpool : readField I PackedStepLayout.poolOffset 13 = 0)
    (htfit : readField I PackedStepLayout.lengthTOffset 9 + 2 < 2 ^ 9) :
    actGates PackedStepLayout.coefficientGates I = I := by
  have hinputPhaseOne : bitValue (input I)
      CompactCoefficientDirty.phaseOneWire = 0 := by
    rw [← readField_one]
    change readField (input I) 0 1 = 0
    calc
      readField (input I) 0 1 =
          readField I PackedStepLayout.phaseOneWire 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 0 I (by decide)
      _ = 0 := by simpa [readField_one] using hphaseOne
  have hinputPhaseTwo : bitValue (input I)
      CompactCoefficientDirty.phaseTwoWire = 0 := by
    rw [← readField_one]
    change readField (input I) 1 1 = 0
    calc
      readField (input I) 1 1 =
          readField I PackedStepLayout.phaseTwoWire 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 1 I (by decide)
      _ = 0 := by simpa [readField_one] using hphaseTwo
  have hinputExtension : bitValue (input I)
      CompactCoefficientDirty.extensionWire = 0 := by
    rw [← readField_one]
    change readField (input I) 534 1 = 0
    calc
      readField (input I) 534 1 =
          readField I PackedStepLayout.extensionWire 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 7 I (by decide)
      _ = 0 := by simpa [readField_one] using hextension
  have hinputControl : bitValue (input I)
      CompactCoefficientDirty.controlWire = 0 := by
    rw [← readField_one]
    change readField (input I) 544 1 = 0
    calc
      readField (input I) 544 1 =
          readField I PackedStepLayout.poolOffset 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 9 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) hpool
  have hinputScratch : readField (input I)
      CompactCoefficientDirty.scratchOffset 9 = 0 := by
    change readField (input I) 546 9 = 0
    calc
      readField (input I) 546 9 =
          readField I (PackedStepLayout.poolOffset + 1) 9 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 11 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) hpool
  have hinputCarry : bitValue (input I)
      CompactCoefficientDirty.carryWire = 0 := by
    rw [← readField_one]
    change readField (input I) 555 1 = 0
    calc
      readField (input I) 555 1 =
          readField I (PackedStepLayout.poolOffset + 10) 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 12 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) hpool
  have hinputAccumulator : bitValue (input I)
      CompactCoefficientDirty.accumulatorWire = 0 := by
    rw [← readField_one]
    change readField (input I) 556 1 = 0
    calc
      readField (input I) 556 1 =
          readField I (PackedStepLayout.poolOffset + 11) 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 13 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) hpool
  have hinputCellScratch : bitValue (input I)
      CompactCoefficientDirty.cellScratchWire = 0 := by
    rw [← readField_one]
    change readField (input I) 557 1 = 0
    calc
      readField (input I) 557 1 =
          readField I (PackedStepLayout.poolOffset + 12) 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 14 I (by decide)
      _ = 0 := readField_sub_zero (by omega) (by omega) hpool
  have hinputLengthT : readField (input I)
      CompactCoefficientDirty.lengthTOffset 9 =
        readField I PackedStepLayout.lengthTOffset 9 := by
    change readField (input I) 517 9 =
      readField I PackedStepLayout.lengthTOffset 9
    simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
      PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
      Layout.size] using input_field 5 I (by decide)
  apply lift_local_identity
  exact CompactCoefficientDirty.phaseOneClear_phaseTwoClear_act
    hinputPhaseOne hinputPhaseTwo hinputControl hinputScratch hinputCarry
    hinputAccumulator hinputCellScratch (by simpa [hinputLengthT] using htfit)

theorem gates_act_phaseOne
    {s : State}
    (hphaseOne : s.phase1 = false)
    (hphaseTwo : s.phase2 = true)
    (hlenTPositive : 0 < s.lenT)
    (hlenTBound : s.lenT < 259) :
    actGates PackedStepLayout.coefficientGates (PackedState.encoded s) =
      PackedState.encoded s := by
  let I := PackedState.encoded s
  let J := input I
  have hinputLengthT : readField J
      CompactCoefficientDirty.lengthTOffset 9 = encodeLength 9 s.lenT := by
    change readField J 517 9 = encodeLength 9 s.lenT
    calc
      readField J 517 9 =
          readField I PackedStepLayout.lengthTOffset 9 := by
        simpa [J, localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 5 I (by decide)
      _ = encodeLength 9 s.lenT := PackedState.read_lengthT s
  have hinputPhaseOne : bitValue J
      CompactCoefficientDirty.phaseOneWire = 0 := by
    rw [← readField_one]
    change readField J 0 1 = 0
    calc
      readField J 0 1 = readField I PackedStepLayout.phaseOneWire 1 := by
        simpa [J, localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 0 I (by decide)
      _ = 0 := by
        rw [readField_one, PackedState.read_phaseOne]
        simp [hphaseOne, boolValue]
  have hinputPhaseTwo : bitValue J
      CompactCoefficientDirty.phaseTwoWire = 1 := by
    rw [← readField_one]
    change readField J 1 1 = 1
    calc
      readField J 1 1 = readField I PackedStepLayout.phaseTwoWire 1 := by
        simpa [J, localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 1 I (by decide)
      _ = 1 := by
        rw [readField_one, PackedState.read_phaseTwo]
        simp [hphaseTwo, boolValue]
  have hinputControl : bitValue J
      CompactCoefficientDirty.controlWire = 0 := by
    rw [← readField_one]
    change readField J 544 1 = 0
    calc
      readField J 544 1 = readField I PackedStepLayout.poolOffset 1 := by
        simpa [J, localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 9 I (by decide)
      _ = 0 := PackedState.read_pool_subfield (by decide) (by decide)
  have hinputScratch : readField J
      CompactCoefficientDirty.scratchOffset 9 = 0 := by
    change readField J 546 9 = 0
    calc
      readField J 546 9 =
          readField I (PackedStepLayout.poolOffset + 1) 9 := by
        simpa [J, localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 11 I (by decide)
      _ = 0 := PackedState.read_pool_subfield (by decide) (by decide)
  have hinputCarry : bitValue J CompactCoefficientDirty.carryWire = 0 := by
    rw [← readField_one]
    change readField J 555 1 = 0
    calc
      readField J 555 1 =
          readField I (PackedStepLayout.poolOffset + 10) 1 := by
        simpa [J, localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 12 I (by decide)
      _ = 0 := PackedState.read_pool_subfield (by decide) (by decide)
  have hinputAccumulator : bitValue J
      CompactCoefficientDirty.accumulatorWire = 0 := by
    rw [← readField_one]
    change readField J 556 1 = 0
    calc
      readField J 556 1 =
          readField I (PackedStepLayout.poolOffset + 11) 1 := by
        simpa [J, localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 13 I (by decide)
      _ = 0 := PackedState.read_pool_subfield (by decide) (by decide)
  have hinputCellScratch : bitValue J
      CompactCoefficientDirty.cellScratchWire = 0 := by
    rw [← readField_one]
    change readField J 557 1 = 0
    calc
      readField J 557 1 =
          readField I (PackedStepLayout.poolOffset + 12) 1 := by
        simpa [J, localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using input_field 14 I (by decide)
      _ = 0 := PackedState.read_pool_subfield (by decide) (by decide)
  have hlenTCode : encodeLength 9 s.lenT = s.lenT - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenTPositive),
      Nat.mod_eq_of_lt]
    omega
  have htfit : readField J CompactCoefficientDirty.lengthTOffset 9 + 2 <
      2 ^ 9 := by
    rw [hinputLengthT, hlenTCode]
    omega
  have hlocal := CompactCoefficientDirty.phaseOneClear_phaseTwoSet_act_mod
    hinputPhaseOne hinputPhaseTwo hinputControl hinputScratch
    hinputCarry hinputAccumulator hinputCellScratch htfit
  have hplaced := lift_local_identity (I := I) (by simpa [J] using hlocal)
  simpa [I] using hplaced

theorem gates_act_phaseFour
    {p : Nat} {s : State}
    (h : ReachableStepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255) :
    actGates PackedStepLayout.coefficientGates (PackedState.encoded s) =
      PackedState.encoded { s with sign := true } := by
  let I := PackedState.encoded s
  have hstate := ReachableStepDomain.phaseFour_stateFacts
    h hphaseOne hphaseTwo
  have hinterval := ReachableStepDomain.phaseFour_coefficientIntervalFit
    h hphaseOne hphaseTwo
  have hinterval' : s.lenT + 1 + s.lenRPrime + s.shift ≤ 259 := by
    simpa [workWidth] using hinterval
  have htPositive : 0 < s.t := h.positiveLiveCoefficient hstate.1
  have hlengthRPrimePositive : 0 < s.lenRPrime := by
    rw [h.stepDomain.valid.1.2.1]
    exact bitLength_pos hstate.1
  have hshiftBound : s.shift < 259 := by
    simpa [workWidth] using hstate.2.2.2.2.1
  have hinputWorkOne : readField (input I)
      CompactCoefficientDirty.workOneOffset 257 =
        readField I PackedStepLayout.workOneOffset 257 := by
    change readField (input I) 3 257 =
      readField I PackedStepLayout.workOneOffset 257
    have hread := input_field 3 I (by decide)
    simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
      PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
      Layout.size] using hread
  have hinputWorkTwo : readField (input I)
      CompactCoefficientDirty.workTwoOffset 257 =
        readField I PackedStepLayout.workTwoOffset 257 := by
    change readField (input I) 260 257 =
      readField I PackedStepLayout.workTwoOffset 257
    have hread := input_field 4 I (by decide)
    simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
      PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
      Layout.size] using hread
  have hinputLengthT : readField (input I)
      CompactCoefficientDirty.lengthTOffset 9 = encodeLength 9 s.lenT := by
    change readField (input I) 517 9 = encodeLength 9 s.lenT
    have hread := input_field 5 I (by decide)
    calc
      readField (input I) 517 9 =
          readField I PackedStepLayout.lengthTOffset 9 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using hread
      _ = encodeLength 9 s.lenT := by
        simpa [I] using PackedState.read_lengthT s
  have hinputLengthRPrime : readField (input I)
      CompactCoefficientDirty.lengthRPrimeOffset 8 =
        encodeLength 8 s.lenRPrime := by
    change readField (input I) 526 8 = encodeLength 8 s.lenRPrime
    have hread := input_field 6 I (by decide)
    calc
      readField (input I) 526 8 =
          readField I PackedStepLayout.lengthRPrimeOffset 8 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using hread
      _ = encodeLength 8 s.lenRPrime := by
        simpa [I] using PackedState.read_lengthRPrime s
  have hinputExtension : bitValue (input I)
      CompactCoefficientDirty.extensionWire = 0 := by
    rw [← readField_one]
    change readField (input I) 534 1 = 0
    have hread := input_field 7 I (by decide)
    calc
      readField (input I) 534 1 =
          readField I PackedStepLayout.extensionWire 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using hread
      _ = 0 := by
        rw [readField_one]
        simpa [I] using PackedState.read_extension s
  have hinputLengthRPrimeFull : readField (input I)
      CompactCoefficientDirty.lengthRPrimeOffset 9 =
        encodeLength 8 s.lenRPrime := by
    exact (CompactCoefficientPass.fullRPrime_of_extension_clear
      hinputExtension).trans hinputLengthRPrime
  have hinputShift : readField (input I)
      CompactCoefficientDirty.shiftOffset 9 = encodeLength 9 s.shift := by
    change readField (input I) 535 9 = encodeLength 9 s.shift
    have hread := input_field 8 I (by decide)
    calc
      readField (input I) 535 9 =
          readField I PackedStepLayout.shiftOffset 9 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using hread
      _ = encodeLength 9 s.shift := by
        simpa [I] using PackedState.read_shift s
  have hinputPhaseOne : bitValue (input I)
      CompactCoefficientDirty.phaseOneWire = 1 := by
    rw [← readField_one]
    change readField (input I) 0 1 = 1
    have hread := input_field 0 I (by decide)
    calc
      readField (input I) 0 1 =
          readField I PackedStepLayout.phaseOneWire 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using hread
      _ = 1 := by
        rw [readField_one]
        simpa [I, hphaseOne, boolValue] using PackedState.read_phaseOne s
  have hinputPhaseTwo : bitValue (input I)
      CompactCoefficientDirty.phaseTwoWire = 1 := by
    rw [← readField_one]
    change readField (input I) 1 1 = 1
    have hread := input_field 1 I (by decide)
    calc
      readField (input I) 1 1 =
          readField I PackedStepLayout.phaseTwoWire 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using hread
      _ = 1 := by
        rw [readField_one]
        simpa [I, hphaseTwo, boolValue] using PackedState.read_phaseTwo s
  have hinputSign : bitValue (input I)
      CompactCoefficientDirty.signWire = boolValue s.sign := by
    rw [← readField_one]
    change readField (input I) 2 1 = boolValue s.sign
    have hread := input_field 2 I (by decide)
    calc
      readField (input I) 2 1 =
          readField I PackedStepLayout.signWire 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using hread
      _ = boolValue s.sign := by
        rw [readField_one]
        simpa [I] using PackedState.read_sign s
  have hinputControl : bitValue (input I)
      CompactCoefficientDirty.controlWire = 0 := by
    rw [← readField_one]
    change readField (input I) 544 1 = 0
    have hread := input_field 9 I (by decide)
    have hpool : bitValue I PackedStepLayout.poolOffset = 0 := by
      rw [← readField_one]
      exact PackedState.read_pool_subfield (by decide) (by decide)
    calc
      readField (input I) 544 1 =
          readField I PackedStepLayout.poolOffset 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using hread
      _ = 0 := by simpa [readField_one] using hpool
  have hinputScratch : readField (input I)
      CompactCoefficientDirty.scratchOffset 9 = 0 := by
    change readField (input I) 546 9 = 0
    have hread := input_field 11 I (by decide)
    have hpool := PackedState.read_pool_subfield (s := s)
      (offset := PackedStepLayout.poolOffset + 1) (width := 9)
      (by decide) (by decide)
    calc
      readField (input I) 546 9 =
          readField I (PackedStepLayout.poolOffset + 1) 9 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using hread
      _ = 0 := by simpa [I] using hpool
  have hinputCarry : bitValue (input I)
      CompactCoefficientDirty.carryWire = 0 := by
    rw [← readField_one]
    change readField (input I) 555 1 = 0
    have hread := input_field 12 I (by decide)
    have hpool : bitValue I (PackedStepLayout.poolOffset + 10) = 0 := by
      rw [← readField_one]
      exact PackedState.read_pool_subfield (by decide) (by decide)
    calc
      readField (input I) 555 1 =
          readField I (PackedStepLayout.poolOffset + 10) 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using hread
      _ = 0 := by simpa [readField_one] using hpool
  have hinputAccumulator : bitValue (input I)
      CompactCoefficientDirty.accumulatorWire = 0 := by
    rw [← readField_one]
    change readField (input I) 556 1 = 0
    have hread := input_field 13 I (by decide)
    have hpool : bitValue I (PackedStepLayout.poolOffset + 11) = 0 := by
      rw [← readField_one]
      exact PackedState.read_pool_subfield (by decide) (by decide)
    calc
      readField (input I) 556 1 =
          readField I (PackedStepLayout.poolOffset + 11) 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using hread
      _ = 0 := by simpa [readField_one] using hpool
  have hinputCellScratch : bitValue (input I)
      CompactCoefficientDirty.cellScratchWire = 0 := by
    rw [← readField_one]
    change readField (input I) 557 1 = 0
    have hread := input_field 14 I (by decide)
    have hpool : bitValue I (PackedStepLayout.poolOffset + 12) = 0 := by
      rw [← readField_one]
      exact PackedState.read_pool_subfield (by decide) (by decide)
    calc
      readField (input I) 557 1 =
          readField I (PackedStepLayout.poolOffset + 12) 1 := by
        simpa [localLayout, wiring, PackedStepLayout.coefficientLayout,
          PackedStepLayout.coefficientWiring, Layout.read, Layout.offset,
          Layout.size] using hread
      _ = 0 := by simpa [readField_one] using hpool
  have hlengthRPrimeCode : encodeLength 8 s.lenRPrime = s.lenRPrime - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hlengthRPrimePositive),
      Nat.mod_eq_of_lt]
    norm_num
    omega
  have hshiftCode : encodeLength 9 s.shift = s.shift - 1 := by
    rw [encodeLength, if_neg (Nat.ne_of_gt hstate.2.2.2.1),
      Nat.mod_eq_of_lt]
    omega
  have hsum : readField (input I)
        CompactCoefficientDirty.lengthRPrimeOffset 9 +
      readField (input I) CompactCoefficientDirty.shiftOffset 9 ≤ 257 := by
    rw [hinputLengthRPrimeFull, hinputShift,
      hlengthRPrimeCode, hshiftCode]
    omega
  have htCode : encodeLength 9 s.lenT = s.lenT - 1 := by
    have hlenTPositive : 0 < s.lenT := by
      rw [h.stepDomain.valid.1.1]
      exact bitLength_pos htPositive
    rw [encodeLength, if_neg (Nat.ne_of_gt hlenTPositive),
      Nat.mod_eq_of_lt]
    have hlenTBound : s.lenT < 259 := by omega
    norm_num
    omega
  have htfit : readField (input I)
      CompactCoefficientDirty.lengthTOffset 9 + 2 < 2 ^ 9 := by
    rw [hinputLengthT, htCode]
    omega
  let G := LuoCoefficientPass.boundaryGather 257 (input I)
  have hsumG : readField G 9 9 + readField G 18 9 ≤ 257 := by
    rw [LuoCoefficientPass.boundaryGather_read_lengthRPrime,
      LuoCoefficientPass.boundaryGather_read_shift]
    exact hsum
  have hboundary : boundary I = 259 - s.lenRPrime - s.shift := by
    have hprepared := LuoCoefficientBoundary.preparedR_eq
      (n := 256) (width := 9) (I := G) (by norm_num) hsumG
    change LuoCoefficientBoundary.preparedR 256 9 G =
      257 - readField G 9 9 - readField G 18 9 at hprepared
    calc
      boundary I = LuoCoefficientBoundary.preparedR 256 9 G := by rfl
      _ = 257 - readField G 9 9 - readField G 18 9 := hprepared
      _ = 259 - s.lenRPrime - s.shift := by
        have hinputLengthRPrimeFull' : readField (input I)
            (LuoCoefficientPass.lengthRPrimeOffset 257) 9 =
              encodeLength 8 s.lenRPrime := hinputLengthRPrimeFull
        have hinputShift' : readField (input I)
            (LuoCoefficientPass.shiftOffset 257) 9 =
              encodeLength 9 s.shift := hinputShift
        rw [LuoCoefficientPass.boundaryGather_read_lengthRPrime,
          LuoCoefficientPass.boundaryGather_read_shift,
          hinputLengthRPrimeFull', hinputShift', hlengthRPrimeCode, hshiftCode]
        omega
  have hboundaryRange : 1 ≤ boundary I ∧
      boundary I < 1 + CompactCoefficientDirty.count := by
    rw [hboundary]
    have hcount : CompactCoefficientDirty.count = 257 := rfl
    omega
  have hboundaryFit : boundary I ≤ 257 := by omega
  have hsource : readField (input I)
      CompactCoefficientDirty.workOneOffset (boundary I) = s.t := by
    calc
      readField (input I) CompactCoefficientDirty.workOneOffset (boundary I) =
          readField (readField (input I)
            CompactCoefficientDirty.workOneOffset 257) 0 (boundary I) := by
        symm
        exact readField_readField (by simpa using hboundaryFit)
      _ = readField (readField I PackedStepLayout.workOneOffset 257)
          0 (boundary I) := by rw [hinputWorkOne]
      _ = readField I PackedStepLayout.workOneOffset (boundary I) := by
        exact readField_readField (by simpa using hboundaryFit)
      _ = readField (readField I PackedStepLayout.workOneOffset 259)
          0 (boundary I) := by
        symm
        exact readField_readField (by omega)
      _ = readField (encodeWork1 256 s % 2 ^ 259) 0 (boundary I) := by
        rw [PackedState.read_workOne]
      _ = s.t := by
        have hdvd : 2 ^ boundary I ∣ 2 ^ 259 :=
          Nat.pow_dvd_pow 2 (hboundaryFit.trans (by omega))
        have hwork := ReachableStepDomain.phaseFour_work1Coefficient
          h hphaseOne hphaseTwo
        have hwork' : readField (encodeWork1 256 s) 0
            (259 - s.lenRPrime - s.shift) = s.t := by
          simpa [workWidth] using hwork
        rw [← hboundary] at hwork'
        simpa [readField, Nat.mod_mod_of_dvd _ hdvd] using
          hwork'
  have htarget : readField (input I)
      CompactCoefficientDirty.workTwoOffset (boundary I) =
        s.tPrime >>> s.shift := by
    calc
      readField (input I) CompactCoefficientDirty.workTwoOffset (boundary I) =
          readField (readField (input I)
            CompactCoefficientDirty.workTwoOffset 257) 0 (boundary I) := by
        symm
        exact readField_readField (by simpa using hboundaryFit)
      _ = readField (readField I PackedStepLayout.workTwoOffset 257)
          0 (boundary I) := by rw [hinputWorkTwo]
      _ = readField I PackedStepLayout.workTwoOffset (boundary I) := by
        exact readField_readField (by simpa using hboundaryFit)
      _ = readField (encodeWork2 256 s) 0 (boundary I) := by
        rw [← PackedState.read_workTwo]
        have hwide : boundary I ≤ 259 := hboundaryFit.trans (by omega)
        exact (readField_readField (i := I)
          (D := PackedStepLayout.workTwoOffset) (W := 259)
          (off := 0) (len := boundary I) (by simpa using hwide)).symm
      _ = s.tPrime >>> s.shift := by
        rw [hboundary]
        exact ReachableStepDomain.phaseFour_work2Coefficient
          h hphaseOne hphaseTwo
  have htWidth : s.t < 2 ^ boundary I := by
    rw [← hsource]
    exact readField_lt _ _ _
  have huWidth : s.tPrime >>> s.shift < 2 ^ boundary I := by
    rw [← htarget]
    exact readField_lt _ _ _
  have hdifference := Adder.difference_add
    (modulus := 2 ^ boundary I) (a := s.t)
    (b := s.tPrime >>> s.shift) (Nat.two_pow_pos _) htWidth huWidth
  have htargetValue : targetValue I = s.tPrime >>> s.shift := by
    simp only [targetValue, total, difference, hsource, htarget]
    rw [Nat.add_comm]
    exact hdifference.1
  have hsignBeforeAdd : signBeforeAdd I = boolValue (!s.sign) := by
    cases hs : s.sign
    · have hzero : bitValue (input I)
          CompactCoefficientDirty.signWire = 0 := by
        simpa [hs, boolValue] using hinputSign
      simpa [signBeforeAdd, hs, boolValue] using
        (PrunedSelectSwap.Tree.bitValue_xor_self_zero hzero)
    · have hone : bitValue (input I)
          CompactCoefficientDirty.signWire = 1 := by
        simpa [hs, boolValue] using hinputSign
      simpa [signBeforeAdd, hs, boolValue] using
        (PrunedSelectSwap.Tree.bitValue_xor_self_one hone)
  have hsignBorrow : boolValue s.sign =
      Adder.borrow s.t (s.tPrime >>> s.shift) := by
    have hcompare : (s.tPrime >>> s.shift < s.t) ↔
        (s.tPrime < shifted s.t s.shift) := by
      have hle := shifted_le_iff_le_shiftRight s.t s.tPrime s.shift
      omega
    rw [hstate.2.2.2.2.2.2]
    by_cases hlt : s.tPrime >>> s.shift < s.t
    · rw [Adder.borrow, if_pos hlt]
      simp [hcompare.mp hlt, boolValue]
    · rw [Adder.borrow, if_neg hlt]
      have hnot : ¬s.tPrime < shifted s.t s.shift := by
        exact fun hlt' => hlt (hcompare.mpr hlt')
      simp [hnot, boolValue]
  have htotalDiv : total I / 2 ^ boundary I =
      Adder.borrow s.t (s.tPrime >>> s.shift) := by
    simp only [total, difference, hsource, htarget]
    rw [Nat.add_comm]
    exact hdifference.2
  have hsignValue : signValue I = 1 := by
    simp only [signValue, hsignBeforeAdd, htotalDiv, ← hsignBorrow]
    cases s.sign <;> rfl
  have hact := gates_act (I := I) hboundaryRange hinputPhaseOne
    hinputPhaseTwo hinputControl hinputScratch hinputCarry hinputAccumulator
    hinputCellScratch htfit hsum
  rw [htargetValue, hsignValue] at hact
  have hphysicalTarget : readField I PackedStepLayout.workTwoOffset
      (boundary I) = s.tPrime >>> s.shift := by
    calc
      readField I PackedStepLayout.workTwoOffset (boundary I) =
          readField (readField I PackedStepLayout.workTwoOffset 259)
            0 (boundary I) := by
        symm
        exact readField_readField (by omega)
      _ = readField (encodeWork2 256 s) 0 (boundary I) := by
        rw [PackedState.read_workTwo]
      _ = s.tPrime >>> s.shift := by
        rw [hboundary]
        exact ReachableStepDomain.phaseFour_work2Coefficient
          h hphaseOne hphaseTwo
  rw [← hphysicalTarget, writeField_read] at hact
  have hphaseOneWrite : writeField I PackedStepLayout.phaseOneWire 1 1 = I := by
    have hread : readField I PackedStepLayout.phaseOneWire 1 = 1 := by
      rw [readField_one]
      simpa [I, hphaseOne, boolValue] using PackedState.read_phaseOne s
    simpa [hread] using
      (writeField_read I PackedStepLayout.phaseOneWire 1)
  have hphaseTwoWrite : writeField I PackedStepLayout.phaseTwoWire 1 1 = I := by
    have hread : readField I PackedStepLayout.phaseTwoWire 1 = 1 := by
      rw [readField_one]
      simpa [I, hphaseTwo, boolValue] using PackedState.read_phaseTwo s
    simpa [hread] using
      (writeField_read I PackedStepLayout.phaseTwoWire 1)
  rw [hact]
  calc
    writeField I PackedStepLayout.signWire 1 1 =
        writeField
          (writeField
            (writeField I PackedStepLayout.phaseOneWire 1 1)
            PackedStepLayout.phaseTwoWire 1 1)
          PackedStepLayout.signWire 1 1 := by
      rw [hphaseOneWrite, hphaseTwoWrite]
    _ = PackedState.encoded { s with sign := true } := by
      simpa [I, hphaseOne, hphaseTwo, boolValue] using
        PackedState.encoded_write_phaseSign s true true true

end PackedCoefficient
end Euclid
end VQ
