/-
Ownership control and phase-wire preparation in the 571-wire Euclidean core.
-/
import VQ.Euclid.PackedPhase
import VQ.Euclid.PackedSwapLengthState

namespace VQ
namespace Euclid
namespace PackedOwnership

open Reversible

def selectorLayout : Layout := Phase.layout 9 9

def selectorWiring : Wiring :=
  [PackedStepLayout.phaseOneWire, PackedStepLayout.phaseTwoWire,
    PackedStepLayout.signWire, PackedStepLayout.lengthQOffset,
    PackedStepLayout.lengthTOffset, PackedStepLayout.shiftOffset,
    PackedStepLayout.poolOffset + 1, PackedStepLayout.extensionWire,
    PackedStepLayout.poolOffset + 2, PackedStepLayout.iterationWire,
    PackedStepLayout.poolOffset + 3, PackedStepLayout.poolOffset + 4]

def selectGates : List RGate :=
  PackedStepLayout.placed selectorLayout selectorWiring
    (Phase.ownershipSelectGates 9 9)

def unselectGates : List RGate :=
  PackedStepLayout.placed selectorLayout selectorWiring
    (Phase.ownershipUnselectGates 9 9)

def selectorInput (I : Nat) : Nat :=
  gatherBits (place selectorLayout selectorWiring) selectorLayout.width I

def zeroQValue (I : Nat) : Nat :=
  Phase.selectorValue 9 PackedStepLayout.lengthQOffset I

def zeroShiftValue (I : Nat) : Nat :=
  Phase.selectorValue 9 PackedStepLayout.shiftOffset I

def selected (I : Nat) : Nat :=
  writeField
    (writeField I (PackedStepLayout.poolOffset + 1) 1 (zeroQValue I))
    (PackedStepLayout.poolOffset + 2) 1 (zeroShiftValue I)

def cleaned (I : Nat) : Nat :=
  writeField
    (writeField I (PackedStepLayout.poolOffset + 2) 1 0)
    (PackedStepLayout.poolOffset + 1) 1 0

theorem selector_disjoint : Wiring.Disjoint selectorLayout selectorWiring := by
  intro j k hj hk hne
  simp [selectorWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [selectorLayout, selectorWiring, Phase.layout, Layout.size,
      PackedStepLayout.phaseOneWire, PackedStepLayout.phaseTwoWire,
      PackedStepLayout.signWire, PackedStepLayout.lengthQOffset,
      PackedStepLayout.lengthTOffset, PackedStepLayout.shiftOffset,
      PackedStepLayout.poolOffset, PackedStepLayout.extensionWire,
      PackedStepLayout.iterationWire]

set_option maxRecDepth 4096 in
theorem selector_bound : ∀ j, j < selectorLayout.length →
    selectorWiring.getD j 0 + selectorLayout.size j ≤
      PackedStepLayout.width := by
  decide +kernel

private theorem selectLocal_wellFormed :
    (Phase.ownershipSelectGates 9 9).all
      (RGate.wellFormed selectorLayout.width) = true := by
  have h := Phase.circuit_wellFormed 9 9
  simp only [Phase.circuit, RCircuit.wellFormed, Phase.gates,
    List.all_append, Bool.and_eq_true] at h
  simp [selectorLayout, Phase.ownershipSelectGates, h.2, h.1.1.2]

private theorem unselectLocal_wellFormed :
    (Phase.ownershipUnselectGates 9 9).all
      (RGate.wellFormed selectorLayout.width) = true := by
  have h := Phase.circuit_wellFormed 9 9
  simp only [Phase.circuit, RCircuit.wellFormed, Phase.gates,
    List.all_append, Bool.and_eq_true] at h
  simp [selectorLayout, Phase.ownershipUnselectGates, h.2, h.1.1.2]

theorem selectGates_wellFormed :
    selectGates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  unfold selectGates PackedStepLayout.placed
  apply wellFormed_placeGates selector_disjoint (by decide) selector_bound
  intro g hg
  exact List.all_eq_true.mp selectLocal_wellFormed g hg

theorem unselectGates_wellFormed :
    unselectGates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  unfold unselectGates PackedStepLayout.placed
  apply wellFormed_placeGates selector_disjoint (by decide) selector_bound
  intro g hg
  exact List.all_eq_true.mp unselectLocal_wellFormed g hg

theorem selectorInput_field (j I : Nat) (hj : j < selectorWiring.length) :
    selectorLayout.read (selectorInput I) j =
      readField I (selectorWiring.getD j 0) (selectorLayout.size j) := by
  exact read_gatherBits selectorLayout selectorWiring j I hj

theorem selectorInput_lengthQ (I : Nat) :
    readField (selectorInput I) Phase.lenQOffset 9 =
      readField I PackedStepLayout.lengthQOffset 9 := by
  simpa [selectorInput, selectorLayout, selectorWiring, Phase.layout,
    Phase.lenQOffset, Layout.read, Layout.offset, Layout.size] using
      selectorInput_field 3 I (by decide)

theorem selectorInput_shift (I : Nat) :
    readField (selectorInput I) (Phase.shiftOffset 9) 9 =
      readField I PackedStepLayout.shiftOffset 9 := by
  simpa [selectorInput, selectorLayout, selectorWiring, Phase.layout,
    Phase.shiftOffset, Layout.read, Layout.offset, Layout.size] using
      selectorInput_field 5 I (by decide)

theorem selectorInput_zeroQ (I : Nat) :
    bitValue (selectorInput I) (Phase.zeroQWire 9 9) =
      bitValue I (PackedStepLayout.poolOffset + 1) := by
  rw [← readField_one, ← readField_one]
  simpa [selectorInput, selectorLayout, selectorWiring, Phase.layout,
    Phase.zeroQWire, Phase.shiftOffset, Layout.read, Layout.offset,
    Layout.size] using selectorInput_field 6 I (by decide)

theorem selectorInput_zeroShift (I : Nat) :
    bitValue (selectorInput I) (Phase.zeroShiftWire 9 9) =
      bitValue I (PackedStepLayout.poolOffset + 2) := by
  rw [← readField_one, ← readField_one]
  simpa [selectorInput, selectorLayout, selectorWiring, Phase.layout,
    Phase.zeroShiftWire, Phase.zeroQWire, Phase.shiftOffset, Layout.read,
    Layout.offset, Layout.size] using selectorInput_field 8 I (by decide)

theorem selectorInput_scratch (I : Nat) :
    readField (selectorInput I) (Phase.poolOffset 9 9) 9 =
      readField I (PackedStepLayout.poolOffset + 4) 9 := by
  simpa [selectorInput, selectorLayout, selectorWiring, Phase.layout,
    Phase.poolOffset, Phase.poolWidth, Phase.zeroQWire, Phase.shiftOffset,
    Layout.read, Layout.offset, Layout.size] using
      selectorInput_field 11 I (by decide)

theorem selectorInput_zeroQValue (I : Nat) :
    Phase.selectorValue 9 Phase.lenQOffset (selectorInput I) =
      zeroQValue I := by
  simp only [Phase.selectorValue, zeroQValue, selectorInput_lengthQ]

theorem selectorInput_zeroShiftValue (I : Nat) :
    Phase.selectorValue 9 (Phase.shiftOffset 9) (selectorInput I) =
      zeroShiftValue I := by
  simp only [Phase.selectorValue, zeroShiftValue, selectorInput_shift]

theorem selectGates_act
    {I : Nat}
    (hzeroQ : bitValue I (PackedStepLayout.poolOffset + 1) = 0)
    (hzeroShift : bitValue I (PackedStepLayout.poolOffset + 2) = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 4) 9 = 0) :
    actGates selectGates I = selected I := by
  let gathered := selectorInput I
  let result := Phase.ownershipSelected 9 9 gathered
  have hlocal :
      actGates (Phase.ownershipSelectGates 9 9) gathered = result := by
    apply Phase.ownershipSelect_act
    · exact (selectorInput_zeroQ I).trans hzeroQ
    · exact (selectorInput_zeroShift I).trans hzeroShift
    · exact (selectorInput_scratch I).trans hscratch
  have hflags := Phase.ownershipSelected_flags 9 9 gathered
  dsimp only at hflags
  have hzeroQResult : bitValue result (Phase.zeroQWire 9 9) = zeroQValue I := by
    rw [hflags.1]
    exact selectorInput_zeroQValue I
  have hzeroShiftResult :
      bitValue result (Phase.zeroShiftWire 9 9) = zeroShiftValue I := by
    rw [hflags.2]
    exact selectorInput_zeroShiftValue I
  have hlocal' :
      actGates (Phase.ownershipSelectGates 9 9) gathered =
        writeField
          (writeField gathered (Phase.zeroQWire 9 9) 1 (zeroQValue I))
          (Phase.zeroShiftWire 9 9) 1 (zeroShiftValue I) := by
    rw [hlocal]
    simpa [result, hzeroQResult, hzeroShiftResult] using
      Phase.ownershipSelected_eq_writeFields 9 9 gathered
  apply actGates_placed_write₂
      (L := selectorLayout) (W := selectorWiring) (k₁ := 6) (k₂ := 8)
      (v₁ := zeroQValue I) (v₂ := zeroShiftValue I)
      selector_disjoint (by decide) (by decide) (by decide) (by decide)
  · intro g hg
    exact List.all_eq_true.mp selectLocal_wellFormed g hg
  · simpa [selectGates, selected, gathered, selectorInput, selectorLayout,
      selectorWiring, Phase.layout, Layout.write, Layout.offset,
      Layout.size, Phase.zeroQWire, Phase.zeroShiftWire,
      Phase.shiftOffset] using hlocal'

theorem unselectGates_act
    {I : Nat}
    (hzeroQ : bitValue I (PackedStepLayout.poolOffset + 1) = zeroQValue I)
    (hzeroShift :
      bitValue I (PackedStepLayout.poolOffset + 2) = zeroShiftValue I)
    (hscratch : readField I (PackedStepLayout.poolOffset + 4) 9 = 0) :
    actGates unselectGates I = cleaned I := by
  let gathered := selectorInput I
  have hlocal :
      actGates (Phase.ownershipUnselectGates 9 9) gathered =
        Phase.ownershipCleaned 9 9 gathered := by
    apply Phase.ownershipUnselect_act
    · rw [selectorInput_zeroQ, hzeroQ, selectorInput_zeroQValue]
    · rw [selectorInput_zeroShift, hzeroShift,
        selectorInput_zeroShiftValue]
    · exact (selectorInput_scratch I).trans hscratch
  rw [Phase.ownershipCleaned_eq_writeFields] at hlocal
  apply actGates_placed_write₂
      (L := selectorLayout) (W := selectorWiring) (k₁ := 8) (k₂ := 6)
      (v₁ := 0) (v₂ := 0) selector_disjoint (by decide)
      (by decide) (by decide) (by decide)
  · intro g hg
    exact List.all_eq_true.mp unselectLocal_wellFormed g hg
  · simpa [unselectGates, cleaned, gathered, selectorInput, selectorLayout,
      selectorWiring, Phase.layout, Layout.write, Layout.offset,
      Layout.size, Phase.zeroQWire, Phase.zeroShiftWire,
      Phase.shiftOffset] using hlocal

def controlWire : Nat := PackedStepLayout.poolOffset

def zeroQWire : Nat := PackedStepLayout.poolOffset + 1

def zeroShiftWire : Nat := PackedStepLayout.poolOffset + 2

def controlGates : List RGate :=
  Phase.ccxGates zeroQWire zeroShiftWire controlWire

theorem controlGates_wellFormed :
    controlGates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  decide

def controlPrepared (I : Nat) : Nat :=
  writeField I controlWire 1
    ((bitValue I controlWire + zeroQValue I * zeroShiftValue I) % 2)

def prepareGates : List RGate :=
  selectGates ++ controlGates ++ unselectGates

theorem zeroQValue_lt (I : Nat) : zeroQValue I < 2 :=
  Phase.selectorValue_lt 9 PackedStepLayout.lengthQOffset I

theorem zeroShiftValue_lt (I : Nat) : zeroShiftValue I < 2 :=
  Phase.selectorValue_lt 9 PackedStepLayout.shiftOffset I

theorem selected_zeroQ (I : Nat) :
    bitValue (selected I) zeroQWire = zeroQValue I := by
  change bitValue (selected I) (PackedStepLayout.poolOffset + 1) = _
  rw [selected, bitValue_write_ne (by decide), bitValue_write_self,
    Nat.mod_eq_of_lt (zeroQValue_lt I)]

theorem selected_zeroShift (I : Nat) :
    bitValue (selected I) zeroShiftWire = zeroShiftValue I := by
  change bitValue (selected I) (PackedStepLayout.poolOffset + 2) = _
  rw [selected, bitValue_write_self,
    Nat.mod_eq_of_lt (zeroShiftValue_lt I)]

theorem selected_control (I : Nat) :
    bitValue (selected I) controlWire = bitValue I controlWire := by
  change bitValue (selected I) PackedStepLayout.poolOffset =
    bitValue I PackedStepLayout.poolOffset
  rw [selected, bitValue_write_ne (by decide),
    bitValue_write_ne (by decide)]

theorem selected_zeroQValue (I : Nat) : zeroQValue (selected I) = zeroQValue I := by
  unfold zeroQValue Phase.selectorValue
  rw [selected, readField_writeField_of_disjoint (by decide),
    readField_writeField_of_disjoint (by decide)]

theorem selected_zeroShiftValue (I : Nat) :
    zeroShiftValue (selected I) = zeroShiftValue I := by
  unfold zeroShiftValue Phase.selectorValue
  rw [selected, readField_writeField_of_disjoint (by decide),
    readField_writeField_of_disjoint (by decide)]

theorem selected_scratch
    {I : Nat} (hscratch :
      readField I (PackedStepLayout.poolOffset + 4) 9 = 0) :
    readField (selected I) (PackedStepLayout.poolOffset + 4) 9 = 0 := by
  rw [selected, readField_writeField_of_disjoint (by decide),
    readField_writeField_of_disjoint (by decide), hscratch]

theorem zeroQValue_writeControl (I value : Nat) :
    zeroQValue (writeField I controlWire 1 value) = zeroQValue I := by
  unfold zeroQValue Phase.selectorValue
  rw [readField_writeField_of_disjoint (by decide)]

theorem zeroShiftValue_writeControl (I value : Nat) :
    zeroShiftValue (writeField I controlWire 1 value) = zeroShiftValue I := by
  unfold zeroShiftValue Phase.selectorValue
  rw [readField_writeField_of_disjoint (by decide)]

theorem cleaned_selected
    {I : Nat}
    (hzeroQ : bitValue I zeroQWire = 0)
    (hzeroShift : bitValue I zeroShiftWire = 0) :
    cleaned (selected I) = I := by
  have hwriteQ : writeField I zeroQWire 1 0 = I := by
    apply write_of_bitValue
    simpa using hzeroQ.symm
  have hwriteShift : writeField I zeroShiftWire 1 0 = I := by
    apply write_of_bitValue
    simpa using hzeroShift.symm
  have hwriteQ' :
      writeField I (PackedStepLayout.poolOffset + 1) 1 0 = I := by
    simpa [zeroQWire] using hwriteQ
  have hwriteShift' :
      writeField I (PackedStepLayout.poolOffset + 2) 1 0 = I := by
    simpa [zeroShiftWire] using hwriteShift
  simp only [cleaned, selected]
  rw [writeField_writeField, writeField_comm (by decide),
    writeField_writeField, hwriteQ', hwriteShift']

theorem prepareGates_act
    {I : Nat}
    (hzeroQ : bitValue I zeroQWire = 0)
    (hzeroShift : bitValue I zeroShiftWire = 0)
    (hscratch : readField I (PackedStepLayout.poolOffset + 4) 9 = 0) :
    actGates prepareGates I = controlPrepared I := by
  have hselect := selectGates_act hzeroQ hzeroShift hscratch
  let C := Phase.ccxOut zeroQWire zeroShiftWire controlWire (selected I)
  have hcontrol : actGates controlGates (selected I) = C := by
    exact Phase.ccxGates_act zeroQWire zeroShiftWire controlWire (selected I)
  have hCzeroQ : bitValue C zeroQWire = zeroQValue C := by
    rw [Phase.ccxOut_ne (by decide), selected_zeroQ]
    symm
    simp only [C, Phase.ccxOut, zeroQValue_writeControl,
      selected_zeroQValue]
  have hCzeroShift : bitValue C zeroShiftWire = zeroShiftValue C := by
    rw [Phase.ccxOut_ne (by decide), selected_zeroShift]
    symm
    simp only [C, Phase.ccxOut, zeroShiftValue_writeControl,
      selected_zeroShiftValue]
  have hCscratch :
      readField C (PackedStepLayout.poolOffset + 4) 9 = 0 := by
    rw [show C = writeField (selected I) controlWire 1
        ((bitValue (selected I) controlWire +
          bitValue (selected I) zeroQWire *
          bitValue (selected I) zeroShiftWire) % 2) by rfl,
      readField_writeField_of_disjoint (by decide),
      selected_scratch hscratch]
  have hunselect := unselectGates_act hCzeroQ hCzeroShift hCscratch
  have hCeq : C = writeField (selected I) controlWire 1
      ((bitValue I controlWire + zeroQValue I * zeroShiftValue I) % 2) := by
    simp only [C, Phase.ccxOut]
    rw [selected_control, selected_zeroQ, selected_zeroShift]
  have hcleaned : cleaned C = controlPrepared I := by
    let value :=
      (bitValue I controlWire + zeroQValue I * zeroShiftValue I) % 2
    calc
      cleaned C = writeField (cleaned (selected I)) controlWire 1 value := by
        rw [hCeq]
        simp only [cleaned, value]
        calc
          writeField
              (writeField
                (writeField (selected I) controlWire 1 value)
                (PackedStepLayout.poolOffset + 2) 1 0)
              (PackedStepLayout.poolOffset + 1) 1 0 =
            writeField
              (writeField
                (writeField (selected I)
                  (PackedStepLayout.poolOffset + 2) 1 0)
                controlWire 1 value)
              (PackedStepLayout.poolOffset + 1) 1 0 := by
                apply congrArg (fun J => writeField J
                  (PackedStepLayout.poolOffset + 1) 1 0)
                exact writeField_comm (by decide)
          _ = writeField
              (writeField
                (writeField (selected I)
                  (PackedStepLayout.poolOffset + 2) 1 0)
                (PackedStepLayout.poolOffset + 1) 1 0)
              controlWire 1 value := writeField_comm (by decide)
      _ = writeField I controlWire 1 value := by
        rw [cleaned_selected hzeroQ hzeroShift]
      _ = controlPrepared I := rfl
  rw [prepareGates, actGates_append, actGates_append, hselect, hcontrol,
    hunselect, hcleaned]

theorem prepareGates_wellFormed :
    prepareGates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  simp [prepareGates, selectGates_wellFormed, controlGates_wellFormed,
    unselectGates_wellFormed]

theorem prepareGates_zeroFields
    {I control : Nat}
    (hcontrol : bitValue I controlWire = control)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 = encodedZero 9)
    (hshift : readField I PackedStepLayout.shiftOffset 9 = encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates prepareGates I =
      writeField I controlWire 1 ((control + 1) % 2) := by
  have hzeroQ : bitValue I zeroQWire = 0 := by
    rw [← readField_one]
    exact readField_narrow (by decide) htail
  have hzeroShift : bitValue I zeroShiftWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero
      (off := PackedStepLayout.poolOffset + 1) (len := 12)
      (o := zeroShiftWire) (l := 1)
      (by simp [zeroShiftWire]) (by simp [zeroShiftWire]) htail
  have hscratch : readField I (PackedStepLayout.poolOffset + 4) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) htail
  have hzeroQValue : zeroQValue I = 1 := by
    unfold zeroQValue Phase.selectorValue
    rw [if_pos hlengthQ]
  have hzeroShiftValue : zeroShiftValue I = 1 := by
    unfold zeroShiftValue Phase.selectorValue
    rw [if_pos hshift]
  rw [prepareGates_act hzeroQ hzeroShift hscratch, controlPrepared,
    hcontrol, hzeroQValue, hzeroShiftValue, Nat.mul_one]

theorem prepareGates_enable
    {I : Nat}
    (hcontrol : bitValue I controlWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 = encodedZero 9)
    (hshift : readField I PackedStepLayout.shiftOffset 9 = encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates prepareGates I = writeField I controlWire 1 1 := by
  simpa using prepareGates_zeroFields hcontrol hlengthQ hshift htail

theorem prepareGates_disable
    {I : Nat}
    (hcontrol : bitValue I controlWire = 1)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 = encodedZero 9)
    (hshift : readField I PackedStepLayout.shiftOffset 9 = encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates prepareGates I = writeField I controlWire 1 0 := by
  simpa using prepareGates_zeroFields hcontrol hlengthQ hshift htail

def phaseClearGates : List RGate :=
  [.cx controlWire PackedStepLayout.phaseOneWire,
    .x PackedStepLayout.phaseOneWire]

def phaseRestoreGates : List RGate :=
  [.x PackedStepLayout.phaseOneWire,
    .cx controlWire PackedStepLayout.phaseOneWire]

theorem phaseClearGates_wellFormed :
    phaseClearGates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  decide

theorem phaseRestoreGates_wellFormed :
    phaseRestoreGates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  decide

theorem phaseClearGates_active
    {I : Nat}
    (hcontrol : bitValue I controlWire = 1)
    (hphase : bitValue I PackedStepLayout.phaseOneWire = 0) :
    actGates phaseClearGates I = I := by
  rw [phaseClearGates, actGates_cons, actGates_cons, actGates_nil,
    act_cx_write, act_x_write, bitValue_write_self, hcontrol, hphase]
  norm_num
  rw [writeField_writeField]
  apply write_of_bitValue
  simp [hphase]

theorem phaseClearGates_inactive
    {I : Nat}
    (hcontrol : bitValue I controlWire = 0)
    (hphase : bitValue I PackedStepLayout.phaseOneWire = 1) :
    actGates phaseClearGates I =
      writeField I PackedStepLayout.phaseOneWire 1 0 := by
  rw [phaseClearGates, actGates_cons, actGates_cons, actGates_nil,
    act_cx_write, act_x_write, bitValue_write_self, hcontrol, hphase]
  norm_num
  rw [writeField_writeField]

theorem phaseRestoreGates_active
    {I : Nat}
    (hcontrol : bitValue I controlWire = 1)
    (hphase : bitValue I PackedStepLayout.phaseOneWire = 0) :
    actGates phaseRestoreGates I = I := by
  rw [phaseRestoreGates, actGates_cons, actGates_cons, actGates_nil, act_x_write,
    act_cx_write, bitValue_write_self,
    bitValue_write_ne (by decide), hcontrol, hphase]
  norm_num
  rw [writeField_writeField]
  apply write_of_bitValue
  simp [hphase]

theorem phaseRestoreGates_inactive
    {I : Nat}
    (hcontrol : bitValue I controlWire = 0)
    (hphase : bitValue I PackedStepLayout.phaseOneWire = 0) :
    actGates phaseRestoreGates I =
      writeField I PackedStepLayout.phaseOneWire 1 1 := by
  rw [phaseRestoreGates, actGates_cons, actGates_cons, actGates_nil, act_x_write,
    act_cx_write, bitValue_write_self,
    bitValue_write_ne (by decide), hcontrol, hphase]
  norm_num
  rw [writeField_writeField]

def iterationGates : List RGate :=
  [.cx controlWire PackedStepLayout.iterationWire]

theorem iterationGates_wellFormed :
    iterationGates.all (RGate.wellFormed PackedStepLayout.width) = true := by
  decide

theorem iterationGates_inactive
    {I : Nat} (hcontrol : bitValue I controlWire = 0) :
    actGates iterationGates I = I := by
  rw [iterationGates, actGates_cons, actGates_nil, act_cx_write, hcontrol]
  norm_num
  apply write_of_bitValue
  simp only [Nat.mod_eq_of_lt
    (bitValue_lt I PackedStepLayout.iterationWire)]

theorem iterationGates_active
    {I : Nat} (hcontrol : bitValue I controlWire = 1) :
    actGates iterationGates I =
      writeField I PackedStepLayout.iterationWire 1
        ((bitValue I PackedStepLayout.iterationWire + 1) % 2) := by
  rw [iterationGates, actGates_cons, actGates_nil, act_cx_write, hcontrol]

def gates : List RGate :=
  prepareGates ++ phaseClearGates ++ PackedSwapLength.gates ++
    phaseRestoreGates ++ iterationGates ++ prepareGates

def circuit : RCircuit :=
  { width := PackedStepLayout.width, gates := gates }

theorem circuit_wellFormed : circuit.wellFormed = true := by
  have hswap : PackedSwapLength.gates.all
      (RGate.wellFormed PackedStepLayout.width) = true := by
    simpa [PackedSwapLength.circuit, RCircuit.wellFormed] using
      PackedSwapLength.circuit_wellFormed
  simp [circuit, RCircuit.wellFormed, gates, prepareGates_wellFormed,
    phaseClearGates_wellFormed, phaseRestoreGates_wellFormed,
    iterationGates_wellFormed, hswap]

def activeOutput (I newLengthT newLengthRPrime : Nat) : Nat :=
  let prepared := writeField I controlWire 1 1
  let swapped := writeField
    (PackedSwapLength.ownershipOutput prepared newLengthT newLengthRPrime)
    PackedStepLayout.extensionWire 1 0
  let iterated := writeField swapped PackedStepLayout.iterationWire 1
    ((bitValue swapped PackedStepLayout.iterationWire + 1) % 2)
  writeField iterated controlWire 1 0

theorem writeEncodedLengthAndClearExtension
    {I length : Nat}
    (hlength : length ≤ 255)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    writeField
        (writeField I PackedStepLayout.lengthRPrimeOffset 9
          (encodeLength 9 length))
        PackedStepLayout.extensionWire 1 0 =
      writeField I PackedStepLayout.lengthRPrimeOffset 8
        (encodeLength 8 length) := by
  have hextensionBit : I.testBit PackedStepLayout.extensionWire = false :=
    (testBit_eq_false_iff_bitValue_eq_zero _ _).2 hextension
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hlow : PackedStepLayout.lengthRPrimeOffset ≤ b ∧
      b < PackedStepLayout.lengthRPrimeOffset + 8
  · have hbelowExtension : b < PackedStepLayout.extensionWire := by
      simp only [PackedStepLayout.extensionWire,
        PackedStepLayout.lengthRPrimeOffset] at hlow ⊢
      omega
    rw [testBit_writeField_outside (Or.inl hbelowExtension),
      testBit_writeField_inside hlow.1 (by omega),
      testBit_writeField_inside hlow.1 hlow.2]
    have hindex : b - PackedStepLayout.lengthRPrimeOffset < 8 := by omega
    have hlowValue := congrArg
      (fun value => value.testBit (b - PackedStepLayout.lengthRPrimeOffset))
      (PackedSwapLength.encodeLength_nine_low hlength)
    simpa only [Nat.testBit_mod_two_pow, hindex, decide_true,
      Bool.true_and] using hlowValue
  · by_cases hhigh : b = PackedStepLayout.extensionWire
    · subst b
      rw [testBit_writeField_inside (by omega) (by omega),
        testBit_writeField_outside (Or.inr (by decide)), hextensionBit]
      norm_num
    · have houtExtension : b < PackedStepLayout.extensionWire ∨
          PackedStepLayout.extensionWire + 1 ≤ b := by
        simp only [PackedStepLayout.extensionWire] at hhigh ⊢
        omega
      have houtNine : b < PackedStepLayout.lengthRPrimeOffset ∨
          PackedStepLayout.lengthRPrimeOffset + 9 ≤ b := by
        simp only [PackedStepLayout.extensionWire,
          PackedStepLayout.lengthRPrimeOffset] at hhigh hlow ⊢
        omega
      have houtEight : b < PackedStepLayout.lengthRPrimeOffset ∨
          PackedStepLayout.lengthRPrimeOffset + 8 ≤ b := by
        omega
      rw [testBit_writeField_outside houtExtension,
        testBit_writeField_outside houtNine,
        testBit_writeField_outside houtEight]

theorem activeOutput_encodedLength
    {I newLengthT length : Nat}
    (hlength : length ≤ 255)
    (hcontrol : bitValue I controlWire = 0)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    activeOutput I newLengthT (encodeLength 9 length) =
      writeField
        (writeField
          (writeField
            (writeField
              (writeField I PackedStepLayout.workOneOffset 259
                (readField I PackedStepLayout.workTwoOffset 259))
              PackedStepLayout.workTwoOffset 259
                (readField I PackedStepLayout.workOneOffset 259))
            PackedStepLayout.lengthTOffset 9 newLengthT)
          PackedStepLayout.lengthRPrimeOffset 8 (encodeLength 8 length))
        PackedStepLayout.iterationWire 1
          ((bitValue I PackedStepLayout.iterationWire + 1) % 2) := by
  let J := writeField I controlWire 1 1
  let C :=
    (writeField
      (writeField
        (writeField J PackedStepLayout.workOneOffset 259
          (readField J PackedStepLayout.workTwoOffset 259))
        PackedStepLayout.workTwoOffset 259
          (readField J PackedStepLayout.workOneOffset 259))
      PackedStepLayout.lengthTOffset 9 newLengthT)
  let A := writeField C PackedStepLayout.lengthRPrimeOffset 9
    (encodeLength 9 length)
  have hreadWorkOne : readField J PackedStepLayout.workOneOffset 259 =
      readField I PackedStepLayout.workOneOffset 259 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide)]
  have hreadWorkTwo : readField J PackedStepLayout.workTwoOffset 259 =
      readField I PackedStepLayout.workTwoOffset 259 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide)]
  have hCextension : bitValue C PackedStepLayout.extensionWire =
      bitValue I PackedStepLayout.extensionWire := by
    simp only [C]
    rw [bitValue_write_out (by decide), bitValue_write_out (by decide),
      bitValue_write_out (by decide)]
    simp only [J]
    rw [bitValue_write_ne (by decide)]
  have hlengthWrite : writeField A PackedStepLayout.extensionWire 1 0 =
      writeField
        (writeField
          (writeField
            (writeField J PackedStepLayout.workOneOffset 259
              (readField J PackedStepLayout.workTwoOffset 259))
            PackedStepLayout.workTwoOffset 259
              (readField J PackedStepLayout.workOneOffset 259))
          PackedStepLayout.lengthTOffset 9 newLengthT)
        PackedStepLayout.lengthRPrimeOffset 8 (encodeLength 8 length) := by
    simpa only [A, C] using writeEncodedLengthAndClearExtension
      (I := C) hlength (hCextension.trans hextension)
  let B := writeField A PackedStepLayout.extensionWire 1 0
  have hiteration : bitValue B PackedStepLayout.iterationWire =
      bitValue I PackedStepLayout.iterationWire := by
    simp only [B, A, C]
    rw [bitValue_write_ne (by decide), bitValue_write_out (by decide),
      bitValue_write_out (by decide), bitValue_write_out (by decide),
      bitValue_write_out (by decide)]
    simp only [J]
    rw [bitValue_write_ne (by decide)]
  simp only [activeOutput, PackedSwapLength.ownershipOutput]
  change writeField
      (writeField B PackedStepLayout.iterationWire 1
        ((bitValue B PackedStepLayout.iterationWire + 1) % 2))
      controlWire 1 0 = _
  rw [hiteration]
  simp only [B]
  rw [hlengthWrite]
  simp only [J]
  rw [hreadWorkOne, hreadWorkTwo]
  rw [writeField_comm (o₁ := PackedStepLayout.iterationWire)
      (o₂ := controlWire) (by decide),
    writeField_comm (o₁ := PackedStepLayout.lengthRPrimeOffset)
      (n₁ := 8) (o₂ := controlWire) (by decide),
    writeField_comm (o₁ := PackedStepLayout.lengthTOffset)
      (n₁ := 9) (o₂ := controlWire) (by decide),
    writeField_comm (o₁ := PackedStepLayout.workTwoOffset)
      (n₁ := 259) (o₂ := controlWire) (by decide),
    writeField_comm (o₁ := PackedStepLayout.workOneOffset)
      (n₁ := 259) (o₂ := controlWire) (by decide),
    writeField_writeField]
  have hclear : writeField I controlWire 1 0 = I := by
    apply write_of_bitValue
    simpa using hcontrol.symm
  rw [hclear]

theorem gates_active
    {p I : Nat} {s : State}
    (hdomain : StepDomain p 256 9 9 s)
    (hphaseOne : s.phase1 = true)
    (hphaseTwo : s.phase2 = true)
    (hlengthRPrimeBound : s.lenRPrime ≤ 255)
    (hcontrol : bitValue I controlWire = 0)
    (hphysicalPhaseOne : bitValue I PackedStepLayout.phaseOneWire = 0)
    (hphysicalSign : bitValue I PackedStepLayout.signWire = 0)
    (hlengthQ : readField I PackedStepLayout.lengthQOffset 9 = encodedZero 9)
    (hshift : readField I PackedStepLayout.shiftOffset 9 = encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0)
    (hworkOne : readField I PackedStepLayout.workOneOffset 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r)
    (hworkTwo : readField I PackedStepLayout.workTwoOffset 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime)
    (hlengthT : readField I PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT)
    (hlengthRPrime : readField I PackedStepLayout.lengthRPrimeOffset 8 =
      encodeLength 8 s.lenRPrime)
    (hextension : bitValue I PackedStepLayout.extensionWire = 0) :
    actGates gates I = activeOutput I
      (encodeLength 9 (bitLength s.tPrime))
      (encodeLength 9 (bitLength s.r)) := by
  let J := writeField I controlWire 1 1
  have hprepared : actGates prepareGates I = J := by
    simpa [J] using prepareGates_enable hcontrol hlengthQ hshift htail
  have hJcontrol : bitValue J controlWire = 1 := by
    simp [J, bitValue_write_self]
  have hJphaseOne : bitValue J PackedStepLayout.phaseOneWire = 0 := by
    simp only [J]
    rw [bitValue_write_ne (by decide), hphysicalPhaseOne]
  have hJsign : bitValue J PackedStepLayout.signWire = 0 := by
    simp only [J]
    rw [bitValue_write_ne (by decide), hphysicalSign]
  have hJlengthQ :
      readField J PackedStepLayout.lengthQOffset 9 = encodedZero 9 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hlengthQ]
  have hJshift :
      readField J PackedStepLayout.shiftOffset 9 = encodedZero 9 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hshift]
  have hJtail : readField J (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), htail]
  have hJworkOne : readField J PackedStepLayout.workOneOffset 259 =
      encodeSplit 259 (s.lenT + 1) s.t s.r := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hworkOne]
  have hJworkTwo : readField J PackedStepLayout.workTwoOffset 259 =
      encodeSplit 259 (259 - s.lenRPrime) s.tPrime s.rPrime := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hworkTwo]
  have hJlengthT : readField J PackedStepLayout.lengthTOffset 9 =
      encodeLength 9 s.lenT := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hlengthT]
  have hJlengthRPrime :
      readField J PackedStepLayout.lengthRPrimeOffset 8 =
        encodeLength 8 s.lenRPrime := by
    simp only [J]
    rw [readField_writeField_of_disjoint (by decide), hlengthRPrime]
  have hJextension : bitValue J PackedStepLayout.extensionWire = 0 := by
    simp only [J]
    rw [bitValue_write_ne (by decide), hextension]
  have hphaseClear : actGates phaseClearGates J = J :=
    phaseClearGates_active hJcontrol hJphaseOne
  let K := writeField
    (PackedSwapLength.ownershipOutput J
      (encodeLength 9 (bitLength s.tPrime))
      (encodeLength 9 (bitLength s.r)))
    PackedStepLayout.extensionWire 1 0
  have hswap : actGates PackedSwapLength.gates J = K := by
    simpa [K] using PackedSwapLength.gates_act_stepDomain
      hdomain hphaseOne hphaseTwo hlengthRPrimeBound hJcontrol hJphaseOne
      hJsign hJtail hJworkOne hJworkTwo hJlengthT hJlengthRPrime hJextension
  have hKcontrol : bitValue K controlWire = 1 := by
    simp only [K]
    rw [bitValue_write_ne (by decide)]
    simpa [controlWire] using
      PackedSwapLength.ownershipOutput_control hJcontrol
  have hKphaseOne : bitValue K PackedStepLayout.phaseOneWire = 0 := by
    simp only [K, PackedSwapLength.ownershipOutput]
    rw [bitValue_write_out (by decide), bitValue_write_out (by decide),
      bitValue_write_out (by decide), bitValue_write_out (by decide),
      bitValue_write_out (by decide)]
    exact hJphaseOne
  have hKlengthQ :
      readField K PackedStepLayout.lengthQOffset 9 = encodedZero 9 := by
    simp only [K, PackedSwapLength.ownershipOutput]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact hJlengthQ
  have hKshift :
      readField K PackedStepLayout.shiftOffset 9 = encodedZero 9 := by
    simp only [K, PackedSwapLength.ownershipOutput]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact hJshift
  have hKtail : readField K (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [K, PackedSwapLength.ownershipOutput]
    rw [readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide),
      readField_writeField_of_disjoint (by decide)]
    exact hJtail
  have hphaseRestore : actGates phaseRestoreGates K = K :=
    phaseRestoreGates_active hKcontrol hKphaseOne
  let L := writeField K PackedStepLayout.iterationWire 1
    ((bitValue K PackedStepLayout.iterationWire + 1) % 2)
  have hiteration : actGates iterationGates K = L := by
    simpa [L] using iterationGates_active hKcontrol
  have hLcontrol : bitValue L controlWire = 1 := by
    simp only [L]
    rw [bitValue_write_ne (by decide), hKcontrol]
  have hLlengthQ :
      readField L PackedStepLayout.lengthQOffset 9 = encodedZero 9 := by
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide), hKlengthQ]
  have hLshift :
      readField L PackedStepLayout.shiftOffset 9 = encodedZero 9 := by
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide), hKshift]
  have hLtail : readField L (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    simp only [L]
    rw [readField_writeField_of_disjoint (by decide), hKtail]
  have hfinal : actGates prepareGates L = writeField L controlWire 1 0 :=
    prepareGates_disable hLcontrol hLlengthQ hLshift hLtail
  simp only [gates, actGates_append]
  rw [hprepared, hphaseClear, hswap, hphaseRestore, hiteration, hfinal]
  rfl

private theorem gates_inactive_of_selector_zero
    {I : Nat}
    (hcontrol : bitValue I controlWire = 0)
    (hselector : zeroQValue I * zeroShiftValue I = 0)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates gates I = I := by
  have hzeroQ : bitValue I zeroQWire = 0 := by
    rw [← readField_one]
    exact readField_narrow (by omega) htail
  have hzeroShift : bitValue I zeroShiftWire = 0 := by
    rw [← readField_one]
    exact readField_sub_zero
      (off := PackedStepLayout.poolOffset + 1) (len := 12)
      (o := zeroShiftWire) (l := 1)
      (by simp [zeroShiftWire]) (by simp [zeroShiftWire]) htail
  have hscratch :
      readField I (PackedStepLayout.poolOffset + 4) 9 = 0 :=
    readField_sub_zero (by omega) (by omega) htail
  have hprepared : actGates prepareGates I = I := by
    rw [prepareGates_act hzeroQ hzeroShift hscratch, controlPrepared,
      hcontrol, hselector]
    simp only [Nat.add_zero, Nat.zero_mod]
    apply write_of_bitValue
    simpa using hcontrol.symm
  let P := actGates phaseClearGates I
  have hcontrolP : bitValue P controlWire = 0 := by
    simp only [P, phaseClearGates, actGates_cons, actGates_nil]
    rw [act_cx_write, act_x_write,
      bitValue_write_ne (by decide), bitValue_write_ne (by decide), hcontrol]
  have htailP : readField P (PackedStepLayout.poolOffset + 1) 12 = 0 := by
    dsimp only [P]
    rw [readField_actGates_of_outside, htail]
    intro g hg q hq
    simp [phaseClearGates] at hg
    rcases hg with rfl | rfl <;>
      simp [RGate.wires, controlWire, PackedStepLayout.poolOffset,
        PackedStepLayout.phaseOneWire] at hq ⊢ <;> omega
  have hownership : actGates PackedSwapLength.gates P = P :=
    PackedSwapLength.gates_inactive hcontrolP htailP
  have hphaseRestore : actGates phaseRestoreGates P = I := by
    change actGates phaseClearGates.reverse (actGates phaseClearGates I) = I
    exact actGates_reverse phaseClearGates_wellFormed I
  have hiteration : actGates iterationGates I = I :=
    iterationGates_inactive hcontrol
  simp only [gates, actGates_append]
  rw [hprepared, hownership, hphaseRestore, hiteration,
    hprepared]

theorem gates_inactive
    {I : Nat}
    (hcontrol : bitValue I controlWire = 0)
    (hshift : readField I PackedStepLayout.shiftOffset 9 ≠ encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates gates I = I := by
  apply gates_inactive_of_selector_zero hcontrol _ htail
  unfold zeroShiftValue Phase.selectorValue
  rw [if_neg hshift, Nat.mul_zero]

theorem gates_inactive_lengthQ
    {I : Nat}
    (hcontrol : bitValue I controlWire = 0)
    (hlengthQ :
      readField I PackedStepLayout.lengthQOffset 9 ≠ encodedZero 9)
    (htail : readField I (PackedStepLayout.poolOffset + 1) 12 = 0) :
    actGates gates I = I := by
  apply gates_inactive_of_selector_zero hcontrol _ htail
  unfold zeroQValue Phase.selectorValue
  rw [if_neg hlengthQ, Nat.zero_mul]

end PackedOwnership
end Euclid
end VQ
