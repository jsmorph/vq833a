import VQ.Euclid.Step

namespace VQ
namespace Euclid
namespace StepBlocks

open Reversible

theorem Internal.auxSubfieldClear
    {n lengthWidth shiftWidth I off width : Nat}
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hlo : StepLayout.auxOffset n lengthWidth shiftWidth ≤ off)
    (hhi : off + width ≤ StepLayout.auxOffset n lengthWidth shiftWidth +
      StepLayout.auxWidth lengthWidth shiftWidth) :
    readField I off width = 0 :=
  readField_sub_zero hlo hhi haux

open Internal

theorem Internal.phaseInputLenQ
    (n lengthWidth shiftWidth I : Nat) :
    readField (StepPlaced.phaseInput n lengthWidth shiftWidth I)
        Phase.lenQOffset lengthWidth =
      readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth := by
  have h := readField_gatherBits
    (Phase.layout lengthWidth shiftWidth)
    (StepLayout.phaseWiring n lengthWidth shiftWidth) 3 I
    (by simp [StepLayout.phaseWiring])
  simpa [StepPlaced.phaseInput, Phase.layout, Layout.offset, Layout.size,
    StepLayout.phaseWiring, Phase.lenQOffset] using h

private theorem phaseInputPhase1
    (n lengthWidth shiftWidth I : Nat) :
    bitValue (StepPlaced.phaseInput n lengthWidth shiftWidth I)
        Phase.phase1Wire =
      bitValue I (StepLayout.phase1Wire n lengthWidth shiftWidth) := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits
    (Phase.layout lengthWidth shiftWidth)
    (StepLayout.phaseWiring n lengthWidth shiftWidth) 0 I
    (by simp [StepLayout.phaseWiring])
  simpa [StepPlaced.phaseInput, Phase.layout, Layout.offset, Layout.size,
    StepLayout.phaseWiring, Phase.phase1Wire] using h

private theorem phaseInputPhase2
    (n lengthWidth shiftWidth I : Nat) :
    bitValue (StepPlaced.phaseInput n lengthWidth shiftWidth I)
        Phase.phase2Wire =
      bitValue I (StepLayout.phase2Wire n lengthWidth shiftWidth) := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits
    (Phase.layout lengthWidth shiftWidth)
    (StepLayout.phaseWiring n lengthWidth shiftWidth) 1 I
    (by simp [StepLayout.phaseWiring])
  simpa [StepPlaced.phaseInput, Phase.layout, Layout.offset, Layout.size,
    StepLayout.phaseWiring, Phase.phase1Wire, Phase.phase2Wire] using h

private theorem phaseInputSign
    (n lengthWidth shiftWidth I : Nat) :
    bitValue (StepPlaced.phaseInput n lengthWidth shiftWidth I)
        Phase.signWire =
      bitValue I (StepLayout.signWire n lengthWidth shiftWidth) := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits
    (Phase.layout lengthWidth shiftWidth)
    (StepLayout.phaseWiring n lengthWidth shiftWidth) 2 I
    (by simp [StepLayout.phaseWiring])
  simpa [StepPlaced.phaseInput, Phase.layout, Layout.offset, Layout.size,
    StepLayout.phaseWiring, Phase.phase1Wire, Phase.signWire] using h

private theorem phaseInputLenRPrime
    (n lengthWidth shiftWidth I : Nat) :
    readField (StepPlaced.phaseInput n lengthWidth shiftWidth I)
        (Phase.lenRPrimeOffset lengthWidth) lengthWidth =
      readField I (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth := by
  have h := readField_gatherBits
    (Phase.layout lengthWidth shiftWidth)
    (StepLayout.phaseWiring n lengthWidth shiftWidth) 4 I
    (by simp [StepLayout.phaseWiring])
  rw [show Phase.lenRPrimeOffset lengthWidth =
      Layout.offset (Phase.layout lengthWidth shiftWidth) 4 by
    simp [Phase.lenRPrimeOffset, Phase.layout, Layout.offset]
    omega]
  simpa [StepPlaced.phaseInput, Phase.layout, Layout.size,
    StepLayout.phaseWiring] using h

theorem Internal.phaseInputShift
    (n lengthWidth shiftWidth I : Nat) :
    readField (StepPlaced.phaseInput n lengthWidth shiftWidth I)
        (Phase.shiftOffset lengthWidth) shiftWidth =
      readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth := by
  have h := readField_gatherBits
    (Phase.layout lengthWidth shiftWidth)
    (StepLayout.phaseWiring n lengthWidth shiftWidth) 5 I
    (by simp [StepLayout.phaseWiring])
  rw [show Phase.shiftOffset lengthWidth =
      Layout.offset (Phase.layout lengthWidth shiftWidth) 5 by
    simp [Phase.shiftOffset, Phase.layout, Layout.offset]
    omega]
  simpa [StepPlaced.phaseInput, Phase.layout, Layout.size,
    StepLayout.phaseWiring] using h

theorem Internal.phaseInputZeroQ
    (n lengthWidth shiftWidth I : Nat) :
    bitValue (StepPlaced.phaseInput n lengthWidth shiftWidth I)
        (Phase.zeroQWire lengthWidth shiftWidth) =
      bitValue I (StepLayout.zeroQWire n lengthWidth shiftWidth) := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits
    (Phase.layout lengthWidth shiftWidth)
    (StepLayout.phaseWiring n lengthWidth shiftWidth) 6 I
    (by simp [StepLayout.phaseWiring])
  rw [show Phase.zeroQWire lengthWidth shiftWidth =
      Layout.offset (Phase.layout lengthWidth shiftWidth) 6 by
    simp [Phase.zeroQWire, Phase.shiftOffset, Phase.layout, Layout.offset]
    omega]
  simpa [StepPlaced.phaseInput, Phase.layout, Layout.size,
    StepLayout.phaseWiring] using h

private theorem phaseInputZeroRPrime
    (n lengthWidth shiftWidth I : Nat) :
    bitValue (StepPlaced.phaseInput n lengthWidth shiftWidth I)
        (Phase.zeroRPrimeWire lengthWidth shiftWidth) =
      bitValue I (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits
    (Phase.layout lengthWidth shiftWidth)
    (StepLayout.phaseWiring n lengthWidth shiftWidth) 7 I
    (by simp [StepLayout.phaseWiring])
  rw [show Phase.zeroRPrimeWire lengthWidth shiftWidth =
      Layout.offset (Phase.layout lengthWidth shiftWidth) 7 by
    simp [Phase.zeroRPrimeWire, Phase.zeroQWire, Phase.shiftOffset,
      Phase.layout, Layout.offset]
    omega]
  simpa [StepPlaced.phaseInput, Phase.layout, Layout.size,
    StepLayout.phaseWiring] using h

theorem Internal.phaseInputZeroShift
    (n lengthWidth shiftWidth I : Nat) :
    bitValue (StepPlaced.phaseInput n lengthWidth shiftWidth I)
        (Phase.zeroShiftWire lengthWidth shiftWidth) =
      bitValue I (StepLayout.zeroShiftWire n lengthWidth shiftWidth) := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits
    (Phase.layout lengthWidth shiftWidth)
    (StepLayout.phaseWiring n lengthWidth shiftWidth) 8 I
    (by simp [StepLayout.phaseWiring])
  rw [show Phase.zeroShiftWire lengthWidth shiftWidth =
      Layout.offset (Phase.layout lengthWidth shiftWidth) 8 by
    simp [Phase.zeroShiftWire, Phase.zeroQWire, Phase.shiftOffset,
      Phase.layout, Layout.offset]
    omega]
  simpa [StepPlaced.phaseInput, Phase.layout, Layout.size,
    StepLayout.phaseWiring] using h

theorem Internal.phaseInputPool
    (n lengthWidth shiftWidth I : Nat) :
    readField (StepPlaced.phaseInput n lengthWidth shiftWidth I)
        (Phase.poolOffset lengthWidth shiftWidth)
        (Phase.poolWidth lengthWidth shiftWidth) =
      readField I (StepLayout.poolOffset n lengthWidth shiftWidth)
        (StepLayout.selectorWidth lengthWidth shiftWidth) := by
  have h := readField_gatherBits
    (Phase.layout lengthWidth shiftWidth)
    (StepLayout.phaseWiring n lengthWidth shiftWidth) 11 I
    (by simp [StepLayout.phaseWiring])
  rw [show Phase.poolOffset lengthWidth shiftWidth =
      Layout.offset (Phase.layout lengthWidth shiftWidth) 11 by
    simp [Phase.poolOffset, Phase.zeroQWire, Phase.shiftOffset,
      Phase.layout, Layout.offset]
    omega]
  simpa [StepPlaced.phaseInput, Phase.layout, Layout.size,
    StepLayout.phaseWiring, Phase.poolWidth,
    StepLayout.selectorWidth] using h

private theorem phaseInputCondition
    (n lengthWidth shiftWidth I : Nat) :
    bitValue (StepPlaced.phaseInput n lengthWidth shiftWidth I)
        (Phase.conditionWire lengthWidth shiftWidth) =
      bitValue I (StepLayout.conditionWire n lengthWidth shiftWidth) := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits
    (Phase.layout lengthWidth shiftWidth)
    (StepLayout.phaseWiring n lengthWidth shiftWidth) 9 I
    (by simp [StepLayout.phaseWiring])
  rw [show Phase.conditionWire lengthWidth shiftWidth =
      Layout.offset (Phase.layout lengthWidth shiftWidth) 9 by
    simp [Phase.conditionWire, Phase.zeroQWire, Phase.shiftOffset,
      Phase.layout, Layout.offset]
    omega]
  simpa [StepPlaced.phaseInput, Phase.layout, Layout.size,
    StepLayout.phaseWiring] using h

private theorem phaseInputTemporary
    (n lengthWidth shiftWidth I : Nat) :
    bitValue (StepPlaced.phaseInput n lengthWidth shiftWidth I)
        (Phase.temporaryWire lengthWidth shiftWidth) =
      bitValue I (StepLayout.temporaryWire n lengthWidth shiftWidth) := by
  rw [← readField_one, ← readField_one]
  have h := readField_gatherBits
    (Phase.layout lengthWidth shiftWidth)
    (StepLayout.phaseWiring n lengthWidth shiftWidth) 10 I
    (by simp [StepLayout.phaseWiring])
  rw [show Phase.temporaryWire lengthWidth shiftWidth =
      Layout.offset (Phase.layout lengthWidth shiftWidth) 10 by
    simp [Phase.temporaryWire, Phase.zeroQWire, Phase.shiftOffset,
      Phase.layout, Layout.offset]
    omega]
  simpa [StepPlaced.phaseInput, Phase.layout, Layout.size,
    StepLayout.phaseWiring] using h

theorem phaseBlock_act
    {n lengthWidth shiftWidth I : Nat}
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0) :
    let result := Phase.out lengthWidth shiftWidth
      (StepPlaced.phaseInput n lengthWidth shiftWidth I)
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField I (StepLayout.phase1Wire n lengthWidth shiftWidth) 1
            (bitValue result Phase.phase1Wire))
          (StepLayout.phase2Wire n lengthWidth shiftWidth) 1
          (bitValue result Phase.phase2Wire))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (bitValue result Phase.signWire) := by
  dsimp only
  apply StepPlaced.phase_act
  · rw [← readField_one]
    have hread := readField_gatherBits
      (Phase.layout lengthWidth shiftWidth)
      (StepLayout.phaseWiring n lengthWidth shiftWidth) 6 I
      (by simp [StepLayout.phaseWiring])
    have hphysical : readField I
        (StepLayout.zeroQWire n lengthWidth shiftWidth) 1 = 0 := by
      apply auxSubfieldClear haux <;>
        simp [StepLayout.zeroQWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth] <;>
        omega
    rw [show Phase.zeroQWire lengthWidth shiftWidth =
        Layout.offset (Phase.layout lengthWidth shiftWidth) 6 by
      simp [Phase.zeroQWire, Phase.shiftOffset, Phase.layout, Layout.offset]
      omega]
    simpa [StepPlaced.phaseInput, Phase.layout, Layout.size] using
      hread.trans hphysical
  · rw [← readField_one]
    have hread := readField_gatherBits
      (Phase.layout lengthWidth shiftWidth)
      (StepLayout.phaseWiring n lengthWidth shiftWidth) 7 I
      (by simp [StepLayout.phaseWiring])
    have hphysical : readField I
        (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) 1 = 0 := by
      apply auxSubfieldClear haux <;>
        simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth] <;>
        omega
    rw [show Phase.zeroRPrimeWire lengthWidth shiftWidth =
        Layout.offset (Phase.layout lengthWidth shiftWidth) 7 by
      simp [Phase.zeroRPrimeWire, Phase.zeroQWire, Phase.shiftOffset,
        Phase.layout, Layout.offset]
      omega]
    simpa [StepPlaced.phaseInput, Phase.layout, Layout.size] using
      hread.trans hphysical
  · rw [← readField_one]
    have hread := readField_gatherBits
      (Phase.layout lengthWidth shiftWidth)
      (StepLayout.phaseWiring n lengthWidth shiftWidth) 8 I
      (by simp [StepLayout.phaseWiring])
    have hphysical : readField I
        (StepLayout.zeroShiftWire n lengthWidth shiftWidth) 1 = 0 := by
      apply auxSubfieldClear haux <;>
        simp [StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth] <;>
        omega
    rw [show Phase.zeroShiftWire lengthWidth shiftWidth =
        Layout.offset (Phase.layout lengthWidth shiftWidth) 8 by
      simp [Phase.zeroShiftWire, Phase.zeroQWire, Phase.shiftOffset,
        Phase.layout, Layout.offset]
      omega]
    simpa [StepPlaced.phaseInput, Phase.layout, Layout.size] using
      hread.trans hphysical
  · rw [← readField_one]
    have hread := readField_gatherBits
      (Phase.layout lengthWidth shiftWidth)
      (StepLayout.phaseWiring n lengthWidth shiftWidth) 9 I
      (by simp [StepLayout.phaseWiring])
    have hphysical : readField I
        (StepLayout.conditionWire n lengthWidth shiftWidth) 1 = 0 := by
      apply auxSubfieldClear haux <;>
        simp [StepLayout.conditionWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth] <;>
        omega
    rw [show Phase.conditionWire lengthWidth shiftWidth =
        Layout.offset (Phase.layout lengthWidth shiftWidth) 9 by
      simp [Phase.conditionWire, Phase.zeroQWire, Phase.shiftOffset,
        Phase.layout, Layout.offset]
      omega]
    simpa [StepPlaced.phaseInput, Phase.layout, Layout.size] using
      hread.trans hphysical
  · rw [← readField_one]
    have hread := readField_gatherBits
      (Phase.layout lengthWidth shiftWidth)
      (StepLayout.phaseWiring n lengthWidth shiftWidth) 10 I
      (by simp [StepLayout.phaseWiring])
    have hphysical : readField I
        (StepLayout.temporaryWire n lengthWidth shiftWidth) 1 = 0 := by
      apply auxSubfieldClear haux <;>
        simp [StepLayout.temporaryWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth] <;>
        omega
    rw [show Phase.temporaryWire lengthWidth shiftWidth =
        Layout.offset (Phase.layout lengthWidth shiftWidth) 10 by
      simp [Phase.temporaryWire, Phase.zeroQWire, Phase.shiftOffset,
        Phase.layout, Layout.offset]
      omega]
    simpa [StepPlaced.phaseInput, Phase.layout, Layout.size] using
      hread.trans hphysical
  · have hread := readField_gatherBits
      (Phase.layout lengthWidth shiftWidth)
      (StepLayout.phaseWiring n lengthWidth shiftWidth) 11 I
      (by simp [StepLayout.phaseWiring])
    have hphysical : readField I
        (StepLayout.poolOffset n lengthWidth shiftWidth)
        (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
      apply auxSubfieldClear haux <;>
        simp [StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth] <;>
        omega
    rw [show Phase.poolOffset lengthWidth shiftWidth =
        Layout.offset (Phase.layout lengthWidth shiftWidth) 11 by
      simp [Phase.poolOffset, Phase.zeroQWire, Phase.shiftOffset,
        Phase.layout, Layout.offset]
      omega]
    simpa [StepPlaced.phaseInput, Phase.layout, Layout.size,
      Phase.poolWidth, StepLayout.selectorWidth] using hread.trans hphysical

theorem phaseBlock_act_phase00
    {n lengthWidth shiftWidth I : Nat}
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
    (hlenQ : readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodedZero lengthWidth)
    (hlenRPrime : readField I
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth ≠
      encodedZero lengthWidth)
    (hshift : readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth ≠
      encodedZero shiftWidth) :
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField I (StepLayout.phase1Wire n lengthWidth shiftWidth) 1 0)
          (StepLayout.phase2Wire n lengthWidth shiftWidth) 1
          (bitValue I (StepLayout.signWire n lengthWidth shiftWidth)))
        (StepLayout.signWire n lengthWidth shiftWidth) 1 0 := by
  let input := StepPlaced.phaseInput n lengthWidth shiftWidth I
  let selected := Phase.selected lengthWidth shiftWidth input
  let result := Phase.out lengthWidth shiftWidth input
  have hconditionPhysical : bitValue I
      (StepLayout.conditionWire n lengthWidth shiftWidth) = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [StepLayout.conditionWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have htemporaryPhysical : bitValue I
      (StepLayout.temporaryWire n lengthWidth shiftWidth) = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [StepLayout.temporaryWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hpoolPhysical : readField I
      (StepLayout.poolOffset n lengthWidth shiftWidth)
      (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
    apply auxSubfieldClear haux <;>
      simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hcondition : bitValue input
      (Phase.conditionWire lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputCondition] using hconditionPhysical
  have htemporary : bitValue input
      (Phase.temporaryWire lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputTemporary] using htemporaryPhysical
  have hpool : readField input (Phase.poolOffset lengthWidth shiftWidth)
      (Phase.poolWidth lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputPool] using hpoolPhysical
  have hselectedFlags := Phase.selected_flags lengthWidth shiftWidth input
  dsimp only at hselectedFlags
  have hselectedQ : bitValue selected
      (Phase.zeroQWire lengthWidth shiftWidth) = 1 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.1]
    simp [Phase.selectorValue, input, phaseInputLenQ, hlenQ]
  have hselectedRPrime : bitValue selected
      (Phase.zeroRPrimeWire lengthWidth shiftWidth) = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.2.1]
    simp [Phase.selectorValue, input, phaseInputLenRPrime, hlenRPrime]
  have hselectedShift : bitValue selected
      (Phase.zeroShiftWire lengthWidth shiftWidth) = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.2.2]
    simp [Phase.selectorValue, input, phaseInputShift, hshift]
  have hselectedPhase1 : bitValue selected Phase.phase1Wire = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.phase1Wire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.phase1Wire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]) (by
        simp [Phase.phase1Wire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputPhase1] using hphase1
  have hselectedPhase2 : bitValue selected Phase.phase2Wire = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.phase2Wire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.phase2Wire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]) (by
        simp [Phase.phase2Wire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputPhase2] using hphase2
  have hselectedSign : bitValue selected Phase.signWire =
      bitValue I (StepLayout.signWire n lengthWidth shiftWidth) := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.signWire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.signWire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]
        omega) (by
        simp [Phase.signWire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simp [input, phaseInputSign]
  have hconditionValue :
      Phase.conditionValue lengthWidth shiftWidth selected = 1 := by
    simp [Phase.conditionValue, hselectedRPrime, hselectedQ]
  have hmiddle :
      Phase.middlePhase2Value lengthWidth shiftWidth selected =
        bitValue I (StepLayout.signWire n lengthWidth shiftWidth) := by
    simp [Phase.middlePhase2Value, hselectedPhase2, hconditionValue,
      hselectedSign, hselectedPhase1,
      Nat.mod_eq_of_lt (bitValue_lt I
        (StepLayout.signWire n lengthWidth shiftWidth))]
  have hbits := Phase.out_bits (i := input) hcondition htemporary hpool
  dsimp only at hbits
  have hresultPhase1 : bitValue result Phase.phase1Wire = 0 := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl, hbits.1]
    simp [Phase.phase1Value, selected, hselectedPhase1, hselectedShift]
  have hresultPhase2 : bitValue result Phase.phase2Wire =
      bitValue I (StepLayout.signWire n lengthWidth shiftWidth) := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl,
      hbits.2.1]
    simp [Phase.phase2Value, selected, hmiddle, hselectedShift,
      Nat.mod_eq_of_lt (bitValue_lt I
        (StepLayout.signWire n lengthWidth shiftWidth))]
  have hresultSign : bitValue result Phase.signWire = 0 := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl,
      hbits.2.2.1]
    rw [Phase.signValue, hselectedSign, hconditionValue, hmiddle]
    have hsign := bitValue_lt I
      (StepLayout.signWire n lengthWidth shiftWidth)
    omega
  have hact := phaseBlock_act (n := n) (lengthWidth := lengthWidth)
    (shiftWidth := shiftWidth) (I := I) haux
  dsimp only at hact
  rw [hact, ← show result = Phase.out lengthWidth shiftWidth input by rfl,
    hresultPhase1, hresultPhase2, hresultSign]

theorem phaseBlock_act_phase01
    {n lengthWidth shiftWidth I : Nat}
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1)
    (hsign : bitValue I
      (StepLayout.signWire n lengthWidth shiftWidth) = 0)
    (hlenQ : readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth ≠
      encodedZero lengthWidth)
    (hlenRPrime : readField I
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth ≠
      encodedZero lengthWidth) :
    let zeroShift := Phase.selectorValue shiftWidth
      (StepLayout.shiftOffset n lengthWidth) I
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField I (StepLayout.phase1Wire n lengthWidth shiftWidth) 1
            zeroShift)
          (StepLayout.phase2Wire n lengthWidth shiftWidth) 1
          ((1 + zeroShift) % 2))
        (StepLayout.signWire n lengthWidth shiftWidth) 1 0 := by
  dsimp only
  let input := StepPlaced.phaseInput n lengthWidth shiftWidth I
  let selected := Phase.selected lengthWidth shiftWidth input
  let result := Phase.out lengthWidth shiftWidth input
  let zeroShift := Phase.selectorValue shiftWidth
    (StepLayout.shiftOffset n lengthWidth) I
  have hconditionPhysical : bitValue I
      (StepLayout.conditionWire n lengthWidth shiftWidth) = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [StepLayout.conditionWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have htemporaryPhysical : bitValue I
      (StepLayout.temporaryWire n lengthWidth shiftWidth) = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [StepLayout.temporaryWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hpoolPhysical : readField I
      (StepLayout.poolOffset n lengthWidth shiftWidth)
      (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
    apply auxSubfieldClear haux <;>
      simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hcondition : bitValue input
      (Phase.conditionWire lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputCondition] using hconditionPhysical
  have htemporary : bitValue input
      (Phase.temporaryWire lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputTemporary] using htemporaryPhysical
  have hpool : readField input (Phase.poolOffset lengthWidth shiftWidth)
      (Phase.poolWidth lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputPool] using hpoolPhysical
  have hselectedFlags := Phase.selected_flags lengthWidth shiftWidth input
  dsimp only at hselectedFlags
  have hselectedQ : bitValue selected
      (Phase.zeroQWire lengthWidth shiftWidth) = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.1]
    simp [Phase.selectorValue, input, phaseInputLenQ, hlenQ]
  have hselectedRPrime : bitValue selected
      (Phase.zeroRPrimeWire lengthWidth shiftWidth) = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.2.1]
    simp [Phase.selectorValue, input, phaseInputLenRPrime, hlenRPrime]
  have hselectedShift : bitValue selected
      (Phase.zeroShiftWire lengthWidth shiftWidth) = zeroShift := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.2.2]
    simp [Phase.selectorValue, input, phaseInputShift, zeroShift]
  have hselectedPhase1 : bitValue selected Phase.phase1Wire = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.phase1Wire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.phase1Wire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]) (by
        simp [Phase.phase1Wire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputPhase1] using hphase1
  have hselectedPhase2 : bitValue selected Phase.phase2Wire = 1 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.phase2Wire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.phase2Wire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]) (by
        simp [Phase.phase2Wire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputPhase2] using hphase2
  have hselectedSign : bitValue selected Phase.signWire = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.signWire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.signWire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]
        omega) (by
        simp [Phase.signWire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputSign] using hsign
  have hconditionValue :
      Phase.conditionValue lengthWidth shiftWidth selected = 0 := by
    simp [Phase.conditionValue, hselectedRPrime, hselectedQ]
  have hmiddle :
      Phase.middlePhase2Value lengthWidth shiftWidth selected = 1 := by
    simp [Phase.middlePhase2Value, hselectedPhase2, hconditionValue]
  have hbits := Phase.out_bits (i := input) hcondition htemporary hpool
  dsimp only at hbits
  have hzeroShiftLt : zeroShift < 2 := by
    exact Phase.selectorValue_lt shiftWidth
      (StepLayout.shiftOffset n lengthWidth) I
  have hresultPhase1 : bitValue result Phase.phase1Wire = zeroShift := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl, hbits.1]
    simp [Phase.phase1Value, selected, hselectedPhase1, hselectedShift,
      Nat.mod_eq_of_lt hzeroShiftLt]
  have hresultPhase2 : bitValue result Phase.phase2Wire =
      (1 + zeroShift) % 2 := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl,
      hbits.2.1]
    simp [Phase.phase2Value, selected, hmiddle, hselectedShift]
  have hresultSign : bitValue result Phase.signWire = 0 := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl,
      hbits.2.2.1]
    simp [Phase.signValue, selected, hselectedSign, hconditionValue]
  have hact := phaseBlock_act (n := n) (lengthWidth := lengthWidth)
    (shiftWidth := shiftWidth) (I := I) haux
  dsimp only at hact
  rw [hact, ← show result = Phase.out lengthWidth shiftWidth input by rfl,
    hresultPhase1, hresultPhase2, hresultSign]

theorem phaseBlock_act_phase10
    {n lengthWidth shiftWidth I : Nat}
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
    (hsign : bitValue I
      (StepLayout.signWire n lengthWidth shiftWidth) = 0)
    (hlenRPrime : readField I
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth ≠
      encodedZero lengthWidth)
    (hshift : readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth ≠
      encodedZero shiftWidth) :
    let zeroQ := Phase.selectorValue lengthWidth
      (StepLayout.lenQOffset n lengthWidth) I
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField I (StepLayout.phase1Wire n lengthWidth shiftWidth) 1 1)
          (StepLayout.phase2Wire n lengthWidth shiftWidth) 1 zeroQ)
        (StepLayout.signWire n lengthWidth shiftWidth) 1 zeroQ := by
  dsimp only
  let input := StepPlaced.phaseInput n lengthWidth shiftWidth I
  let selected := Phase.selected lengthWidth shiftWidth input
  let result := Phase.out lengthWidth shiftWidth input
  let zeroQ := Phase.selectorValue lengthWidth
    (StepLayout.lenQOffset n lengthWidth) I
  have hconditionPhysical : bitValue I
      (StepLayout.conditionWire n lengthWidth shiftWidth) = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [StepLayout.conditionWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have htemporaryPhysical : bitValue I
      (StepLayout.temporaryWire n lengthWidth shiftWidth) = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [StepLayout.temporaryWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hpoolPhysical : readField I
      (StepLayout.poolOffset n lengthWidth shiftWidth)
      (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
    apply auxSubfieldClear haux <;>
      simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hcondition : bitValue input
      (Phase.conditionWire lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputCondition] using hconditionPhysical
  have htemporary : bitValue input
      (Phase.temporaryWire lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputTemporary] using htemporaryPhysical
  have hpool : readField input (Phase.poolOffset lengthWidth shiftWidth)
      (Phase.poolWidth lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputPool] using hpoolPhysical
  have hselectedFlags := Phase.selected_flags lengthWidth shiftWidth input
  dsimp only at hselectedFlags
  have hselectedQ : bitValue selected
      (Phase.zeroQWire lengthWidth shiftWidth) = zeroQ := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.1]
    simp [Phase.selectorValue, input, phaseInputLenQ, zeroQ]
  have hselectedRPrime : bitValue selected
      (Phase.zeroRPrimeWire lengthWidth shiftWidth) = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.2.1]
    simp [Phase.selectorValue, input, phaseInputLenRPrime, hlenRPrime]
  have hselectedShift : bitValue selected
      (Phase.zeroShiftWire lengthWidth shiftWidth) = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.2.2]
    simp [Phase.selectorValue, input, phaseInputShift, hshift]
  have hselectedPhase1 : bitValue selected Phase.phase1Wire = 1 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.phase1Wire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.phase1Wire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]) (by
        simp [Phase.phase1Wire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputPhase1] using hphase1
  have hselectedPhase2 : bitValue selected Phase.phase2Wire = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.phase2Wire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.phase2Wire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]) (by
        simp [Phase.phase2Wire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputPhase2] using hphase2
  have hselectedSign : bitValue selected Phase.signWire = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.signWire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.signWire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]
        omega) (by
        simp [Phase.signWire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputSign] using hsign
  have hzeroQLt : zeroQ < 2 := by
    exact Phase.selectorValue_lt lengthWidth
      (StepLayout.lenQOffset n lengthWidth) I
  have hconditionValue :
      Phase.conditionValue lengthWidth shiftWidth selected = zeroQ := by
    simp [Phase.conditionValue, hselectedRPrime, hselectedQ]
  have hmiddle :
      Phase.middlePhase2Value lengthWidth shiftWidth selected = zeroQ := by
    simp [Phase.middlePhase2Value, hselectedPhase2, hconditionValue,
      hselectedSign, hselectedPhase1, Nat.mod_eq_of_lt hzeroQLt]
  have hbits := Phase.out_bits (i := input) hcondition htemporary hpool
  dsimp only at hbits
  have hresultPhase1 : bitValue result Phase.phase1Wire = 1 := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl, hbits.1]
    simp [Phase.phase1Value, selected, hselectedPhase1, hselectedShift]
  have hresultPhase2 : bitValue result Phase.phase2Wire = zeroQ := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl,
      hbits.2.1]
    simp [Phase.phase2Value, selected, hmiddle, hselectedShift,
      Nat.mod_eq_of_lt hzeroQLt]
  have hresultSign : bitValue result Phase.signWire = zeroQ := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl,
      hbits.2.2.1]
    rw [Phase.signValue, hselectedSign, hconditionValue, hmiddle]
    interval_cases zeroQ <;> simp
  have hact := phaseBlock_act (n := n) (lengthWidth := lengthWidth)
    (shiftWidth := shiftWidth) (I := I) haux
  dsimp only at hact
  rw [hact, ← show result = Phase.out lengthWidth shiftWidth input by rfl,
    hresultPhase1, hresultPhase2, hresultSign]

theorem phaseBlock_act_phase11
    {n lengthWidth shiftWidth I : Nat}
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 1)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 1)
    (hsign : bitValue I
      (StepLayout.signWire n lengthWidth shiftWidth) = 1)
    (hlenQ : readField I (StepLayout.lenQOffset n lengthWidth) lengthWidth =
      encodedZero lengthWidth)
    (hlenRPrime : readField I
      (StepLayout.lenRPrimeOffset n lengthWidth) lengthWidth ≠
      encodedZero lengthWidth) :
    let zeroShift := Phase.selectorValue shiftWidth
      (StepLayout.shiftOffset n lengthWidth) I
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField I (StepLayout.phase1Wire n lengthWidth shiftWidth) 1
            ((1 + zeroShift) % 2))
          (StepLayout.phase2Wire n lengthWidth shiftWidth) 1
          ((1 + zeroShift) % 2))
        (StepLayout.signWire n lengthWidth shiftWidth) 1 0 := by
  dsimp only
  let input := StepPlaced.phaseInput n lengthWidth shiftWidth I
  let selected := Phase.selected lengthWidth shiftWidth input
  let result := Phase.out lengthWidth shiftWidth input
  let zeroShift := Phase.selectorValue shiftWidth
    (StepLayout.shiftOffset n lengthWidth) I
  have hconditionPhysical : bitValue I
      (StepLayout.conditionWire n lengthWidth shiftWidth) = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [StepLayout.conditionWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have htemporaryPhysical : bitValue I
      (StepLayout.temporaryWire n lengthWidth shiftWidth) = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [StepLayout.temporaryWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hpoolPhysical : readField I
      (StepLayout.poolOffset n lengthWidth shiftWidth)
      (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
    apply auxSubfieldClear haux <;>
      simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hcondition : bitValue input
      (Phase.conditionWire lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputCondition] using hconditionPhysical
  have htemporary : bitValue input
      (Phase.temporaryWire lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputTemporary] using htemporaryPhysical
  have hpool : readField input (Phase.poolOffset lengthWidth shiftWidth)
      (Phase.poolWidth lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputPool] using hpoolPhysical
  have hselectedFlags := Phase.selected_flags lengthWidth shiftWidth input
  dsimp only at hselectedFlags
  have hselectedQ : bitValue selected
      (Phase.zeroQWire lengthWidth shiftWidth) = 1 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.1]
    simp [Phase.selectorValue, input, phaseInputLenQ, hlenQ]
  have hselectedRPrime : bitValue selected
      (Phase.zeroRPrimeWire lengthWidth shiftWidth) = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.2.1]
    simp [Phase.selectorValue, input, phaseInputLenRPrime, hlenRPrime]
  have hselectedShift : bitValue selected
      (Phase.zeroShiftWire lengthWidth shiftWidth) = zeroShift := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.2.2]
    simp [Phase.selectorValue, input, phaseInputShift, zeroShift]
  have hselectedPhase1 : bitValue selected Phase.phase1Wire = 1 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.phase1Wire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.phase1Wire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]) (by
        simp [Phase.phase1Wire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputPhase1] using hphase1
  have hselectedPhase2 : bitValue selected Phase.phase2Wire = 1 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.phase2Wire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.phase2Wire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]) (by
        simp [Phase.phase2Wire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputPhase2] using hphase2
  have hselectedSign : bitValue selected Phase.signWire = 1 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.signWire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.signWire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]
        omega) (by
        simp [Phase.signWire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputSign] using hsign
  have hconditionValue :
      Phase.conditionValue lengthWidth shiftWidth selected = 1 := by
    simp [Phase.conditionValue, hselectedRPrime, hselectedQ]
  have hmiddle :
      Phase.middlePhase2Value lengthWidth shiftWidth selected = 1 := by
    simp [Phase.middlePhase2Value, hselectedPhase2, hconditionValue,
      hselectedSign, hselectedPhase1]
  have hbits := Phase.out_bits (i := input) hcondition htemporary hpool
  dsimp only at hbits
  have hresultPhase1 : bitValue result Phase.phase1Wire =
      (1 + zeroShift) % 2 := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl, hbits.1]
    simp [Phase.phase1Value, selected, hselectedPhase1, hselectedShift]
  have hresultPhase2 : bitValue result Phase.phase2Wire =
      (1 + zeroShift) % 2 := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl,
      hbits.2.1]
    simp [Phase.phase2Value, selected, hmiddle, hselectedShift]
  have hresultSign : bitValue result Phase.signWire = 0 := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl,
      hbits.2.2.1]
    simp [Phase.signValue, selected, hselectedSign, hconditionValue, hmiddle]
  have hact := phaseBlock_act (n := n) (lengthWidth := lengthWidth)
    (shiftWidth := shiftWidth) (I := I) haux
  dsimp only at hact
  rw [hact, ← show result = Phase.out lengthWidth shiftWidth input by rfl,
    hresultPhase1, hresultPhase2, hresultSign]

theorem phaseBlock_identity
    {n lengthWidth shiftWidth I : Nat}
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0)
    (hphase1 : bitValue I
      (StepLayout.phase1Wire n lengthWidth shiftWidth) = 0)
    (hphase2 : bitValue I
      (StepLayout.phase2Wire n lengthWidth shiftWidth) = 0)
    (hsign : bitValue I
      (StepLayout.signWire n lengthWidth shiftWidth) = 0)
    (hshift : readField I (StepLayout.shiftOffset n lengthWidth) shiftWidth ≠
      encodedZero shiftWidth) :
    actGates (StepLayout.phaseGates n lengthWidth shiftWidth) I = I := by
  let input := StepPlaced.phaseInput n lengthWidth shiftWidth I
  let selected := Phase.selected lengthWidth shiftWidth input
  let result := Phase.out lengthWidth shiftWidth input
  have hconditionPhysical : bitValue I
      (StepLayout.conditionWire n lengthWidth shiftWidth) = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [StepLayout.conditionWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have htemporaryPhysical : bitValue I
      (StepLayout.temporaryWire n lengthWidth shiftWidth) = 0 := by
    rw [← readField_one]
    apply auxSubfieldClear haux <;>
      simp [StepLayout.temporaryWire, StepLayout.cellScratchWire,
        StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hpoolPhysical : readField I
      (StepLayout.poolOffset n lengthWidth shiftWidth)
      (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
    apply auxSubfieldClear haux <;>
      simp [StepLayout.poolOffset, StepLayout.carryWire,
        StepLayout.auxWidth, StepLayout.selectorWidth] <;>
      omega
  have hcondition : bitValue input
      (Phase.conditionWire lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputCondition] using hconditionPhysical
  have htemporary : bitValue input
      (Phase.temporaryWire lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputTemporary] using htemporaryPhysical
  have hpool : readField input (Phase.poolOffset lengthWidth shiftWidth)
      (Phase.poolWidth lengthWidth shiftWidth) = 0 := by
    simpa [input, phaseInputPool] using hpoolPhysical
  have hselectedFlags := Phase.selected_flags lengthWidth shiftWidth input
  dsimp only at hselectedFlags
  have hselectedShift : bitValue selected
      (Phase.zeroShiftWire lengthWidth shiftWidth) = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      hselectedFlags.2.2]
    simp [Phase.selectorValue, input, phaseInputShift, hshift]
  have hselectedPhase1 : bitValue selected Phase.phase1Wire = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.phase1Wire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.phase1Wire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]) (by
        simp [Phase.phase1Wire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputPhase1] using hphase1
  have hselectedPhase2 : bitValue selected Phase.phase2Wire = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.phase2Wire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.phase2Wire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]) (by
        simp [Phase.phase2Wire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputPhase2] using hphase2
  have hselectedSign : bitValue selected Phase.signWire = 0 := by
    rw [show selected = Phase.selected lengthWidth shiftWidth input by rfl,
      Phase.selected_preserves_bit (by
        simp [Phase.signWire, Phase.zeroQWire, Phase.shiftOffset]
        omega) (by
        simp [Phase.signWire, Phase.zeroRPrimeWire, Phase.zeroQWire,
          Phase.shiftOffset]
        omega) (by
        simp [Phase.signWire, Phase.zeroShiftWire, Phase.zeroQWire,
          Phase.shiftOffset])]
    simpa [input, phaseInputSign] using hsign
  have hmiddle :
      Phase.middlePhase2Value lengthWidth shiftWidth selected = 0 := by
    simp [Phase.middlePhase2Value, hselectedPhase1, hselectedPhase2,
      hselectedSign]
  have hbits := Phase.out_bits (i := input) hcondition htemporary hpool
  dsimp only at hbits
  have hresultPhase1 : bitValue result Phase.phase1Wire = 0 := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl, hbits.1]
    simp [Phase.phase1Value, selected, hselectedPhase1, hselectedShift]
  have hresultPhase2 : bitValue result Phase.phase2Wire = 0 := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl,
      hbits.2.1]
    simp [Phase.phase2Value, selected, hmiddle, hselectedShift]
  have hresultSign : bitValue result Phase.signWire = 0 := by
    rw [show result = Phase.out lengthWidth shiftWidth input by rfl,
      hbits.2.2.1]
    simp [Phase.signValue, selected, hselectedSign, hmiddle]
  have hwritePhase1 : bitValue result Phase.phase1Wire =
      readField I (StepLayout.phase1Wire n lengthWidth shiftWidth) 1 := by
    rw [readField_one, hphase1, hresultPhase1]
  have hwritePhase2 : bitValue result Phase.phase2Wire =
      readField I (StepLayout.phase2Wire n lengthWidth shiftWidth) 1 := by
    rw [readField_one, hphase2, hresultPhase2]
  have hwriteSign : bitValue result Phase.signWire =
      readField I (StepLayout.signWire n lengthWidth shiftWidth) 1 := by
    rw [readField_one, hsign, hresultSign]
  have hact := phaseBlock_act (n := n) (lengthWidth := lengthWidth)
    (shiftWidth := shiftWidth) (I := I) haux
  dsimp only at hact
  rw [hact, ← show result = Phase.out lengthWidth shiftWidth input by rfl,
    hwritePhase1, writeField_read, hwritePhase2, writeField_read,
    hwriteSign, writeField_read]

theorem phaseSelectBlock_act
    {n lengthWidth shiftWidth I : Nat}
    (haux : readField I (StepLayout.auxOffset n lengthWidth shiftWidth)
      (StepLayout.auxWidth lengthWidth shiftWidth) = 0) :
    let result := Phase.selected lengthWidth shiftWidth
      (StepPlaced.phaseInput n lengthWidth shiftWidth I)
    actGates (StepLayout.phaseSelectGates n lengthWidth shiftWidth) I =
      writeField
        (writeField
          (writeField I (StepLayout.zeroQWire n lengthWidth shiftWidth) 1
            (bitValue result (Phase.zeroQWire lengthWidth shiftWidth)))
          (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) 1
          (bitValue result (Phase.zeroRPrimeWire lengthWidth shiftWidth)))
        (StepLayout.zeroShiftWire n lengthWidth shiftWidth) 1
        (bitValue result (Phase.zeroShiftWire lengthWidth shiftWidth)) := by
  dsimp only
  apply StepPlaced.phaseSelect_act
  · rw [← readField_one]
    have hread := readField_gatherBits
      (Phase.layout lengthWidth shiftWidth)
      (StepLayout.phaseWiring n lengthWidth shiftWidth) 6 I
      (by simp [StepLayout.phaseWiring])
    have hphysical : readField I
        (StepLayout.zeroQWire n lengthWidth shiftWidth) 1 = 0 := by
      apply auxSubfieldClear haux <;>
        simp [StepLayout.zeroQWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth] <;>
        omega
    rw [show Phase.zeroQWire lengthWidth shiftWidth =
        Layout.offset (Phase.layout lengthWidth shiftWidth) 6 by
      simp [Phase.zeroQWire, Phase.shiftOffset, Phase.layout, Layout.offset]
      omega]
    simpa [StepPlaced.phaseInput, Phase.layout, Layout.size] using
      hread.trans hphysical
  · rw [← readField_one]
    have hread := readField_gatherBits
      (Phase.layout lengthWidth shiftWidth)
      (StepLayout.phaseWiring n lengthWidth shiftWidth) 7 I
      (by simp [StepLayout.phaseWiring])
    have hphysical : readField I
        (StepLayout.zeroRPrimeWire n lengthWidth shiftWidth) 1 = 0 := by
      apply auxSubfieldClear haux <;>
        simp [StepLayout.zeroRPrimeWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth] <;>
        omega
    rw [show Phase.zeroRPrimeWire lengthWidth shiftWidth =
        Layout.offset (Phase.layout lengthWidth shiftWidth) 7 by
      simp [Phase.zeroRPrimeWire, Phase.zeroQWire, Phase.shiftOffset,
        Phase.layout, Layout.offset]
      omega]
    simpa [StepPlaced.phaseInput, Phase.layout, Layout.size] using
      hread.trans hphysical
  · rw [← readField_one]
    have hread := readField_gatherBits
      (Phase.layout lengthWidth shiftWidth)
      (StepLayout.phaseWiring n lengthWidth shiftWidth) 8 I
      (by simp [StepLayout.phaseWiring])
    have hphysical : readField I
        (StepLayout.zeroShiftWire n lengthWidth shiftWidth) 1 = 0 := by
      apply auxSubfieldClear haux <;>
        simp [StepLayout.zeroShiftWire, StepLayout.cellScratchWire,
          StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth] <;>
        omega
    rw [show Phase.zeroShiftWire lengthWidth shiftWidth =
        Layout.offset (Phase.layout lengthWidth shiftWidth) 8 by
      simp [Phase.zeroShiftWire, Phase.zeroQWire, Phase.shiftOffset,
        Phase.layout, Layout.offset]
      omega]
    simpa [StepPlaced.phaseInput, Phase.layout, Layout.size] using
      hread.trans hphysical
  · have hread := readField_gatherBits
      (Phase.layout lengthWidth shiftWidth)
      (StepLayout.phaseWiring n lengthWidth shiftWidth) 11 I
      (by simp [StepLayout.phaseWiring])
    have hphysical : readField I
        (StepLayout.poolOffset n lengthWidth shiftWidth)
        (StepLayout.selectorWidth lengthWidth shiftWidth) = 0 := by
      apply auxSubfieldClear haux <;>
        simp [StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxWidth, StepLayout.selectorWidth] <;>
        omega
    rw [show Phase.poolOffset lengthWidth shiftWidth =
        Layout.offset (Phase.layout lengthWidth shiftWidth) 11 by
      simp [Phase.poolOffset, Phase.zeroQWire, Phase.shiftOffset,
        Phase.layout, Layout.offset]
      omega]
    simpa [StepPlaced.phaseInput, Phase.layout, Layout.size,
      Phase.poolWidth, StepLayout.selectorWidth] using hread.trans hphysical

end StepBlocks
end Euclid
end VQ
