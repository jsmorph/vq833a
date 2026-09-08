import VQ.Euclid.StepBlocks.Arithmetic

namespace VQ
namespace Euclid
namespace StepBlocks

open Reversible
open Internal

private theorem preShiftControl_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (Step.preShiftControl n lengthWidth shiftWidth).all
      (RGate.wellFormed (StepLayout.layout n lengthWidth shiftWidth).width) =
        true :=
  (Step.controls_wellFormed n lengthWidth shiftWidth).1

private theorem postShiftControl_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (Step.postShiftControl n lengthWidth shiftWidth).all
      (RGate.wellFormed (StepLayout.layout n lengthWidth shiftWidth).width) =
        true :=
  (Step.controls_wellFormed n lengthWidth shiftWidth).2.1

private theorem quotientDecrementControl_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (Step.quotientDecrementControl n lengthWidth shiftWidth).all
      (RGate.wellFormed (StepLayout.layout n lengthWidth shiftWidth).width) =
        true :=
  (Step.controls_wellFormed n lengthWidth shiftWidth).2.2.2.2.2.2.1

private theorem quotientIncrementControl_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (Step.quotientIncrementControl n lengthWidth shiftWidth).all
      (RGate.wellFormed (StepLayout.layout n lengthWidth shiftWidth).width) =
        true :=
  (Step.controls_wellFormed n lengthWidth shiftWidth).2.2.2.2.2.2.2.1

private theorem preShiftControl_wire
    {n lengthWidth shiftWidth q : Nat} {g : RGate}
    (hg : g ∈ Step.preShiftControl n lengthWidth shiftWidth)
    (hq : q ∈ g.wires) :
    q = StepLayout.phase1Wire n lengthWidth shiftWidth ∨
      q = StepLayout.phase2Wire n lengthWidth shiftWidth ∨
      q = StepLayout.plusWire n lengthWidth shiftWidth ∨
      q = StepLayout.minusWire n lengthWidth shiftWidth := by
  have hq' : q ∈
      (Step.preShiftControl n lengthWidth shiftWidth).flatMap RGate.wires := by
    rw [List.mem_flatMap]
    exact ⟨g, hg, hq⟩
  simp [Step.preShiftControl, StepControl.negativeGates, RGate.wires] at hq'
  aesop

private theorem postShiftControl_wire
    {n lengthWidth shiftWidth q : Nat} {g : RGate}
    (hg : g ∈ Step.postShiftControl n lengthWidth shiftWidth)
    (hq : q ∈ g.wires) :
    q = StepLayout.phase1Wire n lengthWidth shiftWidth ∨
      q = StepLayout.phase2Wire n lengthWidth shiftWidth ∨
      q = StepLayout.plusWire n lengthWidth shiftWidth ∨
      q = StepLayout.minusWire n lengthWidth shiftWidth := by
  have hq' : q ∈
      (Step.postShiftControl n lengthWidth shiftWidth).flatMap RGate.wires := by
    rw [List.mem_flatMap]
    exact ⟨g, hg, hq⟩
  simp [Step.postShiftControl, RGate.wires] at hq'
  aesop

private theorem quotientDecrementControl_wire
    {n lengthWidth shiftWidth q : Nat} {g : RGate}
    (hg : g ∈ Step.quotientDecrementControl n lengthWidth shiftWidth)
    (hq : q ∈ g.wires) :
    q = StepLayout.phase1Wire n lengthWidth shiftWidth ∨
      q = StepLayout.phase2Wire n lengthWidth shiftWidth ∨
      q = StepLayout.controlWire n lengthWidth shiftWidth := by
  have hq' : q ∈
      (Step.quotientDecrementControl n lengthWidth shiftWidth).flatMap
        RGate.wires := by
    rw [List.mem_flatMap]
    exact ⟨g, hg, hq⟩
  simp [Step.quotientDecrementControl, Phase.negativeAndGates,
    RGate.wires] at hq'
  aesop

private theorem quotientIncrementControl_wire
    {n lengthWidth shiftWidth q : Nat} {g : RGate}
    (hg : g ∈ Step.quotientIncrementControl n lengthWidth shiftWidth)
    (hq : q ∈ g.wires) :
    q = StepLayout.phase1Wire n lengthWidth shiftWidth ∨
      q = StepLayout.phase2Wire n lengthWidth shiftWidth ∨
      q = StepLayout.controlWire n lengthWidth shiftWidth := by
  have hq' : q ∈
      (Step.quotientIncrementControl n lengthWidth shiftWidth).flatMap
        RGate.wires := by
    rw [List.mem_flatMap]
    exact ⟨g, hg, hq⟩
  simp [Step.quotientIncrementControl, Phase.negativeAndGates,
    RGate.wires] at hq'
  aesop

private theorem preShiftControl_avoids_shift
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.preShiftControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.shiftOffset n lengthWidth ∨
          StepLayout.shiftOffset n lengthWidth + shiftWidth ≤ q := by
  intro g hg q hq
  rcases preShiftControl_wire hg hq with rfl | rfl | rfl | rfl <;>
    simp [StepLayout.phase1Wire, StepLayout.phase2Wire,
      StepLayout.plusWire, StepLayout.minusWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset] <;>
    omega

private theorem preShiftControl_avoids_work2
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.preShiftControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work2Offset n ∨
          StepLayout.work2Offset n + workWidth n ≤ q := by
  intro g hg q hq
  rcases preShiftControl_wire hg hq with rfl | rfl | rfl | rfl <;>
    simp [StepLayout.work2Offset, StepLayout.phase1Wire,
      StepLayout.phase2Wire, StepLayout.plusWire, StepLayout.minusWire,
      StepLayout.cellScratchWire, StepLayout.poolOffset,
      StepLayout.carryWire, StepLayout.auxOffset, StepLayout.shiftOffset,
      workWidth] <;>
    omega

private theorem postShiftControl_avoids_shift
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.postShiftControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.shiftOffset n lengthWidth ∨
          StepLayout.shiftOffset n lengthWidth + shiftWidth ≤ q := by
  intro g hg q hq
  rcases postShiftControl_wire hg hq with rfl | rfl | rfl | rfl <;>
    simp [StepLayout.phase1Wire, StepLayout.phase2Wire,
      StepLayout.plusWire, StepLayout.minusWire, StepLayout.cellScratchWire,
      StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset] <;>
    omega

private theorem postShiftControl_avoids_work2
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.postShiftControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work2Offset n ∨
          StepLayout.work2Offset n + workWidth n ≤ q := by
  intro g hg q hq
  rcases postShiftControl_wire hg hq with rfl | rfl | rfl | rfl <;>
    simp [StepLayout.work2Offset, StepLayout.phase1Wire,
      StepLayout.phase2Wire, StepLayout.plusWire, StepLayout.minusWire,
      StepLayout.cellScratchWire, StepLayout.poolOffset,
      StepLayout.carryWire, StepLayout.auxOffset, StepLayout.shiftOffset,
      workWidth] <;>
    omega

private theorem quotientDecrementControl_avoids_lenQ
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.quotientDecrementControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.lenQOffset n lengthWidth ∨
          StepLayout.lenQOffset n lengthWidth + lengthWidth ≤ q := by
  intro g hg q hq
  rcases quotientDecrementControl_wire hg hq with rfl | rfl | rfl <;>
    simp [StepLayout.lenQOffset, StepLayout.phase1Wire,
      StepLayout.phase2Wire, StepLayout.controlWire,
      StepLayout.shiftOffset, workWidth] <;>
    omega

private theorem quotientIncrementControl_avoids_lenQ
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.quotientIncrementControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.lenQOffset n lengthWidth ∨
          StepLayout.lenQOffset n lengthWidth + lengthWidth ≤ q := by
  intro g hg q hq
  rcases quotientIncrementControl_wire hg hq with rfl | rfl | rfl <;>
    simp [StepLayout.lenQOffset, StepLayout.phase1Wire,
      StepLayout.phase2Wire, StepLayout.controlWire,
      StepLayout.shiftOffset, workWidth] <;>
    omega

theorem preShiftBlock_act
    {n lengthWidth shiftWidth I : Nat}
    (hscratch : Shift.scratch shiftWidth
      (StepPlaced.shiftInput n lengthWidth shiftWidth
        (actGates (Step.preShiftControl n lengthWidth shiftWidth) I)) = 0) :
    let C := actGates (Step.preShiftControl n lengthWidth shiftWidth) I
    let result := Shift.out (workWidth n) shiftWidth
      (StepPlaced.shiftInput n lengthWidth shiftWidth C)
    actGates
        (Step.around (Step.preShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth)) I =
      writeField
        (writeField I (StepLayout.shiftOffset n lengthWidth) shiftWidth
          (Shift.position shiftWidth result))
        (StepLayout.work2Offset n) (workWidth n)
        (Shift.work (workWidth n) shiftWidth result) := by
  dsimp only
  have hbody := StepPlaced.shift_act hscratch
  exact around_write_two
    (preShiftControl_wellFormed n lengthWidth shiftWidth)
    (preShiftControl_avoids_shift n lengthWidth shiftWidth)
    (preShiftControl_avoids_work2 n lengthWidth shiftWidth) hbody

theorem postShiftBlock_act
    {n lengthWidth shiftWidth I : Nat}
    (hscratch : Shift.scratch shiftWidth
      (StepPlaced.shiftInput n lengthWidth shiftWidth
        (actGates (Step.postShiftControl n lengthWidth shiftWidth) I)) = 0) :
    let C := actGates (Step.postShiftControl n lengthWidth shiftWidth) I
    let result := Shift.out (workWidth n) shiftWidth
      (StepPlaced.shiftInput n lengthWidth shiftWidth C)
    actGates
        (Step.around (Step.postShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth)) I =
      writeField
        (writeField I (StepLayout.shiftOffset n lengthWidth) shiftWidth
          (Shift.position shiftWidth result))
        (StepLayout.work2Offset n) (workWidth n)
        (Shift.work (workWidth n) shiftWidth result) := by
  dsimp only
  have hbody := StepPlaced.shift_act hscratch
  exact around_write_two
    (postShiftControl_wellFormed n lengthWidth shiftWidth)
    (postShiftControl_avoids_shift n lengthWidth shiftWidth)
    (postShiftControl_avoids_work2 n lengthWidth shiftWidth) hbody

private theorem shiftOut_identity_of_controls_zero
    {workWidth shiftWidth I : Nat}
    (hplus : bitValue I (Shift.plusWire shiftWidth) = 0)
    (hminus : bitValue I (Shift.minusWire workWidth shiftWidth) = 0) :
    Shift.out workWidth shiftWidth I = I := by
  have hposition : Shift.position shiftWidth I < 2 ^ shiftWidth :=
    readField_lt I Shift.positionOffset shiftWidth
  have hright :
      Shift.rotateRightOut workWidth shiftWidth
          (Shift.plusWire shiftWidth) I = I := by
    simp [Shift.rotateRightOut, hplus]
  have hincrement :
      Shift.incrementOut shiftWidth (Shift.plusWire shiftWidth) I = I := by
    unfold Shift.incrementOut
    rw [hplus, Nat.add_zero, Nat.mod_eq_of_lt hposition]
    exact writeField_read I Shift.positionOffset shiftWidth
  have hleft :
      Shift.rotateLeftOut workWidth shiftWidth
          (Shift.minusWire workWidth shiftWidth) I = I := by
    simp [Shift.rotateLeftOut, hminus]
  have hdecrement :
      Shift.decrementOut shiftWidth
          (Shift.minusWire workWidth shiftWidth) I = I := by
    unfold Shift.decrementOut
    rw [hminus, Nat.sub_zero, Nat.add_mod_right,
      Nat.mod_eq_of_lt hposition]
    exact writeField_read I Shift.positionOffset shiftWidth
  simp [Shift.out, hright, hincrement, hleft, hdecrement]

theorem preShiftBlock_identity
    {n lengthWidth shiftWidth I : Nat}
    (hscratch : Shift.scratch shiftWidth
      (StepPlaced.shiftInput n lengthWidth shiftWidth
        (actGates (Step.preShiftControl n lengthWidth shiftWidth) I)) = 0)
    (hplus : bitValue
      (actGates (Step.preShiftControl n lengthWidth shiftWidth) I)
      (StepLayout.plusWire n lengthWidth shiftWidth) = 0)
    (hminus : bitValue
      (actGates (Step.preShiftControl n lengthWidth shiftWidth) I)
      (StepLayout.minusWire n lengthWidth shiftWidth) = 0) :
    actGates
        (Step.around (Step.preShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth)) I = I := by
  let C := actGates (Step.preShiftControl n lengthWidth shiftWidth) I
  let J := StepPlaced.shiftInput n lengthWidth shiftWidth C
  have hJplus : bitValue J (Shift.plusWire shiftWidth) = 0 := by
    simpa [C, J, StepPlaced.shiftInput_plus] using hplus
  have hJminus : bitValue J (Shift.minusWire (workWidth n) shiftWidth) = 0 := by
    simpa [C, J, StepPlaced.shiftInput_minus] using hminus
  have hout : Shift.out (workWidth n) shiftWidth J = J :=
    shiftOut_identity_of_controls_zero hJplus hJminus
  apply around_identity
    (preShiftControl_wellFormed n lengthWidth shiftWidth)
  have hbody := StepPlaced.shift_act (n := n) (lengthWidth := lengthWidth)
    (shiftWidth := shiftWidth) (I := C) hscratch
  dsimp only at hbody
  rw [hbody, hout]
  rw [StepPlaced.shiftInput_position, StepPlaced.shiftInput_work]
  change writeField
      (writeField C (StepLayout.shiftOffset n lengthWidth) shiftWidth
        (readField C (StepLayout.shiftOffset n lengthWidth) shiftWidth))
      (StepLayout.work2Offset n) (workWidth n)
      (readField C (StepLayout.work2Offset n) (workWidth n)) = C
  rw [writeField_read, writeField_read]

theorem postShiftBlock_identity
    {n lengthWidth shiftWidth I : Nat}
    (hscratch : Shift.scratch shiftWidth
      (StepPlaced.shiftInput n lengthWidth shiftWidth
        (actGates (Step.postShiftControl n lengthWidth shiftWidth) I)) = 0)
    (hplus : bitValue
      (actGates (Step.postShiftControl n lengthWidth shiftWidth) I)
      (StepLayout.plusWire n lengthWidth shiftWidth) = 0)
    (hminus : bitValue
      (actGates (Step.postShiftControl n lengthWidth shiftWidth) I)
      (StepLayout.minusWire n lengthWidth shiftWidth) = 0) :
    actGates
        (Step.around (Step.postShiftControl n lengthWidth shiftWidth)
          (StepLayout.shiftGates n lengthWidth shiftWidth)) I = I := by
  let C := actGates (Step.postShiftControl n lengthWidth shiftWidth) I
  let J := StepPlaced.shiftInput n lengthWidth shiftWidth C
  have hJplus : bitValue J (Shift.plusWire shiftWidth) = 0 := by
    simpa [C, J, StepPlaced.shiftInput_plus] using hplus
  have hJminus : bitValue J (Shift.minusWire (workWidth n) shiftWidth) = 0 := by
    simpa [C, J, StepPlaced.shiftInput_minus] using hminus
  have hout : Shift.out (workWidth n) shiftWidth J = J :=
    shiftOut_identity_of_controls_zero hJplus hJminus
  apply around_identity
    (postShiftControl_wellFormed n lengthWidth shiftWidth)
  have hbody := StepPlaced.shift_act (n := n) (lengthWidth := lengthWidth)
    (shiftWidth := shiftWidth) (I := C) hscratch
  dsimp only at hbody
  rw [hbody, hout]
  rw [StepPlaced.shiftInput_position, StepPlaced.shiftInput_work]
  change writeField
      (writeField C (StepLayout.shiftOffset n lengthWidth) shiftWidth
        (readField C (StepLayout.shiftOffset n lengthWidth) shiftWidth))
      (StepLayout.work2Offset n) (workWidth n)
      (readField C (StepLayout.work2Offset n) (workWidth n)) = C
  rw [writeField_read, writeField_read]

theorem quotientDecrementBlock_act
    {n lengthWidth shiftWidth I : Nat}
    (hscratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth
        (actGates (Step.quotientDecrementControl n lengthWidth shiftWidth) I)) =
          0) :
    let C := actGates
      (Step.quotientDecrementControl n lengthWidth shiftWidth) I
    actGates (Step.quotientDecrementBlock n lengthWidth shiftWidth) I =
      writeField I (StepLayout.lenQOffset n lengthWidth) lengthWidth
        (StepPlaced.quotientDecrementValue n lengthWidth shiftWidth C) := by
  dsimp only
  have hbody := StepPlaced.quotientDecrement_act hscratch
  simpa [Step.quotientDecrementBlock] using
    (around_write
      (quotientDecrementControl_wellFormed n lengthWidth shiftWidth)
      (quotientDecrementControl_avoids_lenQ n lengthWidth shiftWidth) hbody)

theorem quotientIncrementBlock_act
    {n lengthWidth shiftWidth I : Nat}
    (hscratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth
        (actGates (Step.quotientIncrementControl n lengthWidth shiftWidth) I)) =
          0) :
    let C := actGates
      (Step.quotientIncrementControl n lengthWidth shiftWidth) I
    actGates (Step.quotientIncrementBlock n lengthWidth shiftWidth) I =
      writeField I (StepLayout.lenQOffset n lengthWidth) lengthWidth
        (StepPlaced.quotientIncrementValue n lengthWidth shiftWidth C) := by
  dsimp only
  have hbody := StepPlaced.quotientIncrement_act hscratch
  simpa [Step.quotientIncrementBlock] using
    (around_write
      (quotientIncrementControl_wellFormed n lengthWidth shiftWidth)
      (quotientIncrementControl_avoids_lenQ n lengthWidth shiftWidth) hbody)

theorem quotientDecrementBlock_identity
    {n lengthWidth shiftWidth I : Nat}
    (hscratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth
        (actGates (Step.quotientDecrementControl n lengthWidth shiftWidth) I)) =
          0)
    (hcontrol : bitValue
      (actGates (Step.quotientDecrementControl n lengthWidth shiftWidth) I)
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.quotientDecrementBlock n lengthWidth shiftWidth) I = I := by
  let C := actGates (Step.quotientDecrementControl n lengthWidth shiftWidth) I
  apply around_identity
    (quotientDecrementControl_wellFormed n lengthWidth shiftWidth)
  have hbody := StepPlaced.quotientDecrement_act
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    (I := C) hscratch
  rw [hbody]
  simp [StepPlaced.quotientDecrementValue, C, hcontrol,
    Nat.add_mod_right, Nat.mod_eq_of_lt (readField_lt C
      (StepLayout.lenQOffset n lengthWidth) lengthWidth), writeField_read]

theorem quotientIncrementBlock_identity
    {n lengthWidth shiftWidth I : Nat}
    (hscratch : Increment.scratch lengthWidth
      (StepPlaced.quotientInput n lengthWidth shiftWidth
        (actGates (Step.quotientIncrementControl n lengthWidth shiftWidth) I)) =
          0)
    (hcontrol : bitValue
      (actGates (Step.quotientIncrementControl n lengthWidth shiftWidth) I)
      (StepLayout.controlWire n lengthWidth shiftWidth) = 0) :
    actGates (Step.quotientIncrementBlock n lengthWidth shiftWidth) I = I := by
  let C := actGates (Step.quotientIncrementControl n lengthWidth shiftWidth) I
  apply around_identity
    (quotientIncrementControl_wellFormed n lengthWidth shiftWidth)
  have hbody := StepPlaced.quotientIncrement_act
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    (I := C) hscratch
  rw [hbody]
  simp [StepPlaced.quotientIncrementValue, C, hcontrol,
    Nat.mod_eq_of_lt (readField_lt C
      (StepLayout.lenQOffset n lengthWidth) lengthWidth), writeField_read]

private theorem swapPrepare_avoids_work1
    {n lengthWidth shiftWidth : Nat} (hlength : 0 < lengthWidth) :
    ∀ g ∈ StepLayout.swapPrepareGates n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work1Offset ∨
          StepLayout.work1Offset + workWidth n ≤ q := by
  apply endpointPlaced_avoids
  · intro g hg
    exact (List.all_eq_true.mp
      (EndpointPrep.swapPrepare_wellFormed hlength)) g hg
  · exact endpointBlocks_avoid_work1 n lengthWidth shiftWidth

private theorem swapPrepare_avoids_sign
    {n lengthWidth shiftWidth : Nat} (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    ∀ g ∈ StepLayout.swapPrepareGates n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.signWire n lengthWidth shiftWidth ∨
          StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ q := by
  apply endpointPlaced_avoids
  · intro g hg
    exact (List.all_eq_true.mp
      (EndpointPrep.swapPrepare_wellFormed hlength)) g hg
  · exact endpointBlocks_avoid_sign n lengthWidth shiftWidth hwidths

theorem swapBody_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hwork : workWidth n ≤ 2 ^ lengthWidth)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth) I)))
    (haccumulator : bitValue
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth) I))
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0) :
    let P := actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth) I
    let input := StepPlaced.intervalInput n lengthWidth shiftWidth P
    actGates
        (StepLayout.swapPrepareGates n lengthWidth shiftWidth ++
          StepLayout.selectSwapGates n lengthWidth shiftWidth ++
          StepLayout.swapCleanupGates n lengthWidth shiftWidth) I =
      writeField
        (writeField I StepLayout.work1Offset (workWidth n)
          (SelectSwap.workValue left (workWidth n) lengthWidth input))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (SelectSwap.signValue left (workWidth n) lengthWidth input) := by
  dsimp only
  have hbody := StepPlaced.selectSwap_act hwork hstable haccumulator
  simpa [Step.around, StepLayout.swapCleanupGates, List.append_assoc] using
    (around_write_two
      (StepLayout.swapPrepareGates_wellFormed
        (n := n) (shiftWidth := shiftWidth) hlength hwidths)
      (swapPrepare_avoids_work1 hlength)
      (swapPrepare_avoids_sign hlength hwidths) hbody)

theorem swapBody_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth) I))) :
    actGates
        (StepLayout.swapPrepareGates n lengthWidth shiftWidth ++
          StepLayout.selectSwapGates n lengthWidth shiftWidth ++
          StepLayout.swapCleanupGates n lengthWidth shiftWidth) I = I := by
  have hbody := StepPlaced.selectSwapGates_identity h
  simpa [Step.around, StepLayout.swapCleanupGates, List.append_assoc] using
    (around_identity
      (StepLayout.swapPrepareGates_wellFormed
        (n := n) (shiftWidth := shiftWidth) hlength hwidths) hbody)

private theorem swapControl_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (Step.swapControl n lengthWidth shiftWidth).all
      (RGate.wellFormed (StepLayout.layout n lengthWidth shiftWidth).width) =
        true :=
  (Step.controls_wellFormed n lengthWidth shiftWidth).2.2.2.2.2.1

private theorem swapControl_wire
    {n lengthWidth shiftWidth q : Nat} {g : RGate}
    (hg : g ∈ Step.swapControl n lengthWidth shiftWidth)
    (hq : q ∈ g.wires) :
    q = StepLayout.phase1Wire n lengthWidth shiftWidth ∨
      q = StepLayout.phase2Wire n lengthWidth shiftWidth ∨
      q = StepLayout.controlWire n lengthWidth shiftWidth := by
  have hq' : q ∈
      (Step.swapControl n lengthWidth shiftWidth).flatMap RGate.wires := by
    rw [List.mem_flatMap]
    exact ⟨g, hg, hq⟩
  simp [Step.swapControl, Phase.xorPairGates, RGate.wires] at hq'
  aesop

private theorem swapControl_avoids_work1
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.swapControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.work1Offset ∨
          StepLayout.work1Offset + workWidth n ≤ q := by
  intro g hg q hq
  rcases swapControl_wire hg hq with rfl | rfl | rfl <;>
    simp [StepLayout.work1Offset, StepLayout.phase1Wire,
      StepLayout.phase2Wire, StepLayout.controlWire,
      StepLayout.shiftOffset, workWidth] <;>
    omega

private theorem swapControl_avoids_sign
    (n lengthWidth shiftWidth : Nat) :
    ∀ g ∈ Step.swapControl n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < StepLayout.signWire n lengthWidth shiftWidth ∨
          StepLayout.signWire n lengthWidth shiftWidth + 1 ≤ q := by
  intro g hg q hq
  rcases swapControl_wire hg hq with rfl | rfl | rfl <;>
    simp [StepLayout.signWire, StepLayout.phase1Wire,
      StepLayout.phase2Wire, StepLayout.controlWire]

theorem swapBlock_act
    {n lengthWidth shiftWidth I left right : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hwork : workWidth n ≤ 2 ^ lengthWidth)
    (hstable : Interval.Stable left right (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.swapControl n lengthWidth shiftWidth) I))))
    (haccumulator : bitValue
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.swapControl n lengthWidth shiftWidth) I)))
      (Interval.accumulatorWire (workWidth n) lengthWidth) = 0) :
    let C := actGates (Step.swapControl n lengthWidth shiftWidth) I
    let P := actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth) C
    let input := StepPlaced.intervalInput n lengthWidth shiftWidth P
    actGates (Step.swapBlock n lengthWidth shiftWidth) I =
      writeField
        (writeField I StepLayout.work1Offset (workWidth n)
          (SelectSwap.workValue left (workWidth n) lengthWidth input))
        (StepLayout.signWire n lengthWidth shiftWidth) 1
        (SelectSwap.signValue left (workWidth n) lengthWidth input) := by
  dsimp only
  have hbody := swapBody_act hlength hwidths hwork hstable haccumulator
  simpa [Step.swapBlock] using
    (around_write_two
      (swapControl_wellFormed n lengthWidth shiftWidth)
      (swapControl_avoids_work1 n lengthWidth shiftWidth)
      (swapControl_avoids_sign n lengthWidth shiftWidth) hbody)

theorem swapBlock_identity
    {n lengthWidth shiftWidth I : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (h : StepPlaced.IntervalInactive (workWidth n) lengthWidth
      (StepPlaced.intervalInput n lengthWidth shiftWidth
        (actGates (StepLayout.swapPrepareGates n lengthWidth shiftWidth)
          (actGates (Step.swapControl n lengthWidth shiftWidth) I)))) :
    actGates (Step.swapBlock n lengthWidth shiftWidth) I = I := by
  have hbody := swapBody_identity hlength hwidths h
  simpa [Step.swapBlock] using
    (around_identity (swapControl_wellFormed n lengthWidth shiftWidth) hbody)

end StepBlocks
end Euclid
end VQ
