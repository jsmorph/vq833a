import VQ.Euclid.SignCorrection

namespace VQ.Euclid.SignCorrectionPlaced

open Reversible

def layout (n lengthWidth shiftWidth : Nat) : Layout :=
  ExtractionPlaced.layout n lengthWidth shiftWidth

def wiring (n lengthWidth shiftWidth : Nat) : Wiring :=
  [StepLayout.work1Offset,
    ExtractionPlaced.outputOffset n lengthWidth shiftWidth,
    StepLayout.carryWire n lengthWidth shiftWidth,
    StepLayout.iterWire n lengthWidth shiftWidth,
    StepLayout.accumulatorWire n lengthWidth shiftWidth]

def gates (n lengthWidth shiftWidth : Nat) : List RGate :=
  StepLayout.placed (SignCorrection.controlledLayout n)
    (wiring n lengthWidth shiftWidth)
    (SignCorrection.negativeControlledGates n)

def circuit (n lengthWidth shiftWidth : Nat) : RCircuit :=
  { width := (layout n lengthWidth shiftWidth).width,
    gates := gates n lengthWidth shiftWidth }

theorem wiring_disjoint (n lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (SignCorrection.controlledLayout n)
      (wiring n lengthWidth shiftWidth) := by
  intro j k hj hk hne
  simp [wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [SignCorrection.controlledLayout, Layout.size, wiring,
      StepLayout.work1Offset, StepLayout.iterWire, StepLayout.phase1Wire,
      StepLayout.shiftOffset, StepLayout.carryWire, StepLayout.auxOffset,
      StepLayout.accumulatorWire, ExtractionPlaced.outputOffset,
      ExtractionPlaced.baseWidth, StepLayout.layout_width,
      StepLayout.auxWidth, StepLayout.selectorWidth, workWidth] <;>
    omega

theorem wiring_bound (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (SignCorrection.controlledLayout n).length →
      (wiring n lengthWidth shiftWidth).getD j 0 +
          (SignCorrection.controlledLayout n).size j ≤
        (layout n lengthWidth shiftWidth).width := by
  intro j hj
  simp [SignCorrection.controlledLayout] at hj
  interval_cases j <;>
    simp_all [SignCorrection.controlledLayout, Layout.size, wiring, layout,
      ExtractionPlaced.layout_width, StepLayout.work1Offset,
      StepLayout.iterWire, StepLayout.phase1Wire, StepLayout.shiftOffset,
      StepLayout.carryWire, StepLayout.auxOffset, StepLayout.accumulatorWire,
      ExtractionPlaced.outputOffset, ExtractionPlaced.baseWidth,
      StepLayout.layout_width, StepLayout.auxWidth, StepLayout.selectorWidth,
      workWidth] <;>
    omega

theorem gates_act {n lengthWidth shiftWidth I : Nat}
    (hn : 0 < n)
    (hcarry : bitValue I
      (StepLayout.carryWire n lengthWidth shiftWidth) = 0)
    (hscratch : I.testBit
      (StepLayout.accumulatorWire n lengthWidth shiftWidth) = false) :
    actGates (gates n lengthWidth shiftWidth) I =
      if bitValue I (StepLayout.iterWire n lengthWidth shiftWidth) = 0 then
        writeField I
          (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n
          ((readField I StepLayout.work1Offset n + 2 ^ n -
            readField I
              (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n) %
            2 ^ n)
      else I := by
  let L := SignCorrection.controlledLayout n
  let W := wiring n lengthWidth shiftWidth
  let input := gatherBits (place L W) L.width I
  have hsource :
      readField input SignCorrection.sourceOffset n =
        readField I StepLayout.work1Offset n := by
    change L.read input 0 = readField I StepLayout.work1Offset n
    rw [read_gatherBits L W 0 I (by simp [W, wiring])]
    simp [L, W, SignCorrection.controlledLayout, Layout.size, wiring]
  have htarget :
      readField input (SignCorrection.targetOffset n) n =
        readField I
          (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n := by
    change L.read input 1 =
      readField I (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n
    rw [read_gatherBits L W 1 I (by simp [W, wiring])]
    simp [L, W, SignCorrection.controlledLayout, Layout.size, wiring]
  have hcarryInput :
      bitValue input (SignCorrection.carryWire n) = 0 := by
    rw [← readField_one]
    rw [show SignCorrection.carryWire n = L.offset 2 by
      simp [L, SignCorrection.controlledLayout, SignCorrection.carryWire,
        Layout.offset]
      omega]
    change L.read input 2 = 0
    rw [read_gatherBits L W 2 I (by simp [W, wiring])]
    simpa [L, W, SignCorrection.controlledLayout, Layout.size, wiring,
      readField_one] using hcarry
  have hcontrol :
      bitValue input (SignCorrection.controlWire n) =
        bitValue I (StepLayout.iterWire n lengthWidth shiftWidth) := by
    rw [← readField_one, ← readField_one]
    rw [show SignCorrection.controlWire n = L.offset 3 by
      simp [L, SignCorrection.controlledLayout, SignCorrection.controlWire,
        Layout.offset]
      omega]
    change L.read input 3 =
      readField I (StepLayout.iterWire n lengthWidth shiftWidth) 1
    rw [read_gatherBits L W 3 I (by simp [W, wiring])]
    simp [L, W, SignCorrection.controlledLayout, Layout.size, wiring]
  have hscratchInput :
      input.testBit (SignCorrection.controlScratchWire n) = false := by
    have hvalue :
        bitValue input (SignCorrection.controlScratchWire n) = 0 := by
      rw [← readField_one]
      rw [show SignCorrection.controlScratchWire n = L.offset 4 by
        simp [L, SignCorrection.controlledLayout,
          SignCorrection.controlScratchWire, Layout.offset]
        omega]
      change L.read input 4 = 0
      rw [read_gatherBits L W 4 I (by simp [W, wiring])]
      simp [L, W, SignCorrection.controlledLayout, Layout.size, wiring,
        readField_one, bitValue, hscratch]
    cases hbit : input.testBit (SignCorrection.controlScratchWire n) <;>
      simp_all [bitValue]
  have hlocal := SignCorrection.negativeControlledGates_act
    hn hcarryInput hscratchInput
  rw [hsource, htarget, hcontrol] at hlocal
  by_cases hiter :
      bitValue I (StepLayout.iterWire n lengthWidth shiftWidth) = 0
  · rw [if_pos hiter]
    have hlocalWrite :
        actGates (SignCorrection.negativeControlledGates n) input =
          L.write input 1
            ((readField I StepLayout.work1Offset n + 2 ^ n -
              readField I
                (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n) %
              2 ^ n) := by
      rw [hlocal, if_pos hiter]
      rfl
    have hplaced := actGates_placed_write
      (k := 1) (I := I)
      (wiring_disjoint n lengthWidth shiftWidth)
      (by simp [SignCorrection.controlledLayout, wiring])
      (by simp [SignCorrection.controlledLayout])
      (fun g hg => List.all_eq_true.mp
        (SignCorrection.negativeControlledGates_wellFormed n) g hg)
      hlocalWrite
    simpa [gates, StepLayout.placed, L, W, input, wiring,
      SignCorrection.controlledLayout, Layout.size] using hplaced
  · rw [if_neg hiter]
    have hlocalIdentity :
        actGates (SignCorrection.negativeControlledGates n) input = input := by
      rw [hlocal, if_neg hiter]
    have hplaced := actGates_placed_congr (hs := [])
      (wiring_disjoint n lengthWidth shiftWidth)
      (by simp [SignCorrection.controlledLayout, wiring])
      (fun g hg => List.all_eq_true.mp
        (SignCorrection.negativeControlledGates_wellFormed n) g hg)
      (by simp) I
      (by simpa only [actGates_nil] using hlocalIdentity)
    simpa only [gates, StepLayout.placed, L, W, List.map_nil,
      actGates_nil] using hplaced

theorem gates_wellFormed (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply wellFormed_placeGates
    (wiring_disjoint n lengthWidth shiftWidth)
    (by simp [SignCorrection.controlledLayout, wiring])
    (wiring_bound n lengthWidth shiftWidth)
  intro g hg
  exact List.all_eq_true.mp
    (SignCorrection.negativeControlledGates_wellFormed n) g hg

theorem circuit_wellFormed (n lengthWidth shiftWidth : Nat) :
    (circuit n lengthWidth shiftWidth).wellFormed = true :=
  gates_wellFormed n lengthWidth shiftWidth

theorem gates_length (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).length =
      (SignCorrection.negativeControlledGates n).length :=
  StepLayout.placed_length _ _ _

theorem gates_ccx (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).countP RGate.isCcx = 10 * n := by
  rw [gates, StepLayout.placed_ccx,
    SignCorrection.negativeControlledGates_ccx]

theorem gates_length_le (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).length ≤ 11 * n + 4 := by
  rw [gates_length]
  exact SignCorrection.negativeControlledGates_length_le n

theorem gates_cx_le (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).countP RGate.isCx ≤ 7 * n + 2 := by
  rw [gates, StepLayout.placed_cx]
  exact SignCorrection.negativeControlledGates_cx_le n

end VQ.Euclid.SignCorrectionPlaced
