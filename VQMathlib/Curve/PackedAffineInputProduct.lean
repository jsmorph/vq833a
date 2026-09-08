import VQ.Curve.PackedAffineInputProduct
import VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct

namespace VQMathlib.Curve.PackedAffineInputProduct

open VQ
open VQ.Reversible
open VQ.Curve.PackedAffineInputProduct

def gathered (I : Nat) : Nat :=
  gatherBits (place localLayout wiring) localLayout.width I

structure WorkspaceClear (I : Nat) : Prop where
  lengthT : readField I VQ.Euclid.PackedStepLayout.lengthTOffset 9 = 0
  lengthQ : readField I VQ.Euclid.PackedStepLayout.lengthQOffset 9 = 0
  lengthRPrime :
    readField I VQ.Euclid.PackedStepLayout.lengthRPrimeOffset 8 = 0
  phases : readField I VQ.Euclid.PackedStepLayout.phaseOneWire 2 = 0
  pool : readField I VQ.Euclid.PackedStepLayout.poolOffset 13 = 0
  sourceHigh : readField I (sourceOffset + 256) 3 = 0
  multiplierHigh : readField I (multiplierOffset + 256) 3 = 0

theorem gathered_target (I : Nat) :
    VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct.targetValue
        (gathered I) =
      readField I targetOffset 256 := by
  simpa [VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct.targetValue,
    gathered, localLayout, wiring, Layout.offset, Layout.size, targetOffset,
    VQ.Curve.PackedReversibleSecp256k1.wordWidth,
    VQ.Curve.PackedModularAddition.targetOffset] using
      readField_gatherBits localLayout wiring 0 I (by decide)

theorem gathered_source (I : Nat) :
    VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct.sourceValue
        (gathered I) =
      readField I sourceOffset 256 := by
  simpa [VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct.sourceValue,
    gathered, localLayout, wiring, Layout.offset, Layout.size, sourceOffset,
    VQ.Curve.PackedReversibleSecp256k1.wordWidth,
    VQ.Curve.PackedModularAddition.sourceOffset] using
      readField_gatherBits localLayout wiring 2 I (by decide)

theorem place_multiplierWire {bit : Nat}
    (hbit : bit < VQ.Curve.PackedReversibleSecp256k1.wordWidth) :
    place localLayout wiring
        (VQ.Curve.PackedReversibleSecp256k1CompactProduct.multiplierWire bit) =
      multiplierOffset + bit := by
  cases bit with
  | zero => decide +kernel
  | succ bit =>
      cases bit with
      | zero => decide +kernel
      | succ bit =>
          cases bit with
          | zero => decide +kernel
          | succ bit =>
              have htail : bit < 253 := by
                simp only [VQ.Curve.PackedReversibleSecp256k1.wordWidth] at hbit
                omega
              have hplace := place_field localLayout wiring 17 bit
                (by decide) (by
                  simpa [localLayout, Layout.size] using htail)
              rw [
                VQ.Curve.PackedReversibleSecp256k1CompactProduct.multiplierWire]
              change place localLayout wiring (562 + bit) =
                multiplierOffset + (bit + 3)
              calc
                place localLayout wiring (562 + bit) =
                    multiplierOffset + 3 + bit := by
                  simpa [localLayout, wiring, Layout.offset, Layout.size] using
                    hplace
                _ = multiplierOffset + (bit + 3) := by omega

theorem gathered_multiplierBit {I bit : Nat}
    (hbit : bit < VQ.Curve.PackedReversibleSecp256k1.wordWidth) :
    (gathered I).testBit
        (VQ.Curve.PackedReversibleSecp256k1CompactProduct.multiplierWire bit) =
      I.testBit (multiplierOffset + bit) := by
  rw [gathered, testBit_gatherBits]
  have hlocal :
      VQ.Curve.PackedReversibleSecp256k1CompactProduct.multiplierWire bit <
        localLayout.width := by
    rw [localLayout_width]
    exact
      VQ.Curve.PackedReversibleSecp256k1CompactProduct.multiplierWire_lt hbit
  simp [hlocal, place_multiplierWire hbit]

theorem gathered_multiplier (I : Nat) :
    VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct.multiplierValue
        (gathered I) =
      readField I multiplierOffset 256 := by
  unfold
    VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct.multiplierValue
  have hbits :
      (List.range VQ.Curve.PackedReversibleSecp256k1.wordWidth).map
          (fun bit => (gathered I).testBit
            (VQ.Curve.PackedReversibleSecp256k1CompactProduct.multiplierWire
              bit)) =
        (List.range VQ.Curve.PackedReversibleSecp256k1.wordWidth).map
          (fun bit => I.testBit (multiplierOffset + bit)) := by
    apply List.map_congr_left
    intro bit hbit
    exact gathered_multiplierBit (List.mem_range.mp hbit)
  rw [hbits,
    VQMathlib.Curve.PackedReversibleSecp256k1Arithmetic.Product.decode_range_testBits_offset]
  rfl

private theorem gathered_constant {I : Nat} (h : WorkspaceClear I) :
    readField (gathered I)
        VQ.Curve.PackedReversibleSecp256k1Arithmetic.constantOffset
        VQ.Curve.PackedReversibleSecp256k1.chunkWidth = 0 := by
  have h0 := readField_gatherBits localLayout wiring 9 I (by decide)
  have h1 := readField_gatherBits localLayout wiring 10 I (by decide)
  have h2 := readField_gatherBits localLayout wiring 11 I (by decide)
  have h3 := readField_gatherBits localLayout wiring 12 I (by decide)
  have h4 := readField_gatherBits localLayout wiring 13 I (by decide)
  have hz0 : readField (gathered I) 519 9 = 0 := by
    simpa [gathered, localLayout, wiring, Layout.offset, Layout.size] using
      h0.trans h.lengthT
  have hz1 : readField (gathered I) 528 9 = 0 := by
    simpa [gathered, localLayout, wiring, Layout.offset, Layout.size] using
      h1.trans h.lengthQ
  have hz2 : readField (gathered I) 537 8 = 0 := by
    simpa [gathered, localLayout, wiring, Layout.offset, Layout.size] using
      h2.trans h.lengthRPrime
  have hz3 : readField (gathered I) 545 2 = 0 := by
    simpa [gathered, localLayout, wiring, Layout.offset, Layout.size] using
      h3.trans h.phases
  have hpool5 : readField I VQ.Euclid.PackedStepLayout.poolOffset 5 = 0 :=
    readField_sub_zero (by omega) (by omega) h.pool
  have hz4 : readField (gathered I) 547 5 = 0 := by
    simpa [gathered, localLayout, wiring, Layout.offset, Layout.size] using
      h4.trans hpool5
  rw [show VQ.Curve.PackedReversibleSecp256k1Arithmetic.constantOffset = 519 by
      decide +kernel,
    show VQ.Curve.PackedReversibleSecp256k1.chunkWidth =
        9 + (9 + (8 + (2 + 5))) by decide +kernel,
    readField_split]
  refine ⟨hz0, ?_⟩
  rw [readField_split]
  refine ⟨by simpa using hz1, ?_⟩
  rw [readField_split]
  refine ⟨by simpa using hz2, ?_⟩
  rw [readField_split]
  exact ⟨by simpa using hz3, by simpa using hz4⟩

theorem gathered_workspace {I : Nat} (h : WorkspaceClear I) :
    VQ.Curve.PackedReversibleSecp256k1Arithmetic.CorrectionWorkspaceClear
      (gathered I) := by
  constructor
  · exact gathered_constant h
  · rw [← readField_one]
    simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.probeOutputWire] using
        (readField_gatherBits localLayout wiring 14 I (by decide)).trans
          (readField_sub_zero (i := I) (off := multiplierOffset + 256) (len := 3)
            (o := multiplierOffset + 257) (l := 1) (by omega) (by omega)
            h.multiplierHigh)
  · rw [← readField_one]
    simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.oneWire] using
        (readField_gatherBits localLayout wiring 15 I (by decide)).trans
          (readField_sub_zero (i := I) (off := multiplierOffset + 256) (len := 3)
            (o := multiplierOffset + 258) (l := 1) (by omega) (by omega)
            h.multiplierHigh)
  · rw [← readField_one]
    simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
      VQ.Curve.PackedModularAddition.scratchWire,
      VQ.Curve.PackedReversibleSecp256k1.wordWidth] using
        (readField_gatherBits localLayout wiring 6 I (by decide)).trans
          (readField_sub_zero (i := I) (off := sourceOffset + 256) (len := 3)
            (o := sourceOffset + 257) (l := 1) (by omega) (by omega)
            h.sourceHigh)
  · rw [← readField_one]
    simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
      VQ.Curve.PackedModularAddition.carryInWire,
      VQ.Curve.PackedReversibleSecp256k1.wordWidth] using
        (readField_gatherBits localLayout wiring 4 I (by decide)).trans
          (readField_sub_zero (i := I) (off := sourceOffset + 256) (len := 3)
            (o := sourceOffset + 256) (l := 1) (by omega) (by omega)
            h.sourceHigh)
  · intro chunk hchunk
    rw [← readField_one]
    have hpool8 : readField I (VQ.Euclid.PackedStepLayout.poolOffset + 5) 8 =
        0 := readField_sub_zero (by omega) (by omega) h.pool
    simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.carryOffset] using
        (readField_gatherBits_sub localLayout wiring 16 chunk 1 I
          (by decide) (by simp [localLayout, Layout.size]; omega)).trans
            (readField_sub_zero (i := I)
              (off := VQ.Euclid.PackedStepLayout.poolOffset + 5) (len := 8)
              (o := VQ.Euclid.PackedStepLayout.poolOffset + 5 + chunk) (l := 1)
              (by omega) (by omega) hpool8)

theorem gathered_reduction (I : Nat) :
    bitValue (gathered I)
        (VQ.Curve.PackedModularAddition.reductionWire 256) =
      bitValue I (sourceOffset + 258) := by
  rw [← readField_one, ← readField_one]
  simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
    VQ.Curve.PackedModularAddition.reductionWire] using
      readField_gatherBits localLayout wiring 7 I (by decide)

theorem gathered_control (I : Nat) :
    bitValue (gathered I)
        (VQ.Curve.PackedModularAddition.controlWire 256) =
      bitValue I (multiplierOffset + 256) := by
  rw [← readField_one, ← readField_one]
  simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
    VQ.Curve.PackedModularAddition.controlWire] using
      readField_gatherBits localLayout wiring 8 I (by decide)

theorem gates_correct {I : Nat}
    (hsource : readField I sourceOffset 256 ≤ VQ.Curve.p)
    (htarget : readField I targetOffset 256 = 0)
    (hworkspace : WorkspaceClear I) :
    actGates gates I =
      writeField I targetOffset 256
        (readField I multiplierOffset 256 *
          readField I sourceOffset 256 % VQ.Curve.p) := by
  have hsourceLocal :
      VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct.sourceValue
          (gathered I) ≤ VQ.Curve.p := by
    rw [gathered_source]
    exact hsource
  have htargetLocal :
      VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct.targetValue
          (gathered I) = 0 := by
    rw [gathered_target]
    exact htarget
  have hreductionLocal : bitValue (gathered I)
      (VQ.Curve.PackedModularAddition.reductionWire 256) = 0 := by
    rw [gathered_reduction, ← readField_one]
    exact readField_sub_zero (by omega) (by omega) hworkspace.sourceHigh
  have hcontrolLocal : bitValue (gathered I)
      (VQ.Curve.PackedModularAddition.controlWire 256) = 0 := by
    rw [gathered_control, ← readField_one]
    exact readField_sub_zero (by omega) (by omega) hworkspace.multiplierHigh
  have hlocal :=
    VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct.gates_correct
      hsourceLocal htargetLocal (gathered_workspace hworkspace)
      hreductionLocal hcontrolLocal
  have hlocal' :
      actGates VQ.Curve.PackedReversibleSecp256k1CompactProduct.gates
          (gathered I) =
        localLayout.write (gathered I) 0
          (readField I multiplierOffset 256 *
            readField I sourceOffset 256 % VQ.Curve.p) := by
    simpa [localLayout, Layout.write, Layout.offset, Layout.size,
      VQ.Curve.PackedModularAddition.targetOffset,
      VQ.Curve.PackedReversibleSecp256k1.wordWidth,
      gathered_multiplier, gathered_source] using hlocal
  have hplaced := actGates_placed_write
    (gs := VQ.Curve.PackedReversibleSecp256k1CompactProduct.gates)
    (L := localLayout) (W := wiring) (k := 0)
    VQ.Curve.PackedAffineInputProduct.wiring_disjoint
    VQ.Curve.PackedAffineInputProduct.wiring_length (by decide)
    (fun gate hgate => by
      rw [VQ.Curve.PackedAffineInputProduct.localLayout_width]
      exact List.all_eq_true.mp
        VQ.Curve.PackedReversibleSecp256k1CompactProduct.gates_wellFormed
          gate hgate)
    hlocal'
  simpa [gates, localLayout, wiring, Layout.size, targetOffset] using hplaced

theorem gates_reverse_clears {I : Nat}
    (hsource : readField I sourceOffset 256 ≤ VQ.Curve.p)
    (htarget : readField I targetOffset 256 = 0)
    (hworkspace : WorkspaceClear I) :
    actGates gates.reverse
        (writeField I targetOffset 256
          (readField I multiplierOffset 256 *
            readField I sourceOffset 256 % VQ.Curve.p)) =
      I := by
  rw [← gates_correct hsource htarget hworkspace]
  exact actGates_reverse VQ.Curve.PackedAffineInputProduct.gates_wellFormed I
end VQMathlib.Curve.PackedAffineInputProduct
