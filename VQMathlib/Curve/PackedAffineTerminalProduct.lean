import VQ.Curve.PackedAffineTerminalProduct
import VQMathlib.Curve.PackedReversibleSecp256k1CompactProduct

namespace VQMathlib.Curve.PackedAffineTerminalProduct

open VQ
open VQ.Reversible
open VQ.Curve.PackedAffineTerminalProduct

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
  targetHigh : readField I (targetOffset + 256) 3 = 0

structure EncodedWorkspace (I : Nat) : Prop where
  lengthT : readField I VQ.Euclid.PackedStepLayout.lengthTOffset 9 = 255
  lengthQ : readField I VQ.Euclid.PackedStepLayout.lengthQOffset 9 = 511
  lengthRPrime :
    readField I VQ.Euclid.PackedStepLayout.lengthRPrimeOffset 8 = 255
  phases : readField I VQ.Euclid.PackedStepLayout.phaseOneWire 2 = 0
  pool : readField I VQ.Euclid.PackedStepLayout.poolOffset 13 = 0
  sourceHigh : readField I (sourceOffset + 256) 3 = 0
  targetHigh : readField I (targetOffset + 256) 3 = 4

def masked (I : Nat) : Nat :=
  actGates VQ.Curve.PackedAffineTerminalProduct.workspaceMaskGates I

private theorem xorShiftedField_eq_writeField
    (I value offset width : Nat) :
    I ^^^ (readField value 0 width <<< offset) =
      writeField I offset width
        (readField I offset width ^^^ readField value 0 width) := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
  by_cases hin : offset ≤ q ∧ q < offset + width
  · rw [testBit_writeField_inside hin.1 hin.2, Nat.testBit_xor,
      testBit_readField, testBit_readField]
    simp [hin.1, show q - offset < width by omega,
      show offset + (q - offset) = q by omega]
  · rw [testBit_writeField_outside (by omega)]
    by_cases hlo : offset ≤ q
    · have hhi : offset + width ≤ q := by omega
      have hbit : (readField value 0 width).testBit (q - offset) = false := by
        rw [testBit_readField]
        simp [show ¬q - offset < width by omega]
      simp [hlo, hbit]
    · simp [hlo]

private theorem act_constantXorGates_eq_writeField
    (value offset width I : Nat) :
    actGates (constantXorGates value offset width) I =
      writeField I offset width
        (readField I offset width ^^^ readField value 0 width) := by
  rw [act_constantXorGates]
  exact xorShiftedField_eq_writeField I value offset width

theorem workspaceMaskGates_act (I : Nat) :
    actGates VQ.Curve.PackedAffineTerminalProduct.workspaceMaskGates I =
      writeField
        (writeField
          (writeField
            (writeField I VQ.Euclid.PackedStepLayout.lengthTOffset 9
              (readField I VQ.Euclid.PackedStepLayout.lengthTOffset 9 ^^^ 255))
            VQ.Euclid.PackedStepLayout.lengthQOffset 9
              (readField I VQ.Euclid.PackedStepLayout.lengthQOffset 9 ^^^ 511))
          VQ.Euclid.PackedStepLayout.lengthRPrimeOffset 8
            (readField I VQ.Euclid.PackedStepLayout.lengthRPrimeOffset 8 ^^^
              255))
        (targetOffset + 256) 3
          (readField I (targetOffset + 256) 3 ^^^ 4) := by
  let I1 := writeField I VQ.Euclid.PackedStepLayout.lengthTOffset 9
    (readField I VQ.Euclid.PackedStepLayout.lengthTOffset 9 ^^^ 255)
  let I2 := writeField I1 VQ.Euclid.PackedStepLayout.lengthQOffset 9
    (readField I VQ.Euclid.PackedStepLayout.lengthQOffset 9 ^^^ 511)
  let I3 := writeField I2 VQ.Euclid.PackedStepLayout.lengthRPrimeOffset 8
    (readField I VQ.Euclid.PackedStepLayout.lengthRPrimeOffset 8 ^^^ 255)
  have hfirst :
      actGates
          (constantXorGates 255
            VQ.Euclid.PackedStepLayout.lengthTOffset 9) I = I1 := by
    simp [I1, act_constantXorGates_eq_writeField, readField]
  have hsecond :
      actGates
          (constantXorGates 511
            VQ.Euclid.PackedStepLayout.lengthQOffset 9) I1 = I2 := by
    rw [act_constantXorGates_eq_writeField]
    simp only [I2, I1]
    rw [readField_writeField_of_disjoint (Or.inl (by decide))]
    norm_num [readField]
  have hthird :
      actGates
          (constantXorGates 255
            VQ.Euclid.PackedStepLayout.lengthRPrimeOffset 8) I2 = I3 := by
    rw [act_constantXorGates_eq_writeField]
    simp only [I3, I2, I1]
    rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inl (by decide))]
    norm_num [readField]
  simp only [VQ.Curve.PackedAffineTerminalProduct.workspaceMaskGates,
    actGates_append, hfirst, hsecond, hthird,
    act_constantXorGates_eq_writeField]
  simp only [I3, I2, I1]
  rw [readField_writeField_of_disjoint (Or.inr (by decide)),
    readField_writeField_of_disjoint (Or.inr (by decide)),
    readField_writeField_of_disjoint (Or.inr (by decide))]
  norm_num [readField]

theorem masked_workspace {I : Nat} (h : EncodedWorkspace I) :
    WorkspaceClear (masked I) := by
  have hlengthTValue :
      readField I VQ.Euclid.PackedStepLayout.lengthTOffset 9 ^^^ 255 <
        2 ^ 9 :=
    Nat.xor_lt_two_pow (readField_lt _ _ _) (by norm_num)
  have hlengthQValue :
      readField I VQ.Euclid.PackedStepLayout.lengthQOffset 9 ^^^ 511 <
        2 ^ 9 :=
    Nat.xor_lt_two_pow (readField_lt _ _ _) (by norm_num)
  have hlengthRPrimeValue :
      readField I VQ.Euclid.PackedStepLayout.lengthRPrimeOffset 8 ^^^ 255 <
        2 ^ 8 :=
    Nat.xor_lt_two_pow (readField_lt _ _ _) (by norm_num)
  have htargetHighValue : readField I (targetOffset + 256) 3 ^^^ 4 <
      2 ^ 3 :=
    Nat.xor_lt_two_pow (readField_lt _ _ _) (by norm_num)
  rw [masked, workspaceMaskGates_act]
  constructor
  · rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)),
      readField_writeField_self hlengthTValue, h.lengthT, Nat.xor_self]
  · rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)),
      readField_writeField_self hlengthQValue, h.lengthQ, Nat.xor_self]
  · rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_self hlengthRPrimeValue, h.lengthRPrime,
      Nat.xor_self]
  · rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inl (by decide)), h.phases]
  · rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inl (by decide)), h.pool]
  · rw [readField_writeField_of_disjoint (Or.inl (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)),
      readField_writeField_of_disjoint (Or.inr (by decide)), h.sourceHigh]
  · rw [readField_writeField_self htargetHighValue,
      h.targetHigh, Nat.xor_self]

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
          (readField_sub_zero (i := I) (off := targetOffset + 256) (len := 3)
            (o := targetOffset + 257) (l := 1) (by omega) (by omega)
            h.targetHigh)
  · rw [← readField_one]
    simpa [gathered, localLayout, wiring, Layout.offset, Layout.size,
      VQ.Curve.PackedReversibleSecp256k1Arithmetic.oneWire] using
        (readField_gatherBits localLayout wiring 15 I (by decide)).trans
          (readField_sub_zero (i := I) (off := targetOffset + 256) (len := 3)
            (o := targetOffset + 258) (l := 1) (by omega) (by omega)
            h.targetHigh)
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
      bitValue I (targetOffset + 256) := by
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
    exact readField_sub_zero (by omega) (by omega) hworkspace.targetHigh
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
    VQ.Curve.PackedAffineTerminalProduct.wiring_disjoint
    VQ.Curve.PackedAffineTerminalProduct.wiring_length (by decide)
    (fun gate hgate => by
      rw [VQ.Curve.PackedAffineTerminalProduct.localLayout_width]
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
  exact actGates_reverse VQ.Curve.PackedAffineTerminalProduct.gates_wellFormed I

private theorem masked_readField
    {I offset width : Nat}
    (hlengths :
      offset + width ≤ VQ.Euclid.PackedStepLayout.lengthTOffset ∨
        VQ.Euclid.PackedStepLayout.lengthRPrimeOffset + 8 ≤ offset)
    (htarget : offset + width ≤ targetOffset + 256 ∨
      targetOffset + 259 ≤ offset) :
    readField (masked I) offset width = readField I offset width := by
  apply readField_actGates_of_outside
  intro gate hgate q hq
  simp only [VQ.Curve.PackedAffineTerminalProduct.workspaceMaskGates,
    List.mem_append] at hgate
  rcases hgate with ((hgate | hgate) | hgate) | hgate
  · have hwire := constantXorGates_wires gate hgate q hq
    rcases hlengths with hbefore | hafter
    · right
      simp [VQ.Euclid.PackedStepLayout.lengthTOffset] at hwire hbefore ⊢
      omega
    · left
      simp [VQ.Euclid.PackedStepLayout.lengthTOffset,
        VQ.Euclid.PackedStepLayout.lengthRPrimeOffset] at hwire hafter ⊢
      omega
  · have hwire := constantXorGates_wires gate hgate q hq
    rcases hlengths with hbefore | hafter
    · right
      simp [VQ.Euclid.PackedStepLayout.lengthTOffset,
        VQ.Euclid.PackedStepLayout.lengthQOffset] at hwire hbefore ⊢
      omega
    · left
      simp [VQ.Euclid.PackedStepLayout.lengthQOffset,
        VQ.Euclid.PackedStepLayout.lengthRPrimeOffset] at hwire hafter ⊢
      omega
  · have hwire := constantXorGates_wires gate hgate q hq
    rcases hlengths with hbefore | hafter
    · right
      simp [VQ.Euclid.PackedStepLayout.lengthTOffset,
        VQ.Euclid.PackedStepLayout.lengthRPrimeOffset] at hwire hbefore ⊢
      omega
    · left
      simp [VQ.Euclid.PackedStepLayout.lengthRPrimeOffset] at hwire hafter ⊢
      omega
  · have hwire := constantXorGates_wires gate hgate q hq
    rcases htarget with hbefore | hafter
    · right
      simp [targetOffset, VQ.Euclid.PackedStepLayout.workOneOffset] at hwire hbefore ⊢
      omega
    · left
      simp [targetOffset, VQ.Euclid.PackedStepLayout.workOneOffset] at hwire hafter ⊢
      omega

theorem terminalGates_correct {I : Nat}
    (hsource : readField I sourceOffset 256 ≤ VQ.Curve.p)
    (htarget : readField I targetOffset 256 = 0)
    (hworkspace : EncodedWorkspace I) :
    actGates VQ.Curve.PackedAffineTerminalProduct.terminalGates I =
      writeField I targetOffset 256
        (readField I multiplierOffset 256 *
          readField I sourceOffset 256 % VQ.Curve.p) := by
  have hsourceMasked : readField (masked I) sourceOffset 256 ≤ VQ.Curve.p := by
    rw [masked_readField (Or.inl (by decide)) (Or.inr (by decide))]
    exact hsource
  have htargetMasked : readField (masked I) targetOffset 256 = 0 := by
    rw [masked_readField (Or.inl (by decide)) (Or.inl (by decide))]
    exact htarget
  have hmultiplierMasked : readField (masked I) multiplierOffset 256 =
      readField I multiplierOffset 256 := by
    exact masked_readField (Or.inr (by decide)) (Or.inr (by decide))
  have hsourceValueMasked : readField (masked I) sourceOffset 256 =
      readField I sourceOffset 256 := by
    exact masked_readField (Or.inl (by decide)) (Or.inr (by decide))
  have hproduct := gates_correct hsourceMasked htargetMasked
    (masked_workspace hworkspace)
  rw [hmultiplierMasked, hsourceValueMasked] at hproduct
  have havoid :
      ∀ gate ∈ VQ.Curve.PackedAffineTerminalProduct.workspaceMaskGates.reverse,
        ∀ q ∈ gate.wires, q < targetOffset ∨ targetOffset + 256 ≤ q := by
    intro gate hgate
    exact VQ.Curve.PackedAffineTerminalProduct.workspaceMaskGates_avoids_target
      gate (List.mem_reverse.mp hgate)
  simp only [VQ.Curve.PackedAffineTerminalProduct.terminalGates,
    actGates_append]
  change actGates VQ.Curve.PackedAffineTerminalProduct.workspaceMaskGates.reverse
      (actGates gates (masked I)) = _
  rw [hproduct, actGates_write_of_outside havoid]
  unfold masked
  rw [actGates_reverse
    VQ.Curve.PackedAffineTerminalProduct.workspaceMaskGates_wellFormed]

theorem terminalGates_reverse_clears {I : Nat}
    (hsource : readField I sourceOffset 256 ≤ VQ.Curve.p)
    (htarget : readField I targetOffset 256 = 0)
    (hworkspace : EncodedWorkspace I) :
    actGates VQ.Curve.PackedAffineTerminalProduct.terminalGates.reverse
        (writeField I targetOffset 256
          (readField I multiplierOffset 256 *
            readField I sourceOffset 256 % VQ.Curve.p)) =
      I := by
  rw [← terminalGates_correct hsource htarget hworkspace]
  exact actGates_reverse
    VQ.Curve.PackedAffineTerminalProduct.terminalGates_wellFormed I

end VQMathlib.Curve.PackedAffineTerminalProduct
