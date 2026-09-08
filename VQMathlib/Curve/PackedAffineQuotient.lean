import VQ.Curve.PackedAffineQuotient
import VQMathlib.Curve.PackedClearTargetProduct

namespace VQMathlib.Curve.PackedAffineQuotient

open VQ
open VQ.Algebra
open VQ.Reversible
open VQ.Semantics
open VQ.Curve.PackedAffineQuotient

def localIndex (I : Nat) : Nat :=
  sourceIndex embedding
    (VQ.Curve.PackedClearTargetProduct.width 256) I

private theorem placeBranch_state {d width ambient : Nat}
    (f : Nat → Nat) (b : Branch d) :
    (placeBranch f width ambient b).state =
      placeVec f width ambient b.state := rfl

structure AuxiliaryClear (I : Nat) : Prop where
  workHigh : readField I
    (VQ.Euclid.PackedStepLayout.workTwoOffset + 256) 3 = 0
  phaseOne : bitValue I VQ.Euclid.PackedStepLayout.phaseOneWire = 0
  phaseTwo : bitValue I VQ.Euclid.PackedStepLayout.phaseTwoWire = 0
  sign : bitValue I VQ.Euclid.PackedStepLayout.signWire = 0

theorem embedding_multiplier {q : Nat} (hq : q < 256) :
    embedding q = multiplierOffset + q := by
  simpa [embedding, localLayout, wiring, Layout.offset, Layout.size,
    multiplierOffset] using
      place_field localLayout wiring 0 q (by decide) hq

theorem embedding_multiplicand {q : Nat} (hq : q < 256) :
    embedding (256 + q) = multiplicandOffset + q := by
  simpa [embedding, localLayout, wiring, Layout.offset, Layout.size,
    multiplicandOffset] using
      place_field localLayout wiring 1 q (by decide) hq

theorem embedding_target {q : Nat} (hq : q < 256) :
    embedding (512 + q) = targetOffset + q := by
  simpa [embedding, localLayout, wiring, Layout.offset, Layout.size,
    targetOffset] using
      place_field localLayout wiring 2 q (by decide) hq

theorem local_multiplier (I : Nat) :
    readField (localIndex I) 0 256 =
      readField I multiplierOffset 256 := by
  apply readField_sourceIndex
  · norm_num [VQ.Curve.PackedClearTargetProduct.width]
  · intro q hq
    simpa using embedding_multiplier hq

theorem local_multiplicand (I : Nat) :
    readField (localIndex I) 256 256 =
      readField I multiplicandOffset 256 := by
  apply readField_sourceIndex
  · norm_num [VQ.Curve.PackedClearTargetProduct.width]
  · intro q hq
    simpa [Nat.add_assoc] using embedding_multiplicand hq

theorem local_target (I : Nat) :
    readField (localIndex I) 512 256 =
      readField I targetOffset 256 := by
  apply readField_sourceIndex
  · norm_num [VQ.Curve.PackedClearTargetProduct.width]
  · intro q hq
    simpa [Nat.add_assoc] using embedding_target hq

private theorem local_auxiliary_bit (I q : Nat) (hq : q < 6) :
    bitValue (localIndex I) (768 + q) =
      bitValue I (embedding (768 + q)) := by
  change bitValue
      (sourceIndex embedding
        (VQ.Curve.PackedClearTargetProduct.width 256) I) (768 + q) = _
  unfold bitValue
  rw [testBit_sourceIndex]
  norm_num [VQ.Curve.PackedClearTargetProduct.width]
  omega

theorem local_auxiliary {I : Nat} (h : AuxiliaryClear I) :
    VQMathlib.Curve.PackedClearTargetProduct.AuxiliaryClear 256
      (localIndex I) := by
  intro q hq
  change bitValue (localIndex I) (768 + q) = 0
  rw [local_auxiliary_bit I q hq]
  interval_cases q
  · simpa [embedding, localLayout, wiring, Layout.offset, Layout.size,
      place, readField_one] using
        readField_sub_zero (i := I)
          (off := VQ.Euclid.PackedStepLayout.workTwoOffset + 256)
          (len := 3)
          (o := VQ.Euclid.PackedStepLayout.workTwoOffset + 256)
          (l := 1)
          (by omega) (by omega) h.workHigh
  · simpa [embedding, localLayout, wiring, Layout.offset, Layout.size,
      place, readField_one] using
        readField_sub_zero (i := I)
          (off := VQ.Euclid.PackedStepLayout.workTwoOffset + 256)
          (len := 3)
          (o := VQ.Euclid.PackedStepLayout.workTwoOffset + 257)
          (l := 1)
          (by omega) (by omega) h.workHigh
  · simpa [embedding, localLayout, wiring, Layout.offset, Layout.size,
      place, readField_one] using
        readField_sub_zero (i := I)
          (off := VQ.Euclid.PackedStepLayout.workTwoOffset + 256)
          (len := 3)
          (o := VQ.Euclid.PackedStepLayout.workTwoOffset + 258)
          (l := 1)
          (by omega) (by omega) h.workHigh
  · simpa [embedding, localLayout, wiring, Layout.offset, Layout.size,
      place] using
      h.phaseOne
  · simpa [embedding, localLayout, wiring, Layout.offset, Layout.size,
      place] using
      h.phaseTwo
  · simpa [embedding, localLayout, wiring, Layout.offset, Layout.size,
      place] using
      h.sign

theorem replaceBits_targetWrite {I value : Nat} :
    replaceBits embedding
        (VQ.Curve.PackedClearTargetProduct.width 256)
        (writeField (localIndex I) 512 256 value) I =
      writeField I targetOffset 256 value := by
  let f := embedding
  let localWidth := VQ.Curve.PackedClearTargetProduct.width 256
  have hinj : ∀ x y, x < localWidth → y < localWidth →
      f x = f y → x = y := by
    intro x y hx hy hxy
    exact embedding_injective hx hy hxy
  have hmap : ∀ q, q < 256 → f (512 + q) = targetOffset + q := by
    intro q hq
    exact embedding_target hq
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases himage : ∃ r, r < localWidth ∧ f r = q
  · obtain ⟨r, hr, rfl⟩ := himage
    rw [testBit_replaceBits hr hinj]
    by_cases htarget : 512 ≤ r ∧ r < 512 + 256
    · let s := r - 512
      have hs : s < 256 := by simp [s]; omega
      have hrs : r = 512 + s := by simp [s]; omega
      rw [testBit_writeField_inside htarget.1 htarget.2, hrs, hmap s hs,
        testBit_writeField_inside (by simp [targetOffset]) (by
          simp [targetOffset]
          omega)]
      simp [targetOffset]
    · have houtside : f r < targetOffset ∨
          targetOffset + 256 ≤ f r := by
        by_contra h
        have hrange : targetOffset ≤ f r ∧
            f r < targetOffset + 256 := by omega
        let s := f r - targetOffset
        have hs : s < 256 := by simp [s]; omega
        have hfs : f (512 + s) = f r := by
          simp [hmap s hs, s]
          omega
        have hrs : r = 512 + s := hinj r (512 + s) hr (by
          simp [localWidth, VQ.Curve.PackedClearTargetProduct.width]
          omega) hfs.symm
        exact htarget (by omega)
      rw [testBit_writeField_outside (by omega)]
      change (sourceIndex embedding
        (VQ.Curve.PackedClearTargetProduct.width 256) I).testBit r = _
      rw [testBit_sourceIndex (by simpa [localWidth] using hr),
        testBit_writeField_outside houtside]
  · rw [testBit_replaceBits_outside (by
        intro r hr heq
        exact himage ⟨r, hr, heq.symm⟩)]
    by_cases hq : targetOffset ≤ q ∧ q < targetOffset + 256
    · let r := q - targetOffset
      have hr : r < 256 := by simp [r]; omega
      exact (himage ⟨512 + r, by
        simp [localWidth, VQ.Curve.PackedClearTargetProduct.width]
        omega, by simp [hmap r hr, r]; omega⟩).elim
    · rw [testBit_writeField_outside (by omega)]

theorem ops_correct
    {level I input : Nat}
    (hl : 3 ≤ level)
    (hmultiplicand : readField I multiplicandOffset 256 ≤ VQ.Curve.p)
    (htarget : readField I targetOffset 256 = 0)
    (hclear : AuxiliaryClear I)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width ops
      (Branch.mk rec creg (basis I) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^
        ((2 * 256 - 1) * (3 * 256 - 1)) •
      basis (writeField I targetOffset 256
        (readField I multiplierOffset 256 *
          readField I multiplicandOffset 256 % VQ.Curve.p)) := by
  let localWidth := VQ.Curve.PackedClearTargetProduct.width 256
  let localOriginal := localIndex I
  have hinj : ∀ x y, x < localWidth → y < localWidth →
      embedding x = embedding y → x = y := by
    intro x y hx hy hxy
    exact embedding_injective hx hy hxy
  have hrun := runOps_relabel
    (level := level) (width := localWidth)
    (totalWidth := VQ.Curve.PackedAffineLayout.width)
    (inputBits := 0) (cbits := 256) (f := embedding) (ambient := I)
    (ops := VQ.Curve.PackedClearTargetProduct.productOps VQ.Curve.p 256)
    (b := Branch.mk rec creg (basis localOriginal) input)
    (fun _ hq => embedding_lt hq) hinj
    (VQ.Curve.PackedClearTargetProduct.productOps_wellFormed hl (by norm_num))
    (wfVec_basis (sourceIndex_lt embedding localWidth I))
  have hstart : placeBranch embedding localWidth I
      (Branch.mk rec creg (basis localOriginal : Vec (deg level)) input) =
      Branch.mk rec creg (basis I) input := by
    exact placeBranch_sourceIndex_basis hinj rec creg input
  rw [hstart] at hrun
  rw [ops, hrun, List.mem_map] at hb
  obtain ⟨localBranch, hlocalBranch, hbranch⟩ := hb
  have hlocalState :=
    VQMathlib.Curve.PackedClearTargetProduct.productOps_modularProduct_correct
      hl (by norm_num) (by exact VQ.Curve.p_pos)
      (by exact VQ.Reversible.p_lt_two_pow) (by native_decide)
      (by
        change readField (localIndex I) 256 256 ≤ VQ.Curve.p
        rw [local_multiplicand]
        exact hmultiplicand)
      (by
        change readField (localIndex I) 512 256 = 0
        rw [local_target]
        exact htarget)
      (local_auxiliary hclear) rec creg hlocalBranch
  have hlocalState' : localBranch.state =
      Algebra.Dy.invSqrt2 (deg level) ^
          ((2 * 256 - 1) * (3 * 256 - 1)) •
        basis (writeField localOriginal 512 256
          (readField I multiplierOffset 256 *
            readField I multiplicandOffset 256 % VQ.Curve.p)) := by
    change localBranch.state =
      Algebra.Dy.invSqrt2 (deg level) ^
          ((2 * 256 - 1) * (3 * 256 - 1)) •
        basis (writeField localOriginal 512 256
          (readField localOriginal 0 256 *
            readField localOriginal 256 256 % VQ.Curve.p)) at hlocalState
    rw [show readField localOriginal 0 256 =
        readField I multiplierOffset 256 by
          simpa only [localOriginal] using local_multiplier I,
      show readField localOriginal 256 256 =
        readField I multiplicandOffset 256 by
          simpa only [localOriginal] using local_multiplicand I] at hlocalState
    exact hlocalState
  have hresultFit : writeField localOriginal 512 256
      (readField I multiplierOffset 256 *
        readField I multiplicandOffset 256 % VQ.Curve.p) < 2 ^ localWidth := by
    apply writeField_lt
    · simp [localWidth, VQ.Curve.PackedClearTargetProduct.width]
    · exact sourceIndex_lt embedding localWidth I
  have hplaced : placeVec embedding localWidth I localBranch.state =
      Algebra.Dy.invSqrt2 (deg level) ^
          ((2 * 256 - 1) * (3 * 256 - 1)) •
        basis (writeField I targetOffset 256
          (readField I multiplierOffset 256 *
            readField I multiplicandOffset 256 % VQ.Curve.p)) := by
    rw [hlocalState', placeVec_smul]
    rw [placeVec_basis hresultFit]
    rw [replaceBits_targetWrite]
  calc
    b.state =
        (placeBranch embedding localWidth I localBranch).state := by
      exact (congrArg Branch.state hbranch).symm
    _ = placeVec embedding localWidth I localBranch.state :=
      placeBranch_state embedding localBranch
    _ = _ := hplaced

end VQMathlib.Curve.PackedAffineQuotient
