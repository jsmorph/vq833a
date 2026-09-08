/-
The baseline point-addition circuit followed by the verified transposition
implements addition in the full secp256k1 point group.
-/
import VQMathlib.Curve.GroupTotalPointAddition.Transpose
import VQMathlib.Curve.GroupTotal

namespace VQ.Tests.GroupTotalPointAddition

open VQ.Curve.PointAddition

open VQ VQ.Reversible
open VQ.Curve.PointAddition.Runtime
open Arithmetic.Inv.Add

def GroupValid (target offset : Nat) : Prop :=
  Curve.GroupRepresentable (pointX target) (pointY target) = true ∧
    Curve.GroupRepresentable (pointX offset) (pointY offset) = true

def groupAddValue (target offset : Nat) : Nat :=
  let result := Curve.groupAdd (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  packPoint result.1 result.2

def groupPointAddGates : List RGate := pointAddGates ++ transposeGates

def groupPointAddCircuit : RCircuit :=
  { width := width, gates := groupPointAddGates }

theorem groupPointAddCircuit_gates :
    groupPointAddCircuit.gates = groupPointAddGates := rfl

theorem GroupValid.valid {target offset : Nat} (h : GroupValid target offset) :
    Valid target offset := by
  exact ⟨Curve.representable_of_groupRepresentable h.1,
    Curve.representable_of_groupRepresentable h.2⟩

theorem packPoint_injective_of_fits {x₁ y₁ x₂ y₂ : Nat}
    (hx₁ : x₁ < 2 ^ n) (hy₁ : y₁ < 2 ^ n)
    (hx₂ : x₂ < 2 ^ n) (hy₂ : y₂ < 2 ^ n)
    (h : packPoint x₁ y₁ = packPoint x₂ y₂) :
    (x₁, y₁) = (x₂, y₂) := by
  apply Prod.ext
  · have hx := congrArg pointX h
    simpa [pointX_packPoint hx₁, pointX_packPoint hx₂] using hx
  · have hy := congrArg pointY h
    simpa [pointY_packPoint hx₁ hy₁, pointY_packPoint hx₂ hy₂] using hy

set_option exponentiation.threshold 512 in
theorem transposeValue_addValue {target offset : Nat}
    (h : GroupValid target offset) (hoffset : offset < 2 ^ pointWidth) :
    transposeValue (addValue target offset) offset =
      groupAddValue target offset := by
  let totalResult := Curve.totalAdd (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  let groupResult := Curve.groupAdd (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  have hvalid := h.valid
  have htotalRepresentable :
      Curve.Representable totalResult.1 totalResult.2 = true :=
    Curve.representable_totalAdd hvalid.1 hvalid.2
  have htotalFits := representable_fits htotalRepresentable
  have hoffsetFits := representable_fits hvalid.2
  have hoffsetPack : packPoint (pointX offset) (pointY offset) = offset :=
    packPoint_pointX_pointY hoffset
  have hswap : Curve.swapInfinityOffset totalResult
      (pointX offset, pointY offset) = groupResult := by
    exact VQBridge.Curve.swapInfinityOffset_totalAdd h.1 h.2
  change transposeValue (packPoint totalResult.1 totalResult.2) offset =
    packPoint groupResult.1 groupResult.2
  rw [transposeValue_cases]
  cases hi : Curve.IsInfinity totalResult.1 totalResult.2 with
  | true =>
      have hzero := Curve.isInfinity_iff.mp hi
      have htotalZero : totalResult = (0, 0) := Prod.ext hzero.1 hzero.2
      have hpackZero : packPoint totalResult.1 totalResult.2 = 0 := by
        simp [htotalZero, packPoint]
      have hgroup : groupResult = (pointX offset, pointY offset) := by
        simpa [Curve.swapInfinityOffset, hi] using hswap.symm
      rw [if_pos hpackZero, hgroup, hoffsetPack]
  | false =>
      have hpackNonzero : packPoint totalResult.1 totalResult.2 ≠ 0 := by
        intro hzero
        have hp : totalResult = (0, 0) := by
          apply packPoint_injective_of_fits htotalFits.1 htotalFits.2
            (Nat.two_pow_pos n) (Nat.two_pow_pos n)
          simpa [packPoint] using hzero
        have : Curve.IsInfinity totalResult.1 totalResult.2 = true := by
          simp [hp, Curve.IsInfinity]
        rw [hi] at this
        exact Bool.false_ne_true this
      rw [if_neg hpackNonzero]
      by_cases heq : totalResult = (pointX offset, pointY offset)
      · have hpackEq : packPoint totalResult.1 totalResult.2 = offset := by
          rw [heq, hoffsetPack]
        have hioffset : Curve.IsInfinity (pointX offset) (pointY offset) = false := by
          simpa [heq] using hi
        have hgroup : groupResult = (0, 0) := by
          simpa [Curve.swapInfinityOffset, hi, heq, hioffset] using hswap.symm
        rw [if_pos hpackEq, hgroup]
        rfl
      · have hpackNe : packPoint totalResult.1 totalResult.2 ≠ offset := by
          intro hpack
          apply heq
          apply packPoint_injective_of_fits htotalFits.1 htotalFits.2
            hoffsetFits.1 hoffsetFits.2
          simpa [hoffsetPack] using hpack
        have hgroup : groupResult = totalResult := by
          simpa [Curve.swapInfinityOffset, hi, heq] using hswap.symm
        rw [if_neg hpackNe, hgroup]

theorem groupAddValue_representable {target offset : Nat}
    (h : GroupValid target offset) :
    Curve.Representable (pointX (groupAddValue target offset))
      (pointY (groupAddValue target offset)) = true := by
  let result := Curve.groupAdd (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  have hgroup : Curve.GroupRepresentable result.1 result.2 = true :=
    VQBridge.Curve.groupRepresentable_groupAdd h.1 h.2
  have hrepresentable := Curve.representable_of_groupRepresentable hgroup
  have hfits := representable_fits hrepresentable
  change Curve.Representable (pointX (packPoint result.1 result.2))
    (pointY (packPoint result.1 result.2)) = true
  rw [pointX_packPoint hfits.1, pointY_packPoint hfits.1 hfits.2]
  exact hrepresentable

theorem groupAddValue_groupRepresentable {target offset : Nat}
    (h : GroupValid target offset) :
    Curve.GroupRepresentable (pointX (groupAddValue target offset))
      (pointY (groupAddValue target offset)) = true := by
  let result := Curve.groupAdd (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  have hgroup : Curve.GroupRepresentable result.1 result.2 = true :=
    VQBridge.Curve.groupRepresentable_groupAdd h.1 h.2
  have hfits := representable_fits (Curve.representable_of_groupRepresentable hgroup)
  change Curve.GroupRepresentable (pointX (packPoint result.1 result.2))
    (pointY (packPoint result.1 result.2)) = true
  rw [pointX_packPoint hfits.1, pointY_packPoint hfits.1 hfits.2]
  exact hgroup

set_option exponentiation.threshold 512 in
theorem groupAddValue_lt {target offset : Nat} (h : GroupValid target offset) :
    groupAddValue target offset < 2 ^ pointWidth := by
  let result := Curve.groupAdd (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  have hgroup : Curve.GroupRepresentable result.1 result.2 = true :=
    VQBridge.Curve.groupRepresentable_groupAdd h.1 h.2
  have hrepresentable := Curve.representable_of_groupRepresentable hgroup
  have hfits := representable_fits hrepresentable
  exact packPoint_lt hfits.1 hfits.2

theorem pointX_groupAddValue {target offset : Nat} (h : GroupValid target offset) :
    pointX (groupAddValue target offset) =
      (Curve.groupAdd (pointX target) (pointY target)
        (pointX offset) (pointY offset)).1 := by
  let result := Curve.groupAdd (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  have hgroup : Curve.GroupRepresentable result.1 result.2 = true :=
    VQBridge.Curve.groupRepresentable_groupAdd h.1 h.2
  have hfits := representable_fits (Curve.representable_of_groupRepresentable hgroup)
  exact pointX_packPoint hfits.1

theorem pointY_groupAddValue {target offset : Nat} (h : GroupValid target offset) :
    pointY (groupAddValue target offset) =
      (Curve.groupAdd (pointX target) (pointY target)
        (pointX offset) (pointY offset)).2 := by
  let result := Curve.groupAdd (pointX target) (pointY target)
    (pointX offset) (pointY offset)
  have hgroup : Curve.GroupRepresentable result.1 result.2 = true :=
    VQBridge.Curve.groupRepresentable_groupAdd h.1 h.2
  have hfits := representable_fits (Curve.representable_of_groupRepresentable hgroup)
  exact pointY_packPoint hfits.1 hfits.2

theorem groupPoint_groupAddValue {target offset : Nat}
    (h : GroupValid target offset) :
    VQBridge.Curve.groupPoint (pointX (groupAddValue target offset))
        (pointY (groupAddValue target offset)) =
      VQBridge.Curve.groupPoint (pointX target) (pointY target) +
        VQBridge.Curve.groupPoint (pointX offset) (pointY offset) := by
  rw [pointX_groupAddValue h, pointY_groupAddValue h]
  exact VQBridge.Curve.groupPoint_groupAdd h.1 h.2

theorem groupPointAddCircuit_wf : groupPointAddCircuit.wellFormed = true := by
  simp only [groupPointAddCircuit, RCircuit.wellFormed, groupPointAddGates,
    List.all_append, Bool.and_eq_true]
  exact ⟨pointAddCircuit_wf, transposeGates_wf⟩

theorem act_groupPointAddGates {I : Nat}
    (hvalid : GroupValid (readField I source pointWidth)
      (readField I context pointWidth))
    (hdestination : readField I destination pointWidth = 0)
    (hwork : readField I scratch scratchLen = 0) :
    actGates groupPointAddGates I =
      writeField
        (writeField I source pointWidth
          (groupAddValue (readField I source pointWidth)
            (readField I context pointWidth)))
        destination pointWidth 0 := by
  let target := readField I source pointWidth
  let offset := readField I context pointWidth
  let J := writeField
    (writeField I source pointWidth (addValue target offset))
    destination pointWidth 0
  have hbaseline : actGates pointAddGates I = J := by
    exact act_pointAddGates hvalid.valid hdestination hwork
  have hIdifference : readField I transposeDifference pointWidth = 0 := by
    exact readField_sub_zero (off := scratch) (len := scratchLen)
      (o := transposeDifference) (l := pointWidth) (by decide) (by decide) hwork
  have hIscratch : readField I transposeScratch pointWidth = 0 := by
    exact readField_sub_zero (off := scratch) (len := scratchLen)
      (o := transposeScratch) (l := pointWidth) (by decide) (by decide) hwork
  have hIflag : bv I transposeFlag = 0 := by
    rw [← Arithmetic.Inv.Add.readField_one]
    exact scratch_zero_flag (by decide) hwork
  have hJdestination : readField J destination pointWidth = 0 := by
    dsimp [J]
    exact readField_writeField_self (Nat.two_pow_pos pointWidth)
  have hJdifference : readField J transposeDifference pointWidth = 0 := by
    dsimp [J]
    rw [readField_writeField_of_disjoint (by left; decide),
      readField_writeField_of_disjoint (by left; decide), hIdifference]
  have hJscratch : readField J transposeScratch pointWidth = 0 := by
    dsimp [J]
    rw [readField_writeField_of_disjoint (by left; decide),
      readField_writeField_of_disjoint (by left; decide), hIscratch]
  have hJflag : bv J transposeFlag = 0 := by
    dsimp [J]
    rw [bv_write_out (by right; decide), bv_write_out (by right; decide), hIflag]
  have hJsource : readField J source pointWidth = addValue target offset := by
    dsimp [J]
    rw [readField_writeField_of_disjoint (by right; decide),
      readField_writeField_self (addValue_lt hvalid.valid)]
  have hJoffset : readField J context pointWidth = offset := by
    dsimp [J, offset]
    rw [readField_writeField_of_disjoint (by left; decide),
      readField_writeField_of_disjoint (by left; decide)]
  have htranspose := transposeGates_act hJdestination hJdifference hJscratch hJflag
  rw [hJsource, hJoffset] at htranspose
  rw [groupPointAddGates, actGates_append, hbaseline, htranspose,
    transposeValue_addValue hvalid (readField_lt I context pointWidth)]
  dsimp [J, target, offset]
  rw [writeField_comm (by decide), writeField_writeField]

end VQ.Tests.GroupTotalPointAddition
