import VQMathlib.Euclid.LengthWriterCounts

namespace VQMathlib.Euclid.LengthWriterBitCounts

open VQ VQ.Euclid VQ.Reversible
open VQMathlib.Euclid.LengthWriterCounts

set_option maxRecDepth 4096 in
private theorem incrementBits : ∀ i : Fin 259,
    selectedBits 9 ((i.val + 1) ^^^ i.val) + selectedBits 9 (i.val + 1) =
      2 + selectedBits 9 i.val := by
  decide +kernel

theorem increment_bits {i : Nat} (hi : i < 259) :
    selectedBits 9 ((i + 1) ^^^ i) + selectedBits 9 (i + 1) =
      2 + selectedBits 9 i :=
  incrementBits ⟨i, hi⟩

private theorem lowerNode_eq {w j : Nat} (hw : w < 259) (hj : j ≤ w) :
    LengthWriter.lowerNode 256 (259 - w) (w + 1) 9 j = w - j := by
  rw [LengthWriter.lowerNode, if_pos (by omega)]
  simp only [LengthWriter.lowerValue, readField_zero]
  rw [show 256 + 3 - (259 - w + j) = w - j by omega]
  exact Nat.mod_eq_of_lt (by omega)

private theorem lower_delta {w j : Nat} (hw : w < 259) (hj : j < w) :
    LengthWriter.lowerDelta 256 (259 - w) (w + 1) 9 j =
      ((w - (j + 1) + 1) ^^^ (w - (j + 1))) := by
  unfold LengthWriter.lowerDelta
  rw [lowerNode_eq hw (by omega), lowerNode_eq hw (by omega)]
  rw [show w - j = w - (j + 1) + 1 by omega]

private theorem lower_partial {w count : Nat}
    (hw : w < 259) (hc : count ≤ w) :
    dirtyCount (LengthWriter.lowerDelta 256 (259 - w) (w + 1) 9) 9 count +
        selectedBits 9 w =
      2 * count + selectedBits 9 (w - count) := by
  induction count with
  | zero => simp [dirtyCount]
  | succ count ih =>
    have hprev := ih (by omega)
    have hbit := increment_bits (i := w - (count + 1)) (by omega)
    rw [show w - (count + 1) + 1 = w - count by omega] at hbit
    rw [dirtyCount, lower_delta hw (by omega)]
    rw [show w - (count + 1) + 1 = w - count by omega]
    omega

theorem lower_dirtyCount {w : Nat} (hw : w < 259) :
    dirtyCount (LengthWriter.lowerDelta 256 (259 - w) (w + 1) 9) 9 (w + 1) +
        selectedBits 9 w =
      9 + 2 * w := by
  have hpartial := lower_partial hw (Nat.le_refl w)
  have hlast : LengthWriter.lowerDelta 256 (259 - w) (w + 1) 9 w = 511 := by
    unfold LengthWriter.lowerDelta
    rw [lowerNode_eq hw (Nat.le_refl w)]
    simp [LengthWriter.lowerNode, Euclid.encodedZero]
  rw [dirtyCount, hlast]
  have hzero : selectedBits 9 0 = 0 := by decide
  have hall : selectedBits 9 511 = 9 := by decide
  rw [Nat.sub_self, hzero] at hpartial
  rw [hall]
  omega

private theorem upper_delta {j : Nat} (hj : j < 259) :
    LengthWriter.upperDelta 1 9 (j + 1) = ((j + 1) ^^^ j) := by
  rw [LengthWriter.upperDelta, LengthWriter.upperChainPosition,
    LengthWriter.upperChainPosition]
  unfold LengthWriter.encodedPosition
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [Nat.add_sub_cancel_left, readField_zero]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem upper_dirtyCount {w : Nat} (hw : w < 259) :
    dirtyCount (LengthWriter.upperDelta 1 9) 9 (w + 1) + selectedBits 9 w =
      9 + 2 * w := by
  induction w with
  | zero => decide
  | succ w ih =>
    have hprev := ih (by omega)
    have hbit := increment_bits (i := w) (by omega)
    rw [dirtyCount, upper_delta (by omega)]
    omega

def dirtyCountFormula (width : Nat) : Nat :=
  if width = 0 then 0 else 9 + 2 * (width - 1) - selectedBits 9 (width - 1)

theorem upper_dirtyCount_eq {width : Nat} (hw : width ≤ 259) :
    dirtyCount (LengthWriter.upperDelta 1 9) 9 width =
      dirtyCountFormula width := by
  by_cases hzero : width = 0
  · simp [hzero, dirtyCountFormula, dirtyCount]
  · have h := upper_dirtyCount (w := width - 1) (by omega)
    rw [show width - 1 + 1 = width by omega] at h
    simp only [dirtyCountFormula, if_neg hzero]
    omega

theorem lower_dirtyCount_eq (source : Nat) :
    dirtyCount (LengthWriter.lowerDelta 256 (source + 1) (259 - source) 9)
      9 (259 - source) = dirtyCountFormula (259 - source) := by
  by_cases hzero : 259 - source = 0
  · simp [hzero, dirtyCountFormula, dirtyCount]
  · have h := lower_dirtyCount (w := 259 - source - 1) (by omega)
    rw [show 259 - source - 1 + 1 = 259 - source by omega,
      show 259 - (259 - source - 1) = source + 1 by omega] at h
    simp only [dirtyCountFormula, if_neg hzero]
    omega

end VQMathlib.Euclid.LengthWriterBitCounts
