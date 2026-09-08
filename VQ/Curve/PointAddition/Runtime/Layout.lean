import VQ.Curve.ReversibleSpec

namespace VQ.Curve.PointAddition.Runtime

open VQ VQ.Reversible

def n : Nat := 256
def fieldCount : Nat := 38
def field (i : Nat) : Nat := i * n
def flagBase : Nat := fieldCount * n
def flag (i : Nat) : Nat := flagBase + i
def flagCount : Nat := 16
def componentWork : Nat := flagBase + flagCount
def componentWorkLen : Nat := 2573
def width : Nat := componentWork + componentWorkLen

def source : Nat := field 0
def destination : Nat := field 2
def context : Nat := field 4
def scratch : Nat := field 6
def scratchLen : Nat := width - scratch

theorem n_pos : 0 < n := by decide

theorem p_fits : VQ.Curve.p ≤ 2 ^ n := by
  exact Nat.le_of_lt VQ.Reversible.p_lt_two_pow

theorem field_disjoint {i j : Nat} (hij : i ≠ j) :
    field i + n ≤ field j ∨ field j + n ≤ field i := by
  simp only [field, n]
  omega

theorem field_fits {i : Nat} (hi : i < fieldCount) : field i + n ≤ width := by
  simp [fieldCount] at hi
  simp [field, n, fieldCount, width, componentWork, flagBase, flagCount,
    componentWorkLen]
  omega

theorem field_before_flags {i : Nat} (hi : i < fieldCount) :
    field i + n ≤ flagBase := by
  simp [fieldCount] at hi
  simp [field, n, fieldCount, flagBase]
  omega

theorem field_before_flag {i j : Nat} (hi : i < fieldCount) :
    field i + n ≤ flag j := by
  exact Nat.le_trans (field_before_flags hi) (by simp [flag])

theorem flag_fits {i : Nat} (hi : i < flagCount) : flag i < width := by
  simp [flagCount] at hi
  simp [flag, flagBase, fieldCount, n, flagCount, width, componentWork,
    componentWorkLen]
  omega

theorem flag_before_work {i : Nat} (hi : i < flagCount) :
    flag i + 1 ≤ componentWork := by
  simp only [flag, flagBase, componentWork]
  omega

theorem work_fits : componentWork + componentWorkLen = width := rfl

theorem field_before_work {i : Nat} (hi : i < fieldCount) :
    field i + n ≤ componentWork :=
  Nat.le_trans (field_before_flags hi) (by simp [componentWork])

theorem scratch_eq : scratch = 6 * n := rfl

theorem scratch_end : scratch + scratchLen = width := by
  decide

theorem source_destination_disjoint : source + 2 * n ≤ destination := by decide

theorem source_context_disjoint : source + 2 * n ≤ context := by decide

theorem destination_context_disjoint : destination + 2 * n ≤ context := by decide

theorem scratch_after_context : context + 2 * n ≤ scratch := by decide

theorem scratch_zero_field {I i : Nat} (hi : 6 ≤ i) (hj : i < fieldCount)
    (h : readField I scratch scratchLen = 0) : readField I (field i) n = 0 := by
  apply readField_sub_zero (off := scratch) (len := scratchLen)
  · simp [scratch, field, n] at hi ⊢
    omega
  · rw [scratch_end]
    exact field_fits hj
  · exact h

theorem scratch_zero_flag {I i : Nat} (hi : i < flagCount)
    (h : readField I scratch scratchLen = 0) : readField I (flag i) 1 = 0 := by
  apply readField_sub_zero (off := scratch) (len := scratchLen)
  · simp [scratch, flag, flagBase, fieldCount, field, n]
    omega
  · rw [scratch_end]
    have := flag_fits hi
    omega
  · exact h

theorem scratch_zero_componentWork {I : Nat}
    (h : readField I scratch scratchLen = 0) :
    readField I componentWork componentWorkLen = 0 := by
  apply readField_sub_zero (off := scratch) (len := scratchLen)
  · simp [scratch, componentWork, flagBase, fieldCount, field, n, flagCount]
  · rw [scratch_end, work_fits]
    exact Nat.le_refl _
  · exact h

end VQ.Curve.PointAddition.Runtime
