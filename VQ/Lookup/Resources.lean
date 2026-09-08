import VQ.Lookup.Core

namespace VQ.Lookup3

open Reversible

theorem maskBit_ccx (row q : Nat) :
    (maskBit row q).countP RGate.isCcx = 0 := by
  simp [maskBit, RGate.isCcx]

theorem masks_ccx (row : Nat) : (masks row).countP RGate.isCcx = 0 := by
  simp [masks, List.countP_append, maskBit_ccx]

theorem compute_ccx (m row : Nat) :
    (compute m row).countP RGate.isCcx = 2 := by
  simp [compute, List.countP_cons, List.countP_append, masks_ccx, RGate.isCcx]

theorem wordXorsAux_ccx (m word q len : Nat) :
    (wordXorsAux m word q len).countP RGate.isCcx = 0 := by
  induction len generalizing q with
  | zero => rfl
  | succ len ih =>
    simp [wordXorsAux, List.countP_append, RGate.isCcx, ih]

theorem wordXors_ccx (m word : Nat) :
    (wordXors m word).countP RGate.isCcx = 0 :=
  wordXorsAux_ccx m word 0 m

theorem rowLookup_ccx (m row word : Nat) :
    (rowLookup m row word).countP RGate.isCcx = 4 := by
  simp [rowLookup, List.countP_append, compute_ccx, wordXors_ccx]

theorem lookupRows_ccx (table : List Nat) (m : Nat) : ∀ start count,
    (lookupRows table m start count).countP RGate.isCcx = 4 * count := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [lookupRows, List.countP_append, rowLookup_ccx, ih]
    omega

theorem lookupGates_ccx (table : List Nat) (m : Nat) :
    (lookupGates table m).countP RGate.isCcx = 32 := by
  rw [lookupGates, lookupRows_ccx]
  rfl

theorem maskBit_length_le (row q : Nat) : (maskBit row q).length ≤ 1 := by
  by_cases h : row.testBit q = true <;> simp [maskBit, h]

theorem masks_length_le (row : Nat) : (masks row).length ≤ 3 := by
  simp only [masks, List.length_append]
  have h0 := maskBit_length_le row 0
  have h1 := maskBit_length_le row 1
  have h2 := maskBit_length_le row 2
  omega

theorem compute_length_le (m row : Nat) : (compute m row).length ≤ 5 := by
  simp [compute]
  exact masks_length_le row

theorem wordXorsAux_length_le (m word : Nat) : ∀ q len,
    (wordXorsAux m word q len).length ≤ len := by
  intro q len
  induction len generalizing q with
  | zero => simp [wordXorsAux]
  | succ len ih =>
    rw [wordXorsAux, List.length_append]
    have hh :
        (if word.testBit q then
          [RGate.cx (flagWire m) (outputOffset + q)] else []).length ≤ 1 := by
      split <;> simp
    have ht := ih (q + 1)
    omega

theorem wordXors_length_le (m word : Nat) : (wordXors m word).length ≤ m :=
  wordXorsAux_length_le m word 0 m

theorem rowLookup_length_le (m row word : Nat) :
    (rowLookup m row word).length ≤ 10 + m := by
  simp [rowLookup]
  have hc := compute_length_le m row
  have hw := wordXors_length_le m word
  omega

theorem lookupRows_length_le (table : List Nat) (m : Nat) : ∀ start count,
    (lookupRows table m start count).length ≤ count * (10 + m) := by
  intro start count
  induction count generalizing start with
  | zero => simp [lookupRows]
  | succ count ih =>
    rw [lookupRows, List.length_append, Nat.succ_mul]
    have hr := rowLookup_length_le m start (value table m start)
    have ht := ih (start + 1)
    omega

theorem lookupGates_length_le (table : List Nat) (m : Nat) :
    (lookupGates table m).length ≤ 80 + 8 * m := by
  unfold lookupGates
  change (lookupRows table m 0 8).length ≤ 80 + 8 * m
  have h := lookupRows_length_le table m 0 8
  have heq : 8 * (10 + m) = 80 + 8 * m := by omega
  calc
    (lookupRows table m 0 8).length ≤ 8 * (10 + m) := h
    _ = 80 + 8 * m := heq

end VQ.Lookup3
