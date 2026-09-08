import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

namespace VQ.Tests.ECDLPFourierRecovery

def peak (N q t : Nat) : Nat :=
  (2 * N * t + q) / (2 * q)

def decode (q N j : Nat) : Nat :=
  (2 * q * j + N) / (2 * N)

theorem peak_le_center_add_half {N q t : Nat} :
    2 * q * peak N q t ≤ 2 * N * t + q := by
  have h := Nat.div_mul_le_self (2 * N * t + q) (2 * q)
  simpa [peak, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem center_lt_peak_add_half {N q t : Nat} (hq : 0 < q) :
    2 * N * t < 2 * q * peak N q t + q := by
  have hden : 0 < 2 * q := by omega
  have h :
      2 * N * t + q < (peak N q t + 1) * (2 * q) := by
    apply (Nat.div_lt_iff_lt_mul hden).1
    exact Nat.lt_succ_self _
  have h' :
      2 * N * t + q < 2 * q * peak N q t + 2 * q := by
    calc
      2 * N * t + q < (peak N q t + 1) * (2 * q) := h
      _ = 2 * q * peak N q t + 2 * q := by ring
  omega

theorem peak_distance {N q t : Nat} (hq : 0 < q) :
    2 * q * peak N q t ≤ 2 * N * t + q ∧
      2 * N * t ≤ 2 * q * peak N q t + q :=
  ⟨peak_le_center_add_half, (center_lt_peak_add_half hq).le⟩

theorem peak_lt {N q t : Nat} (hq : 0 < q) (hqN : q ≤ N) (ht : t < q) :
    peak N q t < N := by
  have hden : 0 < 2 * q := by omega
  apply (Nat.div_lt_iff_lt_mul hden).2
  have hN : 0 < N := hq.trans_le hqN
  have hqTwoN : q < 2 * N := by omega
  have hstep : N * (t + 1) ≤ N * q :=
    Nat.mul_le_mul_left N (Nat.succ_le_of_lt ht)
  calc
    2 * N * t + q = 2 * (N * t) + q := by ring
    _ < 2 * (N * t) + 2 * N := Nat.add_lt_add_left hqTwoN _
    _ = 2 * (N * (t + 1)) := by ring
    _ ≤ 2 * (N * q) := Nat.mul_le_mul_left 2 hstep
    _ = N * (2 * q) := by ring

theorem peak_self {N t : Nat} (hN : 0 < N) :
    peak N N t = t := by
  unfold peak
  apply Nat.div_eq_of_lt_le
  · calc
      t * (2 * N) = 2 * N * t := by ring
      _ ≤ 2 * N * t + N := Nat.le_add_right _ _
  · calc
      2 * N * t + N < 2 * N * t + 2 * N := by omega
      _ = (t + 1) * (2 * N) := by ring

theorem decode_self {N j : Nat} (hN : 0 < N) :
    decode N N j = j := by
  simpa [decode, peak] using peak_self (N := N) (t := j) hN

theorem decode_le {q N j : Nat} (hq : 0 < q) (hqN : q ≤ N) (hj : j < N) :
    decode q N j ≤ q := by
  have hN : 0 < N := hq.trans_le hqN
  have hden : 0 < 2 * N := by omega
  rw [← Nat.lt_succ_iff]
  apply (Nat.div_lt_iff_lt_mul hden).2
  have hqj : q * j < q * N := (Nat.mul_lt_mul_left hq).2 hj
  have hscaled : 2 * (q * j) < 2 * (q * N) :=
    (Nat.mul_lt_mul_left (by omega)).2 hqj
  calc
    2 * q * j + N = 2 * (q * j) + N := by ring
    _ < 2 * (q * N) + N := Nat.add_lt_add_right hscaled N
    _ < 2 * (q * N) + 2 * N := by omega
    _ = (q + 1) * (2 * N) := by ring

theorem decode_peak {N q t : Nat} (hq : 0 < q) (hqN : q ≤ N) :
    decode q N (peak N q t) = t := by
  by_cases hEq : q = N
  · subst N
    rw [peak_self (N := q) (t := t) hq,
      decode_self (N := q) (j := t) hq]
  · have hqLtN : q < N := lt_of_le_of_ne hqN hEq
    have hUpper := peak_le_center_add_half (N := N) (q := q) (t := t)
    have hLower := center_lt_peak_add_half (N := N) (q := q) (t := t) hq
    unfold decode
    apply Nat.div_eq_of_lt_le
    · calc
        t * (2 * N) = 2 * N * t := by ring
        _ ≤ 2 * q * peak N q t + q := Nat.le_of_lt hLower
        _ ≤ 2 * q * peak N q t + N := Nat.add_le_add_left hqN _
    · have hqAddN : q + N < 2 * N := by omega
      calc
        2 * q * peak N q t + N ≤ 2 * N * t + q + N :=
          Nat.add_le_add_right hUpper N
        _ = 2 * N * t + (q + N) := by omega
        _ < 2 * N * t + 2 * N := Nat.add_lt_add_left hqAddN _
        _ = (t + 1) * (2 * N) := by ring

theorem decode_peak_lt {N q t : Nat}
    (hq : 0 < q) (hqN : q ≤ N) (ht : t < q) :
    decode q N (peak N q t) < q := by
  rw [decode_peak hq hqN]
  exact ht

theorem peak_injective {N q : Nat} (hq : 0 < q) (hqN : q ≤ N) :
    Function.Injective (fun t : Fin q => peak N q t.val) := by
  intro a b hab
  apply Fin.ext
  calc
    a.val = decode q N (peak N q a.val) := (decode_peak hq hqN).symm
    _ = decode q N (peak N q b.val) := congrArg (decode q N) hab
    _ = b.val := decode_peak hq hqN

def peakIndex (N q : Nat) (hq : 0 < q) (hqN : q ≤ N) (t : Fin q) : Fin N :=
  ⟨peak N q t.val, peak_lt hq hqN t.isLt⟩

theorem peakIndex_injective {N q : Nat} (hq : 0 < q) (hqN : q ≤ N) :
    Function.Injective (peakIndex N q hq hqN) := by
  intro a b hab
  apply peak_injective hq hqN
  exact congrArg Fin.val hab

/-- info: 'VQ.Tests.ECDLPFourierRecovery.decode_peak' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decode_peak

/-- info: 'VQ.Tests.ECDLPFourierRecovery.peakIndex_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms peakIndex_injective

end VQ.Tests.ECDLPFourierRecovery
