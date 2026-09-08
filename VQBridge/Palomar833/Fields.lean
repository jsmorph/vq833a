import VQBridge.Palomar833.Execution
import VQBridge.Palomar833.Specification

namespace Palomar833.Connection

open VQ.Reversible

theorem source_branch {d : Nat}
    {bs : List (VQ.Semantics.Branch d)} {cs : List Palomar833.Branch}
    (h : List.Forall₂ Related bs cs) {c : Palomar833.Branch} (hc : c ∈ cs) :
    ∃ b ∈ bs, Related b c := by
  induction h with
  | nil => cases hc
  | @cons b c' bs cs hbc _ ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨b, List.mem_cons_self, hbc⟩
      · obtain ⟨b', hb', hrel⟩ := ih hc
        exact ⟨b', List.mem_cons_of_mem _ hb', hrel⟩

theorem field_eq_of_bits {storage offset width value : Nat}
    (hv : value < 2 ^ width)
    (hbits : ∀ bit, bit < width →
      storage.testBit (offset + bit) = value.testBit bit) :
    readField storage offset width = value := by
  apply Nat.eq_of_testBit_eq
  intro bit
  rw [testBit_readField]
  by_cases hb : bit < width
  · simp only [hb, decide_true, Bool.true_and]
    exact hbits bit hb
  · have hpow : 2 ^ width ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by decide) (by omega)
    simp only [hb, decide_false, Bool.false_and,
      Nat.testBit_eq_false_of_lt (hv.trans_le hpow)]

theorem outcome_first {b : Palomar833.Branch} {value : Nat}
    (hv : value < N)
    (hbits : ∀ bit, bit < 256 → b.storage.testBit (256 + bit) = value.testBit bit) :
    (outcome b).1.val = value := by
  simpa only [outcome, N, readField, Nat.shiftRight_eq_div_pow] using
    field_eq_of_bits hv hbits

theorem outcome_second {b : Palomar833.Branch} {value : Nat}
    (hv : value < N)
    (hbits : ∀ bit, bit < 256 → b.storage.testBit (512 + bit) = value.testBit bit) :
    (outcome b).2.val = value := by
  have hN : N ^ 2 = 2 ^ (256 * 2) := (pow_mul (2 : Nat) 256 2).symm
  change (b.storage / N ^ 2) % N = value
  rw [hN]
  simpa only [N, readField, Nat.shiftRight_eq_div_pow] using
    field_eq_of_bits hv hbits

end Palomar833.Connection
