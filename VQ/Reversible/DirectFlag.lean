import VQ.Reversible.BorrowedEquivalence
import VQ.Reversible.Control

namespace VQ.Reversible.DirectFlag

def copy (compute : List RGate) (source target : Nat) : List RGate :=
  compute ++ [.cx source target] ++ compute.reverse

theorem copy_act {compute : List RGate} {w source target : Nat}
    (hw : compute.all (RGate.wellFormed w) = true)
    (ht : ∀ g ∈ compute, target ∉ g.wires) (I : Nat) :
    actGates (copy compute source target) I =
      writeField I target 1
        ((bitValue I target + bitValue (actGates compute I) source) % 2) := by
  have ho : ∀ g ∈ compute, ∀ k ∈ g.wires, k < target ∨ target + 1 ≤ k := by
    intro g hg k hk
    have : k ≠ target := by intro he; subst k; exact ht g hg hk
    omega
  have he := actGates_compute_use_uncompute hw ho
    (cp := [.cx source target])
    (fun J => by rw [actGates_cons, actGates_nil, act_cx_write]) I
  have hb : bitValue (actGates compute I) target = bitValue I target := by
    rw [← readField_one, ← readField_one]
    exact readField_actGates_of_outside ho I
  rw [hb] at he
  exact he

theorem copy_wellFormed {compute : List RGate} {w source target : Nat}
    (hw : compute.all (RGate.wellFormed w) = true)
    (hs : source < w) (ht : target < w) (hne : source ≠ target) :
    (copy compute source target).all (RGate.wellFormed w) = true := by
  simp [copy, hw, RGate.wellFormed, hs, ht, hne]

theorem copy_avoids {compute : List RGate} {q source target : Nat}
    (hq : ∀ g ∈ compute, q ∉ g.wires) (hs : source ≠ q) (ht : target ≠ q) :
    ∀ g ∈ copy compute source target, q ∉ g.wires := by
  intro g hg
  simp only [copy, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_reverse] at hg
  rcases hg with (hg | rfl) | hg
  · exact hq g hg
  · simp [RGate.wires, Ne.symm hs, Ne.symm ht]
  · exact hq g hg

theorem equivalent {compute : List RGate} {w source flag target : Nat}
    (hw : compute.all (RGate.wellFormed w) = true)
    (hs : source < w) (hf : flag < w)
    (hsf : source ≠ flag) (hst : source ≠ target) (hft : flag ≠ target)
    (haf : ∀ g ∈ compute, flag ∉ g.wires)
    (hat : ∀ g ∈ compute, target ∉ g.wires) :
    BorrowedEquivalent flag (copy (copy compute source flag) flag target)
      (copy compute source target) := by
  have hinner := copy_wellFormed hw hs hf hsf
  have hinnerAvoid := copy_avoids hat hst hft
  constructor
  · intro I
    rw [copy_act hw hat, copy_act hinner hinnerAvoid, copy_act hw haf,
      bitValue_write_self]
    have hc : bitValue (writeField I flag 1 0) flag = 0 := by
      rw [bitValue_write_self]
    have htf : bitValue (writeField I flag 1 0) target = bitValue I target :=
      bitValue_write_ne (Ne.symm hft)
    have he : actGates compute (writeField I flag 1 0) =
        writeField (actGates compute I) flag 1 0 := by
      apply actGates_write_of_outside
      intro g hg k hk
      have : k ≠ flag := by intro he; subst k; exact haf g hg hk
      omega
    rw [hc, htf, he, bitValue_write_ne hsf, Nat.zero_add,
      Nat.mod_eq_of_lt (bitValue_lt (actGates compute I) source),
      Nat.mod_eq_of_lt (bitValue_lt (actGates compute I) source)]
    exact writeField_comm (by omega)
  · exact testBit_actGates_of_outside (copy_avoids haf hsf (Ne.symm hft))

end VQ.Reversible.DirectFlag
