/-
One-bit reversible condition helpers for the Euclidean-step scheduler.

The condition flag starts clear, remains coherent, and is erased by running
the same palindromic gate list again after the controlled operation.  Multi-bit
conjunctions use the Boolean blocks proved in `VQ.Euclid.Phase`.
-/
import VQ.Reversible.Bit

namespace VQ
namespace Euclid
namespace Condition

open Reversible

def notGates (source target : Nat) : List RGate :=
  [.x source, .cx source target, .x source]

def notOut (source target i : Nat) : Nat :=
  writeField i target 1
    ((bitValue i target + if bitValue i source = 0 then 1 else 0) % 2)

theorem not_act {source target i : Nat} (hne : source ≠ target) :
    actGates (notGates source target) i = notOut source target i := by
  let j := writeField i source 1 ((bitValue i source + 1) % 2)
  let u := (bitValue i target + bitValue j source) % 2
  let k := writeField j target 1 u
  have e1 : RGate.act (.x source) i = j := by
    simp only [j, act_x_write]
  have hjSource : bitValue j source = ((bitValue i source + 1) % 2) % 2 :=
    bitValue_write_self _ _ _
  have hjTarget : bitValue j target = bitValue i target :=
    bitValue_write_ne (Ne.symm hne)
  have e2 : RGate.act (.cx source target) j = k := by
    simp only [k, u]
    rw [act_cx_write, hjSource, hjTarget]
  have hkSource : bitValue k source = bitValue j source :=
    bitValue_write_ne hne
  have hsource := bitValue_lt i source
  have hrestore : ((((bitValue i source + 1) % 2) % 2 + 1) % 2) =
      bitValue i source := by omega
  have hu : u =
      (bitValue i target + if bitValue i source = 0 then 1 else 0) % 2 := by
    unfold u
    rw [hjSource]
    by_cases hz : bitValue i source = 0
    · simp [hz]
    · have ho : bitValue i source = 1 := by omega
      simp [ho]
  rw [notGates, actGates_cons, actGates_cons, actGates_cons,
    actGates_nil, e1, e2, act_x_write, hkSource, hjSource, hrestore]
  change writeField (writeField j target 1 u) source 1
    (bitValue i source) = _
  rw [writeField_comm (show target + 1 ≤ source ∨
      source + 1 ≤ target by omega)]
  simp only [j, writeField_writeField]
  rw [show writeField i source 1 (bitValue i source) = i by
      exact write_of_bitValue (by omega), notOut, hu]

theorem notOut_target (source target i : Nat) :
    bitValue (notOut source target i) target =
      (bitValue i target + if bitValue i source = 0 then 1 else 0) % 2 := by
  simp [notOut, bitValue_write_self]

theorem notOut_ne {source target i q : Nat} (hne : q ≠ target) :
    bitValue (notOut source target i) q = bitValue i q :=
  bitValue_write_ne hne

theorem not_reverse (source target : Nat) :
    (notGates source target).reverse = notGates source target := by
  simp [notGates]

theorem not_wellFormed {source target width : Nat}
    (hsource : source < width) (htarget : target < width)
    (hne : source ≠ target) :
    (notGates source target).all (RGate.wellFormed width) = true := by
  simp [notGates, RGate.wellFormed, hsource, htarget, hne]

theorem not_length (source target : Nat) :
    (notGates source target).length = 3 := rfl

theorem not_ccx (source target : Nat) :
    (notGates source target).countP RGate.isCcx = 0 := rfl

theorem not_cx (source target : Nat) :
    (notGates source target).countP RGate.isCx = 1 := rfl

end Condition
end Euclid
end VQ
