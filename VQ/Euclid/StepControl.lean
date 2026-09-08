/-
Coherent negative-literal control used by the Algorithm 3 step.
-/
import VQ.Reversible.Bit

namespace VQ
namespace Euclid
namespace StepControl

open Reversible

def negativeGates (source target : Nat) : List RGate :=
  [.x source, .cx source target, .x source]

def negativeOut (source target i : Nat) : Nat :=
  writeField i target 1
    ((bitValue i target + if bitValue i source = 0 then 1 else 0) % 2)

theorem negative_act {source target i : Nat} (hne : source ≠ target) :
    actGates (negativeGates source target) i =
      negativeOut source target i := by
  let j := writeField i source 1 ((bitValue i source + 1) % 2)
  let k := writeField j target 1
    ((bitValue j target + bitValue j source) % 2)
  have e1 : RGate.act (.x source) i = j := by
    exact act_x_write source i
  have hjs : bitValue j source = (bitValue i source + 1) % 2 := by
    simp only [j]
    rw [bitValue_write_self]
    have hs := bitValue_lt i source
    omega
  have hjt : bitValue j target = bitValue i target := by
    exact bitValue_write_ne (Ne.symm hne)
  have e2 : RGate.act (.cx source target) j = k := by
    simp only [k]
    rw [act_cx_write, hjt, hjs]
  have hks : bitValue k source = bitValue j source := by
    exact bitValue_write_ne hne
  have hrestore : (bitValue j source + 1) % 2 = bitValue i source := by
    rw [hjs]
    have hs := bitValue_lt i source
    omega
  have hvalue :
      (bitValue j target + bitValue j source) % 2 =
        (bitValue i target + if bitValue i source = 0 then 1 else 0) % 2 := by
    rw [hjt, hjs]
    have hs := bitValue_lt i source
    by_cases hzero : bitValue i source = 0
    · simp [hzero]
    · have hone : bitValue i source = 1 := by omega
      simp [hone]
  rw [negativeGates, actGates_cons, actGates_cons, actGates_cons,
    actGates_nil, e1, e2, act_x_write, hks, hrestore]
  simp only [k]
  rw [writeField_comm (by omega)]
  have hjrestore : writeField j source 1 (bitValue i source) = i := by
    simp only [j, writeField_writeField]
    exact write_of_bitValue (by omega)
  rw [hjrestore, negativeOut, hvalue]

theorem negativeOut_target (source target i : Nat) :
    bitValue (negativeOut source target i) target =
      (bitValue i target + if bitValue i source = 0 then 1 else 0) % 2 := by
  simp [negativeOut, bitValue_write_self]

theorem negativeOut_ne {source target i q : Nat} (hne : q ≠ target) :
    bitValue (negativeOut source target i) q = bitValue i q := by
  simp [negativeOut, bitValue_write_ne hne]

theorem negativeGates_wellFormed {source target width : Nat}
    (hs : source < width) (ht : target < width) (hne : source ≠ target) :
    (negativeGates source target).all (RGate.wellFormed width) = true := by
  simp [negativeGates, RGate.wellFormed, hs, ht, hne]

theorem negativeGates_length (source target : Nat) :
    (negativeGates source target).length = 3 := by
  rfl

theorem negativeGates_ccx (source target : Nat) :
    (negativeGates source target).countP RGate.isCcx = 0 := by
  rfl

theorem negativeGates_cx (source target : Nat) :
    (negativeGates source target).countP RGate.isCx = 1 := by
  rfl

end StepControl
end Euclid
end VQ
