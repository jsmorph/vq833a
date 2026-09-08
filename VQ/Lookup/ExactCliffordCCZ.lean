import VQ.Lookup.Unlookup
import VQ.Program.ExactCliffordCCZ

namespace VQ
namespace Lookup3

open Algebra Reversible Semantics

theorem gateOps_allowed (gates : List RGate) :
    Program.ExactCliffordCCZ.opsAllowed (gateOps gates) = true := by
  simpa [gateOps] using
    Program.ExactCliffordCCZ.compileGates_allowed gates

theorem phaseRowOps_allowed (m row : Nat) :
    Program.ExactCliffordCCZ.opsAllowed (phaseRowOps m row) = true := by
  rw [phaseRowOps, Program.ExactCliffordCCZ.opsAllowed_append,
    Program.ExactCliffordCCZ.opsAllowed_append, gateOps_allowed,
    gateOps_allowed]
  rfl

theorem phaseRows_allowed (table : List Nat) (m bit : Nat) : ∀ start count,
    Program.ExactCliffordCCZ.opsAllowed
      (phaseRows table m bit start count) = true := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [phaseRows, Program.ExactCliffordCCZ.opsAllowed_append]
    by_cases hb : (value table m start).testBit bit = true
    · rw [if_pos hb, phaseRowOps_allowed, ih]
      rfl
    · rw [if_neg hb, ih]
      rfl

theorem phaseForBit_allowed (table : List Nat) (m bit : Nat) :
    Program.ExactCliffordCCZ.opsAllowed
      (phaseForBit table m bit) = true :=
  phaseRows_allowed table m bit 0 (2 ^ addressWidth)

theorem unlookupBit_allowed (table : List Nat) (m bit : Nat) :
    Program.ExactCliffordCCZ.opsAllowed
      (unlookupBit table m bit) = true := by
  simp only [unlookupBit, Program.ExactCliffordCCZ.opsAllowed,
    Program.ExactCliffordCCZ.opAllowed,
    Program.ExactCliffordCCZ.opsAllowed_append]
  rw [phaseForBit_allowed]
  rfl

theorem unlookupAux_allowed (table : List Nat) (m : Nat) : ∀ start count,
    Program.ExactCliffordCCZ.opsAllowed
      (unlookupAux table m start count) = true := by
  intro start count
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [unlookupAux, Program.ExactCliffordCCZ.opsAllowed_append,
      unlookupBit_allowed, ih]
    rfl

theorem roundTripProgram_usesOnlyExactCliffordCCZ
    (table : List Nat) (m : Nat) :
    Program.ExactCliffordCCZ.UsesOnly (roundTripProgram table m) := by
  simp [Program.ExactCliffordCCZ.UsesOnly, roundTripProgram,
    Program.ExactCliffordCCZ.opsAllowed_append, gateOps_allowed,
    unlookupOps, unlookupAux_allowed]

end Lookup3
end VQ
