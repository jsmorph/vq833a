import VQ.Euclid.LuoWindowedOwnershipSchedule

namespace VQMathlib.LuoSchedule.WindowedOwnership

open VQ.Euclid.LuoWindowedOwnership
open VQ
open VQ.Euclid
open VQ.Reversible

theorem roundGates_countP (predicate : RGate → Bool) (step : Nat) :
    (roundGates step).countP predicate =
      roundPrefixGates.countP predicate +
        ((ownershipGates step).countP predicate +
          PackedTerminalEpoch.exitGates.countP predicate) := by
  simp only [roundGates, List.countP_append]
  rw [Nat.add_assoc]

def roundFixedCount (predicate : RGate → Bool) : Nat :=
  roundPrefixGates.countP predicate +
    PackedTerminalEpoch.exitGates.countP predicate

theorem roundGates_countP_of
    (predicate : RGate → Bool) (step count : Nat)
    (hcount : (ownershipGates step).countP predicate = count) :
    (roundGates step).countP predicate = roundFixedCount predicate + count := by
  rw [roundGates_countP, hcount]
  unfold roundFixedCount
  rw [← Nat.add_assoc, Nat.add_right_comm]

theorem roundsGatesFrom_countP_of
    (predicate : RGate → Bool) (cost : Nat → Nat)
    (hcount : ∀ step, (roundGates step).countP predicate = cost step)
    (first rounds : Nat) :
    (roundsGatesFrom first rounds).countP predicate =
      ((List.range' first rounds).map cost).sum := by
  induction rounds generalizing first with
  | zero => rfl
  | succ rounds ih =>
      rw [roundsGatesFrom, List.countP_append, hcount, ih,
        List.range'_succ, List.map_cons, List.sum_cons]

theorem sum_map_add_left
    {Index : Type} (fixed : Nat) (cost : Index → Nat)
    (indices : List Index) :
    (indices.map (fun index => fixed + cost index)).sum =
      indices.length * fixed + (indices.map cost).sum := by
  induction indices with
  | nil => simp
  | cons index indices ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih,
        Nat.add_mul, Nat.one_mul]
      ac_rfl

end VQMathlib.LuoSchedule.WindowedOwnership
