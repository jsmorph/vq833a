import VQ.Euclid.LuoWindowedOwnership
import VQ.Euclid.PackedTerminalEndpoint

namespace VQ.Euclid.LuoWindowedOwnership

open VQ
open VQ.Reversible

def roundPrefixGates : List RGate :=
  PackedTerminalEpoch.entryGates ++ PackedTerminalEpoch.prefixRemainderGates ++
    PackedStepLayout.coefficientGates ++ PackedShift.postShiftGates ++
    PackedTerminalEpoch.phaseGates

def roundGates (step : Nat) : List RGate :=
  roundPrefixGates ++ ownershipGates step ++ PackedTerminalEpoch.exitGates

def roundsGatesFrom : Nat → Nat → List RGate
  | _, 0 => []
  | first, rounds + 1 =>
      roundGates first ++ roundsGatesFrom (first + 1) rounds

def roundsGates (rounds : Nat) : List RGate :=
  roundsGatesFrom 1 rounds

theorem roundGates_wellFormed {step : Nat} (hstep : step ≤ 1620) :
    (roundGates step).all (RGate.wellFormed PackedStepLayout.width) = true := by
  have hfixed := PackedTerminalEpoch.gates_wellFormed
  simp only [PackedTerminalEpoch.gates, List.all_append, Bool.and_eq_true] at hfixed
  simp only [roundGates, roundPrefixGates, List.all_append, Bool.and_eq_true]
  exact ⟨⟨hfixed.1.1, ownershipGates_wellFormed hstep⟩, hfixed.2⟩

theorem roundsGatesFrom_wellFormed {first rounds : Nat}
    (hbound : first + rounds ≤ 1621) :
    (roundsGatesFrom first rounds).all
      (RGate.wellFormed PackedStepLayout.width) = true := by
  induction rounds generalizing first with
  | zero => rfl
  | succ rounds ih =>
      simp only [roundsGatesFrom, List.all_append, Bool.and_eq_true]
      exact ⟨roundGates_wellFormed (by omega), ih (by omega)⟩

theorem roundsGates_wellFormed {rounds : Nat} (hbound : rounds ≤ 1620) :
    (roundsGates rounds).all (RGate.wellFormed PackedStepLayout.width) = true :=
  roundsGatesFrom_wellFormed (by omega)

def inverterGates : List RGate :=
  roundsGates 1620 ++ PackedTerminalEndpoint.gates ++ (roundsGates 1620).reverse

theorem inverterGates_wellFormed :
    inverterGates.all (RGate.wellFormed PackedTerminalEndpoint.width) = true := by
  have hrounds : (roundsGates 1620).all
      (RGate.wellFormed PackedTerminalEndpoint.width) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    exact RGate.wellFormed_mono (by decide)
      (List.all_eq_true.mp (roundsGates_wellFormed (by omega)) g hg)
  simp only [inverterGates, List.all_append, List.all_reverse, hrounds,
    PackedTerminalEndpoint.gates_wellFormed, Bool.and_self]

end VQ.Euclid.LuoWindowedOwnership
