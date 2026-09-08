import VQBridge.Palomar833.Curve

open scoped BigOperators

namespace Palomar833

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev Outcome := Fin N × Fin N

def outcome (b : Branch) : Outcome :=
  (⟨(b.storage / N) % N, Nat.mod_lt _ (Nat.two_pow_pos 256)⟩,
   ⟨(b.storage / N ^ 2) % N, Nat.mod_lt _ (Nat.two_pow_pos 256)⟩)

def outcomeMass (program : Program) (input : Nat) (o : Outcome) : ℝ :=
  ((runOps program.ops (initialBranch input)).map fun b =>
    if outcome b = o then weight program.qubits b else 0).sum

def expectedCCZ (program : Program) (input index : Nat) : ℝ :=
  ((runOps program.ops (initialBranch input index)).map fun b =>
    weight program.qubits b * b.cczCount).sum

/-! ## Recovery and independent repetition -/

def peak (k : Nat) : Nat := (2 * N * k + q) / (2 * q)
def roundOutcome (j : Nat) : Nat := (2 * q * j + N) / (2 * N)

def selected (d : Nat) (o : Outcome) : Prop :=
  ∃ k, 0 < k ∧ k < q ∧ o.1.val = peak k ∧ o.2.val = peak ((d * k) % q)

def decode (o : Outcome) : Option Nat :=
  let k : ZMod q := roundOutcome o.1.val
  let v : ZMod q := roundOutcome o.2.val
  if k = 0 then none else some (v * k⁻¹).val

def publicAccepts (pointQ candidate : Nat) : Prop :=
  candidate < q ∧ candidate • generator = decodePoint pointQ

def selectedProbability (program : Program) (input d : Nat) : ℝ :=
  ∑ o : Outcome, if selected d o then outcomeMass program input o else 0

def repetitionMass (program : Program) (input : Nat) (o : Fin 26 → Outcome) : ℝ :=
  ∏ i, outcomeMass program input (o i)

def repeatedProbability (program : Program) (input d : Nat) : ℝ :=
  ∑ o : Fin 26 → Outcome,
    if ∃ i, selected d (o i) then repetitionMass program input o else 0

/-! ## Functional and probability statements -/

def fourierState (d : Nat) (o : Outcome) : State := fun j =>
  (1 / (N : ℂ) ^ 2) * ∑ a : Fin N, ∑ b : Fin N,
    Complex.exp (((2 : Nat) : ℂ) * Real.pi * Complex.I *
      ((a.val * o.1.val + b.val * o.2.val : Nat) : ℂ) / (N : ℂ)) *
    (if j = encodePoint ((a.val + d * b.val) • generator) then 1 else 0)

end

end Palomar833
