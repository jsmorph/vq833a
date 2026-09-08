/-
Immutable classical-input loading for hybrid programs.
-/
import VQ.Program.Semantics
import VQ.Reversible.Reverse

namespace VQ
namespace Program

open Semantics Reversible

/-- XOR consecutive immutable input bits into consecutive quantum wires. -/
def inputXorOps : Nat → Nat → Nat → List Op
  | _, _, 0 => []
  | inputStart, wireStart, len + 1 =>
      .branch (.input inputStart) [.gate (.x wireStart)] [] ::
        inputXorOps (inputStart + 1) (wireStart + 1) len

/-- The bit mask selected by `inputXorOps`. -/
def inputMask (input : Nat) : Nat → Nat → Nat → Nat
  | _, _, 0 => 0
  | inputStart, wireStart, len + 1 =>
      (if input.testBit inputStart then 1 <<< wireStart else 0) ^^^
        inputMask input (inputStart + 1) (wireStart + 1) len

/-- The classical action of `inputXorOps` on a basis index. -/
def inputXorIndex (input : Nat) : Nat → Nat → Nat → Nat → Nat
  | _, _, 0, i => i
  | inputStart, wireStart, len + 1, i =>
      inputXorIndex input (inputStart + 1) (wireStart + 1) len
        (if input.testBit inputStart then i ^^^ (1 <<< wireStart) else i)

theorem inputXorIndex_eq (input inputStart wireStart len i : Nat) :
    inputXorIndex input inputStart wireStart len i =
      i ^^^ inputMask input inputStart wireStart len := by
  induction len generalizing inputStart wireStart i with
  | zero => simp [inputXorIndex, inputMask]
  | succ len ih =>
      rw [inputXorIndex, inputMask, ih]
      split
      · rw [Nat.xor_assoc]
      · rw [Nat.zero_xor]

theorem inputXorIndex_involutive (input inputStart wireStart len i : Nat) :
    inputXorIndex input inputStart wireStart len
      (inputXorIndex input inputStart wireStart len i) = i := by
  rw [inputXorIndex_eq, inputXorIndex_eq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem testBit_inputMask (input inputStart wireStart len b : Nat) :
    (inputMask input inputStart wireStart len).testBit b =
      (decide (wireStart ≤ b) && decide (b < wireStart + len) &&
        input.testBit (inputStart + (b - wireStart))) := by
  induction len generalizing inputStart wireStart with
  | zero =>
      by_cases hlo : wireStart ≤ b
      · have hhi : ¬b < wireStart := by omega
        simp [inputMask, hlo, hhi]
      · simp [inputMask, hlo]
  | succ len ih =>
      rw [inputMask, Nat.testBit_xor, ih]
      by_cases heq : b = wireStart
      · subst b
        have hrest : ¬wireStart + 1 ≤ wireStart := by omega
        by_cases hb : input.testBit inputStart = true
        · simp [Nat.one_shiftLeft, Nat.testBit_two_pow, hb, hrest]
        · simp [Nat.one_shiftLeft, Nat.testBit_two_pow, hb, hrest]
      · by_cases hlt : b < wireStart
        · have hrest : ¬wireStart + 1 ≤ b := by omega
          have hnle : ¬wireStart ≤ b := by omega
          have hne : wireStart ≠ b := Ne.symm heq
          by_cases hb : input.testBit inputStart = true
          · simp [Nat.one_shiftLeft, Nat.testBit_two_pow, hb, hne, hnle, hrest]
          · simp [Nat.one_shiftLeft, Nat.testBit_two_pow, hb, hne, hnle, hrest]
        · have hrest : wireStart + 1 ≤ b := by omega
          have hlo : wireStart ≤ b := by omega
          have hne : wireStart ≠ b := Ne.symm heq
          have hindex : inputStart + 1 + (b - (wireStart + 1)) =
              inputStart + (b - wireStart) := by omega
          have hupper : b < wireStart + 1 + len ↔
              b < wireStart + (len + 1) := by omega
          by_cases hb : input.testBit inputStart = true
          · simp [Nat.one_shiftLeft, Nat.testBit_two_pow, hb, hne, hlo, hrest, hindex,
              hupper]
          · simp [Nat.one_shiftLeft, Nat.testBit_two_pow, hb, hne, hlo, hrest, hindex,
              hupper]

theorem inputMask_eq_shiftedField (input inputStart wireStart len : Nat) :
    inputMask input inputStart wireStart len =
      readField input inputStart len <<< wireStart := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_inputMask, Nat.testBit_shiftLeft, testBit_readField]
  by_cases hlo : wireStart ≤ b
  · by_cases hhi : b < wireStart + len
    · simp [hlo, hhi, show b - wireStart < len by omega]
    · simp [hlo, hhi, show ¬b - wireStart < len by omega]
  · have hlt : b < wireStart := by omega
    simp [hlt, hlo]

theorem inputXorIndex_eq_shiftedField (input inputStart wireStart len i : Nat) :
    inputXorIndex input inputStart wireStart len i =
      i ^^^ (readField input inputStart len <<< wireStart) := by
  rw [inputXorIndex_eq, inputMask_eq_shiftedField]

theorem xor_shiftedField_eq_writeField_of_clear {i value off len : Nat}
    (hclear : readField i off len = 0) (hvalue : value < 2 ^ len) :
    i ^^^ (value <<< off) = writeField i off len value := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge b off with hlo | hlo
  · rw [testBit_writeField_outside (Or.inl hlo)]
    simp [Nat.not_le.mpr hlo]
  · rcases Nat.lt_or_ge b (off + len) with hhi | hhi
    · have hbit := congrArg (fun value => value.testBit (b - off)) hclear
      simp only [testBit_readField, Nat.zero_testBit,
        show b - off < len by omega, decide_true, Bool.true_and,
        show off + (b - off) = b by omega] at hbit
      rw [testBit_writeField_inside hlo hhi]
      simp [hlo, hbit]
    · rw [testBit_writeField_outside (Or.inr hhi)]
      have hv : value.testBit (b - off) = false := by
        apply Nat.testBit_lt_two_pow
        exact Nat.lt_of_lt_of_le hvalue
          (Nat.pow_le_pow_right (by omega) (by omega))
      simp [hlo, hv]

theorem inputXorIndex_eq_writeField_of_clear
    {input inputStart wireStart len i : Nat}
    (hclear : readField i wireStart len = 0) :
    inputXorIndex input inputStart wireStart len i =
      writeField i wireStart len (readField input inputStart len) := by
  rw [inputXorIndex_eq_shiftedField]
  exact xor_shiftedField_eq_writeField_of_clear hclear
    (readField_lt input inputStart len)

theorem inputXorIndex_writeField_of_disjoint
    {input inputStart wireStart loaderLen i off fieldLen value : Nat}
    (hdis : wireStart + loaderLen ≤ off ∨ off + fieldLen ≤ wireStart) :
    inputXorIndex input inputStart wireStart loaderLen
      (writeField i off fieldLen value) =
        writeField (inputXorIndex input inputStart wireStart loaderLen i)
          off fieldLen value := by
  induction loaderLen generalizing inputStart wireStart i with
  | zero => rfl
  | succ loaderLen ih =>
      simp only [inputXorIndex]
      split
      · rw [xor_writeField_of_outside (by rcases hdis with h | h <;> omega),
          ih (by rcases hdis with h | h <;> omega)]
      · exact ih (by rcases hdis with h | h <;> omega)

theorem runOps_inputXorOps {level width inputStart wireStart len input i cr : Nat}
    {rec : List Bool}
    (hwire : wireStart + len ≤ width) :
    runOps level width (inputXorOps inputStart wireStart len)
      (Branch.mk rec cr (basis i) input) =
        [Branch.mk rec cr (basis (inputXorIndex input inputStart wireStart len i)) input] := by
  induction len generalizing inputStart wireStart i with
  | zero => rfl
  | succ len ih =>
      rw [inputXorOps, runOps_cons, runOp_branch]
      dsimp +instances only [CRef.read]
      by_cases hb : input.testBit inputStart = true
      · rw [if_pos hb, runOps_singleton, runOp_gate, List.flatMap_singleton,
          Semantics.apply_x (by omega), ih (by omega)]
        simp [inputXorIndex, hb]
      · rw [if_neg hb, runOps_nil, List.flatMap_singleton, ih (by omega)]
        simp [inputXorIndex, hb]

theorem inputXorOps_wellFormed {level width inputWidth inputStart wireStart len : Nat}
    (hinput : inputStart + len ≤ inputWidth) (hwire : wireStart + len ≤ width) :
    Program.opsWellFormed level width inputWidth 0
      (inputXorOps inputStart wireStart len) = true := by
  induction len generalizing inputStart wireStart with
  | zero => rfl
  | succ len ih =>
      simp only [inputXorOps, Program.opsWellFormed, Program.opWellFormed, CRef.wellFormed,
        Gate.wellFormedAt, Bool.and_eq_true, decide_eq_true_eq]
      rw [ih (by omega) (by omega)]
      simp
      omega

theorem inputXorOps_toffoli (inputStart wireStart len : Nat) :
    Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
      (inputXorOps inputStart wireStart len) = Range.point 0 := by
  induction len generalizing inputStart wireStart with
  | zero => rfl
  | succ len ih =>
      rw [inputXorOps, Program.weighOps, Program.weighOp, ih]
      rfl

theorem inputXorOps_weight_one (f : Gate → Nat)
    (hx : ∀ q, f (.x q) = 1) (inputStart wireStart len : Nat) :
    Program.weighOps f (inputXorOps inputStart wireStart len) =
      { lo := 0, hi := len } := by
  induction len generalizing inputStart wireStart with
  | zero => rfl
  | succ len ih =>
      rw [inputXorOps, Program.weighOps, Program.weighOp, ih]
      simp [Program.weighOps, Program.weighOp, hx, Range.add, Range.choice,
        Range.point, Nat.add_comm]

theorem inputXorOps_weight_zero (f : Gate → Nat)
    (hx : ∀ q, f (.x q) = 0) (inputStart wireStart len : Nat) :
    Program.weighOps f (inputXorOps inputStart wireStart len) = Range.point 0 := by
  induction len generalizing inputStart wireStart with
  | zero => rfl
  | succ len ih =>
      rw [inputXorOps, Program.weighOps, Program.weighOp, ih]
      simp [Program.weighOps, Program.weighOp, hx, Range.add, Range.choice,
        Range.point]

theorem inputXorOps_gates (inputStart wireStart len : Nat) :
    Program.weighOps (fun _ => 1) (inputXorOps inputStart wireStart len) =
      { lo := 0, hi := len } := by
  exact inputXorOps_weight_one (fun _ => 1) (fun _ => rfl) _ _ _

theorem inputXorOps_clifford (inputStart wireStart len : Nat) :
    Program.weighOps (fun g => if g.isNonClifford then 0 else 1)
      (inputXorOps inputStart wireStart len) = { lo := 0, hi := len } := by
  exact inputXorOps_weight_one
    (fun g => if g.isNonClifford then 0 else 1) (fun _ => rfl) _ _ _

theorem inputXorOps_cnot (inputStart wireStart len : Nat) :
    Program.weighOps (fun g => if g.isTwoQubit then 1 else 0)
      (inputXorOps inputStart wireStart len) = Range.point 0 := by
  exact inputXorOps_weight_zero
    (fun g => if g.isTwoQubit then 1 else 0) (fun _ => rfl) _ _ _

theorem inputXorOps_classical (inputStart wireStart len : Nat) :
    Program.classicalOpCountOps (inputXorOps inputStart wireStart len) = Range.point len := by
  induction len generalizing inputStart wireStart with
  | zero => rfl
  | succ len ih =>
      simp [inputXorOps, Program.classicalOpCountOps, Program.classicalOpCountOp, ih,
        Range.add, Range.choice, Range.point]
      omega

end Program
end VQ
