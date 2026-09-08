import VQ.Euclid.ScheduleBound
import VQ.Reversible.BarrelRotate

namespace VQ.Euclid

open Reversible

def fixedWireCoefficient (n : Nat) (s : State) : Nat :=
  readField (encodeWork2 n s) 0 n

def fixedWireSignedOutput (p n : Nat) (s : State) : Nat :=
  if s.iter then fixedWireCoefficient n s
  else (p + 2 ^ n - fixedWireCoefficient n s) % 2 ^ n

theorem readField_barrelRotateState_cancel
    {shiftOffset workOffset width count i raw shift : Nat}
    (hwidth : 0 < width)
    (hdisjoint : shiftOffset + count ≤ workOffset ∨
      workOffset + width ≤ shiftOffset)
    (hshift : readField i shiftOffset count = shift)
    (hwork : readField i workOffset width =
      rotatePositionsLeft width shift raw)
    (hraw : raw < 2 ^ width) :
    readField
        (barrelRotateState shiftOffset workOffset width count i)
        workOffset width = raw := by
  letI : NeZero width := ⟨Nat.ne_of_gt hwidth⟩
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_readField]
  by_cases hq : q < width
  · simp only [hq, decide_true, Bool.true_and]
    rw [testBit_barrelRotateState_cyclic hwidth hdisjoint hq,
      hshift]
    let source : Fin width :=
      ⟨q, hq⟩ - cyclicIndex width shift hwidth
    have hsource : i.testBit (workOffset + source.val) =
        (readField i workOffset width).testBit source.val := by
      rw [testBit_readField]
      simp [source.isLt]
    rw [hsource, hwork,
      testBit_rotatePositionsLeft_cyclic hwidth source.isLt]
    congr 1
    change (source + cyclicIndex width shift hwidth).val =
      (⟨q, hq⟩ : Fin width).val
    apply congrArg Fin.val
    simp [source]
  · have hpow : 2 ^ width ≤ 2 ^ q :=
        Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hq)
    have hbit : raw.testBit q = false :=
      Nat.testBit_lt_two_pow (hraw.trans_le hpow)
    simp [hq, hbit]

def p37TerminalState : State :=
  { t := 37
    q := 0
    r := 1
    tPrime := 17
    rPrime := 0
    lenT := 6
    lenQ := 0
    lenRPrime := 0
    shift := 0
    phase1 := false
    phase2 := false
    iter := false
    sign := false }

theorem p37_first_terminal_state :
    run 3 3 32 (preprocessedState 37 13) = p37TerminalState ∧
      ∀ k, k < 32 →
        ¬ Terminal (run 3 3 k (preprocessedState 37 13)) := by
  unfold Terminal
  decide

theorem p37_first_terminal_state_vq :
    run 4 4 32 (preprocessedState 37 13) = p37TerminalState ∧
      ∀ k, k < 32 →
        ¬ Terminal (run 4 4 k (preprocessedState 37 13)) := by
  unfold Terminal
  decide

theorem p37_fixed_schedule_state :
    run 3 3 36 (preprocessedState 37 13) =
      { p37TerminalState with shift := 4 } := by
  have hterminal : Terminal p37TerminalState := by
    norm_num [Terminal, p37TerminalState]
  have horbit := terminal_run_eq
    (lengthWidth := 3) (shiftWidth := 3) (steps := 4)
    hterminal (by norm_num [p37TerminalState])
  have hcompose := run_add 3 3 32 4 (preprocessedState 37 13)
  rw [p37_first_terminal_state.1] at hcompose
  simpa [p37TerminalState] using hcompose.trans horbit

theorem p37_terminal_inverse :
    decodedInverse 37 p37TerminalState = 20 := by
  decide

theorem p37_fixed_wire_coefficient :
    fixedWireCoefficient 6
        (run 3 3 36 (preprocessedState 37 13)) = 33 := by
  decide

theorem p37_fixed_wire_output :
    fixedWireSignedOutput 37 6
        (run 3 3 36 (preprocessedState 37 13)) = 4 := by
  decide

theorem p37_fixed_wire_output_is_wrong :
    fixedWireSignedOutput 37 6
        (run 3 3 36 (preprocessedState 37 13)) ≠
      decodedInverse 37
        (run 3 3 36 (preprocessedState 37 13)) := by
  decide

theorem p37_fixed_schedule_trace :
    Iteration.TraceAction 6 4 4 36 (preprocessedState 37 13) := by
  apply Iteration.traceAction_of_terminal_entry
      (p := 37) (tau := 32)
  · norm_num [workWidth]
  · norm_num
  · exact preprocessedState_reachable
      (by norm_num) (by norm_num [workWidth])
      (by norm_num) (by norm_num)
  · norm_num
  · exact p37_first_terminal_state_vq.2
  · rw [p37_first_terminal_state_vq.1]
    norm_num [Terminal, p37TerminalState]
  · rw [p37_first_terminal_state_vq.1]
    norm_num [p37TerminalState]

theorem p37_fixed_schedule_circuit :
    act (Iteration.circuit 6 4 4 36)
        (StepState.encoded 6 4 4 (preprocessedState 37 13)) =
      StepState.encoded 6 4 4
        (run 4 4 36 (preprocessedState 37 13)) := by
  exact Iteration.act_circuit_encoded_of_trace p37_fixed_schedule_trace

end VQ.Euclid
