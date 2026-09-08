/-
Fixed repetition of the Algorithm 3 step, parameterized by the exact state
domain on which one-step correctness is available.  The terminal-entry
theorems compose live domain preservation with the decoded terminal orbit, while
leaving existence and bounds of the first terminal index to the inversion
proof.  Reversal uses circuit well-formedness and a proved forward equation.
-/
import VQ.Euclid.StepState

namespace VQ
namespace Euclid
namespace Iteration

open Reversible

def gates (n lengthWidth shiftWidth : Nat) : Nat → List RGate
  | 0 => []
  | steps + 1 =>
      Step.gates n lengthWidth shiftWidth ++
        gates n lengthWidth shiftWidth steps

def circuit (n lengthWidth shiftWidth steps : Nat) : RCircuit :=
  { width := (StepLayout.layout n lengthWidth shiftWidth).width,
    gates := gates n lengthWidth shiftWidth steps }

def reverseCircuit (n lengthWidth shiftWidth steps : Nat) : RCircuit :=
  (circuit n lengthWidth shiftWidth steps).reverse

/-- `StepActionOn` states the encoded action of one physical step on a chosen
state domain.  The predicate supplies the exact premise for each input state.
Domain preservation remains a separate premise. -/
def StepActionOn (n lengthWidth shiftWidth : Nat)
    (domain : State → Prop) : Prop :=
  ∀ s, domain s →
    act (Step.circuit n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      StepState.encoded n lengthWidth shiftWidth
        (step lengthWidth shiftWidth s)

/-- `StepInvariant` states closure of a chosen domain under the decoded step.
The domain may capture parameters such as the modulus width through its
definition.  This premise supports induction across a fixed schedule. -/
def StepInvariant (lengthWidth shiftWidth : Nat)
    (domain : State → Prop) : Prop :=
  ∀ s, domain s → domain (step lengthWidth shiftWidth s)

/-- `TraceAction` records one-step encoded equations along a particular run.
Each equation covers one index below the fixed repetition count.  This trace
premise permits composition without a global domain-preservation theorem. -/
def TraceAction (n lengthWidth shiftWidth steps : Nat) (s : State) : Prop :=
  ∀ k, k < steps →
    act (Step.circuit n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth
          (run lengthWidth shiftWidth k s)) =
      StepState.encoded n lengthWidth shiftWidth
        (step lengthWidth shiftWidth (run lengthWidth shiftWidth k s))

@[simp] theorem gates_zero (n lengthWidth shiftWidth : Nat) :
    gates n lengthWidth shiftWidth 0 = [] := rfl

@[simp] theorem gates_succ (n lengthWidth shiftWidth steps : Nat) :
    gates n lengthWidth shiftWidth (steps + 1) =
      Step.gates n lengthWidth shiftWidth ++
        gates n lengthWidth shiftWidth steps := rfl

@[simp] theorem circuit_width (n lengthWidth shiftWidth steps : Nat) :
    (circuit n lengthWidth shiftWidth steps).width =
      (StepLayout.layout n lengthWidth shiftWidth).width := rfl

@[simp] theorem circuit_gates (n lengthWidth shiftWidth steps : Nat) :
    (circuit n lengthWidth shiftWidth steps).gates =
      gates n lengthWidth shiftWidth steps := rfl

theorem gates_length (n lengthWidth shiftWidth steps : Nat) :
    (gates n lengthWidth shiftWidth steps).length =
      steps * (Step.gates n lengthWidth shiftWidth).length := by
  induction steps with
  | zero =>
      simp only [gates, List.length_nil, Nat.zero_mul]
  | succ steps ih =>
      rw [gates, List.length_append, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

theorem gates_countP (n lengthWidth shiftWidth steps : Nat)
    (p : RGate → Bool) :
    (gates n lengthWidth shiftWidth steps).countP p =
      steps * (Step.gates n lengthWidth shiftWidth).countP p := by
  induction steps with
  | zero =>
      simp only [gates, List.countP_nil, Nat.zero_mul]
  | succ steps ih =>
      rw [gates, List.countP_append, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

theorem gates_wellFormed
    {n lengthWidth shiftWidth steps : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (gates n lengthWidth shiftWidth steps).all
        (RGate.wellFormed
          (StepLayout.layout n lengthWidth shiftWidth).width) = true := by
  have hstep := Step.circuit_wellFormed
    (n := n) (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    hlength hwidths
  simp only [Step.circuit, RCircuit.wellFormed] at hstep
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp [gates, List.all_append, hstep, ih]

theorem circuit_wellFormed
    {n lengthWidth shiftWidth steps : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (circuit n lengthWidth shiftWidth steps).wellFormed = true := by
  exact gates_wellFormed hlength hwidths

theorem reverseCircuit_wellFormed
    {n lengthWidth shiftWidth steps : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth) :
    (reverseCircuit n lengthWidth shiftWidth steps).wellFormed = true := by
  exact RCircuit.wellFormed_reverse (circuit_wellFormed hlength hwidths)

theorem domain_run
    {lengthWidth shiftWidth : Nat} {domain : State → Prop}
    (hinvariant : StepInvariant lengthWidth shiftWidth domain) :
    ∀ {steps : Nat} {s : State}, domain s →
      domain (run lengthWidth shiftWidth steps s) := by
  intro steps
  induction steps with
  | zero =>
      intro s hs
      exact hs
  | succ steps ih =>
      intro s hs
      exact ih (hinvariant s hs)

theorem traceAction_of_stepActionOn
    {n lengthWidth shiftWidth steps : Nat} {domain : State → Prop}
    {s : State}
    (haction : StepActionOn n lengthWidth shiftWidth domain)
    (hinvariant : StepInvariant lengthWidth shiftWidth domain)
    (hs : domain s) :
    TraceAction n lengthWidth shiftWidth steps s := by
  intro k _hk
  exact haction _ (domain_run hinvariant hs)

theorem stepActionOn_reachable
    {p n lengthWidth shiftWidth : Nat}
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    StepActionOn n lengthWidth shiftWidth
      (ReachableStepDomain p n lengthWidth shiftWidth) := by
  intro s h
  simpa [Step.circuit, act] using
    StepState.gates_act h hwork hwidths

theorem traceAction_of_reachable_or_terminal
    {p n lengthWidth shiftWidth steps : Nat} {s : State}
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hdomain : ∀ k, k < steps →
      ReachableStepDomain p n lengthWidth shiftWidth
          (run lengthWidth shiftWidth k s) ∨
        (Terminal (run lengthWidth shiftWidth k s) ∧
          (run lengthWidth shiftWidth k s).shift + 1 <
            2 ^ shiftWidth)) :
    TraceAction n lengthWidth shiftWidth steps s := by
  intro k hk
  rcases hdomain k hk with h | ⟨hterminal, hnowrap⟩
  · simpa [Step.circuit, act] using
      StepState.gates_act h hwork hwidths
  · simpa [Step.circuit, act] using
      StepState.gates_act_terminal hwork hwidths hterminal hnowrap

theorem traceAction_of_terminal
    {n lengthWidth shiftWidth steps : Nat} {s : State}
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hterminal : Terminal s)
    (hcapacity : s.shift + steps + 1 < 2 ^ shiftWidth) :
    TraceAction n lengthWidth shiftWidth steps s := by
  apply traceAction_of_reachable_or_terminal
    (p := 0) hwork hwidths
  intro k hk
  have horbit := terminal_run_orbit
    (lengthWidth := lengthWidth) (shiftWidth := shiftWidth) (steps := k)
    hterminal (by omega)
  exact Or.inr ⟨horbit.1, horbit.2.2⟩

theorem reachable_run_before_terminal
    {p n lengthWidth shiftWidth tau : Nat} {s : State}
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hinitial : ReachableStepDomain p n lengthWidth shiftWidth s)
    (hlive : ∀ k, k < tau →
      ¬ Terminal (run lengthWidth shiftWidth k s)) :
    ∀ k, k ≤ tau →
      ReachableStepDomain p n lengthWidth shiftWidth
        (run lengthWidth shiftWidth k s) := by
  intro k hk
  induction k with
  | zero => simpa [run] using hinitial
  | succ k ih =>
      have hkTau : k < tau := by omega
      have hreach := ih (by omega)
      have hnext := ReachableStepDomain.reachable_after_step_of_not_terminal
        hreach hwork hwidths (hlive k hkTau)
      change ReachableStepDomain p n lengthWidth shiftWidth
        (run lengthWidth shiftWidth (k + 1) s)
      rw [run_add lengthWidth shiftWidth k 1 s]
      simpa [run] using hnext

theorem reachable_or_terminal_run_of_terminal_entry
    {p n lengthWidth shiftWidth steps tau : Nat} {s : State}
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hinitial : ReachableStepDomain p n lengthWidth shiftWidth s)
    (htau : tau ≤ steps)
    (hlive : ∀ k, k < tau →
      ¬ Terminal (run lengthWidth shiftWidth k s))
    (hterminal : Terminal (run lengthWidth shiftWidth tau s))
    (hcapacity :
      (run lengthWidth shiftWidth tau s).shift + (steps - tau) + 1 <
        2 ^ shiftWidth) :
    (∀ k, k < steps →
      ReachableStepDomain p n lengthWidth shiftWidth
          (run lengthWidth shiftWidth k s) ∨
        (Terminal (run lengthWidth shiftWidth k s) ∧
          (run lengthWidth shiftWidth k s).shift + 1 <
            2 ^ shiftWidth)) ∧
      Terminal (run lengthWidth shiftWidth steps s) ∧
      (run lengthWidth shiftWidth steps s).shift =
        (run lengthWidth shiftWidth tau s).shift + (steps - tau) ∧
      (run lengthWidth shiftWidth steps s).shift + 1 <
        2 ^ shiftWidth := by
  have hreachable := reachable_run_before_terminal
    hwork hwidths hinitial hlive
  have hfinalOrbit := terminal_run_orbit
    (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    (steps := steps - tau) hterminal hcapacity
  have hfinalCompose := run_add lengthWidth shiftWidth tau (steps - tau) s
  have hfinalSum : tau + (steps - tau) = steps := by omega
  rw [hfinalSum] at hfinalCompose
  constructor
  · intro k hk
    by_cases hbefore : k < tau
    · exact Or.inl (hreachable k (by omega))
    · have htauk : tau ≤ k := Nat.le_of_not_gt hbefore
      have hcapacity' :
          (run lengthWidth shiftWidth tau s).shift + (k - tau) + 1 <
            2 ^ shiftWidth := by
        omega
      have horbit := terminal_run_orbit
        (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
        (steps := k - tau) hterminal hcapacity'
      have hcompose := run_add lengthWidth shiftWidth tau (k - tau) s
      have hsum : tau + (k - tau) = k := by omega
      rw [hsum] at hcompose
      rw [hcompose]
      exact Or.inr ⟨horbit.1, horbit.2.2⟩
  · rw [hfinalCompose]
    exact ⟨hfinalOrbit.1, hfinalOrbit.2.1, hfinalOrbit.2.2⟩

theorem traceAction_of_terminal_entry
    {p n lengthWidth shiftWidth steps tau : Nat} {s : State}
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hinitial : ReachableStepDomain p n lengthWidth shiftWidth s)
    (htau : tau ≤ steps)
    (hlive : ∀ k, k < tau →
      ¬ Terminal (run lengthWidth shiftWidth k s))
    (hterminal : Terminal (run lengthWidth shiftWidth tau s))
    (hcapacity :
      (run lengthWidth shiftWidth tau s).shift + (steps - tau) + 1 <
        2 ^ shiftWidth) :
    TraceAction n lengthWidth shiftWidth steps s := by
  exact traceAction_of_reachable_or_terminal hwork hwidths
    (reachable_or_terminal_run_of_terminal_entry
      hwork hwidths hinitial htau hlive hterminal hcapacity).1

theorem reachable_or_terminal_run_256_of_terminal_entry
    {p tau : Nat} {s : State}
    (htauLower : 1024 ≤ tau) (htauUpper : tau ≤ 1476)
    (hinitial : ReachableStepDomain p 256 9 9 s)
    (hlive : ∀ k, k < tau → ¬ Terminal (run 9 9 k s))
    (hterminal : Terminal (run 9 9 tau s))
    (hshift : (run 9 9 tau s).shift = 0) :
    (∀ k, k < 1476 →
      ReachableStepDomain p 256 9 9 (run 9 9 k s) ∨
        (Terminal (run 9 9 k s) ∧
          (run 9 9 k s).shift + 1 < 2 ^ 9)) ∧
      Terminal (run 9 9 1476 s) ∧
      (run 9 9 1476 s).shift = 1476 - tau ∧
      (run 9 9 1476 s).shift + 1 < 2 ^ 9 := by
  have hpadding : 1476 - tau ≤ 452 := by omega
  have hcapacity :
      (run 9 9 tau s).shift + (1476 - tau) + 1 < 2 ^ 9 := by
    rw [hshift]
    norm_num
    omega
  have hresult := reachable_or_terminal_run_of_terminal_entry
    (p := p) (n := 256) (lengthWidth := 9) (shiftWidth := 9)
    (steps := 1476) (tau := tau)
    (by norm_num [workWidth]) (by norm_num) hinitial htauUpper hlive
    hterminal hcapacity
  simpa [hshift] using hresult

theorem traceAction_256_of_terminal_entry
    {p tau : Nat} {s : State}
    (htauLower : 1024 ≤ tau) (htauUpper : tau ≤ 1476)
    (hinitial : ReachableStepDomain p 256 9 9 s)
    (hlive : ∀ k, k < tau →
      ¬ Terminal (run 9 9 k s))
    (hterminal : Terminal (run 9 9 tau s))
    (hshift : (run 9 9 tau s).shift = 0) :
    TraceAction 256 9 9 1476 s := by
  exact traceAction_of_reachable_or_terminal
    (by norm_num [workWidth]) (by norm_num)
    (reachable_or_terminal_run_256_of_terminal_entry
      htauLower htauUpper hinitial hlive hterminal hshift).1

theorem act_gates_encoded_of_trace
    {n lengthWidth shiftWidth steps : Nat} {s : State}
    (htrace : TraceAction n lengthWidth shiftWidth steps s) :
    actGates (gates n lengthWidth shiftWidth steps)
        (StepState.encoded n lengthWidth shiftWidth s) =
      StepState.encoded n lengthWidth shiftWidth
        (run lengthWidth shiftWidth steps s) := by
  induction steps generalizing s with
  | zero => rfl
  | succ steps ih =>
      rw [gates, actGates_append]
      have hfirst := htrace 0 (by omega)
      change actGates (Step.gates n lengthWidth shiftWidth)
          (StepState.encoded n lengthWidth shiftWidth
            (run lengthWidth shiftWidth 0 s)) = _ at hfirst
      simp only [run] at hfirst
      rw [hfirst]
      apply ih
      intro k hk
      simpa [run] using htrace (k + 1) (by omega)

theorem act_circuit_encoded_of_trace
    {n lengthWidth shiftWidth steps : Nat} {s : State}
    (htrace : TraceAction n lengthWidth shiftWidth steps s) :
    act (circuit n lengthWidth shiftWidth steps)
        (StepState.encoded n lengthWidth shiftWidth s) =
      StepState.encoded n lengthWidth shiftWidth
        (run lengthWidth shiftWidth steps s) := by
  exact act_gates_encoded_of_trace htrace

theorem act_circuit_encoded
    {n lengthWidth shiftWidth steps : Nat} {domain : State → Prop}
    {s : State}
    (haction : StepActionOn n lengthWidth shiftWidth domain)
    (hinvariant : StepInvariant lengthWidth shiftWidth domain)
    (hs : domain s) :
    act (circuit n lengthWidth shiftWidth steps)
        (StepState.encoded n lengthWidth shiftWidth s) =
      StepState.encoded n lengthWidth shiftWidth
        (run lengthWidth shiftWidth steps s) := by
  exact act_circuit_encoded_of_trace
    (traceAction_of_stepActionOn haction hinvariant hs)

theorem reverseCircuit_act_after
    {n lengthWidth shiftWidth steps : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (i : Nat) :
    act (reverseCircuit n lengthWidth shiftWidth steps)
        (act (circuit n lengthWidth shiftWidth steps) i) = i := by
  exact act_reverse (circuit_wellFormed hlength hwidths) i

theorem reverseCircuit_recovers_image
    {n lengthWidth shiftWidth steps input output : Nat}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (hforward :
      act (circuit n lengthWidth shiftWidth steps) input = output) :
    act (reverseCircuit n lengthWidth shiftWidth steps) output = input := by
  rw [← hforward]
  exact reverseCircuit_act_after hlength hwidths input

theorem reverseCircuit_recovers_encoded_of_trace
    {n lengthWidth shiftWidth steps : Nat} {s : State}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (htrace : TraceAction n lengthWidth shiftWidth steps s) :
    act (reverseCircuit n lengthWidth shiftWidth steps)
        (StepState.encoded n lengthWidth shiftWidth
          (run lengthWidth shiftWidth steps s)) =
      StepState.encoded n lengthWidth shiftWidth s := by
  exact reverseCircuit_recovers_image hlength hwidths
    (act_circuit_encoded_of_trace htrace)

theorem reverseCircuit_recovers_encoded
    {n lengthWidth shiftWidth steps : Nat} {domain : State → Prop}
    {s : State}
    (hlength : 0 < lengthWidth) (hwidths : lengthWidth ≤ shiftWidth)
    (haction : StepActionOn n lengthWidth shiftWidth domain)
    (hinvariant : StepInvariant lengthWidth shiftWidth domain)
    (hs : domain s) :
    act (reverseCircuit n lengthWidth shiftWidth steps)
        (StepState.encoded n lengthWidth shiftWidth
          (run lengthWidth shiftWidth steps s)) =
      StepState.encoded n lengthWidth shiftWidth s := by
  exact reverseCircuit_recovers_encoded_of_trace hlength hwidths
    (traceAction_of_stepActionOn haction hinvariant hs)

end Iteration
end Euclid
end VQ
