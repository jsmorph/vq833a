import VQ.Euclid.StepResources
import VQ.Euclid.TerminalBounds

namespace VQ.Euclid.Inverter

open Reversible

def layout (n lengthWidth shiftWidth : Nat) : Layout :=
  TerminalCircuit.layout n lengthWidth shiftWidth

def forwardGates (rounds n lengthWidth shiftWidth : Nat) : List RGate :=
  StepResources.fixedRoundGates rounds n lengthWidth shiftWidth ++
    TerminalCircuit.gates n lengthWidth shiftWidth

def gates (rounds n lengthWidth shiftWidth : Nat) : List RGate :=
  forwardGates rounds n lengthWidth shiftWidth ++
    (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth).reverse

def circuit (rounds n lengthWidth shiftWidth : Nat) : RCircuit :=
  { width := (layout n lengthWidth shiftWidth).width,
    gates := gates rounds n lengthWidth shiftWidth }

theorem forwardGates_act_encoded_of_trace
    {p rounds n lengthWidth shiftWidth : Nat} {s : State}
    (hn : 0 < n)
    (htrace : Iteration.TraceAction n lengthWidth shiftWidth rounds s)
    (hfinalPacked : Packed n lengthWidth shiftWidth
      (run lengthWidth shiftWidth rounds s))
    (hfinalTerminal : Terminal (run lengthWidth shiftWidth rounds s))
    (hfinalGcd : Nat.gcd
      (run lengthWidth shiftWidth rounds s).r
      (run lengthWidth shiftWidth rounds s).rPrime = 1)
    (hfinalRelation : Relation p (run lengthWidth shiftWidth rounds s))
    (htPrimePos : 0 < (run lengthWidth shiftWidth rounds s).tPrime)
    (htPrimeLt : (run lengthWidth shiftWidth rounds s).tPrime < p)
    (hpFit : p < 2 ^ n) :
    actGates (forwardGates rounds n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      writeField
        (StepState.encoded n lengthWidth shiftWidth
          (run lengthWidth shiftWidth rounds s))
        (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n
        (decodedInverse p (run lengthWidth shiftWidth rounds s)) := by
  have hfixedAction :
      actGates (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth)
          (StepState.encoded n lengthWidth shiftWidth s) =
        StepState.encoded n lengthWidth shiftWidth
          (run lengthWidth shiftWidth rounds s) := by
    simpa [StepResources.fixedRoundGates] using
      Iteration.act_gates_encoded_of_trace htrace
  rw [forwardGates, actGates_append, hfixedAction]
  exact TerminalCircuit.gates_act_encoded_decodedInverse
    hn hfinalPacked hfinalTerminal hfinalGcd hfinalRelation
    htPrimePos htPrimeLt hpFit

theorem forwardGates_act_encoded_zero_of_trace
    {rounds n lengthWidth shiftWidth : Nat} {s : State}
    (hn : 0 < n)
    (htrace : Iteration.TraceAction n lengthWidth shiftWidth rounds s)
    (hfinalPacked : Packed n lengthWidth shiftWidth
      (run lengthWidth shiftWidth rounds s))
    (hfinalTerminal : Terminal (run lengthWidth shiftWidth rounds s))
    (hfinalIter : (run lengthWidth shiftWidth rounds s).iter = true)
    (hfinalTPrime : (run lengthWidth shiftWidth rounds s).tPrime = 0) :
    actGates (forwardGates rounds n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      writeField
        (StepState.encoded n lengthWidth shiftWidth
          (run lengthWidth shiftWidth rounds s))
        (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n 0 := by
  have hfixedAction :
      actGates (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth)
          (StepState.encoded n lengthWidth shiftWidth s) =
        StepState.encoded n lengthWidth shiftWidth
          (run lengthWidth shiftWidth rounds s) := by
    simpa [StepResources.fixedRoundGates] using
      Iteration.act_gates_encoded_of_trace htrace
  rw [forwardGates, actGates_append, hfixedAction]
  simpa [hfinalTPrime] using TerminalCircuit.gates_act_encoded_of_iter_true
    hn hfinalPacked hfinalTerminal hfinalIter (by simp [hfinalTPrime])

theorem fixedRoundGates_avoid_output
    {rounds n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    ∀ g ∈ StepResources.fixedRoundGates rounds n lengthWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < ExtractionPlaced.outputOffset n lengthWidth shiftWidth ∨
          ExtractionPlaced.outputOffset n lengthWidth shiftWidth + n ≤ q := by
  intro g hg q hq
  left
  have hfixed := Iteration.gates_wellFormed
    (n := n) (steps := rounds) hlength hwidths
  have hgWellFormed := List.all_eq_true.mp hfixed g (by
    simpa [StepResources.fixedRoundGates] using hg)
  simpa [ExtractionPlaced.outputOffset, ExtractionPlaced.baseWidth] using
    wire_lt_of_wellFormed hgWellFormed hq

theorem gates_act_encoded_of_trace
    {p rounds n lengthWidth shiftWidth : Nat} {s : State}
    (hn : 0 < n)
    (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (htrace : Iteration.TraceAction n lengthWidth shiftWidth rounds s)
    (hfinalPacked : Packed n lengthWidth shiftWidth
      (run lengthWidth shiftWidth rounds s))
    (hfinalTerminal : Terminal (run lengthWidth shiftWidth rounds s))
    (hfinalGcd : Nat.gcd
      (run lengthWidth shiftWidth rounds s).r
      (run lengthWidth shiftWidth rounds s).rPrime = 1)
    (hfinalRelation : Relation p (run lengthWidth shiftWidth rounds s))
    (htPrimePos : 0 < (run lengthWidth shiftWidth rounds s).tPrime)
    (htPrimeLt : (run lengthWidth shiftWidth rounds s).tPrime < p)
    (hpFit : p < 2 ^ n) :
    actGates (gates rounds n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      writeField (StepState.encoded n lengthWidth shiftWidth s)
        (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n
        (decodedInverse p (run lengthWidth shiftWidth rounds s)) := by
  have hforward := forwardGates_act_encoded_of_trace
    hn htrace hfinalPacked hfinalTerminal hfinalGcd hfinalRelation
    htPrimePos htPrimeLt hpFit
  have hfixedAction :
      actGates (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth)
          (StepState.encoded n lengthWidth shiftWidth s) =
        StepState.encoded n lengthWidth shiftWidth
          (run lengthWidth shiftWidth rounds s) := by
    simpa [StepResources.fixedRoundGates] using
      Iteration.act_gates_encoded_of_trace htrace
  have hfixedWellFormed := Iteration.gates_wellFormed
    (n := n) (steps := rounds) hlength hwidths
  have hundo :
      actGates
          (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth).reverse
          (actGates
            (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth)
            (StepState.encoded n lengthWidth shiftWidth s)) =
        StepState.encoded n lengthWidth shiftWidth s := by
    simpa [StepResources.fixedRoundGates] using
      actGates_reverse hfixedWellFormed
        (StepState.encoded n lengthWidth shiftWidth s)
  have hreverseOutside :
      ∀ g ∈ (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth).reverse,
        ∀ q ∈ g.wires,
          q < ExtractionPlaced.outputOffset n lengthWidth shiftWidth ∨
            ExtractionPlaced.outputOffset n lengthWidth shiftWidth + n ≤ q := by
    intro g hg
    exact fixedRoundGates_avoid_output hlength hwidths g
      (List.mem_reverse.mp hg)
  rw [gates, actGates_append, hforward]
  rw [actGates_write_of_outside hreverseOutside]
  rw [← hfixedAction]
  rw [hundo]

theorem gates_act_encoded_zero_of_trace
    {rounds n lengthWidth shiftWidth : Nat} {s : State}
    (hn : 0 < n)
    (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (htrace : Iteration.TraceAction n lengthWidth shiftWidth rounds s)
    (hfinalPacked : Packed n lengthWidth shiftWidth
      (run lengthWidth shiftWidth rounds s))
    (hfinalTerminal : Terminal (run lengthWidth shiftWidth rounds s))
    (hfinalIter : (run lengthWidth shiftWidth rounds s).iter = true)
    (hfinalTPrime : (run lengthWidth shiftWidth rounds s).tPrime = 0) :
    actGates (gates rounds n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      writeField (StepState.encoded n lengthWidth shiftWidth s)
        (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n 0 := by
  have hforward := forwardGates_act_encoded_zero_of_trace
    hn htrace hfinalPacked hfinalTerminal hfinalIter hfinalTPrime
  have hfixedAction :
      actGates (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth)
          (StepState.encoded n lengthWidth shiftWidth s) =
        StepState.encoded n lengthWidth shiftWidth
          (run lengthWidth shiftWidth rounds s) := by
    simpa [StepResources.fixedRoundGates] using
      Iteration.act_gates_encoded_of_trace htrace
  have hfixedWellFormed := Iteration.gates_wellFormed
    (n := n) (steps := rounds) hlength hwidths
  have hundo :
      actGates
          (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth).reverse
          (actGates
            (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth)
            (StepState.encoded n lengthWidth shiftWidth s)) =
        StepState.encoded n lengthWidth shiftWidth s := by
    simpa [StepResources.fixedRoundGates] using
      actGates_reverse hfixedWellFormed
        (StepState.encoded n lengthWidth shiftWidth s)
  have hreverseOutside :
      ∀ g ∈ (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth).reverse,
        ∀ q ∈ g.wires,
          q < ExtractionPlaced.outputOffset n lengthWidth shiftWidth ∨
            ExtractionPlaced.outputOffset n lengthWidth shiftWidth + n ≤ q := by
    intro g hg
    exact fixedRoundGates_avoid_output hlength hwidths g
      (List.mem_reverse.mp hg)
  rw [gates, actGates_append, hforward]
  rw [actGates_write_of_outside hreverseOutside]
  rw [← hfixedAction]
  rw [hundo]

theorem gates_act_zeroPrepared_linear_schedule
    {p n lengthWidth shiftWidth : Nat}
    (hn : 0 < n)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n + 1 < 2 ^ shiftWidth) :
    actGates (gates (12 * n) n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth
          (zeroPreparedState p)) =
      writeField
        (StepState.encoded n lengthWidth shiftWidth
          (zeroPreparedState p))
        (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n 0 := by
  have hlength : 0 < lengthWidth := by
    by_contra hnot
    have hzero : lengthWidth = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hwork
    simp [workWidth] at hwork
  have hterminal := zeroPreparedState_terminal p
  have hcapacity :
      (zeroPreparedState p).shift + 12 * n + 1 < 2 ^ shiftWidth := by
    simpa [zeroPreparedState, preprocessedState] using hscheduleFit
  have htrace := Iteration.traceAction_of_terminal
    hwork hwidths hterminal hcapacity
  have hfinalPacked := packed_terminal_run
    (zeroPreparedState_packed hpFit hwork) hterminal hcapacity
  have hrun := terminal_run_eq
    (lengthWidth := lengthWidth) (shiftWidth := shiftWidth)
    (steps := 12 * n) hterminal hcapacity
  apply gates_act_encoded_zero_of_trace
    hn hlength hwidths htrace hfinalPacked
  · exact (terminal_run_orbit hterminal hcapacity).1
  · rw [hrun]
    simp [zeroPreparedState]
  · rw [hrun]
    simp [zeroPreparedState, preprocessedState]

theorem circuit_spec_zeroPrepared_linear_schedule
    {p n lengthWidth shiftWidth : Nat}
    (hn : 0 < n)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n + 1 < 2 ^ shiftWidth) :
    act (circuit (12 * n) n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth
          (zeroPreparedState p)) =
      writeField
        (StepState.encoded n lengthWidth shiftWidth
          (zeroPreparedState p))
        (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n 0 := by
  simpa [circuit, Reversible.act] using
    gates_act_zeroPrepared_linear_schedule
      hn hpFit hwork hwidths hscheduleFit

theorem gates_act_preprocessed_linear_schedule
    {p a n lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n < 2 ^ shiftWidth)
    (ha0 : 0 < a)
    (ha : a < p) :
    let final := run lengthWidth shiftWidth (12 * n)
      (preprocessedState p a)
    actGates (gates (12 * n) n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth
          (preprocessedState p a)) =
      writeField
        (StepState.encoded n lengthWidth shiftWidth
          (preprocessedState p a))
        (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n
        (decodedInverse p final) := by
  dsimp only
  have hn : 0 < n := by
    by_contra hnot
    have hnZero : n = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hnZero] at hpFit
    simp only [pow_zero] at hpFit
    omega
  have hlength : 0 < lengthWidth := by
    by_contra hnot
    have hzero : lengthWidth = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hwork
    simp [workWidth] at hwork
  have hschedule := preprocessed_linear_schedule
    hpPrime hpFit hwork hwidths hscheduleFit ha0 ha
  have hfacts := preprocessed_linear_schedule_terminal_facts
    hpPrime hpFit hwork hwidths hscheduleFit ha0 ha
  exact gates_act_encoded_of_trace
    hn hlength hwidths hschedule.2.2.2 hfacts.2.1 hfacts.1
    hfacts.2.2.2.1 hfacts.2.2.1 hfacts.2.2.2.2.1
    hfacts.2.2.2.2.2 hpFit

theorem circuit_spec_preprocessed_linear_schedule
    {p a n lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n < 2 ^ shiftWidth)
    (ha0 : 0 < a)
    (ha : a < p) :
    let final := run lengthWidth shiftWidth (12 * n)
      (preprocessedState p a)
    act (circuit (12 * n) n lengthWidth shiftWidth)
          (StepState.encoded n lengthWidth shiftWidth
            (preprocessedState p a)) =
        writeField
          (StepState.encoded n lengthWidth shiftWidth
            (preprocessedState p a))
          (ExtractionPlaced.outputOffset n lengthWidth shiftWidth) n
          (decodedInverse p final) ∧
      decodedInverse p final < p ∧
      a * decodedInverse p final ≡ 1 [MOD p] := by
  dsimp only
  have haction := gates_act_preprocessed_linear_schedule
    hpPrime hpFit hwork hwidths hscheduleFit ha0 ha
  have hschedule := preprocessed_linear_schedule
    hpPrime hpFit hwork hwidths hscheduleFit ha0 ha
  exact ⟨by simpa [circuit, Reversible.act] using haction,
    hschedule.2.1, hschedule.2.2.1⟩

theorem forwardGates_wellFormed
    {rounds n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    (forwardGates rounds n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  have hfixed := Iteration.gates_wellFormed
    (n := n) (steps := rounds) hlength hwidths
  have hbaseLe :
      (StepLayout.layout n lengthWidth shiftWidth).width ≤
        (layout n lengthWidth shiftWidth).width := by
    rw [layout, TerminalCircuit.layout, ExtractionPlaced.layout_width]
    simp [ExtractionPlaced.baseWidth]
  have hfixedWide :
      (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth).all
        (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    exact RGate.wellFormed_mono hbaseLe
      (List.all_eq_true.mp hfixed g hg)
  rw [forwardGates, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨hfixedWide, by
    simpa [layout, TerminalCircuit.layout] using
      TerminalCircuit.gates_wellFormed n lengthWidth shiftWidth⟩

theorem gates_wellFormed
    {rounds n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    (gates rounds n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  have hforward := forwardGates_wellFormed
    (rounds := rounds) (n := n) hlength hwidths
  have hfixed := Iteration.gates_wellFormed
    (n := n) (steps := rounds) hlength hwidths
  have hbaseLe :
      (StepLayout.layout n lengthWidth shiftWidth).width ≤
        (layout n lengthWidth shiftWidth).width := by
    rw [layout, TerminalCircuit.layout, ExtractionPlaced.layout_width]
    simp [ExtractionPlaced.baseWidth]
  have hfixedWide :
      (StepResources.fixedRoundGates rounds n lengthWidth shiftWidth).all
        (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    exact RGate.wellFormed_mono hbaseLe
      (List.all_eq_true.mp hfixed g (by
        simpa [StepResources.fixedRoundGates] using hg))
  simp [gates, hforward, hfixedWide, List.all_reverse]

theorem circuit_wellFormed
    {rounds n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    (circuit rounds n lengthWidth shiftWidth).wellFormed = true :=
  gates_wellFormed hlength hwidths

theorem forwardGates_length_le (rounds n lengthWidth shiftWidth : Nat) :
    (forwardGates rounds n lengthWidth shiftWidth).length ≤
      rounds * StepResources.gateBound n lengthWidth shiftWidth +
        (2 * (Increment.lengthCost shiftWidth + 2 +
          3 * workWidth n * shiftWidth) + n + (11 * n + 4)) := by
  rw [forwardGates, List.length_append]
  exact Nat.add_le_add
    (StepResources.fixedRoundGates_length_le
      rounds n lengthWidth shiftWidth)
    (TerminalCircuit.gates_length_le n lengthWidth shiftWidth)

theorem forwardGates_ccx_le (rounds n lengthWidth shiftWidth : Nat) :
    (forwardGates rounds n lengthWidth shiftWidth).countP RGate.isCcx ≤
      rounds * StepResources.ccxBound n lengthWidth shiftWidth +
        (2 * (Increment.ccxCost shiftWidth + workWidth n * shiftWidth) +
          10 * n) := by
  rw [forwardGates, List.countP_append]
  exact Nat.add_le_add
    (StepResources.fixedRoundGates_ccx_le
      rounds n lengthWidth shiftWidth)
    (TerminalCircuit.gates_ccx_le n lengthWidth shiftWidth)

theorem forwardGates_cx_le (rounds n lengthWidth shiftWidth : Nat) :
    (forwardGates rounds n lengthWidth shiftWidth).countP RGate.isCx ≤
      rounds * StepResources.cxBound n lengthWidth shiftWidth +
        (2 * (Increment.cxCost shiftWidth + 2 * workWidth n * shiftWidth) + n +
          (7 * n + 2)) := by
  rw [forwardGates, List.countP_append]
  exact Nat.add_le_add
    (StepResources.fixedRoundGates_cx_le
      rounds n lengthWidth shiftWidth)
    (TerminalCircuit.gates_cx_le n lengthWidth shiftWidth)

theorem gates_length_le (rounds n lengthWidth shiftWidth : Nat) :
    (gates rounds n lengthWidth shiftWidth).length ≤
      2 * (rounds * StepResources.gateBound n lengthWidth shiftWidth) +
        (2 * (Increment.lengthCost shiftWidth + 2 +
          3 * workWidth n * shiftWidth) + n + (11 * n + 4)) := by
  have hfixed := StepResources.fixedRoundGates_length_le
    rounds n lengthWidth shiftWidth
  have hterminal := TerminalCircuit.gates_length_le n lengthWidth shiftWidth
  simp only [gates, forwardGates, List.length_append, List.length_reverse]
  omega

theorem gates_ccx_le (rounds n lengthWidth shiftWidth : Nat) :
    (gates rounds n lengthWidth shiftWidth).countP RGate.isCcx ≤
      2 * (rounds * StepResources.ccxBound n lengthWidth shiftWidth) +
        (2 * (Increment.ccxCost shiftWidth + workWidth n * shiftWidth) +
          10 * n) := by
  have hfixed := StepResources.fixedRoundGates_ccx_le
    rounds n lengthWidth shiftWidth
  have hterminal := TerminalCircuit.gates_ccx_le n lengthWidth shiftWidth
  simp only [gates, forwardGates, List.countP_append, List.countP_reverse]
  omega

theorem gates_cx_le (rounds n lengthWidth shiftWidth : Nat) :
    (gates rounds n lengthWidth shiftWidth).countP RGate.isCx ≤
      2 * (rounds * StepResources.cxBound n lengthWidth shiftWidth) +
        (2 * (Increment.cxCost shiftWidth + 2 * workWidth n * shiftWidth) + n +
          (7 * n + 2)) := by
  have hfixed := StepResources.fixedRoundGates_cx_le
    rounds n lengthWidth shiftWidth
  have hterminal := TerminalCircuit.gates_cx_le n lengthWidth shiftWidth
  simp only [gates, forwardGates, List.countP_append, List.countP_reverse]
  omega

end VQ.Euclid.Inverter
