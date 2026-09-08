import VQMathlib.Algorithms.QFT

namespace VQ.Tests.ApproximateQFT

open VQ VQ.Circuit VQ.Gate

def phaseRows (cutoff : Nat) : List Nat → Nat → Nat → List Gate
  | [], _, _ => []
  | r :: rest, start, q =>
      (if start + 2 ≤ cutoff then Circuit.cphase (start + 2) r q else []) ++
        phaseRows cutoff rest (start + 1) q

def noSwap (cutoff : Nat) : List Nat → List Gate
  | [] => []
  | q :: rest => Gate.h q :: phaseRows cutoff rest 0 q ++ noSwap cutoff rest

def gates (cutoff : Nat) (wires : List Nat) : List Gate :=
  noSwap cutoff wires ++ QFT.qftSwaps wires

def circuit (n cutoff : Nat) : Circuit :=
  Circuit.ofGates n (gates cutoff (List.range n).reverse)

def rowCost (cutoff : Nat) (cost : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | start, n + 1 =>
      (if start + 2 ≤ cutoff then cost (start + 2) else 0) +
        rowCost cutoff cost (start + 1) n

def noSwapCost (cutoff hCost : Nat) (phaseCost : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      hCost + rowCost cutoff phaseCost 0 n + noSwapCost cutoff hCost phaseCost n

def retainedPairs (n cutoff : Nat) : Nat :=
  noSwapCost cutoff 0 (fun _ => 1) n

theorem rowCost_const (cutoff value start count : Nat) :
    rowCost cutoff (fun _ => value) start count =
      value * rowCost cutoff (fun _ => 1) start count := by
  induction count generalizing start with
  | zero => simp [rowCost]
  | succ count ih =>
      by_cases hkeep : start + 2 ≤ cutoff
      · simp [rowCost, hkeep, ih, Nat.mul_add]
      · simp [rowCost, hkeep, ih]

theorem noSwapCost_const (cutoff hCost value n : Nat) :
    noSwapCost cutoff hCost (fun _ => value) n =
      hCost * n + value * retainedPairs n cutoff := by
  induction n with
  | zero => simp [noSwapCost, retainedPairs]
  | succ n ih =>
      rw [noSwapCost, ih, rowCost_const]
      simp only [retainedPairs, noSwapCost]
      rw [Nat.mul_succ, Nat.zero_add, Nat.mul_add]
      omega

theorem phaseRows_eq_full {cutoff start : Nat} (rest : List Nat) (q : Nat)
    (hcutoff : start + rest.length + 1 ≤ cutoff) :
    phaseRows cutoff rest start q =
      (rest.zipIdx start |>.flatMap fun ri => Circuit.cphase (ri.2 + 2) ri.1 q) := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      simp only [List.length_cons] at hcutoff
      simp only [phaseRows, List.zipIdx_cons, List.flatMap_cons]
      rw [if_pos (by omega), ih (by omega)]

theorem noSwap_eq_qftNoSwap {cutoff : Nat} (wires : List Nat)
    (hcutoff : wires.length ≤ cutoff) :
    noSwap cutoff wires = Circuit.qftNoSwap wires := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      simp only [List.length_cons] at hcutoff
      change Gate.h q :: phaseRows cutoff rest 0 q ++ noSwap cutoff rest =
        Gate.h q ::
          ((rest.zipIdx.flatMap fun ri => Circuit.cphase (ri.2 + 2) ri.1 q) ++
            Circuit.qftNoSwap rest)
      rw [phaseRows_eq_full rest q (by omega), ih (by omega)]
      simp

theorem circuit_eq_qftCircuit {n cutoff : Nat} (hcutoff : n ≤ cutoff) :
    circuit n cutoff = QFT.qftCircuit n := by
  rw [circuit, QFT.qftCircuit]
  congr 1
  rw [gates, Circuit.qft]
  change noSwap cutoff (List.range n).reverse ++ QFT.qftSwaps (List.range n).reverse =
    Circuit.qftNoSwap (List.range n).reverse ++ QFT.qftSwaps (List.range n).reverse
  rw [noSwap_eq_qftNoSwap (cutoff := cutoff) _ (by simpa using hcutoff)]

theorem phaseRows_wellFormedAt {level width cutoff start q : Nat}
    (rest : List Nat) (hq : q < width)
    (hrest : ∀ r ∈ rest, r < width) (hneq : q ∉ rest)
    (hlevel : cutoff + 1 ≤ level) :
    (phaseRows cutoff rest start q).all (Gate.wellFormedAt level width) = true := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      have hr : r < width := hrest r (by simp)
      have hrq : r ≠ q := by
        intro h
        apply hneq
        simp [h]
      have hrest' : ∀ s ∈ rest, s < width := by
        intro s hs
        exact hrest s (by simp [hs])
      have hneq' : q ∉ rest := by
        intro h
        exact hneq (by simp [h])
      by_cases hkeep : start + 2 ≤ cutoff
      · have hcphase : (Circuit.cphase (start + 2) r q).all
            (Gate.wellFormedAt level width) = true :=
          QFT.cphase_wellFormedAt (k := start + 2) (a := r) (b := q)
            (by omega) (by omega) hr hq hrq
        simp [phaseRows, hkeep, hcphase, ih hrest' hneq']
      · simp [phaseRows, hkeep, ih hrest' hneq']

theorem noSwap_wellFormedAt {level width cutoff : Nat} (wires : List Nat)
    (hw : ∀ q ∈ wires, q < width) (hnodup : wires.Nodup)
    (hl3 : 3 ≤ level) (hlevel : cutoff + 1 ≤ level) :
    (noSwap cutoff wires).all (Gate.wellFormedAt level width) = true := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      have hq : q < width := hw q (by simp)
      have hrest : ∀ r ∈ rest, r < width := by
        intro r hr
        exact hw r (by simp [hr])
      have hsplit : q ∉ rest ∧ rest.Nodup := by simpa using hnodup
      have hphase := phaseRows_wellFormedAt (start := 0) rest hq hrest hsplit.1 hlevel
      have htail := ih hrest hsplit.2
      simp [noSwap, Gate.wellFormedAt, hq, hl3, hphase, htail]

theorem circuit_wellFormedAt {level n cutoff : Nat}
    (hl3 : 3 ≤ level) (hlevel : cutoff + 1 ≤ level) :
    (circuit n cutoff).wellFormedAt level = true := by
  change (gates cutoff (List.range n).reverse).all
    (Gate.wellFormedAt level n) = true
  rw [gates, List.all_append,
    noSwap_wellFormedAt (List.range n).reverse
      (by intro q hq; simpa using List.mem_range.mp (List.mem_reverse.mp hq))
      (List.nodup_reverse.mpr List.nodup_range) hl3 hlevel,
    QFT.qftSwaps_wellFormedAt (List.range n).reverse
      (by intro q hq; simpa using List.mem_range.mp (List.mem_reverse.mp hq))
      (List.nodup_reverse.mpr List.nodup_range)]
  rfl

theorem phaseRows_length (cutoff : Nat) (rest : List Nat) (start q : Nat) :
    (phaseRows cutoff rest start q).length =
      rowCost cutoff (fun _ => 5) start rest.length := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      rw [phaseRows, List.length_append]
      by_cases hkeep : start + 2 ≤ cutoff
      · rw [if_pos hkeep, QFT.cphase_length (by omega), ih]
        simp [rowCost, hkeep]
      · rw [if_neg hkeep, ih]
        simp [rowCost, hkeep]

theorem phaseRows_countP (cutoff : Nat) (rest : List Nat) (start q : Nat)
    (p : Gate → Bool) (cost : Nat → Nat)
    (hcost : ∀ k a b, 2 ≤ k →
      (Circuit.cphase k a b).countP p = cost k) :
    (phaseRows cutoff rest start q).countP p =
      rowCost cutoff cost start rest.length := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      rw [phaseRows, List.countP_append]
      by_cases hkeep : start + 2 ≤ cutoff
      · rw [if_pos hkeep, hcost (start + 2) r q (by omega), ih]
        simp [rowCost, hkeep]
      · rw [if_neg hkeep, ih]
        simp [rowCost, hkeep]

theorem noSwap_length (cutoff : Nat) (wires : List Nat) :
    (noSwap cutoff wires).length =
      noSwapCost cutoff 1 (fun _ => 5) wires.length := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      rw [noSwap, List.length_append, List.length_cons,
        phaseRows_length, ih]
      simp [noSwapCost]
      omega

theorem noSwap_countP (cutoff : Nat) (wires : List Nat)
    (p : Gate → Bool) (hCost : Nat) (cost : Nat → Nat)
    (hh : ∀ q, (if p (.h q) then 1 else 0) = hCost)
    (hphase : ∀ k a b, 2 ≤ k →
      (Circuit.cphase k a b).countP p = cost k) :
    (noSwap cutoff wires).countP p =
      noSwapCost cutoff hCost cost wires.length := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      rw [noSwap, List.countP_append, List.countP_cons,
        phaseRows_countP cutoff rest 0 q p cost hphase, ih, hh]
      simp [noSwapCost]
      omega

def tCost (k : Nat) : Nat := if k = 2 then 3 else 0

def phaseCost (k : Nat) : Nat := if 3 ≤ k then 3 else 0

theorem cphase_t_cost {k a b : Nat} (hk : 2 ≤ k) :
    (Circuit.cphase k a b).countP Gate.isT = tCost k := by
  by_cases htwo : k = 2
  · subst k
    exact QFT.cphase_t_two a b
  · rw [QFT.cphase_t_of_three (by omega), tCost, if_neg htwo]

theorem cphase_phaseCost {k a b : Nat} (hk : 2 ≤ k) :
    (Circuit.cphase k a b).countP Gate.isPhase = phaseCost k := by
  by_cases hthree : 3 ≤ k
  · rw [QFT.cphase_phase_of_three hthree, phaseCost, if_pos hthree]
  · have htwo : k = 2 := by omega
    subst k
    exact QFT.cphase_phase_two a b

theorem circuit_gateCount (n cutoff : Nat) :
    (circuit n cutoff).gateCount =
      n + 5 * retainedPairs n cutoff + 3 * (n / 2) := by
  change (gates cutoff (List.range n).reverse).length = _
  rw [gates, List.length_append, noSwap_length, QFT.qftSwaps_length]
  simp only [List.length_reverse, List.length_range]
  rw [noSwapCost_const]
  omega

theorem circuit_cnotCount (n cutoff : Nat) :
    (circuit n cutoff).cnotCount =
      2 * retainedPairs n cutoff + 3 * (n / 2) := by
  change (gates cutoff (List.range n).reverse).countP Gate.isTwoQubit = _
  rw [gates, List.countP_append,
    noSwap_countP cutoff _ Gate.isTwoQubit 0 (fun _ => 2)
      (by intro q; rfl) (by intro k a b hk; exact QFT.cphase_cnot hk),
    QFT.qftSwaps_cnot, QFT.qftSwaps_length]
  simp only [List.length_reverse, List.length_range]
  rw [noSwapCost_const]
  omega

theorem circuit_tCount (n cutoff : Nat) :
    (circuit n cutoff).tCount = noSwapCost cutoff 0 tCost n := by
  change (gates cutoff (List.range n).reverse).countP Gate.isT = _
  rw [gates, List.countP_append,
    noSwap_countP cutoff _ Gate.isT 0 tCost
      (by intro q; rfl) (by intro k a b hk; exact cphase_t_cost hk),
    QFT.qftSwaps_t]
  simp

theorem circuit_phaseCount (n cutoff : Nat) :
    (circuit n cutoff).phaseCount = noSwapCost cutoff 0 phaseCost n := by
  change (gates cutoff (List.range n).reverse).countP Gate.isPhase = _
  rw [gates, List.countP_append,
    noSwap_countP cutoff _ Gate.isPhase 0 phaseCost
      (by intro q; rfl) (by intro k a b hk; exact cphase_phaseCost hk),
    QFT.qftSwaps_phase]
  simp

theorem circuit_nonCliffordCount (n cutoff : Nat) :
    (circuit n cutoff).nonCliffordCount =
      3 * retainedPairs n cutoff := by
  change (gates cutoff (List.range n).reverse).countP Gate.isNonClifford = _
  rw [gates, List.countP_append,
    noSwap_countP cutoff _ Gate.isNonClifford 0 (fun _ => 3)
      (by intro q; rfl) (by intro k a b hk; exact QFT.cphase_nonClifford hk),
    QFT.qftSwaps_nonClifford]
  simp only [List.length_reverse, List.length_range]
  rw [noSwapCost_const]
  omega

theorem circuit_cliffordCount (n cutoff : Nat) :
    (circuit n cutoff).cliffordCount =
      n + 2 * retainedPairs n cutoff + 3 * (n / 2) := by
  change (gates cutoff (List.range n).reverse).countP
    (fun g => !g.isNonClifford) = _
  rw [gates, List.countP_append,
    noSwap_countP cutoff _ (fun g => !g.isNonClifford) 1 (fun _ => 2)
      (by intro q; rfl) (by intro k a b hk; exact QFT.cphase_clifford hk),
    QFT.qftSwaps_clifford, QFT.qftSwaps_length, noSwapCost_const]
  simp only [List.length_reverse, List.length_range]
  omega

theorem circuit_hadamardCount (n cutoff : Nat) :
    Circuit.countKind Circuit.GateKind.h (circuit n cutoff) = n := by
  change (gates cutoff (List.range n).reverse).countP
    (fun g => g.kind == Circuit.GateKind.h) = _
  rw [gates, List.countP_append,
    noSwap_countP cutoff _ (fun g => g.kind == Circuit.GateKind.h) 1 (fun _ => 0)
      (by intro q; rfl) (by intro k a b hk; exact QFT.cphase_hadamard hk),
    QFT.qftSwaps_hadamard, noSwapCost_const]
  simp

theorem circuit_toffoliCount (n cutoff : Nat) :
    (circuit n cutoff).toffoliCount = 0 := by
  change (gates cutoff (List.range n).reverse).countP Gate.isCcz = 0
  rw [gates, List.countP_append,
    noSwap_countP cutoff _ Gate.isCcz 0 (fun _ => 0)
      (by intro q; rfl) (by intro k a b hk; exact QFT.cphase_toffoli hk),
    QFT.qftSwaps_toffoli, noSwapCost_const]
  simp

theorem retainedPairs_eq_triangle {n cutoff : Nat} (hcutoff : n ≤ cutoff) :
    retainedPairs n cutoff = QFT.triangle n := by
  have h := congrArg Circuit.nonCliffordCount (circuit_eq_qftCircuit hcutoff)
  rw [circuit_nonCliffordCount, QFT.qftCircuit_nonCliffordCount] at h
  omega

theorem rowCost_one_le (cutoff start count : Nat) :
    rowCost cutoff (fun _ => 1) start count ≤ count := by
  induction count generalizing start with
  | zero => simp [rowCost]
  | succ count ih =>
      by_cases hkeep : start + 2 ≤ cutoff
      · have htail := ih (start + 1)
        simp [rowCost, hkeep]
        omega
      · simp [rowCost, hkeep]
        exact Nat.le_succ_of_le (ih (start + 1))

theorem retainedPairs_le_triangle (n cutoff : Nat) :
    retainedPairs n cutoff ≤ QFT.triangle n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [retainedPairs, noSwapCost, QFT.triangle]
      have hrow := rowCost_one_le cutoff 0 n
      have ih' : noSwapCost cutoff 0 (fun _ => 1) n ≤ QFT.triangle n := by
        simpa [retainedPairs] using ih
      omega

#guard circuit 3 2 == Circuit.ofGates 3
  ([.h 2] ++ Circuit.cphase 2 1 2 ++ [.h 1] ++
    Circuit.cphase 2 0 1 ++ [.h 0] ++ Circuit.swap 2 0)

#guard circuit 3 3 == QFT.qftCircuit 3
#guard circuit 3 2 != QFT.qftCircuit 3
#guard retainedPairs 3 2 == 2
#guard (circuit 3 2).gateCount == 16
#guard (circuit 3 2).cnotCount == 7
#guard (circuit 3 2).tCount == 6
#guard (circuit 3 2).phaseCount == 0
#guard (circuit 3 2).nonCliffordCount == 6
#guard (circuit 3 2).cliffordCount == 10

/-- info: 'VQ.Tests.ApproximateQFT.circuit_eq_qftCircuit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms circuit_eq_qftCircuit

/-- info: 'VQ.Tests.ApproximateQFT.circuit_wellFormedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms circuit_wellFormedAt

/-- info: 'VQ.Tests.ApproximateQFT.circuit_gateCount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms circuit_gateCount

/-- info: 'VQ.Tests.ApproximateQFT.circuit_tCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms circuit_tCount

/-- info: 'VQ.Tests.ApproximateQFT.circuit_phaseCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms circuit_phaseCount

/-- info: 'VQ.Tests.ApproximateQFT.retainedPairs_le_triangle' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms retainedPairs_le_triangle

end VQ.Tests.ApproximateQFT
