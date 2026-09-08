import VQ.Circuit.Compose
import VQ.Reversible.Denote

namespace VQ.Tests.Adjoint

open Algebra Semantics

theorem gate_adjoint_adjoint (g : Gate) : g.adjoint.adjoint = g := by
  cases g <;> rfl

theorem gate_adjoint_wellFormedAt (level width : Nat) (g : Gate) :
    g.adjoint.wellFormedAt level width = g.wellFormedAt level width := by
  cases g <;> rfl

theorem gate_adjoint_isTwoQubit (g : Gate) :
    g.adjoint.isTwoQubit = g.isTwoQubit := by
  cases g <;> rfl

theorem gate_adjoint_isT (g : Gate) : g.adjoint.isT = g.isT := by
  cases g <;> rfl

theorem gate_adjoint_isPhase (g : Gate) : g.adjoint.isPhase = g.isPhase := by
  cases g <;> rfl

theorem gate_adjoint_isCcz (g : Gate) : g.adjoint.isCcz = g.isCcz := by
  cases g <;> rfl

theorem gate_adjoint_isNonClifford (g : Gate) :
    g.adjoint.isNonClifford = g.isNonClifford := by
  cases g <;> rfl

theorem gate_adjoint_isClifford (g : Gate) :
    (!g.adjoint.isNonClifford) = !g.isNonClifford := by
  rw [gate_adjoint_isNonClifford]

theorem countP_map_adjoint (p : Gate → Bool)
    (hp : ∀ g, p g.adjoint = p g) (gs : List Gate) :
    (gs.map Gate.adjoint).countP p = gs.countP p := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.map_cons, List.countP_cons, ih, hp]

theorem circuit_adjoint_adjoint (c : Circuit) : c.adjoint.adjoint = c := by
  cases c with
  | mk width gates =>
      simp only [Circuit.adjoint, List.map_reverse, List.reverse_reverse,
        List.map_map]
      rw [show Gate.adjoint ∘ Gate.adjoint = id from by
        funext g
        exact gate_adjoint_adjoint g, List.map_id]

theorem circuit_adjoint_wellFormedAt (level : Nat) (c : Circuit) :
    c.adjoint.wellFormedAt level = c.wellFormedAt level := by
  change ((c.gates.map Gate.adjoint).reverse).all
      (Gate.wellFormedAt level c.width) =
    c.gates.all (Gate.wellFormedAt level c.width)
  rw [List.all_reverse]
  induction c.gates with
  | nil => rfl
  | cons g gs ih => simp [gate_adjoint_wellFormedAt, ih]

theorem circuit_adjoint_gateCount (c : Circuit) :
    c.adjoint.gateCount = c.gateCount := by
  simp [Circuit.adjoint, Circuit.gateCount]

theorem circuit_adjoint_cnotCount (c : Circuit) :
    c.adjoint.cnotCount = c.cnotCount := by
  simp [Circuit.adjoint, Circuit.cnotCount, List.countP_reverse,
    countP_map_adjoint Gate.isTwoQubit gate_adjoint_isTwoQubit]

theorem circuit_adjoint_tCount (c : Circuit) :
    c.adjoint.tCount = c.tCount := by
  simp [Circuit.adjoint, Circuit.tCount, List.countP_reverse,
    countP_map_adjoint Gate.isT gate_adjoint_isT]

theorem circuit_adjoint_phaseCount (c : Circuit) :
    c.adjoint.phaseCount = c.phaseCount := by
  simp [Circuit.adjoint, Circuit.phaseCount, List.countP_reverse,
    countP_map_adjoint Gate.isPhase gate_adjoint_isPhase]

theorem circuit_adjoint_toffoliCount (c : Circuit) :
    c.adjoint.toffoliCount = c.toffoliCount := by
  simp [Circuit.adjoint, Circuit.toffoliCount, List.countP_reverse,
    countP_map_adjoint Gate.isCcz gate_adjoint_isCcz]

theorem circuit_adjoint_nonCliffordCount (c : Circuit) :
    c.adjoint.nonCliffordCount = c.nonCliffordCount := by
  simp [Circuit.adjoint, Circuit.nonCliffordCount, List.countP_reverse,
    countP_map_adjoint Gate.isNonClifford gate_adjoint_isNonClifford]

theorem circuit_adjoint_cliffordCount (c : Circuit) :
    c.adjoint.cliffordCount = c.cliffordCount := by
  simp [Circuit.adjoint, Circuit.cliffordCount, List.countP_reverse,
    countP_map_adjoint (fun g => !g.isNonClifford) gate_adjoint_isClifford]

theorem phase_mul_phaseInv {level k : Nat} (hk : 1 ≤ k) (hkl : k ≤ level) :
    phase level k * phaseInv level k = Dy.one (deg level) := by
  unfold phase phaseInv
  rw [← Dy.pow_add]
  have he : 2 ^ (level - k) ≤ 2 ^ level :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le level k)
  rw [Nat.add_sub_of_le he]
  have hd : 2 ^ level = deg level + deg level := by
    show 2 ^ level = 2 ^ (level - 1) + 2 ^ (level - 1)
    calc
      2 ^ level = 2 ^ ((level - 1) + 1) := by congr 1; omega
      _ = 2 ^ (level - 1) * 2 := Nat.pow_succ 2 (level - 1)
      _ = 2 ^ (level - 1) + 2 ^ (level - 1) := Nat.mul_two _
  rw [hd, zeta_pow_two_deg]

theorem phase_two_sq {level : Nat} (hl : 2 ≤ level) :
    phase level 2 * phase level 2 = -Dy.one (deg level) := by
  unfold phase
  rw [← Dy.pow_add]
  have he : 2 ^ (level - 2) + 2 ^ (level - 2) = deg level := by
    show 2 ^ (level - 2) + 2 ^ (level - 2) = 2 ^ (level - 1)
    calc
      2 ^ (level - 2) + 2 ^ (level - 2) =
          2 ^ (level - 2) * 2 := (Nat.mul_two _).symm
      _ = 2 ^ ((level - 2) + 1) := (Nat.pow_succ 2 (level - 2)).symm
      _ = 2 ^ (level - 1) := by congr 1; omega
  rw [he, Dy.zeta_pow_d]

theorem flipVec_involutive (q : Nat) (u : Vec d) :
    flipVec q (flipVec q u) = u := by
  apply Vec.ext
  intro i
  exact congrArg u (xor_cancel i q)

theorem cxVec_involutive {a b : Nat} (hab : a ≠ b) (u : Vec d) :
    cxVec a b (cxVec a b u) = u := by
  apply Vec.ext
  intro i
  exact congrArg u (cxIndex_involutive hab i)

theorem diagVec_inverse (q : Nat) {a b : Dy d}
    (hba : b * a = Dy.one d) (u : Vec d) :
    diagVec q b (diagVec q a u) = u := by
  apply Vec.ext
  intro i
  by_cases hb : i.testBit q
  · simp only [diagVec, if_pos hb]
    rw [← Dy.mul_assoc, hba, Dy.one_mul]
  · simp [diagVec, hb]

theorem yVec_involutive {level q : Nat} (hl : 2 ≤ level)
    (u : Vec (deg level)) :
    yVec q (phase level 2) (yVec q (phase level 2) u) = u := by
  have hs := phase_two_sq hl
  apply Vec.ext
  intro i
  have hcancel := xor_cancel i q
  have hbit := testBit_xor_self i q
  cases hi : i.testBit q
  · simp only [yVec, hi, Bool.false_eq_true, if_false, hbit,
      Bool.not_false, if_true, hcancel]
    rw [← Dy.mul_assoc, Dy.neg_mul, hs, Dy.neg_neg, Dy.one_mul]
  · simp only [yVec, hi, if_true, hbit, Bool.not_true,
      Bool.false_eq_true, if_false, hcancel]
    rw [← Dy.mul_assoc, Dy.mul_neg, hs, Dy.neg_neg, Dy.one_mul]

theorem hVec_involutive {level q : Nat} (hl : 3 ≤ level)
    (u : Vec (deg level)) : hVec q (hVec q u) = u := by
  have hs := Reversible.two_invSqrt2_sq (deg_eq_four_mul hl).symm
  apply Vec.ext
  intro i
  have hcancel := xor_cancel i q
  have hbit := testBit_xor_self i q
  cases hi : i.testBit q <;>
    simp only [hVec, hi, hbit, hcancel, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, if_true, if_false] <;>
    grind

theorem cczVec_involutive (a b c : Nat) (u : Vec d) :
    cczVec a b c (cczVec a b c u) = u := by
  apply Vec.ext
  intro i
  by_cases hb : i.testBit a && i.testBit b && i.testBit c
  · simp [cczVec, hb, Dy.neg_neg]
  · simp [cczVec, hb]

theorem gateVec_adjoint_gateVec {level w : Nat} {g : Gate}
    (hw : g.wellFormedAt level w = true) (u : Vec (deg level)) :
    gateVec level w g.adjoint (gateVec level w g u) = u := by
  have hwa : g.adjoint.wellFormedAt level w = true := by
    rw [gate_adjoint_wellFormedAt, hw]
  rw [gateVec_of_wf hwa, gateVec_of_wf hw]
  cases g with
  | h q =>
      have hl : 3 ≤ level := by
        simp [Gate.wellFormedAt] at hw
        omega
      exact hVec_involutive hl u
  | x q => exact flipVec_involutive q u
  | y q =>
      have hl : 2 ≤ level := by
        simp [Gate.wellFormedAt] at hw
        omega
      exact yVec_involutive hl u
  | z q =>
      apply diagVec_inverse
      rw [Dy.neg_mul, Dy.mul_neg, Dy.one_mul, Dy.neg_neg]
  | s q =>
      apply diagVec_inverse
      rw [Dy.mul_comm, phase_mul_phaseInv (by omega) (by
        simp [Gate.wellFormedAt] at hw
        omega)]
  | sdg q =>
      apply diagVec_inverse
      exact phase_mul_phaseInv (by omega) (by
        simp [Gate.wellFormedAt] at hw
        omega)
  | t q =>
      apply diagVec_inverse
      rw [Dy.mul_comm, phase_mul_phaseInv (by omega) (by
        simp [Gate.wellFormedAt] at hw
        omega)]
  | tdg q =>
      apply diagVec_inverse
      exact phase_mul_phaseInv (by omega) (by
        simp [Gate.wellFormedAt] at hw
        omega)
  | p k q =>
      apply diagVec_inverse
      have hk : 1 ≤ k := by
        simp [Gate.wellFormedAt] at hw
        omega
      have hkl : k ≤ level := by
        simp [Gate.wellFormedAt] at hw
        omega
      rw [Dy.mul_comm, phase_mul_phaseInv hk hkl]
  | pdg k q =>
      apply diagVec_inverse
      have hk : 1 ≤ k := by
        simp [Gate.wellFormedAt] at hw
        omega
      have hkl : k ≤ level := by
        simp [Gate.wellFormedAt] at hw
        omega
      exact phase_mul_phaseInv hk hkl
  | cx a b =>
      have hab : a ≠ b := by
        simp [Gate.wellFormedAt] at hw
        exact hw.2
      exact cxVec_involutive hab u
  | ccz a b c => exact cczVec_involutive a b c u

theorem runGates_adjoint_runGates {level w : Nat} {gs : List Gate}
    (hgs : ∀ g ∈ gs, g.wellFormedAt level w = true)
    (u : Vec (deg level)) :
    runGates level w (gs.map Gate.adjoint).reverse
        (runGates level w gs u) = u := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih =>
      have hg : g.wellFormedAt level w = true := hgs g List.mem_cons_self
      have hrest : ∀ h ∈ gs, h.wellFormedAt level w = true := by
        intro h hh
        exact hgs h (List.mem_cons_of_mem g hh)
      simp only [List.map_cons, List.reverse_cons, runGates_cons,
        runGates_append, runGates_nil]
      rw [ih hrest, gateVec_adjoint_gateVec hg]

theorem run_adjoint_run {level : Nat} {c : Circuit}
    (hc : c.wellFormedAt level = true) (u : Vec (deg level)) :
    run level c.adjoint (run level c u) = u := by
  cases c with
  | mk w gs =>
      change runGates level w (gs.map Gate.adjoint).reverse
          (runGates level w gs u) = u
      apply runGates_adjoint_runGates
      simpa only [Circuit.wellFormedAt, List.all_eq_true] using hc

theorem run_run_adjoint {level : Nat} {c : Circuit}
    (hc : c.wellFormedAt level = true) (u : Vec (deg level)) :
    run level c (run level c.adjoint u) = u := by
  have hca : c.adjoint.wellFormedAt level = true := by
    rw [circuit_adjoint_wellFormedAt, hc]
  have h := run_adjoint_run (c := c.adjoint) hca u
  rwa [circuit_adjoint_adjoint] at h

/-! ## Axiom guards -/

/-- info: 'VQ.Tests.Adjoint.circuit_adjoint_adjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms circuit_adjoint_adjoint

/-- info: 'VQ.Tests.Adjoint.circuit_adjoint_wellFormedAt' depends on axioms: [propext] -/
#guard_msgs in #print axioms circuit_adjoint_wellFormedAt

/-- info: 'VQ.Tests.Adjoint.circuit_adjoint_cliffordCount' depends on axioms: [propext] -/
#guard_msgs in #print axioms circuit_adjoint_cliffordCount

/-- info: 'VQ.Tests.Adjoint.gateVec_adjoint_gateVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gateVec_adjoint_gateVec

/-- info: 'VQ.Tests.Adjoint.run_adjoint_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_adjoint_run

/-- info: 'VQ.Tests.Adjoint.run_run_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_run_adjoint

end VQ.Tests.Adjoint
