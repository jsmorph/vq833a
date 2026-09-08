/-
The Clifford+T expansion of `ccz` and its denotational equivalence proof.

`toffoliCount c` and `tCount (Circuit.expand c)` are the two resource measures the
literature quotes for the same circuit: four Toffolis before Gidney and Fowler
(arXiv:1812.01238) and twenty-eight T gates after decomposition.  Two numbers
attached to two gate lists are two claims until something says the gate lists
denote one operator.  `denote_expand` is that theorem.

The proof is the phase-polynomial identity `4xyz = x + y + z - (x⊕y) - (y⊕z) -
(x⊕z) + (x⊕y⊕z)` read in the exponent of the eighth root of unity: the thirteen
gates apply `ζ` to a sequence of parities, the six CNOTs restore the index they
started from, and the accumulated exponent is `4 * deg level` when the three
wires are not all set and `deg level` when they are.  `ζ ^ deg level = -1` is
the ring's defining relation, so the composite is the CCZ phase.
-/
import VQ.Semantics.Circuit
import VQ.Circuit.Library

namespace VQ
namespace Semantics

open Algebra

variable {level w a b c : Nat}

/-! ## Powers of the root of unity

At level three and above the ring degree is four times `2 ^ (level - 3)`, and
the T phase is `ζ ^ 2 ^ (level - 3)`.  Every exponent in the decomposition is a multiple of
that step, and the two that arise are `deg level` and `4 * deg level`. -/

theorem deg_eq_four_mul (hl : 3 ≤ level) : deg level = 4 * 2 ^ (level - 3) := by
  show 2 ^ (level - 1) = 4 * 2 ^ (level - 3)
  rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]
  congr 1
  omega

theorem two_pow_eq_eight_mul (hl : 3 ≤ level) : (2 : Nat) ^ level = 8 * 2 ^ (level - 3) := by
  rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_add]
  congr 1
  omega

theorem zeta_pow_two_deg :
    Dy.zeta (deg level) ^ (deg level + deg level) = Dy.one (deg level) := by
  rw [Dy.pow_add, Dy.zeta_pow_d, Dy.neg_mul, Dy.mul_neg, Dy.one_mul, Dy.neg_neg]

/-- No phase: none of the four `t` gates or two `tdg` gates is enabled. -/
theorem smul_basis_of_pow_zero {N j : Nat} (h : N = 0) :
    (Dy.zeta (deg level) ^ N) • (basis j : Vec (deg level)) = basis j := by
  subst h
  exact Vec.one_smul _

/-- The accumulated phase when the three wires are not all set. -/
theorem smul_basis_of_pow_four {N j : Nat} (h : N = 4 * deg level) :
    (Dy.zeta (deg level) ^ N) • (basis j : Vec (deg level)) = basis j := by
  subst h
  rw [show 4 * deg level = (deg level + deg level) + (deg level + deg level) from by omega,
    Dy.pow_add, zeta_pow_two_deg, Dy.one_mul, Vec.one_smul]

/-- The accumulated phase when all three wires are set: the ring's defining
relation `ζ ^ d = -1`. -/
theorem smul_basis_of_pow_deg {N j : Nat} (h : N = deg level) :
    (Dy.zeta (deg level) ^ N) • (basis j : Vec (deg level))
      = (-Dy.one (deg level)) • (basis j : Vec (deg level)) := by
  subst h
  rw [Dy.zeta_pow_d]

/-! ## Gate action on a phased basis state

Every gate of the expansion is a CNOT, which permutes the index and leaves the
scalar alone, or a diagonal gate, which fixes the index and multiplies the
scalar by a power of `ζ`.  The expansion proof composes these lemmas over the
gate list. -/

theorem smul_basis_cx {q r : Nat} (hq : q < w) (hr : r < w) (hqr : q ≠ r)
    (s : Dy (deg level)) (m : Nat) :
    gateVec level w (Gate.cx q r) (s • (basis m : Vec (deg level)))
      = s • (basis (cxIndex q r m) : Vec (deg level)) := by
  rw [gateVec_smul, apply_cx hq hr hqr]
  rfl

theorem smul_basis_t {q : Nat} (hq : q < w) (hl : 3 ≤ level) (n m : Nat) :
    gateVec level w (Gate.t q) ((Dy.zeta (deg level) ^ n) • (basis m : Vec (deg level)))
      = (Dy.zeta (deg level) ^ (n + (if m.testBit q then 2 ^ (level - 3) else 0)))
        • (basis m : Vec (deg level)) := by
  rw [gateVec_smul, apply_t hq hl]
  by_cases hbit : m.testBit q = true
  · rw [if_pos hbit, if_pos hbit, Vec.smul_smul]
    congr 1
    exact (Dy.pow_add _ n (2 ^ (level - 3))).symm
  · rw [if_neg hbit, if_neg hbit, Nat.add_zero]

theorem smul_basis_tdg {q : Nat} (hq : q < w) (hl : 3 ≤ level) (n m : Nat) :
    gateVec level w (Gate.tdg q) ((Dy.zeta (deg level) ^ n) • (basis m : Vec (deg level)))
      = (Dy.zeta (deg level) ^ (n + (if m.testBit q then 2 ^ level - 2 ^ (level - 3) else 0)))
        • (basis m : Vec (deg level)) := by
  rw [gateVec_smul, apply_tdg hq hl]
  by_cases hbit : m.testBit q = true
  · rw [if_pos hbit, if_pos hbit, Vec.smul_smul]
    congr 1
    exact (Dy.pow_add _ n (2 ^ level - 2 ^ (level - 3))).symm
  · rw [if_neg hbit, if_neg hbit, Nat.add_zero]

/-! ## The expansion of one `ccz` -/

/--
The thirteen-gate Clifford+T list acts on a basis state exactly as `ccz` does.

The eight cases are the eight settings of the three wires.  In seven of them the
two enabled `t` gates and two enabled `tdg` gates contribute
`2 * 2 ^ (level - 3) + 2 * (2 ^ level - 2 ^ (level - 3)) = 4 * deg level`.  In the
eighth all four `t` gates are enabled and contribute `deg level`.
-/
theorem run_cczT (hl : 3 ≤ level) (ha : a < w) (hb : b < w) (hc : c < w)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (j : Nat) :
    runGates level w (Circuit.cczT a b c) (basis j : Vec (deg level))
      = gateVec level w (Gate.ccz a b c) (basis j) := by
  have hd : deg level = 4 * 2 ^ (level - 3) := deg_eq_four_mul hl
  have h8 : (2 : Nat) ^ level = 8 * 2 ^ (level - 3) := two_pow_eq_eight_mul hl
  have hstart : (basis j : Vec (deg level))
      = (Dy.zeta (deg level) ^ 0) • (basis j : Vec (deg level)) := by
    show _ = Dy.one (deg level) • _
    exact (Vec.one_smul _).symm
  rw [apply_ccz ha hb hc hab hbc hac (by omega)]
  conv => lhs; rw [hstart]
  cases hja : j.testBit a <;> cases hjb : j.testBit b <;> cases hjc : j.testBit c <;>
    simp only [Circuit.cczT, runGates_cons, runGates_nil, cxIndex,
      smul_basis_cx hb hc hbc, smul_basis_cx ha hc hac, smul_basis_cx ha hb hab,
      smul_basis_t ha hl, smul_basis_t hb hl, smul_basis_t hc hl,
      smul_basis_tdg hb hl, smul_basis_tdg hc hl,
      hja, hjb, hjc, testBit_xor_self, testBit_xor_of_ne hab, testBit_xor_of_ne hac,
      testBit_xor_of_ne hbc, xor_cancel, Bool.not_true, Bool.not_false,
      Bool.and_true, Bool.and_false, Bool.false_eq_true, if_true, if_false,
      Nat.add_zero, Nat.zero_add] <;>
    first
      | (refine smul_basis_of_pow_zero ?_; omega)
      | (refine smul_basis_of_pow_four ?_; omega)
      | (refine smul_basis_of_pow_deg ?_; omega)

/-! ## The expansion of a circuit -/

/-- One gate, expanded, on a state supported on the block the width addresses.

The support hypothesis is what carries the basis identity to a general state: a
state supported below `2 ^ w` is a finite combination of the basis states there,
and both sides are linear. -/
theorem runGates_expandGate (hl : 3 ≤ level) (g : Gate) {u : Vec (deg level)}
    (hu : WFVec (2 ^ w) u) :
    runGates level w (Circuit.expandGate g) u = gateVec level w g u := by
  cases g with
  | h q | x q | y q | z q | s q | sdg q | t q | tdg q => rfl
  | p k q | pdg k q => rfl
  | cx q r => rfl
  | ccz a b c =>
    by_cases hwf : (Gate.ccz a b c).wellFormedAt level w = true
    · have hf : ((a < w ∧ b < w ∧ c < w) ∧ (a ≠ b ∧ b ≠ c ∧ a ≠ c)) ∧ 1 ≤ level := by
        simpa [Gate.wellFormedAt, and_assoc] using hwf
      obtain ⟨⟨⟨haw, hbw, hcw⟩, hab, hbc, hac⟩, _⟩ := hf
      have hgv : ∀ (n : Nat) (f : Nat → Vec (deg level)),
          gateVec level w (Gate.ccz a b c) (vsum n f)
            = vsum n (fun k => gateVec level w (Gate.ccz a b c) (f k)) :=
        fun n f => runGates_vsum level w [Gate.ccz a b c] n f
      show runGates level w (Circuit.cczT a b c) u = _
      conv => lhs; rw [eq_vsum_basis hu]
      conv => rhs; rw [eq_vsum_basis hu]
      rw [runGates_vsum, hgv]
      refine vsum_congr (fun k _ => ?_)
      rw [runGates_smul, gateVec_smul, run_cczT hl haw hbw hcw hab hbc hac k]
    · have hbad : ∃ g' ∈ Circuit.cczT a b c, g'.wellFormedAt level w = false := by
        by_cases haw : a < w
        · by_cases hbw : b < w
          · by_cases hcw : c < w
            · by_cases hab : a = b
              · exact ⟨Gate.cx a b, by simp [Circuit.cczT],
                  by simp [Gate.wellFormedAt, hab]⟩
              · by_cases hbc : b = c
                · exact ⟨Gate.cx b c, by simp [Circuit.cczT],
                    by simp [Gate.wellFormedAt, hbc]⟩
                · by_cases hac : a = c
                  · exact ⟨Gate.cx a c, by simp [Circuit.cczT],
                      by simp [Gate.wellFormedAt, hac]⟩
                  · exact absurd (by
                      simp [Gate.wellFormedAt, haw, hbw, hcw, hab, hbc, hac]; omega) hwf
            · exact ⟨Gate.t c, by simp [Circuit.cczT], by simp [Gate.wellFormedAt, hcw]⟩
          · exact ⟨Gate.t b, by simp [Circuit.cczT], by simp [Gate.wellFormedAt, hbw]⟩
        · exact ⟨Gate.t a, by simp [Circuit.cczT], by simp [Gate.wellFormedAt, haw]⟩
      obtain ⟨g', hmem, hbadg⟩ := hbad
      show runGates level w (Circuit.cczT a b c) u = _
      rw [runGates_eq_zero_of_mem hmem hbadg,
        gateVec_of_not_wf (Bool.eq_false_iff.mpr hwf)]

theorem runGates_expand (hl : 3 ≤ level) (gs : List Gate) {u : Vec (deg level)}
    (hu : WFVec (2 ^ w) u) :
    runGates level w (gs.flatMap Circuit.expandGate) u = runGates level w gs u := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatMap_cons, runGates_append, runGates_expandGate hl g hu, runGates_cons]
    exact ih (wfVec_gateVec level w g hu)

/--
The expansion theorem.  A circuit and its Clifford+T expansion denote the
same matrix on the block their width addresses.

`MatEq` constrains the `2 ^ w` rows and columns in the circuit's block.
`denote` repeats that block on higher cosets, while `WFMat (2 ^ w) (2 ^ w)`
requires zero entries outside it.  Circuit-matrix statements therefore use the
bounded relation.

`3 ≤ level` is the hypothesis the expansion needs and the gate does not.  `ccz`
introduces only the amplitude `-1`, which lies in `R(1)`.  Its decomposition
introduces `exp (2 * pi * I / 8)`, which needs `R(3)`.  At level one or two the
expansion denotes zero, because its `t` gates are ill formed there, and the
circuit it came from does not.
-/
theorem denote_expand (hl : 3 ≤ level) (c : Circuit) :
    MatEq (2 ^ c.width) (2 ^ c.width)
      (denote level (Circuit.expand c)) (denote level c) :=
  fun i _ _j hj => congrFun (runGates_expand hl c.gates (wfVec_basis hj)) i

/-- The expansion preserves the declared width, so the block the theorem speaks
about is the same block for both circuits. -/
theorem width_expand (c : Circuit) : (Circuit.expand c).width = c.width := rfl

end Semantics
end VQ
