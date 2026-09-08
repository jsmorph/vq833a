/-
Unitarity, over the complex numbers.

The complex matrix of a circuit on the block addressed by its width satisfies
`Mᴴ * M = 1` exactly when the circuit passes `Circuit.wellFormedAt`.

The argument goes through two shapes.  A one-wire gate is `M` on its wire and
the identity elsewhere, so a column of the block matrix has two nonzero entries
and the inner product of two columns collapses to a column of `Mᴴ * M`.  CNOT is
a permutation matrix, whose unitarity needs only that the permutation is
injective.  Composition is the matrix product on the block, so the circuit
follows by induction over the gate list.
-/
import VQMathlib.Semantics.Gate
import VQ.Semantics.Circuit
import Mathlib.LinearAlgebra.UnitaryGroup

namespace VQBridge

open VQ VQ.Algebra VQ.Semantics
open scoped Matrix

/-! ## Two-by-two unitarity -/

theorem unitary_two {M : Matrix (Fin 2) (Fin 2) ℂ}
    (h00 : star (M 0 0) * M 0 0 + star (M 1 0) * M 1 0 = 1)
    (h01 : star (M 0 0) * M 0 1 + star (M 1 0) * M 1 1 = 0)
    (h10 : star (M 0 1) * M 0 0 + star (M 1 1) * M 1 0 = 0)
    (h11 : star (M 0 1) * M 0 1 + star (M 1 1) * M 1 1 = 1) :
    Mᴴ * M = 1 := by
  ext x y
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply]
  fin_cases x <;> fin_cases y
  · simpa using h00
  · simpa using h01
  · simpa using h10
  · simpa using h11

/-- The phase gates are `diag (1, c)` with `c` on the unit circle. -/
theorem unitary_diag {c : ℂ} (hc : star c * c = 1) :
    (!![1, 0; 0, c] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * !![1, 0; 0, c] = 1 := by
  rw [Complex.star_def] at hc
  refine unitary_two ?_ ?_ ?_ ?_ <;> simp [hc]

theorem star_exp_ofReal_mul_I (r : ℝ) :
    star (Complex.exp ((r : ℂ) * Complex.I)) * Complex.exp ((r : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj,
    show (starRingEnd ℂ) ((r : ℂ) * Complex.I) = -((r : ℂ) * Complex.I) from by
      simp [Complex.conj_ofReal, Complex.conj_I],
    ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

theorem unitary_matX : matXᴴ * matX = 1 := by
  refine unitary_two ?_ ?_ ?_ ?_ <;> simp [matX]

theorem unitary_matY : matYᴴ * matY = 1 := by
  refine unitary_two ?_ ?_ ?_ ?_ <;> simp [matY]

theorem unitary_matZ : matZᴴ * matZ = 1 := by
  refine unitary_two ?_ ?_ ?_ ?_ <;> simp [matZ]

theorem unitary_matS : matSᴴ * matS = 1 := by
  refine unitary_two ?_ ?_ ?_ ?_ <;> simp [matS]

theorem unitary_matSdg : matSdgᴴ * matSdg = 1 := by
  refine unitary_two ?_ ?_ ?_ ?_ <;> simp [matSdg]

theorem unitary_matT : matTᴴ * matT = 1 := by
  refine unitary_diag ?_
  rw [show (Real.pi : ℂ) * Complex.I / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I from by
    push_cast; ring]
  exact star_exp_ofReal_mul_I _

theorem unitary_matTdg : matTdgᴴ * matTdg = 1 := by
  refine unitary_diag ?_
  rw [show -((Real.pi : ℂ) * Complex.I / 4) = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I from by
    push_cast; ring]
  exact star_exp_ofReal_mul_I _

theorem unitary_matP (k : Nat) : (matP k)ᴴ * matP k = 1 := by
  refine unitary_diag ?_
  rw [show 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ k : Nat) : ℂ)
      = ((2 * Real.pi / 2 ^ k : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  exact star_exp_ofReal_mul_I _

theorem unitary_matPdg (k : Nat) : (matPdg k)ᴴ * matPdg k = 1 := by
  refine unitary_diag ?_
  rw [show -(2 * (Real.pi : ℂ) * Complex.I / ((2 ^ k : Nat) : ℂ))
      = ((-(2 * Real.pi / 2 ^ k) : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  exact star_exp_ofReal_mul_I _

theorem unitary_matH : matHᴴ * matH = 1 := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := sqrt_two_sq
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := sqrt_two_ne_zero
  have hstar : star ((1 : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) = 1 / ((Real.sqrt 2 : ℝ) : ℂ) := by
    simp [Complex.conj_ofReal]
  have e00 : matH 0 0 = 1 / ((Real.sqrt 2 : ℝ) : ℂ) := by simp [matH]
  have e01 : matH 0 1 = 1 / ((Real.sqrt 2 : ℝ) : ℂ) := by simp [matH]
  have e10 : matH 1 0 = 1 / ((Real.sqrt 2 : ℝ) : ℂ) := by simp [matH]
  have e11 : matH 1 1 = -(1 / ((Real.sqrt 2 : ℝ) : ℂ)) := by simp [matH]
  refine unitary_two ?_ ?_ ?_ ?_ <;>
    simp only [e00, e01, e10, e11, star_neg, hstar] <;>
    field_simp <;>
    rw [hs] <;>
    ring

/-! ## Block matrix of a primitive gate -/

/-- The complex matrix of a gate on the block the width addresses. -/
noncomputable def cgate (level w : Nat) (g : Gate) : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ :=
  fun i j => dtoC (gateVec level w g (basis j) i)

/-- The complex matrix of a gate list on the block the width addresses. -/
noncomputable def cmat (level w : Nat) (gs : List Gate) : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ :=
  fun i j => dtoC (denote level (Circuit.mk w gs) i j)

theorem two_pow_lt {q w : Nat} (hq : q < w) : (1 <<< q) < 2 ^ w := by
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_of_lt (by omega) hq

/-- Flipping wire `q` stays inside the block. -/
def flipFin {w : Nat} (q : Nat) (hq : q < w) (i : Fin (2 ^ w)) : Fin (2 ^ w) :=
  ⟨(i : Nat) ^^^ (1 <<< q), Nat.xor_lt_two_pow i.isLt (two_pow_lt hq)⟩

/-- The matrix of `M` acting on wire `q`, on the block. -/
noncomputable def wireMat (M : Matrix (Fin 2) (Fin 2) ℂ) (w q : Nat) :
    Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ := fun i j => wireEntry M q (i : Nat) (j : Nat)

/-! ## Permutation matrices -/

theorem unitary_of_perm {n : Nat} {M : Matrix (Fin n) (Fin n) ℂ} {σ : Fin n → Fin n}
    (hσ : Function.Injective σ) (hM : ∀ i j, M i j = if i = σ j then 1 else 0) :
    Mᴴ * M = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin n, Mᴴ i k * M k j
      = if k = σ i then (if σ i = σ j then 1 else 0) else 0 := by
    intro k
    rw [Matrix.conjTranspose_apply, hM, hM]
    by_cases h : k = σ i
    · subst h
      rw [if_pos rfl, if_pos rfl, star_one, one_mul]
    · rw [if_neg h, if_neg h, star_zero, zero_mul]
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    Finset.sum_ite_eq' Finset.univ (σ i) (fun _ => if σ i = σ j then 1 else 0), if_pos (by simp)]
  by_cases h : i = j
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun he => h (hσ he))]

/-! ## Diagonal matrices

A diagonal matrix whose entries lie on the unit circle is unitary, and the
argument is shorter than the one-wire argument below because the sum collapses
to a single term.  `ccz` is the primitive this covers: it moves no amplitude and
its only entry off one is `-1`. -/

theorem unitary_of_diag {n : Nat} {M : Matrix (Fin n) (Fin n) ℂ} {f : Fin n → ℂ}
    (hf : ∀ i, star (f i) * f i = 1) (hM : ∀ i j, M i j = if i = j then f i else 0) :
    Mᴴ * M = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin n, Mᴴ i k * M k j
      = if k = i then (if i = j then star (f i) * f i else 0) else 0 := by
    intro k
    rw [Matrix.conjTranspose_apply, hM k i, hM k j]
    by_cases h : k = i
    · subst h
      rw [if_pos rfl, if_pos rfl]
      by_cases h2 : k = j
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2, mul_zero]
    · rw [if_neg h, if_neg h, star_zero, zero_mul]
  rw [Finset.sum_congr rfl (fun k _ => hterm k),
    Finset.sum_ite_eq' Finset.univ i (fun _ => if i = j then star (f i) * f i else 0),
    if_pos (Finset.mem_univ i)]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, hf i]
  · rw [if_neg h, if_neg h]

/-! ## One-wire gates on the block -/

theorem unitary_wireMat {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : Mᴴ * M = 1) {w q : Nat}
    (hq : q < w) : (wireMat M w q)ᴴ * wireMat M w q = 1 := by
  have key : ∀ x y : Fin 2, star (M 0 x) * M 0 y + star (M 1 x) * M 1 y
      = if x = y then 1 else 0 := by
    intro x y
    have h := congrFun (congrFun hM x) y
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply] at h
    exact h
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hFval : ((flipFin q hq i : Fin (2 ^ w)) : Nat) = (i : Nat) ^^^ (1 <<< q) := rfl
  have hFne : (flipFin q hq i) ≠ i := fun he => xor_ne_self (i : Nat) q (by rw [← hFval, he])
  -- On the two indices that agree with `i` off wire `q`, the entry is `M` at the bits.
  have hagree : ∀ k j' : Fin (2 ^ w), (k = i ∨ k = flipFin q hq i) →
      (j' = i ∨ j' = flipFin q hq i) →
      wireMat M w q k j' = M (bitIdx (k : Nat) q) (bitIdx (j' : Nat) q) := by
    rintro k j' (rfl | rfl) (rfl | rfl)
    · exact if_pos (Or.inl rfl)
    · exact if_pos (Or.inr (by rw [hFval, xor_cancel]))
    · exact if_pos (Or.inr hFval)
    · exact if_pos (Or.inl rfl)
  -- Off those two indices the entry vanishes.
  have hout : ∀ k j' : Fin (2 ^ w), (k = i ∨ k = flipFin q hq i) →
      j' ≠ i → j' ≠ flipFin q hq i → wireMat M w q k j' = 0 := by
    rintro k j' (rfl | rfl) h1 h2
    · refine if_neg ?_
      rintro (h | h)
      · exact h1 (Fin.ext h.symm)
      · exact h2 (Fin.ext (by rw [hFval, h, xor_cancel]))
    · refine if_neg ?_
      rintro (h | h)
      · exact h2 (Fin.ext h.symm)
      · exact h1 (Fin.ext (by rw [← xor_cancel (j' : Nat) q, ← h, hFval, xor_cancel]))
  have hzero : ∀ k : Fin (2 ^ w), k ∉ ({i, flipFin q hq i} : Finset (Fin (2 ^ w))) →
      (wireMat M w q)ᴴ i k * wireMat M w q k j = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [Matrix.conjTranspose_apply,
      show wireMat M w q k i = 0 from if_neg (by
        rintro (h | h)
        · exact hk.1 (Fin.ext h)
        · exact hk.2 (Fin.ext (by rw [hFval]; exact h))),
      star_zero, zero_mul]
  have hbitne : bitIdx (i : Nat) q ≠ bitIdx ((flipFin q hq i : Fin (2 ^ w)) : Nat) q := by
    rw [hFval, bitIdx, bitIdx, testBit_xor_self]
    cases hb : (i : Nat).testBit q <;> simp
  rw [← Finset.sum_subset (Finset.subset_univ ({i, flipFin q hq i} : Finset (Fin (2 ^ w))))
      (fun k _ hk => hzero k hk),
    Finset.sum_pair (Ne.symm hFne), Matrix.conjTranspose_apply, Matrix.conjTranspose_apply,
    hagree i i (Or.inl rfl) (Or.inl rfl),
    hagree (flipFin q hq i) i (Or.inr rfl) (Or.inl rfl)]
  by_cases hj : j = i ∨ j = flipFin q hq i
  · rw [hagree i j (Or.inl rfl) hj, hagree (flipFin q hq i) j (Or.inr rfl) hj,
      show star (M (bitIdx (i : Nat) q) (bitIdx (i : Nat) q))
              * M (bitIdx (i : Nat) q) (bitIdx (j : Nat) q)
            + star (M (bitIdx ((flipFin q hq i : Fin (2 ^ w)) : Nat) q) (bitIdx (i : Nat) q))
              * M (bitIdx ((flipFin q hq i : Fin (2 ^ w)) : Nat) q) (bitIdx (j : Nat) q)
          = if bitIdx (i : Nat) q = bitIdx (j : Nat) q then 1 else 0 from by
        cases hb : (i : Nat).testBit q
        · rw [show bitIdx (i : Nat) q = 0 from by rw [bitIdx, hb]; rfl,
            show bitIdx ((flipFin q hq i : Fin (2 ^ w)) : Nat) q = 1 from by
              rw [hFval, bitIdx, testBit_xor_self, hb]; rfl]
          exact key 0 _
        · rw [show bitIdx (i : Nat) q = 1 from by rw [bitIdx, hb]; rfl,
            show bitIdx ((flipFin q hq i : Fin (2 ^ w)) : Nat) q = 0 from by
              rw [hFval, bitIdx, testBit_xor_self, hb]; rfl, add_comm]
          exact key 1 _]
    rcases hj with h | h
    · rw [h, if_pos rfl, if_pos rfl]
    · rw [h, if_neg hbitne, if_neg (Ne.symm hFne)]
  · rw [not_or] at hj
    rw [hout i j (Or.inl rfl) hj.1 hj.2, hout (flipFin q hq i) j (Or.inr rfl) hj.1 hj.2,
      mul_zero, mul_zero, add_zero, if_neg (fun he => hj.1 he.symm)]

/-! ## Primitive-gate unitarity -/

theorem cgate_eq_wireMat_of {level w : Nat} {g : Gate} {M : Matrix (Fin 2) (Fin 2) ℂ} {q : Nat}
    (h : ∀ i j : Nat, dtoC (gateVec level w g (basis j) i) = wireEntry M q i j) :
    cgate level w g = wireMat M w q :=
  Matrix.ext (fun i j => h i j)

theorem unitary_cgate {level w : Nat} {g : Gate} (hg : g.wellFormedAt level w = true) :
    (cgate level w g)ᴴ * cgate level w g = 1 := by
  cases g with
  | x q =>
    have hq : q < w := by simpa [Gate.wellFormedAt] using hg
    rw [cgate_eq_wireMat_of (fun i j => gate_x hq i j)]
    exact unitary_wireMat unitary_matX hq
  | z q =>
    have h : q < w ∧ 1 ≤ level := by simpa [Gate.wellFormedAt] using hg
    rw [cgate_eq_wireMat_of (fun i j => gate_z h.1 h.2 i j)]
    exact unitary_wireMat unitary_matZ h.1
  | y q =>
    have h : q < w ∧ 2 ≤ level := by simpa [Gate.wellFormedAt] using hg
    rw [cgate_eq_wireMat_of (fun i j => gate_y h.1 h.2 i j)]
    exact unitary_wireMat unitary_matY h.1
  | s q =>
    have h : q < w ∧ 2 ≤ level := by simpa [Gate.wellFormedAt] using hg
    rw [cgate_eq_wireMat_of (fun i j => gate_s h.1 h.2 i j)]
    exact unitary_wireMat unitary_matS h.1
  | sdg q =>
    have h : q < w ∧ 2 ≤ level := by simpa [Gate.wellFormedAt] using hg
    rw [cgate_eq_wireMat_of (fun i j => gate_sdg h.1 h.2 i j)]
    exact unitary_wireMat unitary_matSdg h.1
  | t q =>
    have h : q < w ∧ 3 ≤ level := by simpa [Gate.wellFormedAt] using hg
    rw [cgate_eq_wireMat_of (fun i j => gate_t h.1 h.2 i j)]
    exact unitary_wireMat unitary_matT h.1
  | tdg q =>
    have h : q < w ∧ 3 ≤ level := by simpa [Gate.wellFormedAt] using hg
    rw [cgate_eq_wireMat_of (fun i j => gate_tdg h.1 h.2 i j)]
    exact unitary_wireMat unitary_matTdg h.1
  | h q =>
    have h : q < w ∧ 3 ≤ level := by simpa [Gate.wellFormedAt] using hg
    rw [cgate_eq_wireMat_of (fun i j => gate_h h.1 h.2 i j)]
    exact unitary_wireMat unitary_matH h.1
  | p k q =>
    have h : (q < w ∧ 4 ≤ k) ∧ k ≤ level := by simpa [Gate.wellFormedAt, and_assoc] using hg
    rw [cgate_eq_wireMat_of (fun i j => gate_p h.1.1 h.1.2 h.2 i j)]
    exact unitary_wireMat (unitary_matP k) h.1.1
  | pdg k q =>
    have h : (q < w ∧ 4 ≤ k) ∧ k ≤ level := by simpa [Gate.wellFormedAt, and_assoc] using hg
    rw [cgate_eq_wireMat_of (fun i j => gate_pdg h.1.1 h.1.2 h.2 i j)]
    exact unitary_wireMat (unitary_matPdg k) h.1.1
  | ccz a b c =>
    have h : ((a < w ∧ b < w ∧ c < w) ∧ (a ≠ b ∧ b ≠ c ∧ a ≠ c)) ∧ 1 ≤ level := by
      simpa [Gate.wellFormedAt, and_assoc] using hg
    obtain ⟨⟨⟨ha, hb, hc⟩, hab, hbc, hac⟩, hl⟩ := h
    refine unitary_of_diag
      (f := fun i : Fin (2 ^ w) =>
        if (i : Nat).testBit a && (i : Nat).testBit b && (i : Nat).testBit c then -1 else 1)
      (fun i => ?_) (fun i j => ?_)
    · by_cases hbit : (i : Nat).testBit a && (i : Nat).testBit b && (i : Nat).testBit c <;>
        simp [hbit]
    · show dtoC (gateVec level w (Gate.ccz a b c) (basis (j : Nat)) (i : Nat)) = _
      rw [gateVec_of_wf (by simp [Gate.wellFormedAt, ha, hb, hc, hab, hbc, hac, hl])]
      show dtoC (cczVec a b c (basis (j : Nat)) (i : Nat)) = _
      rw [cczVec_basis_apply (deg_pos level)]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (fun he => hij (Fin.ext he)), if_neg hij]
  | cx a b =>
    have h : (a < w ∧ b < w) ∧ a ≠ b := by simpa [Gate.wellFormedAt, and_assoc] using hg
    obtain ⟨⟨ha, hb⟩, hab⟩ := h
    have hbound : ∀ j : Fin (2 ^ w), cxIndex a b (j : Nat) < 2 ^ w := by
      intro j
      rw [cxIndex]
      by_cases hc : (j : Nat).testBit a
      · rw [if_pos hc]
        exact Nat.xor_lt_two_pow j.isLt (two_pow_lt hb)
      · rw [if_neg hc]
        exact j.isLt
    refine unitary_of_perm (σ := fun j => ⟨cxIndex a b (j : Nat), hbound j⟩) ?_ ?_
    · intro x y hxy
      have h1 : cxIndex a b (x : Nat) = cxIndex a b (y : Nat) := congrArg Fin.val hxy
      refine Fin.ext ?_
      have := congrArg (cxIndex a b) h1
      rwa [cxIndex_involutive hab, cxIndex_involutive hab] at this
    · intro i j
      show dtoC (gateVec level w (Gate.cx a b) (basis (j : Nat)) (i : Nat)) = _
      rw [gateVec_of_wf (by simp [Gate.wellFormedAt, ha, hb, hab])]
      show dtoC (cxVec a b (basis (j : Nat)) (i : Nat)) = _
      rw [cxVec_basis hab, dtoC_basis (deg_pos level)]
      by_cases hc : (i : Nat) = cxIndex a b (j : Nat)
      · rw [if_pos hc, if_pos (Fin.ext hc)]
      · rw [if_neg hc, if_neg (fun he => hc (congrArg Fin.val he))]

/-! ## Unitary composition -/

theorem dtoC_dsum {d : Nat} (n : Nat) (f : Nat → Dy d) :
    dtoC (dsum n f) = ∑ i ∈ Finset.range n, dtoC (f i) := by
  induction n with
  | zero => exact dtoC_zero
  | succ n ih => rw [dsum_succ, dtoC_add, ih, Finset.sum_range_succ]

theorem cmat_nil (level w : Nat) : cmat level w [] = 1 := by
  ext i j
  show dtoC (denote level (Circuit.id w) i j) = _
  rw [denote_id, Matrix.one_apply]
  show dtoC (if (i : Nat) = (j : Nat) then Dy.one (deg level) else Dy.zero (deg level)) = _
  by_cases h : i = j
  · rw [if_pos (congrArg Fin.val h), if_pos h, dtoC_one (deg_pos level)]
  · rw [if_neg (fun he => h (Fin.ext he)), if_neg h, dtoC_zero]

theorem cmat_append (level w : Nat) (a b : List Gate) :
    cmat level w (a ++ b) = cmat level w b * cmat level w a := by
  ext i j
  rw [Matrix.mul_apply]
  show dtoC (denote level (Circuit.mk w (a ++ b)) (i : Nat) (j : Nat)) = _
  rw [denote_append_apply level w a b j.isLt (i : Nat), dtoC_dsum,
    Finset.sum_congr rfl (fun k _ => dtoC_mul (deg_pos level) _ _),
    ← Fin.sum_univ_eq_sum_range
      (fun k => dtoC (denote level (Circuit.mk w b) (i : Nat) k)
        * dtoC (denote level (Circuit.mk w a) k (j : Nat))) (2 ^ w)]
  rfl

theorem cmat_cons (level w : Nat) (g : Gate) (gs : List Gate) :
    cmat level w (g :: gs) = cmat level w gs * cgate level w g := by
  rw [show g :: gs = [g] ++ gs from rfl, cmat_append]
  rfl

/-! ## Circuit unitarity -/

/-- The complex matrix of a well-formed circuit is unitary on the block its
width addresses. -/
theorem unitary_cmat {level w : Nat} {gs : List Gate}
    (h : ∀ g ∈ gs, g.wellFormedAt level w = true) :
    (cmat level w gs)ᴴ * cmat level w gs = 1 := by
  induction gs with
  | nil => rw [cmat_nil, Matrix.conjTranspose_one, Matrix.one_mul]
  | cons g gs ih =>
    have hg : g.wellFormedAt level w = true := h g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, g'.wellFormedAt level w = true :=
      fun g' hg' => h g' (List.mem_cons_of_mem g hg')
    rw [cmat_cons, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cmat _ _ _)ᴴ,
      ih hgs, Matrix.one_mul, unitary_cgate hg]

/-- A circuit that passes
`Circuit.wellFormedAt` denotes a unitary matrix over ℂ. -/
theorem unitary_denote {level : Nat} {c : Circuit} (h : c.wellFormedAt level = true) :
    (cmat level c.width c.gates)ᴴ * cmat level c.width c.gates = 1 :=
  unitary_cmat (fun g hg => (List.all_eq_true.mp h) g hg)

/-! ## Unitarity implies well-formedness

An ill-formed gate denotes the zero map, and the zero state is a fixed point of
every action, so one such gate takes the whole block matrix to zero.  Because
the zero matrix is nonunitary, unitarity is equivalent to well-formedness.  A
circuit that indexes a wire beyond its width or uses an unavailable phase
therefore fails the unitary equation. -/

theorem cmat_eq_zero_of_not_wf {level w : Nat} {gs : List Gate}
    (h : gs.all (Gate.wellFormedAt level w) ≠ true) : cmat level w gs = 0 := by
  obtain ⟨g, hg, hgf⟩ : ∃ g ∈ gs, g.wellFormedAt level w = false := by
    by_contra hc
    refine h (List.all_eq_true.mpr (fun g hg => ?_))
    by_contra hgt
    exact hc ⟨g, hg, Bool.eq_false_iff.mpr hgt⟩
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hg
  ext i j
  show dtoC (denote level (Circuit.mk w (s ++ g :: t)) (i : Nat) (j : Nat)) = _
  rw [denote_apply, run_eq_zero_of_not_wf hgf, Vec.zero_apply, dtoC_zero, Matrix.zero_apply]

theorem one_ne_zero_block {w : Nat} : (1 : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ) ≠ 0 := by
  intro h
  have hi : (0 : Nat) < 2 ^ w := by positivity
  have h0 : (1 : Matrix (Fin (2 ^ w)) (Fin (2 ^ w)) ℂ) ⟨0, hi⟩ ⟨0, hi⟩ = 0 := by
    rw [h]; rfl
  rw [Matrix.one_apply_eq] at h0
  exact one_ne_zero h0

/-- Well-formedness and unitarity are the same condition over ℂ. -/
theorem unitary_iff_wellFormedAt {level : Nat} (c : Circuit) :
    (cmat level c.width c.gates)ᴴ * cmat level c.width c.gates = 1
      ↔ c.wellFormedAt level = true := by
  refine ⟨fun hu => ?_, unitary_denote⟩
  by_contra hw
  rw [show cmat level c.width c.gates = 0 from cmat_eq_zero_of_not_wf hw,
    Matrix.conjTranspose_zero, Matrix.zero_mul] at hu
  exact one_ne_zero_block hu.symm

/-- The same, as membership in Mathlib's unitary group. -/
theorem mem_unitaryGroup_denote {level : Nat} {c : Circuit} (h : c.wellFormedAt level = true) :
    cmat level c.width c.gates ∈ Matrix.unitaryGroup (Fin (2 ^ c.width)) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (unitary_denote h)

end VQBridge
