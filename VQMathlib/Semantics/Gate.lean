/-
The gate table, checked against the textbook complex matrices.

`VQ.Semantics` defines each primitive by its action on a basis index.
`Tests/Reference.lean` compares that action with a second implementation over
the same amplitude ring.  This module proves correspondence with the standard
complex matrices.

Each one-wire gate is `I ⊗ M ⊗ I`, whose entry at `(i, j)` is `M` read at the bits of
`i` and `j` on that wire when `i` and `j` agree everywhere else, and zero when
they do not.  Two indices agree off wire `q` exactly when `i = j` or
`i = j ⊕ 2 ^ q`.  `wireEntry` encodes this condition.  `pairEntry` gives the
two-wire form, with the control as the high bit of the four-valued index used by
the standard `4 × 4` matrix.
-/
import VQMathlib.Algebra.Dyadic
import VQ.Semantics.Gate
import Mathlib.LinearAlgebra.Matrix.Notation

namespace VQBridge

open VQ VQ.Algebra VQ.Semantics

/-! ## Reading an index as a matrix index -/

/-- Bit `q` of the index, as a row or column of a one-wire matrix. -/
def bitIdx (i q : Nat) : Fin 2 := if i.testBit q then 1 else 0

/-- Bits `a` and `b` of the index, as a row or column of a two-wire matrix, with
`a` the high bit: the column order is `|00⟩, |01⟩, |10⟩, |11⟩` with the control
first, which is the order the usual `4 × 4` CNOT is written in. -/
def bitPair (i a b : Nat) : Fin 4 :=
  if i.testBit a then (if i.testBit b then 3 else 2) else (if i.testBit b then 1 else 0)

/-- Bits `a`, `b`, and `c` of the index, as a row or column of a three-wire
matrix, with `a` the high bit: the column order is `|000⟩` through `|111⟩`, which
is the order the usual `8 × 8` CCZ is written in. -/
def bitTriple (i a b c : Nat) : Fin 8 :=
  if i.testBit a then
    (if i.testBit b then (if i.testBit c then 7 else 6) else (if i.testBit c then 5 else 4))
  else
    (if i.testBit b then (if i.testBit c then 3 else 2) else (if i.testBit c then 1 else 0))

/-- The entry of `M` acting on wire `q` and the identity elsewhere. -/
noncomputable def wireEntry (M : Matrix (Fin 2) (Fin 2) ℂ) (q i j : Nat) : ℂ :=
  if i = j ∨ i = j ^^^ (1 <<< q) then M (bitIdx i q) (bitIdx j q) else 0

/-- The entry of `M` acting on wires `a` and `b` and the identity elsewhere. -/
noncomputable def pairEntry (M : Matrix (Fin 4) (Fin 4) ℂ) (a b i j : Nat) : ℂ :=
  if i = j ∨ i = j ^^^ (1 <<< a) ∨ i = j ^^^ (1 <<< b) ∨ i = j ^^^ (1 <<< a) ^^^ (1 <<< b)
    then M (bitPair i a b) (bitPair j a b) else 0

/-- The eight indices that agree with `j` off wires `a`, `b`, and `c`. -/
def tripleCoset (a b c j : Nat) : List Nat :=
  [ j
  , j ^^^ (1 <<< a), j ^^^ (1 <<< b), j ^^^ (1 <<< c)
  , j ^^^ (1 <<< a) ^^^ (1 <<< b), j ^^^ (1 <<< a) ^^^ (1 <<< c)
  , j ^^^ (1 <<< b) ^^^ (1 <<< c)
  , j ^^^ (1 <<< a) ^^^ (1 <<< b) ^^^ (1 <<< c) ]

/-- The entry of `M` acting on wires `a`, `b`, and `c` and the identity
elsewhere.  The membership test is the three-wire form of the disjunction in
`pairEntry`, written as a list because eight disjuncts do not read. -/
noncomputable def tripleEntry (M : Matrix (Fin 8) (Fin 8) ℂ) (a b c i j : Nat) : ℂ :=
  if i ∈ tripleCoset a b c j then M (bitTriple i a b c) (bitTriple j a b c) else 0

/-- A one-wire action is determined by its values at `j` and `j ⊕ 2 ^ q`. -/
theorem wireEntry_eq {M : Matrix (Fin 2) (Fin 2) ℂ} {q i j : Nat} {f : Nat → ℂ}
    (hdiag : f j = M (bitIdx j q) (bitIdx j q))
    (hoff : f (j ^^^ (1 <<< q)) = M (bitIdx (j ^^^ (1 <<< q)) q) (bitIdx j q))
    (hzero : ∀ k, k ≠ j → k ≠ j ^^^ (1 <<< q) → f k = 0) :
    f i = wireEntry M q i j := by
  unfold wireEntry
  by_cases h1 : i = j
  · subst h1
    rw [if_pos (Or.inl rfl), hdiag]
  · by_cases h2 : i = j ^^^ (1 <<< q)
    · subst h2
      rw [if_pos (Or.inr rfl), hoff]
    · rw [if_neg (by tauto), hzero i h1 h2]

/-- A two-wire action is determined by its values at the four indices that agree
with `j` off those wires. -/
theorem pairEntry_eq {M : Matrix (Fin 4) (Fin 4) ℂ} {a b i j : Nat} {f : Nat → ℂ}
    (h0 : f j = M (bitPair j a b) (bitPair j a b))
    (hA : f (j ^^^ (1 <<< a)) = M (bitPair (j ^^^ (1 <<< a)) a b) (bitPair j a b))
    (hB : f (j ^^^ (1 <<< b)) = M (bitPair (j ^^^ (1 <<< b)) a b) (bitPair j a b))
    (hAB : f (j ^^^ (1 <<< a) ^^^ (1 <<< b))
      = M (bitPair (j ^^^ (1 <<< a) ^^^ (1 <<< b)) a b) (bitPair j a b))
    (hzero : ∀ k, k ≠ j → k ≠ j ^^^ (1 <<< a) → k ≠ j ^^^ (1 <<< b) →
      k ≠ j ^^^ (1 <<< a) ^^^ (1 <<< b) → f k = 0) :
    f i = pairEntry M a b i j := by
  unfold pairEntry
  by_cases h1 : i = j
  · subst h1; rw [if_pos (Or.inl rfl), h0]
  · by_cases h2 : i = j ^^^ (1 <<< a)
    · subst h2; rw [if_pos (Or.inr (Or.inl rfl)), hA]
    · by_cases h3 : i = j ^^^ (1 <<< b)
      · subst h3; rw [if_pos (Or.inr (Or.inr (Or.inl rfl))), hB]
      · by_cases h4 : i = j ^^^ (1 <<< a) ^^^ (1 <<< b)
        · subst h4; rw [if_pos (Or.inr (Or.inr (Or.inr rfl))), hAB]
        · rw [if_neg (by tauto), hzero i h1 h2 h3 h4]

/-! ## XOR and bit-index identities -/

theorem testBit_ne {x y : Nat} (r : Nat) (h : x.testBit r ≠ y.testBit r) : x ≠ y :=
  fun he => h (by rw [he])

theorem xor_ne_self (j q : Nat) : j ^^^ (1 <<< q) ≠ j :=
  testBit_ne q (by rw [testBit_xor_self]; exact Bool.not_ne_self _)

theorem xor_pair_ne_self (j : Nat) {a b : Nat} (hab : a ≠ b) :
    j ^^^ (1 <<< a) ^^^ (1 <<< b) ≠ j :=
  testBit_ne a (by
    rw [testBit_xor_of_ne hab, testBit_xor_self]
    exact Bool.not_ne_self _)

/-- `bitTriple` reads exactly the three bits, so indices that disagree on those
bits map to different rows. -/
theorem bitTriple_ne {i j a b c : Nat}
    (h : i.testBit a ≠ j.testBit a ∨ i.testBit b ≠ j.testBit b
      ∨ i.testBit c ≠ j.testBit c) :
    bitTriple i a b c ≠ bitTriple j a b c := by
  unfold bitTriple
  cases hia : i.testBit a <;> cases hib : i.testBit b <;> cases hic : i.testBit c <;>
    cases hja : j.testBit a <;> cases hjb : j.testBit b <;> cases hjc : j.testBit c <;>
    simp_all

/-- The one row `bitTriple` sends the all-set index to. -/
theorem bitTriple_eq_seven {i a b c : Nat}
    (h : (i.testBit a && i.testBit b && i.testBit c) = true) : bitTriple i a b c = 7 := by
  unfold bitTriple
  simp_all

theorem bitTriple_ne_seven {i a b c : Nat}
    (h : (i.testBit a && i.testBit b && i.testBit c) = false) : bitTriple i a b c ≠ 7 := by
  unfold bitTriple
  cases hia : i.testBit a <;> cases hib : i.testBit b <;> cases hic : i.testBit c <;>
    simp_all

/-! ## Amplitude ring at a phase level -/

theorem deg_pos (level : Nat) : 0 < deg level := by positivity

theorem dtoC_basis {d : Nat} (hd : 0 < d) (j i : Nat) :
    dtoC ((basis j : Vec d) i) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, basis_self, dtoC_one hd]
  · rw [if_neg h, basis_of_ne h, dtoC_zero]

/-! ## Primitive matrices -/

def matX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

noncomputable def matY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

def matZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

noncomputable def matS : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.I]

noncomputable def matSdg : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -Complex.I]

noncomputable def matT : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (Real.pi * Complex.I / 4)]

noncomputable def matTdg : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (-(Real.pi * Complex.I / 4))]

/-- The phase gate at level `k`: `diag (1, exp (2 π i / 2 ^ k))`. -/
noncomputable def matP (k : Nat) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (2 * Real.pi * Complex.I / (2 ^ k : Nat))]

noncomputable def matPdg (k : Nat) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (-(2 * Real.pi * Complex.I / (2 ^ k : Nat)))]

noncomputable def matH : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / ((Real.sqrt 2 : ℝ) : ℂ)) • !![1, 1; 1, -1]

def matCX : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

/-- CCZ: the identity with the `|111⟩` entry negated. -/
def matCCZ : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, -1]

/-- The same matrix read as a diagonal, which is the form every proof about it
uses.  Stating the literal above and deriving this keeps the textbook matrix in
the file rather than a paraphrase of it. -/
theorem matCCZ_apply (x y : Fin 8) :
    matCCZ x y = if x = y then (if x = 7 then -1 else 1) else 0 := by
  fin_cases x <;> fin_cases y <;> simp [matCCZ]

/-! ## Entrywise primitive semantics -/

theorem entry_flipVec {d : Nat} (hd : 0 < d) (q i j : Nat) :
    dtoC (flipVec q (basis j : Vec d) i) = wireEntry matX q i j := by
  have hf : ∀ k, dtoC (flipVec q (basis j : Vec d) k)
      = if k = j ^^^ (1 <<< q) then 1 else 0 := by
    intro k
    rw [flipVec_basis, dtoC_basis hd]
  refine wireEntry_eq (M := matX)
    (f := fun k => dtoC (flipVec q (basis j : Vec d) k)) ?_ ?_ ?_
  · rw [hf, if_neg (Ne.symm (xor_ne_self j q))]
    cases hb : j.testBit q <;> simp [bitIdx, matX, hb]
  · rw [hf, if_pos rfl]
    cases hb : j.testBit q <;> simp [bitIdx, matX, hb]
  · intro k _ h2
    rw [hf, if_neg h2]

theorem entry_diagVec {d : Nat} (hd : 0 < d) (q : Nat) (a : Dy d) (i j : Nat) :
    dtoC (diagVec q a (basis j : Vec d) i) = wireEntry !![1, 0; 0, dtoC a] q i j := by
  have hf : ∀ k, dtoC (diagVec q a (basis j : Vec d) k)
      = (if j.testBit q then dtoC a else 1) * (if k = j then 1 else 0) := by
    intro k
    rw [diagVec_basis]
    by_cases hb : j.testBit q = true
    · rw [if_pos hb, if_pos hb, Vec.smul_apply, dtoC_mul hd, dtoC_basis hd]
    · rw [if_neg hb, if_neg hb, dtoC_basis hd, one_mul]
  refine wireEntry_eq (M := !![1, 0; 0, dtoC a])
    (f := fun k => dtoC (diagVec q a (basis j : Vec d) k)) ?_ ?_ ?_
  · rw [hf, if_pos rfl, mul_one]
    cases hb : j.testBit q <;> simp [bitIdx, hb]
  · rw [hf, if_neg (xor_ne_self j q), mul_zero]
    cases hb : j.testBit q <;> simp [bitIdx, hb]
  · intro k h1 _
    rw [hf, if_neg h1, mul_zero]

theorem entry_yVec {d : Nat} (hd : 0 < d) (q : Nat) (a : Dy d) (i j : Nat) :
    dtoC (yVec q a (basis j : Vec d) i)
      = wireEntry !![0, -dtoC a; dtoC a, 0] q i j := by
  have hf : ∀ k, dtoC (yVec q a (basis j : Vec d) k)
      = (if j.testBit q then -dtoC a else dtoC a) * (if k = j ^^^ (1 <<< q) then 1 else 0) := by
    intro k
    rw [yVec_basis, Vec.smul_apply, dtoC_mul hd, dtoC_basis hd]
    by_cases hb : j.testBit q = true
    · rw [if_pos hb, if_pos hb, dtoC_neg]
    · rw [if_neg hb, if_neg hb]
  refine wireEntry_eq (M := !![0, -dtoC a; dtoC a, 0])
    (f := fun k => dtoC (yVec q a (basis j : Vec d) k)) ?_ ?_ ?_
  · rw [hf, if_neg (Ne.symm (xor_ne_self j q)), mul_zero]
    cases hb : j.testBit q <;> simp [bitIdx, hb]
  · rw [hf, if_pos rfl, mul_one]
    cases hb : j.testBit q <;> simp [bitIdx, hb]
  · intro k _ h2
    rw [hf, if_neg h2, mul_zero]

theorem entry_hVec {d e : Nat} (hde : d = 4 * e) (he : 0 < e) (q i j : Nat) :
    dtoC (hVec q (basis j : Vec d) i) = wireEntry matH q i j := by
  have hd : 0 < d := by omega
  have hinv : dtoC (Dy.invSqrt2 d) = 1 / ((Real.sqrt 2 : ℝ) : ℂ) := by
    subst hde; exact dtoC_invSqrt2 he
  by_cases hb : j.testBit q = true
  · have hf : ∀ k, dtoC (hVec q (basis j : Vec d) k)
        = (1 / ((Real.sqrt 2 : ℝ) : ℂ))
          * ((if k = j ^^^ (1 <<< q) then 1 else 0) - (if k = j then 1 else 0)) := by
      intro k
      rw [hVec_basis_of_true hb, Vec.smul_apply, dtoC_mul hd, hinv]
      congr 1
      show dtoC ((basis (j ^^^ (1 <<< q)) : Vec d) k - (basis j : Vec d) k) = _
      rw [dtoC_sub, dtoC_basis hd, dtoC_basis hd]
    refine wireEntry_eq (M := matH)
      (f := fun k => dtoC (hVec q (basis j : Vec d) k)) ?_ ?_ ?_
    · rw [hf, if_neg (Ne.symm (xor_ne_self j q)), if_pos rfl]
      simp [bitIdx, matH, hb]
    · rw [hf, if_pos rfl, if_neg (xor_ne_self j q)]
      simp [bitIdx, matH, hb]
    · intro k h1 h2
      rw [hf, if_neg h2, if_neg h1]
      simp
  · have hb' : j.testBit q = false := Bool.eq_false_iff.mpr hb
    have hf : ∀ k, dtoC (hVec q (basis j : Vec d) k)
        = (1 / ((Real.sqrt 2 : ℝ) : ℂ))
          * ((if k = j then 1 else 0) + (if k = j ^^^ (1 <<< q) then 1 else 0)) := by
      intro k
      rw [hVec_basis_of_false hb', Vec.smul_apply, dtoC_mul hd, hinv]
      congr 1
      show dtoC ((basis j : Vec d) k + (basis (j ^^^ (1 <<< q)) : Vec d) k) = _
      rw [dtoC_add, dtoC_basis hd, dtoC_basis hd]
    refine wireEntry_eq (M := matH)
      (f := fun k => dtoC (hVec q (basis j : Vec d) k)) ?_ ?_ ?_
    · rw [hf, if_pos rfl, if_neg (Ne.symm (xor_ne_self j q))]
      simp [bitIdx, matH, hb']
    · rw [hf, if_neg (xor_ne_self j q), if_pos rfl]
      simp [bitIdx, matH, hb']
    · intro k h1 h2
      rw [hf, if_neg h1, if_neg h2]
      simp

theorem entry_cxVec {d : Nat} (hd : 0 < d) {a b : Nat} (hab : a ≠ b) (i j : Nat) :
    dtoC (cxVec a b (basis j : Vec d) i) = pairEntry matCX a b i j := by
  have hf : ∀ k, dtoC (cxVec a b (basis j : Vec d) k)
      = if k = cxIndex a b j then 1 else 0 := by
    intro k
    rw [cxVec_basis hab, dtoC_basis hd]
  have hba : b ≠ a := Ne.symm hab
  have e1 : j ≠ j ^^^ (1 <<< b) := Ne.symm (xor_ne_self j b)
  have e2 : j ^^^ (1 <<< a) ≠ j := xor_ne_self j a
  have e3 : j ^^^ (1 <<< a) ≠ j ^^^ (1 <<< b) :=
    testBit_ne a (by
      rw [testBit_xor_self, testBit_xor_of_ne hab]
      exact Bool.not_ne_self _)
  have e4 : j ^^^ (1 <<< b) ≠ j := xor_ne_self j b
  have e5 : j ^^^ (1 <<< a) ^^^ (1 <<< b) ≠ j := xor_pair_ne_self j hab
  have e6 : j ^^^ (1 <<< a) ^^^ (1 <<< b) ≠ j ^^^ (1 <<< b) :=
    testBit_ne a (by
      rw [testBit_xor_of_ne hab, testBit_xor_self, testBit_xor_of_ne hab]
      exact Bool.not_ne_self _)
  refine pairEntry_eq (M := matCX)
    (f := fun k => dtoC (cxVec a b (basis j : Vec d) k)) ?_ ?_ ?_ ?_ ?_
  · cases hja : j.testBit a <;> cases hjb : j.testBit b <;>
      simp [hf, cxIndex, bitPair, matCX, hja, hjb, e1]
  · cases hja : j.testBit a <;> cases hjb : j.testBit b <;>
      simp [hf, cxIndex, bitPair, matCX, hja, hjb, e2, e3,
        testBit_xor_of_ne hba]
  · cases hja : j.testBit a <;> cases hjb : j.testBit b <;>
      simp [hf, cxIndex, bitPair, matCX, hja, hjb, e4, testBit_xor_of_ne hab]
  · cases hja : j.testBit a <;> cases hjb : j.testBit b <;>
      simp [hf, cxIndex, bitPair, matCX, hja, hjb, e5, e6,
        testBit_xor_of_ne hab, testBit_xor_of_ne hba]
  · intro k h1 _ h3 _
    show dtoC (cxVec a b (basis j : Vec d) k) = 0
    rw [hf, cxIndex]
    cases hja : j.testBit a <;> simp [h1, h3]

/-- CCZ is diagonal, so its column `j` has one entry.  This is the form the
unitarity proof reads, and `entry_cczVec` below turns it into the textbook
matrix. -/
theorem cczVec_basis_apply {d : Nat} (hd : 0 < d) (a b c : Nat) (i j : Nat) :
    dtoC (cczVec a b c (basis j : Vec d) i)
      = if i = j then (if j.testBit a && j.testBit b && j.testBit c then -1 else 1) else 0 := by
  show dtoC (if i.testBit a && i.testBit b && i.testBit c then -(basis j : Vec d) i
      else (basis j : Vec d) i) = _
  by_cases hij : i = j
  · subst hij
    by_cases hb : i.testBit a && i.testBit b && i.testBit c
    · rw [if_pos hb, if_pos rfl, if_pos hb, basis_self, dtoC_neg, dtoC_one hd]
    · rw [if_neg hb, if_pos rfl, if_neg hb, basis_self, dtoC_one hd]
  · rw [basis_of_ne hij, if_neg hij, neg_zero, ite_self, dtoC_zero]

theorem entry_cczVec {d : Nat} (hd : 0 < d) {a b c : Nat} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (i j : Nat) :
    dtoC (cczVec a b c (basis j : Vec d) i) = tripleEntry matCCZ a b c i j := by
  rw [cczVec_basis_apply hd, tripleEntry]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos (show i ∈ tripleCoset a b c i from by simp [tripleCoset])]
    by_cases hb : i.testBit a && i.testBit b && i.testBit c
    · rw [if_pos hb, matCCZ_apply, if_pos rfl, if_pos (bitTriple_eq_seven hb)]
    · rw [if_neg hb, matCCZ_apply, if_pos rfl,
        if_neg (bitTriple_ne_seven (Bool.eq_false_iff.mpr hb))]
  · rw [if_neg hij]
    by_cases hmem : i ∈ tripleCoset a b c j
    · have hne : bitTriple i a b c ≠ bitTriple j a b c := by
        simp only [tripleCoset, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h | h | h | h | h | h | h
        · exact absurd h hij
        all_goals subst h
        all_goals refine bitTriple_ne ?_
        all_goals
          simp [testBit_xor_of_ne hab, testBit_xor_of_ne hac,
            testBit_xor_of_ne hbc, testBit_xor_of_ne (Ne.symm hab),
            testBit_xor_of_ne (Ne.symm hac), testBit_xor_of_ne (Ne.symm hbc)]
      rw [if_pos hmem, matCCZ_apply, if_neg hne]
    · rw [if_neg hmem]

/-! ## Phase interpretation

`phase level k` is `ζ ^ 2 ^ (level - k)`, and `ζ` is the `2 ^ level`-th root of
unity.  The gate phase equals `exp (2 π i / 2 ^ k)` when `k ≤ level`, the
condition required by `Gate.wellFormedAt`. -/

theorem dtoC_phase {level k : Nat} (hl : 0 < level) (hk : k ≤ level) :
    dtoC (phase level k) = Complex.exp (2 * Real.pi * Complex.I / (2 ^ k : Nat)) := by
  rw [phase, dtoC_pow (deg_pos level), dtoC_zeta (deg_pos level), zetaC_deg hl,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  rw [show ((2 : ℂ) ^ level) = 2 ^ (level - k) * 2 ^ k from by
    rw [← pow_add]; congr 1; omega]
  have h2 : ((2 : ℂ)) ^ (level - k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : ((2 : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

theorem dtoC_phaseInv {level k : Nat} (hl : 0 < level) (hk : k ≤ level) :
    dtoC (phaseInv level k) = Complex.exp (-(2 * Real.pi * Complex.I / (2 ^ k : Nat))) := by
  have hle : 2 ^ (level - k) ≤ 2 ^ level := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : ((2 : ℂ)) ^ (level - k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : ((2 : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsplit : ((2 : ℂ) ^ level) = 2 ^ (level - k) * 2 ^ k := by
    rw [← pow_add]; congr 1; omega
  rw [phaseInv, dtoC_pow (deg_pos level), dtoC_zeta (deg_pos level), zetaC_deg hl,
    ← Complex.exp_nat_mul,
    show ((2 ^ level - 2 ^ (level - k) : Nat) : ℂ)
        * (2 * (Real.pi : ℂ) * Complex.I / ((2 ^ level : Nat) : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I
        - 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ k : Nat) : ℂ) from by
      rw [Nat.cast_sub hle]
      push_cast
      rw [hsplit]
      field_simp,
    Complex.exp_sub, Complex.exp_two_pi_mul_I, Complex.exp_neg, one_div]

theorem phaseC_two : Complex.exp (2 * Real.pi * Complex.I / (2 ^ 2 : Nat)) = Complex.I := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I / ((2 ^ 2 : Nat) : ℂ)
      = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I from by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  push_cast
  ring

theorem phaseC_three : Complex.exp (2 * Real.pi * Complex.I / (2 ^ 3 : Nat))
    = Complex.exp (Real.pi * Complex.I / 4) := by
  congr 1
  push_cast
  ring

theorem phaseC_two_inv :
    Complex.exp (-(2 * Real.pi * Complex.I / (2 ^ 2 : Nat))) = -Complex.I := by
  rw [show -(2 * (Real.pi : ℂ) * Complex.I / ((2 ^ 2 : Nat) : ℂ))
      = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I from by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  ring

theorem phaseC_three_inv : Complex.exp (-(2 * Real.pi * Complex.I / (2 ^ 3 : Nat)))
    = Complex.exp (-(Real.pi * Complex.I / 4)) := by
  congr 1
  push_cast
  ring

/-- At level three and above, the degree is a multiple of four and the ring
contains `1 / √2`. -/
theorem deg_eq_four_mul {level : Nat} (h : 3 ≤ level) : deg level = 4 * 2 ^ (level - 3) := by
  show 2 ^ (level - 1) = 4 * 2 ^ (level - 3)
  rw [show (4 : Nat) = 2 ^ 2 from rfl, ← pow_add]
  congr 1
  omega

/-! ## Primitive-gate correspondence

Each primitive acts as the standard complex matrix on its wire and as the
identity on every other wire. -/

theorem gate_x {level w q : Nat} (hq : q < w) (i j : Nat) :
    dtoC (gateVec level w (Gate.x q) (basis j) i) = wireEntry matX q i j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq])]
  exact entry_flipVec (deg_pos level) q i j

theorem gate_z {level w q : Nat} (hq : q < w) (hl : 1 ≤ level) (i j : Nat) :
    dtoC (gateVec level w (Gate.z q) (basis j) i) = wireEntry matZ q i j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  have h : dtoC (-Dy.one (deg level)) = -1 := by
    rw [dtoC_neg, dtoC_one (deg_pos level)]
  rw [show matZ = !![1, 0; 0, dtoC (-Dy.one (deg level))] from by rw [h]; rfl]
  exact entry_diagVec (deg_pos level) q _ i j

theorem gate_s {level w q : Nat} (hq : q < w) (hl : 2 ≤ level) (i j : Nat) :
    dtoC (gateVec level w (Gate.s q) (basis j) i) = wireEntry matS q i j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  have h : dtoC (phase level 2) = Complex.I := by
    rw [dtoC_phase (by omega) hl, phaseC_two]
  rw [show matS = !![1, 0; 0, dtoC (phase level 2)] from by rw [h]; rfl]
  exact entry_diagVec (deg_pos level) q _ i j

theorem gate_sdg {level w q : Nat} (hq : q < w) (hl : 2 ≤ level) (i j : Nat) :
    dtoC (gateVec level w (Gate.sdg q) (basis j) i) = wireEntry matSdg q i j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  have h : dtoC (phaseInv level 2) = -Complex.I := by
    rw [dtoC_phaseInv (by omega) hl, phaseC_two_inv]
  rw [show matSdg = !![1, 0; 0, dtoC (phaseInv level 2)] from by rw [h]; rfl]
  exact entry_diagVec (deg_pos level) q _ i j

theorem gate_t {level w q : Nat} (hq : q < w) (hl : 3 ≤ level) (i j : Nat) :
    dtoC (gateVec level w (Gate.t q) (basis j) i) = wireEntry matT q i j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  have h : dtoC (phase level 3) = Complex.exp (Real.pi * Complex.I / 4) := by
    rw [dtoC_phase (by omega) hl, phaseC_three]
  rw [show matT = !![1, 0; 0, dtoC (phase level 3)] from by rw [h]; rfl]
  exact entry_diagVec (deg_pos level) q _ i j

theorem gate_tdg {level w q : Nat} (hq : q < w) (hl : 3 ≤ level) (i j : Nat) :
    dtoC (gateVec level w (Gate.tdg q) (basis j) i) = wireEntry matTdg q i j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  have h : dtoC (phaseInv level 3) = Complex.exp (-(Real.pi * Complex.I / 4)) := by
    rw [dtoC_phaseInv (by omega) hl, phaseC_three_inv]
  rw [show matTdg = !![1, 0; 0, dtoC (phaseInv level 3)] from by rw [h]; rfl]
  exact entry_diagVec (deg_pos level) q _ i j

theorem gate_p {level w q k : Nat} (hq : q < w) (h4 : 4 ≤ k) (hk : k ≤ level) (i j : Nat) :
    dtoC (gateVec level w (Gate.p k q) (basis j) i) = wireEntry (matP k) q i j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, h4, hk])]
  have h : dtoC (phase level k) = Complex.exp (2 * Real.pi * Complex.I / (2 ^ k : Nat)) :=
    dtoC_phase (by omega) hk
  rw [show matP k = !![1, 0; 0, dtoC (phase level k)] from by rw [h]; rfl]
  exact entry_diagVec (deg_pos level) q _ i j

theorem gate_pdg {level w q k : Nat} (hq : q < w) (h4 : 4 ≤ k) (hk : k ≤ level) (i j : Nat) :
    dtoC (gateVec level w (Gate.pdg k q) (basis j) i) = wireEntry (matPdg k) q i j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, h4, hk])]
  have h : dtoC (phaseInv level k)
      = Complex.exp (-(2 * Real.pi * Complex.I / (2 ^ k : Nat))) :=
    dtoC_phaseInv (by omega) hk
  rw [show matPdg k = !![1, 0; 0, dtoC (phaseInv level k)] from by rw [h]; rfl]
  exact entry_diagVec (deg_pos level) q _ i j

theorem gate_y {level w q : Nat} (hq : q < w) (hl : 2 ≤ level) (i j : Nat) :
    dtoC (gateVec level w (Gate.y q) (basis j) i) = wireEntry matY q i j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  have h : dtoC (phase level 2) = Complex.I := by
    rw [dtoC_phase (by omega) hl, phaseC_two]
  rw [show matY = !![0, -dtoC (phase level 2); dtoC (phase level 2), 0] from by rw [h]; rfl]
  exact entry_yVec (deg_pos level) q _ i j

theorem gate_h {level w q : Nat} (hq : q < w) (hl : 3 ≤ level) (i j : Nat) :
    dtoC (gateVec level w (Gate.h q) (basis j) i) = wireEntry matH q i j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, hq, hl])]
  exact entry_hVec (deg_eq_four_mul hl) (by positivity) q i j

theorem gate_cx {level w a b : Nat} (ha : a < w) (hb : b < w) (hab : a ≠ b) (i j : Nat) :
    dtoC (gateVec level w (Gate.cx a b) (basis j) i) = pairEntry matCX a b i j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, ha, hb, hab])]
  exact entry_cxVec (deg_pos level) hab i j

theorem gate_ccz {level w a b c : Nat} (ha : a < w) (hb : b < w) (hc : c < w)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hl : 1 ≤ level) (i j : Nat) :
    dtoC (gateVec level w (Gate.ccz a b c) (basis j) i) = tripleEntry matCCZ a b c i j := by
  rw [gateVec_of_wf (by simp [Gate.wellFormedAt, ha, hb, hc, hab, hbc, hac, hl])]
  exact entry_cczVec (deg_pos level) hab hbc hac i j

end VQBridge
