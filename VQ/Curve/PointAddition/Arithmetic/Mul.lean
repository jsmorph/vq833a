import VQ.Reversible.ArithmeticSpec
import VQ.Reversible.Compile
import VQ.Curve.Field

open VQ VQ.Reversible

namespace VQ.Curve.PointAddition.Arithmetic
namespace Mul

/-! ## Modulus, widths, and wire assignment

The modulus is fixed and the width `n` is the family
parameter.  Both operands the specification covers are below the modulus, so
only the low `k` bits of each carry information, where `k` is the bit length of
the modulus.  The circuit is a gadget of fixed size placed at width-dependent
offsets, and every resource count is a constant.

`kp` is `k - 1` and `dkp` is `dk - 1`, written so that `k` and `dk` are
syntactically successors: the carry wire at the top of a chain of `dk` positions
is then `A + dkp` by definition. -/

/-- One less than the bit length of the modulus. -/
def kp : Nat := 255

/-- The bit length of the modulus. -/
def k : Nat := kp + 1

/-- The modulus. -/
def m : Nat := VQ.Curve.p

/-- The width of a shifted addend: the `k` bits of an operand and one more, so
that the carry out of the addition stays inside the window. -/
def sk : Nat := k + 1

/-- One less than the width of the product accumulator. -/
def dkp : Nat := 2 * kp + 1

/-- The width of the product accumulator, which holds a full `2 k`-bit
product. -/
def dk : Nat := dkp + 1

/-- The workspace: the shifted addend, the accumulator, a constant register, the
quotient bits, and one carry ancilla. -/
def ws : Nat := 6 * k + 2

/-- The shifted addend register, `sk` wires. -/
def sReg (n : Nat) : Nat := 3 * n

/-- The product accumulator, `dk` wires. -/
def pReg (n : Nat) : Nat := 3 * n + sk

/-- The register the classical constants are loaded into, `dk` wires. -/
def vReg (n : Nat) : Nat := 3 * n + sk + dk

/-- The quotient bits of the reduction, `k` wires. -/
def qReg (n : Nat) : Nat := 3 * n + sk + dk + dk

/-- The carry-in ancilla of every chain. -/
def cReg (n : Nat) : Nat := 3 * n + sk + dk + dk + k

theorem e_sk : sk = k + 1 := rfl
theorem e_dk : dk = 2 * k := rfl
theorem e_ws : ws = 6 * k + 2 := rfl
theorem e_s (n : Nat) : sReg n = 3 * n := rfl
theorem e_p (n : Nat) : pReg n = 3 * n + sk := rfl
theorem e_v (n : Nat) : vReg n = 3 * n + sk + dk := rfl
theorem e_q (n : Nat) : qReg n = 3 * n + sk + dk + dk := rfl
theorem e_c (n : Nat) : cReg n = 3 * n + sk + dk + dk + k := rfl

theorem m_pos : 0 < m := by decide

theorem m_lt : m < 2 ^ k := by decide

theorem k_pos : 0 < k := by decide

/-- If width `n` holds the modulus, its bit length `k` satisfies `k ≤ n`. -/
theorem k_le {n : Nat} (h : m ≤ 2 ^ n) : k ≤ n := by
  rcases Nat.lt_or_ge n k with hc | hc
  · have hk : k = kp + 1 := rfl
    have h1 : n ≤ kp := by omega
    have h2 : (2 : Nat) ^ n ≤ 2 ^ kp := Nat.pow_le_pow_right (by omega) h1
    have h3 : (2 : Nat) ^ kp < m := by decide
    omega
  · exact hc

/-! ## Circuit construction

Modular multiplication is a schoolbook product followed by a reduction, and both
halves are uncomputed at the end.  The product accumulator holds `a * b` in full
`2 k`-bit precision, so the round for bit `t` of the second operand adds the
first operand into the accumulator at bit offset `t` rather than doubling the
accumulator.  A doubling would have to move the accumulator's bits, which uses
a wire permutation.  A shifted addend uses the same gates at a different offset.

The reduction then subtracts `m * 2 ^ t` from the accumulator for `t` from
`k - 1` down to zero, conditionally on the accumulator being at least that.  The
bit recording each subtraction is the corresponding quotient bit.  The
product-to-residue map is noninjective, while the residue and quotient together
determine the product.

The forward pass therefore leaves the quotient register populated.
The residue is copied out into the product field and the forward pass is then
run backwards, which restores every workspace wire and both operands.  The
reversed list undoes the forward one because every gate here is an involution,
which is `VQ.Curve.PointAddition.Arithmetic.Mul.revUndo`. -/

/-- Cuccaro's MAJ on the carry-in wire `c`, the addend wire `b`, and the augend
wire `a`.  It sends `(c, b, a)` to `(c ^^^ a, b ^^^ a, maj a b c)`, so the carry
out of this position ends up on the augend wire. -/
def maj (c b a : Nat) : List RGate :=
  [RGate.cx a b, RGate.cx a c, RGate.ccx c b a]

/-- Cuccaro's UMA, the two-CNOT form.  It restores `c` and `a` and leaves the
sum bit on `b`. -/
def uma (c b a : Nat) : List RGate :=
  [RGate.ccx c b a, RGate.cx a c, RGate.cx c b]

/-- The wire carrying the carry into position `st` of a chain whose augend field
starts at `A` and whose carry-in ancilla is `c`.  Position zero reads the
ancilla.  Every later position reads the augend wire below, which the MAJ step
has overwritten with that position's carry out. -/
def cwire (A c : Nat) : Nat → Nat
  | 0 => c
  | s + 1 => A + s

/-- The ripple-carry chain: MAJ up the positions, `mid` at the top, UMA back
down.  The augend field starts at `A`, the addend field at `B`, and the sum
lands in the addend field.  `mid` runs where the carry out of the whole chain is
readable on the top carry wire. -/
def achain (A B c : Nat) (mid : List RGate) : Nat → Nat → List RGate
  | _, 0 => mid
  | st, p + 1 =>
      maj (cwire A c st) (B + st) (A + st) ++ achain A B c mid (st + 1) p
        ++ uma (cwire A c st) (B + st) (A + st)

/-- Exclusive-or of the classical constant `v` into the `p`-bit register at `D`,
one `x` gate per set bit. -/
def loadX : Nat → Nat → Nat → List RGate
  | _, 0, _ => []
  | D, p + 1, v => (if v % 2 = 1 then [RGate.x D] else []) ++ loadX (D + 1) p (v / 2)

/-- The same exclusive-or under the control of wire `c`, one CNOT per set bit.
Conditional loading applies a CNOT to each set bit.  The adder remains
uncontrolled. -/
def loadC (c : Nat) : Nat → Nat → Nat → List RGate
  | _, 0, _ => []
  | D, p + 1, v =>
      (if v % 2 = 1 then [RGate.cx c D] else []) ++ loadC c (D + 1) p (v / 2)

/-- Exclusive-or of the `p`-bit register at `A` into the one at `D`. -/
def pcopy : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | A, D, p + 1 => RGate.cx A D :: pcopy (A + 1) (D + 1) p

/-- The same under the control of wire `ctl`, one Toffoli per position.  This is
how one operand is gated by a bit of the other. -/
def ccopy (ctl : Nat) : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | A, D, p + 1 => RGate.ccx ctl A D :: ccopy ctl (A + 1) (D + 1) p

/-- One round of the product: gate the first operand by bit `t` of the second,
add it into the accumulator at offset `t`, and clear the gated copy. -/
def mround (n t : Nat) : List RGate :=
  ccopy (n + t) 0 (sReg n) k
    ++ achain (sReg n) (pReg n + t) (cReg n) [] 0 sk
    ++ ccopy (n + t) 0 (sReg n) k

/-- The rounds for bits `0` through `t - 1` of the second operand, in that
order. -/
def mloop (n : Nat) : Nat → List RGate
  | 0 => []
  | t + 1 => mloop n t ++ mround n t

/-- One step of the reduction: subtract `m * 2 ^ t` from the accumulator, keep
the carry out as the quotient bit, and add the constant back when the
subtraction was unnecessary. -/
def rstep (n t : Nat) : List RGate :=
  loadX (vReg n) dk (2 ^ dk - m * 2 ^ t)
    ++ achain (vReg n) (pReg n) (cReg n) [RGate.cx (vReg n + dkp) (qReg n + t)] 0 dk
    ++ loadX (vReg n) dk (2 ^ dk - m * 2 ^ t)
    ++ [RGate.x (qReg n + t)]
    ++ loadC (qReg n + t) (vReg n) dk (m * 2 ^ t)
    ++ achain (vReg n) (pReg n) (cReg n) [] 0 dk
    ++ loadC (qReg n + t) (vReg n) dk (m * 2 ^ t)
    ++ [RGate.x (qReg n + t)]

/-- The reduction steps for `t - 1` down to `0`, in that order. -/
def rloop (n : Nat) : Nat → List RGate
  | 0 => []
  | t + 1 => rstep n t ++ rloop n t

/-- The forward pass: the product, then the reduction. -/
def fwd (n : Nat) : List RGate := mloop n k ++ rloop n k

/-- The whole gadget: compute, copy the residue into the product field, and
uncompute. -/
def body (n : Nat) : List RGate :=
  fwd n ++ pcopy (pReg n) (2 * n) k ++ (fwd n).reverse

/-- The generator.  Below the bit length of the modulus the register cannot hold
it, the claim is vacuous, and the circuit is the identity. -/
def gen (n : Nat) : RCircuit :=
  { width := 3 * n + ws, gates := if k ≤ n then body n else [] }

/-! ## Well-formedness

Each chain and each load is one induction over the positions, and each loop is
one induction over the rounds.  The geometric hypotheses are that the registers
are disjoint and inside the declared width.  Everything else is arithmetic. -/

/-- The carry wire of a position is either the ancilla or a wire inside the
augend field strictly below that position. -/
theorem cwire_cases {A c K st : Nat} (hst : st < K) :
    cwire A c st = c ∨
      (A ≤ cwire A c st ∧ cwire A c st < A + K ∧ cwire A c st + 1 ≤ A + st) := by
  cases st with
  | zero => exact Or.inl rfl
  | succ s =>
    refine Or.inr ⟨?_, ?_, ?_⟩
    · show A ≤ A + s; omega
    · show A + s < A + K; omega
    · show A + s + 1 ≤ A + (s + 1); omega

/-- The carry wire at the top of a chain of `dk` positions. -/
theorem cwire_dk (A c : Nat) : cwire A c dk = A + dkp := rfl

theorem maj_wf {w c b a : Nat} (ha : a < w) (hb : b < w) (hc : c < w)
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    (maj c b a).all (RGate.wellFormed w) = true := by
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  simp [maj, RGate.wellFormed, ha, hb, hc, hab, hac, hcb, hba, hca]

theorem uma_wf {w c b a : Nat} (ha : a < w) (hb : b < w) (hc : c < w)
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    (uma c b a).all (RGate.wellFormed w) = true := by
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  simp [uma, RGate.wellFormed, ha, hb, hc, hac, hcb, hba, hca]

theorem achain_wf {A B c w K : Nat} {mid : List RGate}
    (hA : A + K ≤ w) (hB : B + K ≤ w) (hc : c < w) (hK : 0 < K)
    (hAB : A + K ≤ B ∨ B + K ≤ A)
    (hcA : c < A ∨ A + K ≤ c) (hcB : c < B ∨ B + K ≤ c)
    (hmid : mid.all (RGate.wellFormed w) = true) :
    ∀ p st, st + p = K → (achain A B c mid st p).all (RGate.wellFormed w) = true := by
  intro p
  induction p with
  | zero => intro st _; exact hmid
  | succ p ih =>
    intro st hst
    have hlt : st < K := by omega
    have hcc := cwire_cases (A := A) (c := c) (K := K) hlt
    have ha : A + st < w := by omega
    have hb : B + st < w := by omega
    have hcw : cwire A c st < w := by rcases hcc with h | h <;> omega
    have hab : A + st ≠ B + st := by omega
    have hac : A + st ≠ cwire A c st := by rcases hcc with h | h <;> omega
    have hcb : cwire A c st ≠ B + st := by rcases hcc with h | h <;> omega
    simp only [achain, List.all_append, Bool.and_eq_true]
    exact ⟨⟨maj_wf ha hb hcw hab hac hcb, ih (st + 1) (by omega)⟩,
      uma_wf ha hb hcw hab hac hcb⟩

theorem x_wf {w a : Nat} (ha : a < w) : ([RGate.x a]).all (RGate.wellFormed w) = true := by
  simp [RGate.wellFormed, ha]

theorem cx_wf {w a b : Nat} (ha : a < w) (hb : b < w) (hab : a ≠ b) :
    ([RGate.cx a b]).all (RGate.wellFormed w) = true := by
  simp [RGate.wellFormed, ha, hb, hab]

theorem loadX_wf {w : Nat} : ∀ (p D v : Nat), D + p ≤ w →
    (loadX D p v).all (RGate.wellFormed w) = true := by
  intro p
  induction p with
  | zero => intro D v _; rfl
  | succ p ih =>
    intro D v hD
    simp only [loadX, List.all_append, Bool.and_eq_true]
    refine ⟨?_, ih (D + 1) (v / 2) (by omega)⟩
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; exact x_wf (by omega)
    · rw [if_neg hv]; rfl

theorem loadC_wf {w c : Nat} (hc : c < w) : ∀ (p D v : Nat), D + p ≤ w → c < D ∨ D + p ≤ c →
    (loadC c D p v).all (RGate.wellFormed w) = true := by
  intro p
  induction p with
  | zero => intro D v _ _; rfl
  | succ p ih =>
    intro D v hD hcD
    simp only [loadC, List.all_append, Bool.and_eq_true]
    refine ⟨?_, ih (D + 1) (v / 2) (by omega) (by omega)⟩
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; exact cx_wf hc (by omega) (by omega)
    · rw [if_neg hv]; rfl

theorem pcopy_wf {w : Nat} : ∀ (p A D : Nat), A + p ≤ w → D + p ≤ w →
    (A + p ≤ D ∨ D + p ≤ A) → (pcopy A D p).all (RGate.wellFormed w) = true := by
  intro p
  induction p with
  | zero => intro A D _ _ _; rfl
  | succ p ih =>
    intro A D hA hD hAD
    simp only [pcopy, List.all_cons, Bool.and_eq_true]
    exact ⟨by simpa [RGate.wellFormed] using ⟨⟨by omega, by omega⟩, by omega⟩,
      ih (A + 1) (D + 1) (by omega) (by omega) (by omega)⟩

theorem ccopy_wf {w ctl : Nat} (hctl : ctl < w) : ∀ (p A D : Nat), A + p ≤ w → D + p ≤ w →
    (ctl < A ∨ A + p ≤ ctl) → (ctl < D ∨ D + p ≤ ctl) → (A + p ≤ D ∨ D + p ≤ A) →
    (ccopy ctl A D p).all (RGate.wellFormed w) = true := by
  intro p
  induction p with
  | zero => intro A D _ _ _ _ _; rfl
  | succ p ih =>
    intro A D hA hD hcA hcD hAD
    simp only [ccopy, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ih (A + 1) (D + 1) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
    simpa [RGate.wellFormed] using
      ⟨⟨⟨⟨⟨hctl, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩

theorem mround_wf {n : Nat} (hk : k ≤ n) {t : Nat} (ht : t < k) :
    (mround n t).all (RGate.wellFormed (3 * n + ws)) = true := by
  have h1 := e_sk
  have h2 := e_dk
  have h3 := e_ws
  have h4 := e_s n
  have h5 := e_p n
  have h6 := e_v n
  have h7 := e_q n
  have h8 := e_c n
  have hcp : (ccopy (n + t) 0 (sReg n) k).all (RGate.wellFormed (3 * n + ws)) = true :=
    ccopy_wf (by omega) k 0 (sReg n) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hch : (achain (sReg n) (pReg n + t) (cReg n) [] 0 sk).all
      (RGate.wellFormed (3 * n + ws)) = true :=
    achain_wf (A := sReg n) (B := pReg n + t) (c := cReg n) (K := sk)
      (by omega) (by omega) (by omega) (by omega)
      (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) rfl sk 0 (by omega)
  simp only [mround, List.all_append, Bool.and_eq_true]
  exact ⟨⟨hcp, hch⟩, hcp⟩

theorem mloop_wf {n : Nat} (hk : k ≤ n) : ∀ t, t ≤ k →
    (mloop n t).all (RGate.wellFormed (3 * n + ws)) = true := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    simp only [mloop, List.all_append, Bool.and_eq_true]
    exact ⟨ih (by omega), mround_wf hk (by omega)⟩

theorem rstep_wf {n : Nat} (_hk : k ≤ n) {t : Nat} (ht : t < k) :
    (rstep n t).all (RGate.wellFormed (3 * n + ws)) = true := by
  have h1 := e_sk
  have h2 := e_dk
  have h3 := e_ws
  have h4 := e_s n
  have h5 := e_p n
  have h6 := e_v n
  have h7 := e_q n
  have h8 := e_c n
  have hdkp : dk = dkp + 1 := rfl
  have hmid : ([RGate.cx (vReg n + dkp) (qReg n + t)]).all
      (RGate.wellFormed (3 * n + ws)) = true :=
    cx_wf (by omega) (by omega) (by omega)
  have hc1 : (achain (vReg n) (pReg n) (cReg n)
      [RGate.cx (vReg n + dkp) (qReg n + t)] 0 dk).all
      (RGate.wellFormed (3 * n + ws)) = true :=
    achain_wf (A := vReg n) (B := pReg n) (c := cReg n) (K := dk)
      (by omega) (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) hmid dk 0 (by omega)
  have hc2 : (achain (vReg n) (pReg n) (cReg n) [] 0 dk).all
      (RGate.wellFormed (3 * n + ws)) = true :=
    achain_wf (A := vReg n) (B := pReg n) (c := cReg n) (K := dk)
      (by omega) (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) rfl dk 0 (by omega)
  have hlx : ∀ v, (loadX (vReg n) dk v).all (RGate.wellFormed (3 * n + ws)) = true :=
    fun v => loadX_wf dk (vReg n) v (by omega)
  have hlc : ∀ v, (loadC (qReg n + t) (vReg n) dk v).all
      (RGate.wellFormed (3 * n + ws)) = true :=
    fun v => loadC_wf (by omega) dk (vReg n) v (by omega) (Or.inr (by omega))
  have hx : ([RGate.x (qReg n + t)]).all (RGate.wellFormed (3 * n + ws)) = true :=
    x_wf (by omega)
  simp only [rstep, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨hlx _, hc1⟩, hlx _⟩, hx⟩, hlc _⟩, hc2⟩, hlc _⟩, hx⟩

theorem rloop_wf {n : Nat} (hk : k ≤ n) : ∀ t, t ≤ k →
    (rloop n t).all (RGate.wellFormed (3 * n + ws)) = true := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    simp only [rloop, List.all_append, Bool.and_eq_true]
    exact ⟨rstep_wf hk (by omega), ih (by omega)⟩

theorem all_reverse {gs : List RGate} {w : Nat} (h : gs.all (RGate.wellFormed w) = true) :
    gs.reverse.all (RGate.wellFormed w) = true := by
  refine List.all_eq_true.mpr (fun g hg => ?_)
  exact List.all_eq_true.mp h g (List.mem_reverse.mp hg)

theorem fwd_wf {n : Nat} (hk : k ≤ n) :
    (fwd n).all (RGate.wellFormed (3 * n + ws)) = true := by
  simp only [fwd, List.all_append, Bool.and_eq_true]
  exact ⟨mloop_wf hk k (Nat.le_refl _), rloop_wf hk k (Nat.le_refl _)⟩

theorem body_wf {n : Nat} (hk : k ≤ n) :
    (body n).all (RGate.wellFormed (3 * n + ws)) = true := by
  have h1 := e_sk
  have h2 := e_dk
  have h3 := e_ws
  have h5 := e_p n
  have hf := fwd_wf hk
  have hcp : (pcopy (pReg n) (2 * n) k).all (RGate.wellFormed (3 * n + ws)) = true :=
    pcopy_wf k (pReg n) (2 * n) (by omega) (by omega) (Or.inr (by omega))
  simp only [body, List.all_append, Bool.and_eq_true]
  exact ⟨⟨hf, hcp⟩, all_reverse hf⟩

theorem wf : ∀ n : Nat, VQ.Reversible.RCircuit.wellFormed (VQ.Curve.PointAddition.Arithmetic.Mul.gen n) = true := by
  intro n
  show (if k ≤ n then body n else []).all (RGate.wellFormed (3 * n + ws)) = true
  by_cases hk : k ≤ n
  · rw [if_pos hk]; exact body_wf hk
  · rw [if_neg hk]; rfl

/-! ## Resource bounds

Every count is a constant.  The gate list does not grow with the width: it is
one gadget of `k` rounds and `k` reduction steps placed at width-dependent
offsets, and it is empty below the width that can hold the modulus.

The loads are bounded rather than counted, since their length depends on the bit
pattern of the constant they carry. -/

theorem achain_length (A B c : Nat) (mid : List RGate) (p st : Nat) :
    (achain A B c mid st p).length = 6 * p + mid.length := by
  induction p generalizing st with
  | zero => simp [achain]
  | succ p ih =>
    simp only [achain, List.length_append, ih (st + 1), maj, uma, List.length_cons,
      List.length_nil]
    omega

theorem achain_ccx (A B c : Nat) (mid : List RGate) (p st : Nat) :
    (achain A B c mid st p).countP RGate.isCcx = 2 * p + mid.countP RGate.isCcx := by
  induction p generalizing st with
  | zero => simp [achain]
  | succ p ih =>
    have hm : (maj (cwire A c st) (B + st) (A + st)).countP RGate.isCcx = 1 := rfl
    have hu : (uma (cwire A c st) (B + st) (A + st)).countP RGate.isCcx = 1 := rfl
    simp only [achain, List.countP_append, ih (st + 1), hm, hu]
    omega

theorem achain_cx (A B c : Nat) (mid : List RGate) (p st : Nat) :
    (achain A B c mid st p).countP RGate.isCx = 4 * p + mid.countP RGate.isCx := by
  induction p generalizing st with
  | zero => simp [achain]
  | succ p ih =>
    have hm : (maj (cwire A c st) (B + st) (A + st)).countP RGate.isCx = 2 := rfl
    have hu : (uma (cwire A c st) (B + st) (A + st)).countP RGate.isCx = 2 := rfl
    simp only [achain, List.countP_append, ih (st + 1), hm, hu]
    omega

theorem loadX_length : ∀ (p D v : Nat), (loadX D p v).length ≤ p := by
  intro p
  induction p with
  | zero => intro D v; simp [loadX]
  | succ p ih =>
    intro D v
    have := ih (D + 1) (v / 2)
    simp only [loadX, List.length_append]
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; simp only [List.length_cons, List.length_nil]; omega
    · rw [if_neg hv]; simp only [List.length_nil]; omega

theorem loadC_length : ∀ (p c D v : Nat), (loadC c D p v).length ≤ p := by
  intro p
  induction p with
  | zero => intro c D v; simp [loadC]
  | succ p ih =>
    intro c D v
    have := ih c (D + 1) (v / 2)
    simp only [loadC, List.length_append]
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; simp only [List.length_cons, List.length_nil]; omega
    · rw [if_neg hv]; simp only [List.length_nil]; omega

theorem loadX_ccx : ∀ (p D v : Nat), (loadX D p v).countP RGate.isCcx = 0 := by
  intro p
  induction p with
  | zero => intro D v; rfl
  | succ p ih =>
    intro D v
    have := ih (D + 1) (v / 2)
    simp only [loadX, List.countP_append, this]
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; rfl
    · rw [if_neg hv]; rfl

theorem loadX_cx : ∀ (p D v : Nat), (loadX D p v).countP RGate.isCx = 0 := by
  intro p
  induction p with
  | zero => intro D v; rfl
  | succ p ih =>
    intro D v
    have := ih (D + 1) (v / 2)
    simp only [loadX, List.countP_append, this]
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; rfl
    · rw [if_neg hv]; rfl

theorem loadC_ccx : ∀ (p c D v : Nat), (loadC c D p v).countP RGate.isCcx = 0 := by
  intro p
  induction p with
  | zero => intro c D v; rfl
  | succ p ih =>
    intro c D v
    have := ih c (D + 1) (v / 2)
    simp only [loadC, List.countP_append, this]
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; rfl
    · rw [if_neg hv]; rfl

theorem loadC_cx : ∀ (p c D v : Nat), (loadC c D p v).countP RGate.isCx ≤ p := by
  intro p
  induction p with
  | zero => intro c D v; simp [loadC]
  | succ p ih =>
    intro c D v
    have := ih c (D + 1) (v / 2)
    simp only [loadC, List.countP_append]
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]
      have h1 : ([RGate.cx c D]).countP RGate.isCx = 1 := rfl
      omega
    · rw [if_neg hv]
      have h1 : ([] : List RGate).countP RGate.isCx = 0 := rfl
      omega

theorem pcopy_length : ∀ (p A D : Nat), (pcopy A D p).length = p := by
  intro p
  induction p with
  | zero => intro A D; rfl
  | succ p ih => intro A D; simp only [pcopy, List.length_cons, ih (A + 1) (D + 1)]

theorem pcopy_ccx : ∀ (p A D : Nat), (pcopy A D p).countP RGate.isCcx = 0 := by
  intro p
  induction p with
  | zero => intro A D; rfl
  | succ p ih => intro A D; simp only [pcopy, List.countP_cons, ih (A + 1) (D + 1)]; rfl

theorem pcopy_cx : ∀ (p A D : Nat), (pcopy A D p).countP RGate.isCx = p := by
  intro p
  induction p with
  | zero => intro A D; rfl
  | succ p ih =>
    intro A D
    have h : ((pcopy (A + 1) (D + 1) p).countP RGate.isCx) = p := ih (A + 1) (D + 1)
    simp only [pcopy, List.countP_cons, h]
    rfl

theorem ccopy_length : ∀ (p ctl A D : Nat), (ccopy ctl A D p).length = p := by
  intro p
  induction p with
  | zero => intro ctl A D; rfl
  | succ p ih => intro ctl A D; simp only [ccopy, List.length_cons, ih ctl (A + 1) (D + 1)]

theorem ccopy_ccx : ∀ (p ctl A D : Nat), (ccopy ctl A D p).countP RGate.isCcx = p := by
  intro p
  induction p with
  | zero => intro ctl A D; rfl
  | succ p ih =>
    intro ctl A D
    have h : ((ccopy ctl (A + 1) (D + 1) p).countP RGate.isCcx) = p := ih ctl (A + 1) (D + 1)
    simp only [ccopy, List.countP_cons, h]
    rfl

theorem ccopy_cx : ∀ (p ctl A D : Nat), (ccopy ctl A D p).countP RGate.isCx = 0 := by
  intro p
  induction p with
  | zero => intro ctl A D; rfl
  | succ p ih =>
    intro ctl A D
    simp only [ccopy, List.countP_cons, ih ctl (A + 1) (D + 1)]
    rfl

/-- The three counts of one product round. -/
theorem mround_counts (n t : Nat) :
    (mround n t).length = 2 * k + 6 * sk ∧
      (mround n t).countP RGate.isCcx = 2 * k + 2 * sk ∧
      (mround n t).countP RGate.isCx = 4 * sk := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [mround, List.length_append, ccopy_length, achain_length, List.length_nil]
    omega
  · simp only [mround, List.countP_append, ccopy_ccx, achain_ccx]
    have h : ([] : List RGate).countP RGate.isCcx = 0 := rfl
    omega
  · simp only [mround, List.countP_append, ccopy_cx, achain_cx]
    have h : ([] : List RGate).countP RGate.isCx = 0 := rfl
    omega

theorem mloop_counts (n : Nat) : ∀ t,
    (mloop n t).length = t * (2 * k + 6 * sk) ∧
      (mloop n t).countP RGate.isCcx = t * (2 * k + 2 * sk) ∧
      (mloop n t).countP RGate.isCx = t * (4 * sk) := by
  intro t
  induction t with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ t ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    obtain ⟨r1, r2, r3⟩ := mround_counts n t
    have s1 : (t + 1) * (2 * k + 6 * sk) = t * (2 * k + 6 * sk) + (2 * k + 6 * sk) :=
      Nat.succ_mul t _
    have s2 : (t + 1) * (2 * k + 2 * sk) = t * (2 * k + 2 * sk) + (2 * k + 2 * sk) :=
      Nat.succ_mul t _
    have s3 : (t + 1) * (4 * sk) = t * (4 * sk) + 4 * sk := Nat.succ_mul t _
    refine ⟨?_, ?_, ?_⟩
    · rw [show mloop n (t + 1) = mloop n t ++ mround n t from rfl, List.length_append, i1, r1, s1]
    · rw [show mloop n (t + 1) = mloop n t ++ mround n t from rfl, List.countP_append, i2, r2, s2]
    · rw [show mloop n (t + 1) = mloop n t ++ mround n t from rfl, List.countP_append, i3, r3, s3]

/-- The three counts of one reduction step.  Only the Toffoli count is exact:
the two constant loads cost one gate per set bit of the constant. -/
theorem rstep_counts (n t : Nat) :
    (rstep n t).length ≤ 16 * dk + 3 ∧
      (rstep n t).countP RGate.isCcx = 4 * dk ∧
      (rstep n t).countP RGate.isCx ≤ 10 * dk + 1 := by
  have l1 := loadX_length dk (vReg n) (2 ^ dk - m * 2 ^ t)
  have l2 := loadC_length dk (qReg n + t) (vReg n) (m * 2 ^ t)
  have l3 := loadC_cx dk (qReg n + t) (vReg n) (m * 2 ^ t)
  have e1 : ([RGate.cx (vReg n + dkp) (qReg n + t)]).length = 1 := rfl
  have e2 : ([RGate.cx (vReg n + dkp) (qReg n + t)]).countP RGate.isCcx = 0 := rfl
  have e3 : ([RGate.cx (vReg n + dkp) (qReg n + t)]).countP RGate.isCx = 1 := rfl
  have e4 : ([RGate.x (qReg n + t)]).length = 1 := rfl
  have e5 : ([RGate.x (qReg n + t)]).countP RGate.isCcx = 0 := rfl
  have e6 : ([RGate.x (qReg n + t)]).countP RGate.isCx = 0 := rfl
  have e7 : ([] : List RGate).countP RGate.isCcx = 0 := rfl
  have e8 : ([] : List RGate).countP RGate.isCx = 0 := rfl
  have e9 : ([] : List RGate).length = 0 := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [rstep, List.length_append, achain_length, e1, e4, e9]
    omega
  · simp only [rstep, List.countP_append, achain_ccx, loadX_ccx, loadC_ccx, e2, e5, e7]
    omega
  · simp only [rstep, List.countP_append, achain_cx, loadX_cx, e3, e6, e8]
    omega

theorem rloop_counts (n : Nat) : ∀ t,
    (rloop n t).length ≤ t * (16 * dk + 3) ∧
      (rloop n t).countP RGate.isCcx = t * (4 * dk) ∧
      (rloop n t).countP RGate.isCx ≤ t * (10 * dk + 1) := by
  intro t
  induction t with
  | zero => exact ⟨Nat.le_refl _, rfl, Nat.le_refl _⟩
  | succ t ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    obtain ⟨r1, r2, r3⟩ := rstep_counts n t
    have s1 : (t + 1) * (16 * dk + 3) = t * (16 * dk + 3) + (16 * dk + 3) := Nat.succ_mul t _
    have s2 : (t + 1) * (4 * dk) = t * (4 * dk) + 4 * dk := Nat.succ_mul t _
    have s3 : (t + 1) * (10 * dk + 1) = t * (10 * dk + 1) + (10 * dk + 1) := Nat.succ_mul t _
    refine ⟨?_, ?_, ?_⟩
    · rw [show rloop n (t + 1) = rstep n t ++ rloop n t from rfl, List.length_append, s1]
      omega
    · rw [show rloop n (t + 1) = rstep n t ++ rloop n t from rfl, List.countP_append, i2, r2, s2]
      omega
    · rw [show rloop n (t + 1) = rstep n t ++ rloop n t from rfl, List.countP_append, s3]
      omega

theorem fwd_counts (n : Nat) :
    (fwd n).length ≤ k * (2 * k + 6 * sk) + k * (16 * dk + 3) ∧
      (fwd n).countP RGate.isCcx = k * (2 * k + 2 * sk) + k * (4 * dk) ∧
      (fwd n).countP RGate.isCx ≤ k * (4 * sk) + k * (10 * dk + 1) := by
  obtain ⟨m1, m2, m3⟩ := mloop_counts n k
  obtain ⟨r1, r2, r3⟩ := rloop_counts n k
  refine ⟨?_, ?_, ?_⟩
  · rw [show fwd n = mloop n k ++ rloop n k from rfl, List.length_append, m1]; omega
  · rw [show fwd n = mloop n k ++ rloop n k from rfl, List.countP_append, m2, r2]
  · rw [show fwd n = mloop n k ++ rloop n k from rfl, List.countP_append, m3]; omega

theorem body_counts (n : Nat) :
    (body n).length ≤ 2 * (k * (2 * k + 6 * sk) + k * (16 * dk + 3)) + k ∧
      (body n).countP RGate.isCcx = 2 * (k * (2 * k + 2 * sk) + k * (4 * dk)) ∧
      (body n).countP RGate.isCx ≤ 2 * (k * (4 * sk) + k * (10 * dk + 1)) + k := by
  obtain ⟨f1, f2, f3⟩ := fwd_counts n
  have hr1 : (fwd n).reverse.length = (fwd n).length := List.length_reverse
  have hr2 : (fwd n).reverse.countP RGate.isCcx = (fwd n).countP RGate.isCcx :=
    List.countP_reverse
  have hr3 : (fwd n).reverse.countP RGate.isCx = (fwd n).countP RGate.isCx :=
    List.countP_reverse
  have p1 := pcopy_length k (pReg n) (2 * n)
  have p2 := pcopy_ccx k (pReg n) (2 * n)
  have p3 := pcopy_cx k (pReg n) (2 * n)
  refine ⟨?_, ?_, ?_⟩
  · simp only [body, List.length_append, hr1, p1]; omega
  · simp only [body, List.countP_append, hr2, p2, f2]; omega
  · simp only [body, List.countP_append, hr3, p3]; omega

theorem toffoli_le : ∀ n : Nat,
    VQ.Circuit.toffoliCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Mul.gen n)) ≤ 1573888 := by
  intro n
  rw [VQ.Reversible.toffoliCount_compile]
  show (if k ≤ n then body n else []).countP RGate.isCcx ≤ 1573888
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    have h := (body_counts n).2.1
    have e1 : k = 256 := rfl
    have e2 : sk = 257 := rfl
    have e3 : dk = 512 := rfl
    rw [e1, e2, e3] at h
    omega
  · rw [if_neg hk]; decide

theorem cnot_le : ∀ n : Nat,
    VQ.Circuit.cnotCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Mul.gen n)) ≤ 3148544 := by
  intro n
  rw [VQ.Reversible.cnotCount_compile]
  show (if k ≤ n then body n else []).countP RGate.isCx ≤ 3148544
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    have h := (body_counts n).2.2
    have e1 : k = 256 := rfl
    have e2 : sk = 257 := rfl
    have e3 : dk = 512 := rfl
    rw [e1, e2, e3] at h
    omega
  · rw [if_neg hk]; decide

/-! ### Wire bounds

`usedWires` counts the distinct wires a gate list names, which is the length of
a deduplicated list rather than a count over the gates, so the bound goes
through a pigeonhole: a deduplicated list whose entries all lie in a list of
`3 * k + ws` wires has at most that many entries. -/

theorem dedup_le : ∀ (K : Nat) (s l : List Nat), s.length ≤ K → (∀ x ∈ l, x ∈ s) →
    l.eraseDups.length ≤ s.length := by
  intro K
  induction K with
  | zero =>
    intro s l hs hl
    cases l with
    | nil => simp
    | cons a as =>
      have hnil : s = [] := List.eq_nil_of_length_eq_zero (by omega)
      have := hl a List.mem_cons_self
      rw [hnil] at this
      exact absurd this (by simp)
  | succ K ih =>
    intro s l hs hl
    cases l with
    | nil => simp
    | cons a as =>
      have ha : a ∈ s := hl a List.mem_cons_self
      have hpos : 0 < s.length := by
        cases s with
        | nil => exact absurd ha (by simp)
        | cons x xs => simp
      have hlen : (s.erase a).length + 1 = s.length := by
        rw [List.length_erase_of_mem ha]
        omega
      have hsub : ∀ x ∈ as.filter (fun b => !b == a), x ∈ s.erase a := by
        intro x hx
        have hx' := List.mem_filter.mp hx
        have hne : x ≠ a := by
          have h2 := hx'.2
          simp at h2
          exact h2
        exact (List.mem_erase_of_ne hne).mpr (hl x (List.mem_cons_of_mem a hx'.1))
      have hrec := ih (s.erase a) (as.filter (fun b => !b == a)) (by omega) hsub
      rw [List.eraseDups_cons, List.length_cons]
      omega

/-- The wires the gadget names: the low `k` of each of the three data fields and
the whole workspace. -/
def uw (n : Nat) : List Nat :=
  List.range k ++ (List.range k).map (fun j => n + j)
    ++ (List.range k).map (fun j => 2 * n + j)
    ++ (List.range ws).map (fun j => 3 * n + j)

theorem uw_length (n : Nat) : (uw n).length = 3 * k + ws := by
  simp only [uw, List.length_append, List.length_map, List.length_range]
  omega

theorem mem_uw_a {n j : Nat} (h : j < k) : j ∈ uw n := by
  simp only [uw, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inl h))

theorem mem_uw_b {n j : Nat} (h : j < k) : n + j ∈ uw n := by
  simp only [uw, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl (Or.inr ⟨j, h, rfl⟩))

theorem mem_uw_p {n j : Nat} (h : j < k) : 2 * n + j ∈ uw n := by
  simp only [uw, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨j, h, rfl⟩)

theorem mem_uw_w {n j : Nat} (h : j < ws) : 3 * n + j ∈ uw n := by
  simp only [uw, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inr ⟨j, h, rfl⟩

theorem achain_mem {A B c K : Nat} {mid : List RGate} {P : Nat → Prop}
    (hA : ∀ j, j < K → P (A + j)) (hB : ∀ j, j < K → P (B + j)) (hc : P c)
    (hmid : ∀ g ∈ mid, ∀ q ∈ g.wires, P q) :
    ∀ p st, st + p = K → ∀ g ∈ achain A B c mid st p, ∀ q ∈ g.wires, P q := by
  intro p
  induction p with
  | zero => intro st _; exact hmid
  | succ p ih =>
    intro st hst g hg q hq
    have hcw : P (cwire A c st) := by
      cases st with
      | zero => exact hc
      | succ s => exact hA s (by omega)
    have hpa : P (A + st) := hA st (by omega)
    have hpb : P (B + st) := hB st (by omega)
    simp only [achain, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · simp only [maj, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;>
        · simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl <;> assumption
    · exact ih (st + 1) (by omega) g hg q hq
    · simp only [uma, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;>
        · simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl <;> assumption

theorem loadX_mem {P : Nat → Prop} : ∀ (p D v : Nat), (∀ j, j < p → P (D + j)) →
    ∀ g ∈ loadX D p v, ∀ q ∈ g.wires, P q := by
  intro p
  induction p with
  | zero => intro D v _ g hg; simp [loadX] at hg
  | succ p ih =>
    intro D v hD g hg q hq
    simp only [loadX, List.mem_append] at hg
    rcases hg with hg | hg
    · have h0 : P D := by have := hD 0 (by omega); simpa using this
      by_cases hv : v % 2 = 1
      · rw [if_pos hv] at hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        subst hg
        simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        exact h0
      · rw [if_neg hv] at hg; simp at hg
    · exact ih (D + 1) (v / 2) (fun j hj => by
        have := hD (j + 1) (by omega)
        have he : D + 1 + j = D + (j + 1) := by omega
        rw [he]; exact this) g hg q hq

theorem loadC_mem {P : Nat → Prop} {c : Nat} (hc : P c) :
    ∀ (p D v : Nat), (∀ j, j < p → P (D + j)) → ∀ g ∈ loadC c D p v, ∀ q ∈ g.wires, P q := by
  intro p
  induction p with
  | zero => intro D v _ g hg; simp [loadC] at hg
  | succ p ih =>
    intro D v hD g hg q hq
    simp only [loadC, List.mem_append] at hg
    rcases hg with hg | hg
    · have h0 : P D := by have := hD 0 (by omega); simpa using this
      by_cases hv : v % 2 = 1
      · rw [if_pos hv] at hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        subst hg
        simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hc
        · exact h0
      · rw [if_neg hv] at hg; simp at hg
    · exact ih (D + 1) (v / 2) (fun j hj => by
        have := hD (j + 1) (by omega)
        have he : D + 1 + j = D + (j + 1) := by omega
        rw [he]; exact this) g hg q hq

theorem pcopy_mem {P : Nat → Prop} : ∀ (p A D : Nat), (∀ j, j < p → P (A + j)) →
    (∀ j, j < p → P (D + j)) → ∀ g ∈ pcopy A D p, ∀ q ∈ g.wires, P q := by
  intro p
  induction p with
  | zero => intro A D _ _ g hg; simp [pcopy] at hg
  | succ p ih =>
    intro A D hA hD g hg q hq
    have hA0 : P A := by have := hA 0 (by omega); simpa using this
    have hD0 : P D := by have := hD 0 (by omega); simpa using this
    simp only [pcopy, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hA0
      · exact hD0
    · refine ih (A + 1) (D + 1) (fun j hj => ?_) (fun j hj => ?_) g hg q hq
      · have := hA (j + 1) (by omega)
        have he : A + 1 + j = A + (j + 1) := by omega
        rw [he]; exact this
      · have := hD (j + 1) (by omega)
        have he : D + 1 + j = D + (j + 1) := by omega
        rw [he]; exact this

theorem ccopy_mem {P : Nat → Prop} {ctl : Nat} (hctl : P ctl) :
    ∀ (p A D : Nat), (∀ j, j < p → P (A + j)) → (∀ j, j < p → P (D + j)) →
      ∀ g ∈ ccopy ctl A D p, ∀ q ∈ g.wires, P q := by
  intro p
  induction p with
  | zero => intro A D _ _ g hg; simp [ccopy] at hg
  | succ p ih =>
    intro A D hA hD g hg q hq
    have hA0 : P A := by have := hA 0 (by omega); simpa using this
    have hD0 : P D := by have := hD 0 (by omega); simpa using this
    simp only [ccopy, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact hctl
      · exact hA0
      · exact hD0
    · refine ih (A + 1) (D + 1) (fun j hj => ?_) (fun j hj => ?_) g hg q hq
      · have := hA (j + 1) (by omega)
        have he : A + 1 + j = A + (j + 1) := by omega
        rw [he]; exact this
      · have := hD (j + 1) (by omega)
        have he : D + 1 + j = D + (j + 1) := by omega
        rw [he]; exact this

theorem mround_mem {n : Nat} {P : Nat → Prop} (_hk : k ≤ n) {t : Nat} (ht : t < k)
    (hA : ∀ j, j < k → P j) (hB : ∀ j, j < k → P (n + j))
    (hW : ∀ j, j < ws → P (3 * n + j)) :
    ∀ g ∈ mround n t, ∀ q ∈ g.wires, P q := by
  have h1 := e_sk
  have h2 := e_dk
  have h3 := e_ws
  have hA' : ∀ j, j < k → P (0 + j) := by
    intro j hj; rw [Nat.zero_add]; exact hA j hj
  have hctl : P (n + t) := hB t ht
  have hS : ∀ j, j < sk → P (sReg n + j) := by
    intro j hj
    have he : sReg n + j = 3 * n + j := rfl
    rw [he]; exact hW j (by omega)
  have hP : ∀ j, j < sk → P (pReg n + t + j) := by
    intro j hj
    have he : pReg n + t + j = 3 * n + (sk + t + j) := by rw [e_p]; omega
    rw [he]; exact hW _ (by omega)
  have hc : P (cReg n) := by
    have he : cReg n = 3 * n + (sk + dk + dk + k) := by rw [e_c]; omega
    rw [he]; exact hW _ (by omega)
  have hcp : ∀ g ∈ ccopy (n + t) 0 (sReg n) k, ∀ q ∈ g.wires, P q :=
    ccopy_mem hctl k 0 (sReg n) hA' (fun j hj => hS j (by omega))
  have hch := achain_mem (K := sk) (mid := []) hS hP hc (by intro g hg; cases hg) sk 0 (by omega)
  intro g hg
  simp only [mround, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact hcp g hg
  · exact hch g hg
  · exact hcp g hg

theorem mloop_mem {n : Nat} {P : Nat → Prop} (hk : k ≤ n)
    (hA : ∀ j, j < k → P j) (hB : ∀ j, j < k → P (n + j))
    (hW : ∀ j, j < ws → P (3 * n + j)) : ∀ t, t ≤ k →
    ∀ g ∈ mloop n t, ∀ q ∈ g.wires, P q := by
  intro t
  induction t with
  | zero => intro _ g hg; cases hg
  | succ t ih =>
    intro ht g hg
    have hg' : g ∈ mloop n t ++ mround n t := hg
    rcases List.mem_append.mp hg' with h | h
    · exact ih (by omega) g h
    · exact mround_mem hk (by omega) hA hB hW g h

theorem rstep_mem {n : Nat} {P : Nat → Prop} (_hk : k ≤ n) {t : Nat} (ht : t < k)
    (hW : ∀ j, j < ws → P (3 * n + j)) :
    ∀ g ∈ rstep n t, ∀ q ∈ g.wires, P q := by
  have h1 := e_sk
  have h2 := e_dk
  have h3 := e_ws
  have hdkp : dk = dkp + 1 := rfl
  have hV : ∀ j, j < dk → P (vReg n + j) := by
    intro j hj
    have he : vReg n + j = 3 * n + (sk + dk + j) := by rw [e_v]; omega
    rw [he]; exact hW _ (by omega)
  have hP : ∀ j, j < dk → P (pReg n + j) := by
    intro j hj
    have he : pReg n + j = 3 * n + (sk + j) := by rw [e_p]; omega
    rw [he]; exact hW _ (by omega)
  have hq : P (qReg n + t) := by
    have he : qReg n + t = 3 * n + (sk + dk + dk + t) := by rw [e_q]; omega
    rw [he]; exact hW _ (by omega)
  have hc : P (cReg n) := by
    have he : cReg n = 3 * n + (sk + dk + dk + k) := by rw [e_c]; omega
    rw [he]; exact hW _ (by omega)
  have hmid : ∀ g ∈ [RGate.cx (vReg n + dkp) (qReg n + t)], ∀ q ∈ g.wires, P q := by
    intro g hg q hqq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hqq
    rcases hqq with rfl | rfl
    · exact hV dkp (by omega)
    · exact hq
  have hx : ∀ g ∈ [RGate.x (qReg n + t)], ∀ q ∈ g.wires, P q := by
    intro g hg q hqq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hqq
    subst hqq
    exact hq
  have h4 := achain_mem (K := dk) hV hP hc hmid dk 0 (by omega)
  have h5 := achain_mem (K := dk) (mid := []) hV hP hc (by intro g hg; cases hg) dk 0 (by omega)
  have h6 : ∀ v, ∀ g ∈ loadX (vReg n) dk v, ∀ q ∈ g.wires, P q :=
    fun v => loadX_mem dk (vReg n) v hV
  have h7 : ∀ v, ∀ g ∈ loadC (qReg n + t) (vReg n) dk v, ∀ q ∈ g.wires, P q :=
    fun v => loadC_mem hq dk (vReg n) v hV
  intro g hg
  simp only [rstep, List.mem_append] at hg
  rcases hg with ((((((hg | hg) | hg) | hg) | hg) | hg) | hg) | hg
  · exact h6 _ g hg
  · exact h4 g hg
  · exact h6 _ g hg
  · exact hx g hg
  · exact h7 _ g hg
  · exact h5 g hg
  · exact h7 _ g hg
  · exact hx g hg

theorem rloop_mem {n : Nat} {P : Nat → Prop} (hk : k ≤ n)
    (hW : ∀ j, j < ws → P (3 * n + j)) : ∀ t, t ≤ k →
    ∀ g ∈ rloop n t, ∀ q ∈ g.wires, P q := by
  intro t
  induction t with
  | zero => intro _ g hg; cases hg
  | succ t ih =>
    intro ht g hg
    have hg' : g ∈ rstep n t ++ rloop n t := hg
    rcases List.mem_append.mp hg' with h | h
    · exact rstep_mem hk (by omega) hW g h
    · exact ih (by omega) g h

theorem fwd_mem {n : Nat} {P : Nat → Prop} (hk : k ≤ n)
    (hA : ∀ j, j < k → P j) (hB : ∀ j, j < k → P (n + j))
    (hW : ∀ j, j < ws → P (3 * n + j)) : ∀ g ∈ fwd n, ∀ q ∈ g.wires, P q := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact mloop_mem hk hA hB hW k (Nat.le_refl _) g h
  · exact rloop_mem hk hW k (Nat.le_refl _) g h

theorem body_mem {n : Nat} {P : Nat → Prop} (hk : k ≤ n)
    (hA : ∀ j, j < k → P j) (hB : ∀ j, j < k → P (n + j))
    (hD : ∀ j, j < k → P (2 * n + j)) (hW : ∀ j, j < ws → P (3 * n + j)) :
    ∀ g ∈ body n, ∀ q ∈ g.wires, P q := by
  have h1 := e_sk
  have h3 := e_ws
  have hcp : ∀ g ∈ pcopy (pReg n) (2 * n) k, ∀ q ∈ g.wires, P q := by
    refine pcopy_mem k (pReg n) (2 * n) (fun j hj => ?_) (fun j hj => hD j hj)
    have he : pReg n + j = 3 * n + (sk + j) := by rw [e_p]; omega
    rw [he]; exact hW _ (by omega)
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · rcases List.mem_append.mp h with h' | h'
    · exact fwd_mem hk hA hB hW g h'
    · exact hcp g h'
  · exact fwd_mem hk hA hB hW g (List.mem_reverse.mp h)

/-- Every wire the gadget names is one of the wires it is allowed to name. -/
theorem body_uw {n : Nat} (hk : k ≤ n) : ∀ g ∈ body n, ∀ q ∈ g.wires, q ∈ uw n :=
  body_mem (P := fun q => q ∈ uw n) hk (fun _ hj => mem_uw_a hj) (fun _ hj => mem_uw_b hj)
    (fun _ hj => mem_uw_p hj) (fun _ hj => mem_uw_w hj)

/-- The forward pass avoids every wire of the product field, so the residue can
be copied out between the forward pass and its reverse. -/
theorem fwd_out {n : Nat} (hk : k ≤ n) :
    ∀ g ∈ fwd n, ∀ q ∈ g.wires, q < 2 * n ∨ 2 * n + k ≤ q := by
  have hkp := k_pos
  exact fwd_mem (P := fun q => q < 2 * n ∨ 2 * n + k ≤ q) hk
    (fun j hj => Or.inl (by omega)) (fun j hj => Or.inl (by omega))
    (fun j hj => Or.inr (by omega))


theorem compileGate_wires {g : RGate} {p : Gate} (hp : p ∈ VQ.Reversible.compileGate g)
    {q : Nat} (hq : q ∈ p.wires) : q ∈ g.wires := by
  cases g with
  | x a =>
    have he : p = Gate.x a := by simpa [VQ.Reversible.compileGate] using hp
    subst he
    simpa [Gate.wires, RGate.wires] using hq
  | cx a b =>
    have he : p = Gate.cx a b := by simpa [VQ.Reversible.compileGate] using hp
    subst he
    simpa [Gate.wires, RGate.wires] using hq
  | ccx a b c =>
    have hm : p = Gate.h c ∨ p = Gate.ccz a b c ∨ p = Gate.h c := by
      simpa [VQ.Reversible.compileGate, VQ.Circuit.ccx] using hp
    rcases hm with rfl | rfl | rfl
    · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      simp [RGate.wires]
    · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      simpa [RGate.wires] using hq
    · simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq
      simp [RGate.wires]

theorem wires_le : ∀ n : Nat,
    VQ.Circuit.usedWires (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Mul.gen n)) ≤ 2306 := by
  intro n
  by_cases hk : k ≤ n
  · have hsub : ∀ q ∈ (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Mul.gen n)).gates.flatMap Gate.wires,
        q ∈ uw n := by
      intro q hq
      obtain ⟨pg, hp, hqp⟩ := List.exists_of_mem_flatMap hq
      have hp' : pg ∈ (VQ.Curve.PointAddition.Arithmetic.Mul.gen n).gates.flatMap VQ.Reversible.compileGate := hp
      obtain ⟨g, hg, hpg⟩ := List.exists_of_mem_flatMap hp'
      have hg' : g ∈ body n := by
        have : (VQ.Curve.PointAddition.Arithmetic.Mul.gen n).gates = if k ≤ n then body n else [] := rfl
        rw [this, if_pos hk] at hg
        exact hg
      exact body_uw hk g hg' q (compileGate_wires hpg hqp)
    have h := dedup_le (3 * k + ws) (uw n)
      ((VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Mul.gen n)).gates.flatMap Gate.wires)
      (Nat.le_of_eq (uw_length n)) hsub
    rw [uw_length] at h
    show ((VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Mul.gen n)).gates.flatMap Gate.wires).eraseDups.length ≤ 2306
    have e1 : k = 256 := rfl
    have e2 : ws = 1538 := rfl
    omega
  · show ((VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Mul.gen n)).gates.flatMap Gate.wires).eraseDups.length ≤ 2306
    have he : (VQ.Curve.PointAddition.Arithmetic.Mul.gen n).gates = [] := by
      have : (VQ.Curve.PointAddition.Arithmetic.Mul.gen n).gates = if k ≤ n then body n else [] := rfl
      rw [this, if_neg hk]
    have : (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Mul.gen n)).gates = [] := by
      show (VQ.Curve.PointAddition.Arithmetic.Mul.gen n).gates.flatMap VQ.Reversible.compileGate = []
      rw [he]; rfl
    rw [this]
    simp

/-! ## Correctness

The proof evaluates one basis index at a time.  `bv i q` gives the value on wire
`q`, and `readField i off len` gives the value of a contiguous wire range.  Each
gate action is a single-wire write on `Nat`, reducing correctness to arithmetic
on basis indices.  The lemmas through `VQ.Curve.PointAddition.Arithmetic.Mul.act_ccx` establish the required
bit-level gate semantics. -/

/-- The value on wire `q` of the basis index `i`. -/
def bv (i q : Nat) : Nat := if i.testBit q then 1 else 0

theorem bv_lt (i q : Nat) : bv i q < 2 := by
  unfold bv; split <;> omega

theorem readField_one (i q : Nat) : readField i q 1 = bv i q := by
  have h : (i >>> q).testBit 0 = i.testBit q := by simp
  show (i >>> q) % 2 ^ 1 = bv i q
  rw [Nat.pow_one, bv, ← h, Nat.testBit_zero]
  by_cases hx : (i >>> q) % 2 = 1 <;> simp [hx] <;> omega

theorem writeField_read (i off len : Nat) :
    writeField i off len (readField i off len) = i := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases hlo : off ≤ b
  · by_cases hhi : b < off + len
    · rw [testBit_writeField_inside hlo hhi, testBit_readField]
      simp [show b - off < len by omega, show off + (b - off) = b by omega]
    · rw [testBit_writeField_outside (Or.inr (by omega))]
  · rw [testBit_writeField_outside (Or.inl (by omega))]

theorem writeField_zero (i off v : Nat) : writeField i off 0 v = i := by
  show (i % 2 ^ off ||| (i >>> (off + 0)) <<< (off + 0)) ||| (v % 2 ^ 0) <<< off = i
  rw [Nat.add_zero, Nat.pow_zero, Nat.mod_one, Nat.zero_shiftLeft, Nat.or_zero]
  exact Layout.mod_or_shiftLeft_shiftRight i off

theorem writeField_mod (i off n v : Nat) :
    writeField i off n (v % 2 ^ n) = writeField i off n v := by
  unfold writeField
  rw [Nat.mod_mod_of_dvd _ (Nat.dvd_refl (2 ^ n))]

theorem write_congr {i q v w : Nat} (h : v % 2 = w % 2) :
    writeField i q 1 v = writeField i q 1 w := by
  rw [← writeField_mod i q 1 v, ← writeField_mod i q 1 w, Nat.pow_one, h]

theorem write_of_bv {i q v : Nat} (h : v % 2 = bv i q) : writeField i q 1 v = i := by
  rw [← writeField_mod i q 1 v, Nat.pow_one, h, ← readField_one, writeField_read]

theorem bv_write_self (i q v : Nat) : bv (writeField i q 1 v) q = v % 2 := by
  rw [← readField_one, readField_writeField, Nat.pow_one]

theorem bv_write_ne {i q r v : Nat} (h : r ≠ q) : bv (writeField i q 1 v) r = bv i r := by
  rw [← readField_one, ← readField_one, readField_writeField_of_disjoint (by omega)]

theorem bv_write_out {i off len v r : Nat} (h : r < off ∨ off + len ≤ r) :
    bv (writeField i off len v) r = bv i r := by
  rw [← readField_one, ← readField_one, readField_writeField_of_disjoint (by omega)]

theorem readField_succ (i off p : Nat) :
    readField i off (p + 1) = bv i off + 2 * readField i (off + 1) p := by
  rw [← readField_one]
  show (i >>> off) % 2 ^ (p + 1) = (i >>> off) % 2 ^ 1 + 2 * ((i >>> (off + 1)) % 2 ^ p)
  rw [Nat.pow_one, Nat.pow_succ', Nat.mod_mul, Nat.shiftRight_add]
  simp [Nat.shiftRight_eq_div_pow]

theorem writeField_succ (i off p v : Nat) :
    writeField i off (p + 1) v = writeField (writeField i off 1 (v % 2)) (off + 1) p (v / 2) := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases h1 : b < off
  · rw [testBit_writeField_outside (Or.inl h1), testBit_writeField_outside (Or.inl (by omega)),
      testBit_writeField_outside (Or.inl h1)]
  · by_cases h2 : b < off + 1
    · have hb : b = off := by omega
      subst hb
      rw [testBit_writeField_inside (Nat.le_refl _) (by omega),
        testBit_writeField_outside (Or.inl (by omega)),
        testBit_writeField_inside (Nat.le_refl _) (by omega), Nat.sub_self, Nat.testBit_zero,
        Nat.testBit_zero]
      have : v % 2 % 2 = v % 2 := by omega
      rw [this]
    · by_cases h3 : b < off + (p + 1)
      · rw [testBit_writeField_inside (by omega) h3,
          testBit_writeField_inside (by omega) (by omega), Nat.testBit_div_two]
        congr 1
        omega
      · rw [testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_outside (Or.inr (by omega))]

/-- A clear field has clear sub-runs, so the workspace hypothesis applies to
each workspace register. -/
theorem readField_sub_zero {i off K d e : Nat} (h : readField i off K = 0) (hde : d + e ≤ K) :
    readField i (off + d) e = 0 := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  rw [testBit_readField, Nat.zero_testBit]
  by_cases hb : b < e
  · have h2 : (readField i off K).testBit (d + b) = false := by rw [h]; exact Nat.zero_testBit _
    rw [testBit_readField] at h2
    have h3 : d + b < K := by omega
    simp only [h3, decide_true, Bool.true_and] at h2
    have he : off + d + b = off + (d + b) := by omega
    rw [he]
    simp [h2]
  · simp [hb]

/-- A field read below its own width is the same field read narrower. -/
theorem readField_narrow (i off p q : Nat) (h : p ≤ q) :
    readField i off p = readField i off q % 2 ^ p := by
  show (i >>> off) % 2 ^ p = ((i >>> off) % 2 ^ q) % 2 ^ p
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]

/-- If a wide field contains a narrow value, writing another narrow value to it
equals a narrow-field write.  A gadget that acts on only the low `k` bits of a field
therefore satisfies a specification over the full `n`-bit field. -/
theorem write_widen {i off p q v : Nat} (hpq : p ≤ q) (hv : v < 2 ^ p)
    (hi : readField i off q < 2 ^ p) :
    writeField i off p v = writeField i off q v := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases h1 : b < off
  · rw [testBit_writeField_outside (Or.inl h1), testBit_writeField_outside (Or.inl h1)]
  · by_cases h2 : b < off + p
    · rw [testBit_writeField_inside (by omega) h2, testBit_writeField_inside (by omega) (by omega)]
    · by_cases h3 : b < off + q
      · rw [testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_inside (by omega) h3]
        have hvb : v.testBit (b - off) = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))
        have hib : (readField i off q).testBit (b - off) = false :=
          Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) (by omega)))
        rw [testBit_readField] at hib
        have h4 : b - off < q := by omega
        simp only [h4, decide_true, Bool.true_and] at hib
        have he : off + (b - off) = b := by omega
        rw [he] at hib
        rw [hib, hvb]
      · rw [testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_outside (Or.inr (by omega))]

/-! ### Two-part field decomposition

A window of the accumulator is a field of it, and the round for bit `t` writes
that window rather than the whole register.  These four lemmas carry a
statement about the window to a statement about the register: a read splits into
low and high parts, a write splits into a write of each part, a sub-read of a
written field reads the value written, and a write of a window is a write of the
whole field when the parts outside the window are left where they were. -/

theorem readField_split (i off p q : Nat) :
    readField i off (p + q) = readField i off p + 2 ^ p * readField i (off + p) q := by
  show (i >>> off) % 2 ^ (p + q) = (i >>> off) % 2 ^ p + 2 ^ p * ((i >>> (off + p)) % 2 ^ q)
  rw [Nat.pow_add, Nat.mod_mul, Nat.shiftRight_add]
  simp [Nat.shiftRight_eq_div_pow]

theorem writeField_split (i off p q v : Nat) :
    writeField i off (p + q) v
      = writeField (writeField i off p (v % 2 ^ p)) (off + p) q (v / 2 ^ p) := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases h1 : b < off
  · rw [testBit_writeField_outside (Or.inl h1), testBit_writeField_outside (Or.inl (by omega)),
      testBit_writeField_outside (Or.inl h1)]
  · by_cases h2 : b < off + p
    · rw [testBit_writeField_inside (by omega) (by omega),
        testBit_writeField_outside (Or.inl (by omega)),
        testBit_writeField_inside (by omega) h2, Nat.testBit_mod_two_pow]
      simp [show b - off < p by omega]
    · by_cases h3 : b < off + (p + q)
      · rw [testBit_writeField_inside (by omega) h3,
          testBit_writeField_inside (by omega) (by omega), Nat.testBit_div_two_pow]
        congr 1
        omega
      · rw [testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_outside (Or.inr (by omega))]

theorem readField_write_sub {x off N v d e : Nat} (h : d + e ≤ N) :
    readField (writeField x off N v) (off + d) e = v / 2 ^ d % 2 ^ e := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  rw [testBit_readField, Nat.testBit_mod_two_pow]
  by_cases hb : b < e
  · rw [testBit_writeField_inside (by omega) (by omega), Nat.testBit_div_two_pow]
    simp only [hb, decide_true, Bool.true_and]
    congr 1
    omega
  · simp [hb]

/-- A write of a window is a write of the whole field.  The value written to
the whole field must agree with what is already there below the window and above
it.  Inside, it is the window's own value. -/
theorem write_window {i off j K r N v w : Nat} (hN : j + K + r = N)
    (hlo : v % 2 ^ j = readField i off j)
    (hmid : v / 2 ^ j % 2 ^ K = w)
    (hhi : v / 2 ^ (j + K) = readField i (off + j + K) r) :
    writeField i off N v = writeField i (off + j) K w := by
  subst hN
  have hd : v / 2 ^ j / 2 ^ K = readField (writeField i (off + j) K w) (off + j + K) r := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hhi,
      readField_writeField_of_disjoint (Or.inl (by omega))]
  rw [show j + K + r = j + (K + r) by omega, writeField_split i off j (K + r) v, hlo,
    writeField_read, writeField_split i (off + j) K r (v / 2 ^ j), hmid, hd, writeField_read]

/-! ### Single-gate write semantics -/

theorem flip_eq (i q : Nat) : i ^^^ (1 <<< q) = writeField i q 1 ((bv i q + 1) % 2) := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases hb : b = q
  · subst hb
    rw [testBit_writeField_inside (Nat.le_refl _) (by omega), Nat.sub_self,
      Nat.one_shiftLeft, Nat.testBit_xor, Nat.testBit_two_pow_self]
    cases h : i.testBit b <;> simp [bv, h]
  · rw [testBit_writeField_outside (by omega), RGate.testBit_xor_of_ne hb]

theorem act_x (q i : Nat) :
    RGate.act (RGate.x q) i = writeField i q 1 ((bv i q + 1) % 2) := flip_eq i q

theorem act_cx (x y i : Nat) :
    RGate.act (RGate.cx x y) i = writeField i y 1 ((bv i y + bv i x) % 2) := by
  show (if i.testBit x then i ^^^ (1 <<< y) else i) = _
  cases h : i.testBit x with
  | false =>
    rw [if_neg (by simp)]
    refine (write_of_bv ?_).symm
    have hy := bv_lt i y
    have hx : bv i x = 0 := by simp [bv, h]
    omega
  | true =>
    rw [if_pos (by simp), flip_eq]
    have hx : bv i x = 1 := by simp [bv, h]
    rw [hx]

theorem act_ccx (x y z i : Nat) :
    RGate.act (RGate.ccx x y z) i = writeField i z 1 ((bv i z + bv i x * bv i y) % 2) := by
  show (if i.testBit x && i.testBit y then i ^^^ (1 <<< z) else i) = _
  by_cases h : i.testBit x && i.testBit y
  · rw [if_pos h, flip_eq]
    have hx : bv i x = 1 := by simp [bv]; simp at h; exact h.1
    have hy : bv i y = 1 := by simp [bv]; simp at h; exact h.2
    rw [hx, hy]
  · rw [if_neg h]
    refine (write_of_bv ?_).symm
    have hz := bv_lt i z
    have hxy : bv i x * bv i y = 0 := by
      cases hx : i.testBit x <;> cases hy : i.testBit y <;> simp_all [bv]
    omega

/-! ### Gate/write commutation -/

theorem act_x_write {q z v i : Nat} (h : q ≠ z) :
    RGate.act (RGate.x q) (writeField i z 1 v)
      = writeField (RGate.act (RGate.x q) i) z 1 v := by
  rw [act_x, act_x, bv_write_ne h, writeField_comm (by omega)]

theorem act_cx_write {x y z v i : Nat} (hx : x ≠ z) (hy : y ≠ z) :
    RGate.act (RGate.cx x y) (writeField i z 1 v)
      = writeField (RGate.act (RGate.cx x y) i) z 1 v := by
  rw [act_cx, act_cx, bv_write_ne hy, bv_write_ne hx, writeField_comm (by omega)]

theorem act_ccx_write {x y u z v i : Nat} (hx : x ≠ z) (hy : y ≠ z) (hu : u ≠ z) :
    RGate.act (RGate.ccx x y u) (writeField i z 1 v)
      = writeField (RGate.act (RGate.ccx x y u) i) z 1 v := by
  rw [act_ccx, act_ccx, bv_write_ne hu, bv_write_ne hx, bv_write_ne hy,
    writeField_comm (by omega)]

theorem uma_write {c b a z v i : Nat} (ha : a ≠ z) (hb : b ≠ z) (hc : c ≠ z) :
    actGates (uma c b a) (writeField i z 1 v)
      = writeField (actGates (uma c b a) i) z 1 v := by
  show RGate.act (RGate.cx c b) (RGate.act (RGate.cx a c)
      (RGate.act (RGate.ccx c b a) (writeField i z 1 v)))
    = writeField (RGate.act (RGate.cx c b) (RGate.act (RGate.cx a c)
      (RGate.act (RGate.ccx c b a) i))) z 1 v
  rw [act_ccx_write hc hb ha, act_cx_write ha hc, act_cx_write hc hb]

/-- A gate naming no wire of a field commutes with a write to that field.
This separation permits a residue copy between the forward pass and its
reverse, which never names the written field. -/
theorem act_out {g : RGate} {off len v i : Nat}
    (h : ∀ q ∈ g.wires, q < off ∨ off + len ≤ q) :
    g.act (writeField i off len v) = writeField (g.act i) off len v := by
  cases g with
  | x q =>
    have hq : q < off ∨ off + len ≤ q := h q (by simp [RGate.wires])
    rw [act_x, act_x, bv_write_out hq, writeField_comm (by omega)]
  | cx a b =>
    have ha : a < off ∨ off + len ≤ a := h a (by simp [RGate.wires])
    have hb : b < off ∨ off + len ≤ b := h b (by simp [RGate.wires])
    rw [act_cx, act_cx, bv_write_out ha, bv_write_out hb, writeField_comm (by omega)]
  | ccx a b c =>
    have ha : a < off ∨ off + len ≤ a := h a (by simp [RGate.wires])
    have hb : b < off ∨ off + len ≤ b := h b (by simp [RGate.wires])
    have hc : c < off ∨ off + len ≤ c := h c (by simp [RGate.wires])
    rw [act_ccx, act_ccx, bv_write_out ha, bv_write_out hb, bv_write_out hc,
      writeField_comm (by omega)]

theorem actGates_out {gs : List RGate} {off len v : Nat}
    (h : ∀ g ∈ gs, ∀ q ∈ g.wires, q < off ∨ off + len ≤ q) : ∀ i,
    actGates gs (writeField i off len v) = writeField (actGates gs i) off len v := by
  induction gs with
  | nil => intro i; rfl
  | cons g gs ih =>
    intro i
    rw [actGates_cons, actGates_cons, act_out (h g List.mem_cons_self),
      ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))]

/-- Reversing a well-formed gate list yields its inverse.  Every gate is an
involution, and well-formedness excludes `cx a a`, which flips the bit it reads. -/
theorem revUndo {gs : List RGate} {w : Nat} (h : gs.all (RGate.wellFormed w) = true) :
    ∀ i, actGates gs.reverse (actGates gs i) = i := by
  induction gs with
  | nil => intro i; rfl
  | cons g gs ih =>
    intro i
    have hg : g.wellFormed w = true := (List.all_eq_true.mp h) g List.mem_cons_self
    have hgs : gs.all (RGate.wellFormed w) = true :=
      List.all_eq_true.mpr (fun g' hg' => (List.all_eq_true.mp h) g' (List.mem_cons_of_mem g hg'))
    rw [List.reverse_cons, actGates_cons, actGates_append, ih hgs]
    show RGate.act g (RGate.act g i) = i
    exact RGate.act_act hg i

/-! ### Full-adder halves -/

theorem majval {A B C : Nat} (hA : A < 2) (hB : B < 2) (hC : C < 2) :
    (A + (C + A) % 2 * ((B + A) % 2)) % 2 = (A + B + C) / 2 := by
  have ha : A = 0 ∨ A = 1 := by omega
  have hb : B = 0 ∨ B = 1 := by omega
  have hc : C = 0 ∨ C = 1 := by omega
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rfl

theorem umaval {A B C : Nat} (hA : A < 2) (hB : B < 2) (hC : C < 2) :
    ((A + B + C) / 2 + (C + A) % 2 * ((B + A) % 2)) % 2 = A := by
  have ha : A = 0 ∨ A = 1 := by omega
  have hb : B = 0 ∨ B = 1 := by omega
  have hc : C = 0 ∨ C = 1 := by omega
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rfl

theorem act_maj {c b a : Nat} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (i : Nat) :
    actGates (maj c b a) i =
      writeField (writeField (writeField i b 1 ((bv i b + bv i a) % 2))
        c 1 ((bv i c + bv i a) % 2)) a 1 ((bv i a + bv i b + bv i c) / 2) := by
  show RGate.act (RGate.ccx c b a) (RGate.act (RGate.cx a c) (RGate.act (RGate.cx a b) i)) = _
  rw [act_cx, act_cx, act_ccx, bv_write_ne hcb, bv_write_ne hab, bv_write_ne hac,
    bv_write_ne hab, bv_write_self, bv_write_ne (Ne.symm hcb), bv_write_self]
  refine write_congr ?_
  rw [← majval (bv_lt i a) (bv_lt i b) (bv_lt i c)]
  have h1 : (bv i c + bv i a) % 2 % 2 = (bv i c + bv i a) % 2 := by omega
  have h2 : (bv i b + bv i a) % 2 % 2 = (bv i b + bv i a) % 2 := by omega
  rw [h1, h2]

theorem act_uma {c b a : Nat} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    {i A B C : Nat} (hA : A < 2) (hB : B < 2) (hC : C < 2)
    (ha : bv i a = (A + B + C) / 2) (hb : bv i b = (B + A) % 2)
    (hc : bv i c = (C + A) % 2) :
    actGates (uma c b a) i =
      writeField (writeField (writeField i a 1 A) c 1 C) b 1 ((A + B + C) % 2) := by
  have h1 : RGate.act (RGate.ccx c b a) i = writeField i a 1 A := by
    rw [act_ccx, ha, hb, hc, umaval hA hB hC]
  have ha1 : bv (writeField i a 1 A) a = A := by rw [bv_write_self]; omega
  have hb1 : bv (writeField i a 1 A) b = (B + A) % 2 := by rw [bv_write_ne (Ne.symm hab), hb]
  have hc1 : bv (writeField i a 1 A) c = (C + A) % 2 := by rw [bv_write_ne (Ne.symm hac), hc]
  have h2 : RGate.act (RGate.cx a c) (writeField i a 1 A)
      = writeField (writeField i a 1 A) c 1 C := by
    rw [act_cx, hc1, ha1]
    exact write_congr (by omega)
  have hb2 : bv (writeField (writeField i a 1 A) c 1 C) b = (B + A) % 2 := by
    rw [bv_write_ne (Ne.symm hcb), hb1]
  have hc2 : bv (writeField (writeField i a 1 A) c 1 C) c = C := by rw [bv_write_self]; omega
  have h3 : RGate.act (RGate.cx c b) (writeField (writeField i a 1 A) c 1 C)
      = writeField (writeField (writeField i a 1 A) c 1 C) b 1 ((A + B + C) % 2) := by
    rw [act_cx, hb2, hc2]
    exact write_congr (by omega)
  show RGate.act (RGate.cx c b) (RGate.act (RGate.cx a c) (RGate.act (RGate.ccx c b a) i)) = _
  rw [h1, h2, h3]

/-! ### Chain-step semantics -/

/-- The basis index after the MAJ half, with `A`, `B`, and `C` the values on the
augend, addend, and carry-in wires before it. -/
def majState (i a b c A B C : Nat) : Nat :=
  writeField (writeField (writeField i b 1 ((B + A) % 2)) c 1 ((C + A) % 2))
    a 1 ((A + B + C) / 2)

theorem act_maj' {c b a : Nat} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    {i A B C : Nat} (hA : bv i a = A) (hB : bv i b = B) (hC : bv i c = C) :
    actGates (maj c b a) i = majState i a b c A B C := by
  unfold majState
  rw [act_maj hab hac hcb, hA, hB, hC]

theorem bv_majState_a {i a b c A B C : Nat} (hA : A < 2) (hB : B < 2) (hC : C < 2) :
    bv (majState i a b c A B C) a = (A + B + C) / 2 := by
  unfold majState
  rw [bv_write_self]
  omega

theorem bv_majState_b {i a b c A B C : Nat} (hab : a ≠ b) (hcb : c ≠ b) :
    bv (majState i a b c A B C) b = (B + A) % 2 := by
  unfold majState
  rw [bv_write_ne (Ne.symm hab), bv_write_ne (Ne.symm hcb), bv_write_self]
  omega

theorem bv_majState_c {i a b c A B C : Nat} (hac : a ≠ c) :
    bv (majState i a b c A B C) c = (C + A) % 2 := by
  unfold majState
  rw [bv_write_ne (Ne.symm hac), bv_write_self]
  omega

theorem bv_majState_out {i a b c A B C z : Nat} (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    bv (majState i a b c A B C) z = bv i z := by
  unfold majState
  rw [bv_write_ne hza, bv_write_ne hzc, bv_write_ne hzb]

theorem readField_majState {i a b c A B C o len : Nat}
    (h1 : b + 1 ≤ o ∨ o + len ≤ b) (h2 : c + 1 ≤ o ∨ o + len ≤ c)
    (h3 : a + 1 ≤ o ∨ o + len ≤ a) :
    readField (majState i a b c A B C) o len = readField i o len := by
  unfold majState
  rw [readField_writeField_of_disjoint h3, readField_writeField_of_disjoint h2,
    readField_writeField_of_disjoint h1]

theorem majState_restore_a {i a b c A B C : Nat} (hab : a ≠ b) (hac : a ≠ c)
    (hA : bv i a = A) (hA2 : A < 2) :
    writeField (majState i a b c A B C) a 1 A
      = writeField (writeField i b 1 ((B + A) % 2)) c 1 ((C + A) % 2) := by
  unfold majState
  rw [writeField_writeField]
  refine write_of_bv ?_
  rw [bv_write_ne hac, bv_write_ne hab, hA]
  omega

theorem majState_restore_c {i b c A B C : Nat} (hcb : c ≠ b)
    (hC : bv i c = C) (hC2 : C < 2) :
    writeField (writeField (writeField i b 1 ((B + A) % 2)) c 1 ((C + A) % 2)) c 1 C
      = writeField i b 1 ((B + A) % 2) := by
  rw [writeField_writeField]
  refine write_of_bv ?_
  rw [bv_write_ne hcb, hC]
  omega

theorem uma_collapse {i a b c A B C X p : Nat} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (hm : a + 1 + p ≤ b ∨ b + 1 + p ≤ a) (hc : c + 1 ≤ b ∨ b + 1 + p ≤ c)
    (hA : bv i a = A) (hA2 : A < 2) (hC : bv i c = C) (hC2 : C < 2) :
    writeField (writeField (writeField (writeField (majState i a b c A B C) (b + 1) p X)
        a 1 A) c 1 C) b 1 ((A + B + C) % 2)
      = writeField (writeField i b 1 ((A + B + C) % 2)) (b + 1) p X := by
  rw [writeField_comm (i := majState i a b c A B C) (o₁ := b + 1) (n₁ := p) (v := X)
        (o₂ := a) (n₂ := 1) (u := A) (by omega),
    majState_restore_a hab hac hA hA2,
    writeField_comm (i := writeField (writeField i b 1 ((B + A) % 2)) c 1 ((C + A) % 2))
      (o₁ := b + 1) (n₁ := p) (v := X) (o₂ := c) (n₂ := 1) (u := C) (by omega),
    majState_restore_c hcb hC hC2,
    writeField_comm (i := writeField i b 1 ((B + A) % 2)) (o₁ := b + 1) (n₁ := p) (v := X)
      (o₂ := b) (n₂ := 1) (u := (A + B + C) % 2) (by omega),
    writeField_writeField]

/-- One position of the ripple carry, with the carry out of the whole chain
carried along on the wire `z`.  The augend field may lie above or below the
addend field.  Disjoint operand fields suffice, so the lemma applies to the
shifted operand and the constant. -/
theorem achain_step {a b c z p : Nat} {φ : Nat → Nat → Nat} (gs : List RGate) (i : Nat)
    (hab : a + 1 + p ≤ b ∨ b + 1 + p ≤ a)
    (hca : c + 1 ≤ a ∨ a + 1 + p ≤ c)
    (hcb : c + 1 ≤ b ∨ b + 1 + p ≤ c)
    (hza : z < a ∨ a + 1 + p ≤ z)
    (hzb : z < b ∨ b + 1 + p ≤ z)
    (hzc : z ≠ c)
    (hinner : ∀ j, actGates gs j =
      writeField (writeField j (b + 1) p
          ((readField j (a + 1) p + readField j (b + 1) p + bv j a) % 2 ^ p))
        z 1 (φ (bv j z)
          ((readField j (a + 1) p + readField j (b + 1) p + bv j a) / 2 ^ p))) :
    actGates (maj c b a ++ gs ++ uma c b a) i =
      writeField (writeField i b (p + 1)
          ((readField i a (p + 1) + readField i b (p + 1) + bv i c) % 2 ^ (p + 1)))
        z 1 (φ (bv i z)
          ((readField i a (p + 1) + readField i b (p + 1) + bv i c) / 2 ^ (p + 1))) := by
  have hab' : a ≠ b := by omega
  have hac' : a ≠ c := by omega
  have hcb' : c ≠ b := by omega
  have haz : a ≠ z := by omega
  have hbz : b ≠ z := by omega
  have hcz : c ≠ z := fun h => hzc h.symm
  obtain ⟨A, hA⟩ : ∃ x, bv i a = x := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ x, bv i b = x := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ x, bv i c = x := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ x, readField i (a + 1) p = x := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ x, readField i (b + 1) p = x := ⟨_, rfl⟩
  have hA2 : A < 2 := hA ▸ bv_lt i a
  have hB2 : B < 2 := hB ▸ bv_lt i b
  have hC2 : C < 2 := hC ▸ bv_lt i c
  rw [readField_succ i a p, readField_succ i b p, hA, hB, hC, hA', hB']
  rw [actGates_append, actGates_append, act_maj' hab' hac' hcb' hA hB hC,
    hinner (majState i a b c A B C),
    readField_majState (o := a + 1) (len := p) (by omega) (by omega) (by omega),
    readField_majState (o := b + 1) (len := p) (by omega) (by omega) (by omega),
    bv_majState_a hA2 hB2 hC2, bv_majState_out (Ne.symm haz) (Ne.symm hbz) (Ne.symm hcz),
    hA', hB']
  obtain ⟨X, hX⟩ : ∃ x, (A' + B' + (A + B + C) / 2) % 2 ^ p = x := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ y, (A' + B' + (A + B + C) / 2) / 2 ^ p = y := ⟨_, rfl⟩
  rw [hX, hY, uma_write haz hbz hcz]
  have hja : bv (writeField (majState i a b c A B C) (b + 1) p X) a = (A + B + C) / 2 := by
    rw [bv_write_out (by omega), bv_majState_a hA2 hB2 hC2]
  have hjb : bv (writeField (majState i a b c A B C) (b + 1) p X) b = (B + A) % 2 := by
    rw [bv_write_out (Or.inl (by omega)), bv_majState_b hab' hcb']
  have hjc : bv (writeField (majState i a b c A B C) (b + 1) p X) c = (C + A) % 2 := by
    rw [bv_write_out (by omega), bv_majState_c hac']
  have hpow : (2 : Nat) ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ]; omega
  have hV : (A + 2 * A' + (B + 2 * B') + C) % 2 ^ (p + 1) = (A + B + C) % 2 + 2 * X := by
    rw [hpow, Nat.mod_mul]
    have h1 : (A + 2 * A' + (B + 2 * B') + C) % 2 = (A + B + C) % 2 := by omega
    have h2 : (A + 2 * A' + (B + 2 * B') + C) / 2 = (A + B + C) / 2 + A' + B' := by omega
    have h3 : (A + B + C) / 2 + A' + B' = A' + B' + (A + B + C) / 2 := by omega
    rw [h1, h2, h3, hX]
  have hW : (A + 2 * A' + (B + 2 * B') + C) / 2 ^ (p + 1) = Y := by
    rw [hpow, ← Nat.div_div_eq_div_mul]
    have h2 : (A + 2 * A' + (B + 2 * B') + C) / 2 = A' + B' + (A + B + C) / 2 := by omega
    rw [h2, hY]
  rw [act_uma hab' hac' hcb' hA2 hB2 hC2 hja hjb hjc,
    uma_collapse hab' hac' hcb' hab hcb hA hA2 hC hC2,
    writeField_succ i b p ((A + 2 * A' + (B + 2 * B') + C) % 2 ^ (p + 1)), hV, hW,
    show ((A + B + C) % 2 + 2 * X) % 2 = (A + B + C) % 2 by omega,
    show ((A + B + C) % 2 + 2 * X) / 2 = X by omega]

/-- The whole ripple-carry chain.  `mid` sees the carry out of the chain on
the top carry wire and may record it on `z`.  The sum lands in the addend
field. -/
theorem achain_act {A B c z K : Nat} {φ : Nat → Nat → Nat} {mid : List RGate}
    (hAB : A + K ≤ B ∨ B + K ≤ A)
    (hcA : c < A ∨ A + K ≤ c) (hcB : c < B ∨ B + K ≤ c)
    (hzA : z < A ∨ A + K ≤ z) (hzB : z < B ∨ B + K ≤ z) (hzc : z ≠ c)
    (hmid : ∀ j, actGates mid j = writeField j z 1 (φ (bv j z) (bv j (cwire A c K)))) :
    ∀ p st, st + p = K → ∀ i,
      actGates (achain A B c mid st p) i =
        writeField (writeField i (B + st) p
            ((readField i (A + st) p + readField i (B + st) p + bv i (cwire A c st)) % 2 ^ p))
          z 1 (φ (bv i z)
            ((readField i (A + st) p + readField i (B + st) p + bv i (cwire A c st)) / 2 ^ p)) := by
  intro p
  induction p with
  | zero =>
    intro st hst i
    have hs : st = K := by omega
    subst hs
    rw [show achain A B c mid st 0 = mid from rfl, hmid i, readField_size_zero,
      readField_size_zero, writeField_zero]
    simp
  | succ p ih =>
    intro st hst i
    have hlt : st < K := by omega
    have hcc := cwire_cases (A := A) (c := c) (K := K) hlt
    exact achain_step (a := A + st) (b := B + st) (c := cwire A c st) (p := p) (φ := φ)
      (achain A B c mid (st + 1) p) i
      (by omega) (by rcases hcc with h | h <;> omega) (by rcases hcc with h | h <;> omega)
      (by omega) (by omega) (by rcases hcc with h | h <;> omega)
      (fun j => ih (st + 1) (by omega) j)

/-! ### Copy and load semantics

All four move one register's bits into another with an exclusive-or, so their
effect is stated with `Nat.xor` and the two bit identities below are what
carries each induction. -/

theorem mod_two_bv (x : Nat) : x % 2 = bv x 0 := by
  have h : readField x 0 1 = bv x 0 := readField_one x 0
  rw [← h]
  show x % 2 = (x >>> 0) % 2 ^ 1
  simp

theorem xor_bit (x y : Nat) : (x ^^^ y) % 2 = (x % 2 + y % 2) % 2 := by
  rw [mod_two_bv (x ^^^ y), mod_two_bv x, mod_two_bv y]
  unfold bv
  rw [Nat.testBit_xor]
  cases hx : x.testBit 0 <;> cases hy : y.testBit 0 <;> simp

theorem xor_div_two (x y : Nat) : (x ^^^ y) / 2 = (x / 2) ^^^ (y / 2) := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_div_two,
    Nat.testBit_div_two]

theorem loadX_act : ∀ (p D v i : Nat),
    actGates (loadX D p v) i = writeField i D p ((readField i D p) ^^^ v) := by
  intro p
  induction p with
  | zero => intro D v i; rw [writeField_zero]; rfl
  | succ p ih =>
    intro D v i
    have hbw := bv_lt i D
    have hr := readField_succ i D p
    have hhead : actGates (if v % 2 = 1 then [RGate.x D] else []) i
        = writeField i D 1 ((bv i D + v % 2) % 2) := by
      by_cases hv : v % 2 = 1
      · rw [if_pos hv]
        show RGate.act (RGate.x D) i = _
        rw [act_x, hv]
      · rw [if_neg hv]
        have hv0 : v % 2 = 0 := by omega
        rw [hv0]
        show i = writeField i D 1 ((bv i D + 0) % 2)
        exact (write_of_bv (by omega)).symm
    have hα : ((readField i D (p + 1)) ^^^ v) % 2 = (bv i D + v % 2) % 2 := by
      rw [xor_bit]
      have : readField i D (p + 1) % 2 = bv i D := by omega
      rw [this]
    have hβ : ((readField i D (p + 1)) ^^^ v) / 2 = (readField i (D + 1) p) ^^^ (v / 2) := by
      rw [xor_div_two]
      have : readField i D (p + 1) / 2 = readField i (D + 1) p := by omega
      rw [this]
    rw [loadX, actGates_append, hhead, ih (D + 1) (v / 2),
      readField_writeField_of_disjoint (Or.inl (by omega)),
      writeField_succ i D p ((readField i D (p + 1)) ^^^ v), hα, hβ]

theorem loadC_act {c : Nat} : ∀ (p D v i : Nat), (c < D ∨ D + p ≤ c) →
    actGates (loadC c D p v) i = writeField i D p ((readField i D p) ^^^ (bv i c * v)) := by
  intro p
  induction p with
  | zero => intro D v i _; rw [writeField_zero]; rfl
  | succ p ih =>
    intro D v i hcD
    have hbw := bv_lt i D
    have hbc := bv_lt i c
    have hr := readField_succ i D p
    have ht : bv i c = 0 ∨ bv i c = 1 := by omega
    have hcne : c ≠ D := by omega
    have hhead : actGates (if v % 2 = 1 then [RGate.cx c D] else []) i
        = writeField i D 1 ((bv i D + bv i c * (v % 2)) % 2) := by
      by_cases hv : v % 2 = 1
      · rw [if_pos hv]
        show RGate.act (RGate.cx c D) i = _
        rw [act_cx, hv]
        exact write_congr (by omega)
      · rw [if_neg hv]
        have hv0 : v % 2 = 0 := by omega
        rw [hv0]
        show i = writeField i D 1 ((bv i D + bv i c * 0) % 2)
        exact (write_of_bv (by omega)).symm
    have hbc1 : bv (writeField i D 1 ((bv i D + bv i c * (v % 2)) % 2)) c = bv i c :=
      bv_write_ne hcne
    have hmul2 : (bv i c * v) % 2 = (bv i c * (v % 2)) % 2 := by
      rcases ht with ht | ht <;> rw [ht] <;> omega
    have hmuld : (bv i c * v) / 2 = bv i c * (v / 2) := by
      rcases ht with ht | ht <;> rw [ht] <;> omega
    have hα : ((readField i D (p + 1)) ^^^ (bv i c * v)) % 2
        = (bv i D + bv i c * (v % 2)) % 2 := by
      rw [xor_bit, hmul2]
      have : readField i D (p + 1) % 2 = bv i D := by omega
      rw [this]
      omega
    have hβ : ((readField i D (p + 1)) ^^^ (bv i c * v)) / 2
        = (readField i (D + 1) p) ^^^ (bv i c * (v / 2)) := by
      rw [xor_div_two, hmuld]
      have : readField i D (p + 1) / 2 = readField i (D + 1) p := by omega
      rw [this]
    rw [loadC, actGates_append, hhead, ih (D + 1) (v / 2) _ (by omega), hbc1,
      readField_writeField_of_disjoint (Or.inl (by omega)),
      writeField_succ i D p ((readField i D (p + 1)) ^^^ (bv i c * v)), hα, hβ]

theorem pcopy_act : ∀ (p A D i : Nat), (A + p ≤ D ∨ D + p ≤ A) →
    actGates (pcopy A D p) i = writeField i D p ((readField i D p) ^^^ (readField i A p)) := by
  intro p
  induction p with
  | zero => intro A D i _; rw [writeField_zero]; rfl
  | succ p ih =>
    intro A D i hAD
    have hbw := bv_lt i D
    have hba := bv_lt i A
    have hrD := readField_succ i D p
    have hrA := readField_succ i A p
    have hne : A ≠ D := by omega
    have hhead : RGate.act (RGate.cx A D) i = writeField i D 1 ((bv i D + bv i A) % 2) :=
      act_cx A D i
    have hkeep : readField (writeField i D 1 ((bv i D + bv i A) % 2)) (A + 1) p
        = readField i (A + 1) p :=
      readField_writeField_of_disjoint (by omega)
    have hα : ((readField i D (p + 1)) ^^^ (readField i A (p + 1))) % 2
        = (bv i D + bv i A) % 2 := by
      rw [xor_bit]
      have h1 : readField i D (p + 1) % 2 = bv i D := by omega
      have h2 : readField i A (p + 1) % 2 = bv i A := by omega
      rw [h1, h2]
    have hβ : ((readField i D (p + 1)) ^^^ (readField i A (p + 1))) / 2
        = (readField i (D + 1) p) ^^^ (readField i (A + 1) p) := by
      rw [xor_div_two]
      have h1 : readField i D (p + 1) / 2 = readField i (D + 1) p := by omega
      have h2 : readField i A (p + 1) / 2 = readField i (A + 1) p := by omega
      rw [h1, h2]
    rw [show pcopy A D (p + 1) = RGate.cx A D :: pcopy (A + 1) (D + 1) p from rfl,
      actGates_cons, hhead, ih (A + 1) (D + 1) _ (by omega), hkeep,
      readField_writeField_of_disjoint (Or.inl (by omega)),
      writeField_succ i D p ((readField i D (p + 1)) ^^^ (readField i A (p + 1))), hα, hβ]

theorem ccopy_act {ctl : Nat} : ∀ (p A D i : Nat), (ctl < D ∨ D + p ≤ ctl) →
    (A + p ≤ D ∨ D + p ≤ A) →
    actGates (ccopy ctl A D p) i
      = writeField i D p ((readField i D p) ^^^ (bv i ctl * readField i A p)) := by
  intro p
  induction p with
  | zero => intro A D i _ _; rw [writeField_zero]; rfl
  | succ p ih =>
    intro A D i hcD hAD
    have hbw := bv_lt i D
    have hba := bv_lt i A
    have hbc := bv_lt i ctl
    have hrD := readField_succ i D p
    have hrA := readField_succ i A p
    have ht : bv i ctl = 0 ∨ bv i ctl = 1 := by omega
    have hne : A ≠ D := by omega
    have hcne : ctl ≠ D := by omega
    have hhead : RGate.act (RGate.ccx ctl A D) i
        = writeField i D 1 ((bv i D + bv i ctl * bv i A) % 2) := act_ccx ctl A D i
    have hkeepA : readField (writeField i D 1 ((bv i D + bv i ctl * bv i A) % 2)) (A + 1) p
        = readField i (A + 1) p :=
      readField_writeField_of_disjoint (by omega)
    have hkeepC : bv (writeField i D 1 ((bv i D + bv i ctl * bv i A) % 2)) ctl = bv i ctl :=
      bv_write_ne hcne
    have hmul2 : (bv i ctl * readField i A (p + 1)) % 2 = (bv i ctl * bv i A) % 2 := by
      rcases ht with ht | ht <;> rw [ht] <;> omega
    have hmuld : (bv i ctl * readField i A (p + 1)) / 2 = bv i ctl * readField i (A + 1) p := by
      rcases ht with ht | ht <;> rw [ht] <;> omega
    have hα : ((readField i D (p + 1)) ^^^ (bv i ctl * readField i A (p + 1))) % 2
        = (bv i D + bv i ctl * bv i A) % 2 := by
      rw [xor_bit, hmul2]
      have h1 : readField i D (p + 1) % 2 = bv i D := by omega
      rw [h1]
      omega
    have hβ : ((readField i D (p + 1)) ^^^ (bv i ctl * readField i A (p + 1))) / 2
        = (readField i (D + 1) p) ^^^ (bv i ctl * readField i (A + 1) p) := by
      rw [xor_div_two, hmuld]
      have h1 : readField i D (p + 1) / 2 = readField i (D + 1) p := by omega
      rw [h1]
    rw [show ccopy ctl A D (p + 1) = RGate.ccx ctl A D :: ccopy ctl (A + 1) (D + 1) p from rfl,
      actGates_cons, hhead, ih (A + 1) (D + 1) _ (by omega) (by omega), hkeepA, hkeepC,
      readField_writeField_of_disjoint (Or.inl (by omega)),
      writeField_succ i D p ((readField i D (p + 1)) ^^^ (bv i ctl * readField i A (p + 1))),
      hα, hβ]

/-! ### Subfield reads -/

theorem readField_sub_read {i off N d e : Nat} (h : d + e ≤ N) :
    readField i (off + d) e = readField i off N / 2 ^ d % 2 ^ e := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  rw [testBit_readField, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, testBit_readField]
  by_cases hb : b < e
  · have h1 : b + d < N := by omega
    simp only [hb, h1, decide_true, Bool.true_and]
    congr 1
    omega
  · simp [hb]

/-- A write of a low window is a write of the whole field. -/
theorem write_low {i off K r N v w : Nat} (hN : K + r = N)
    (hmid : v % 2 ^ K = w) (hhi : v / 2 ^ K = readField i (off + K) r) :
    writeField i off N v = writeField i off K w := by
  have h := write_window (i := i) (off := off) (j := 0) (K := K) (r := r) (N := N) (v := v)
    (w := w) (by omega) (by rw [Nat.pow_zero, Nat.mod_one, readField_size_zero])
    (by rw [Nat.pow_zero, Nat.div_one]; exact hmid)
    (by rw [Nat.zero_add]; rw [Nat.add_zero]; exact hhi)
  rw [Nat.add_zero] at h
  exact h

/-! ### Product semantics

`ms n i s p` is the index with the shifted addend holding `s` and the
accumulator holding `p`.  Only those two registers move during the product, so
each round is three rewrites. -/

def ms (n i s p : Nat) : Nat :=
  writeField (writeField i (sReg n) sk s) (pReg n) dk p

theorem ms_readS {n i s p d e : Nat} (h : d + e ≤ sk) :
    readField (ms n i s p) (sReg n + d) e = s / 2 ^ d % 2 ^ e := by
  have h1 := e_s n
  have h2 := e_p n
  unfold ms
  rw [readField_writeField_of_disjoint (Or.inr (by omega)), readField_write_sub h]

theorem ms_readP {n i s p d e : Nat} (h : d + e ≤ dk) :
    readField (ms n i s p) (pReg n + d) e = p / 2 ^ d % 2 ^ e := by
  unfold ms
  rw [readField_write_sub h]

theorem ms_out {n i s p o e : Nat} (h : o + e ≤ sReg n) :
    readField (ms n i s p) o e = readField i o e := by
  have h1 := e_s n
  have h2 := e_p n
  have h3 := e_sk
  unfold ms
  rw [readField_writeField_of_disjoint (Or.inr (by omega)),
    readField_writeField_of_disjoint (Or.inr (by omega))]

theorem ms_above {n i s p o e : Nat} (h : pReg n + dk ≤ o) :
    readField (ms n i s p) o e = readField i o e := by
  have h1 := e_s n
  have h2 := e_p n
  have h3 := e_sk
  unfold ms
  rw [readField_writeField_of_disjoint (Or.inl (by omega)),
    readField_writeField_of_disjoint (Or.inl (by omega))]

theorem ms_setS {n : Nat} (i s p v : Nat) : writeField (ms n i s p) (sReg n) sk v = ms n i v p := by
  have h1 := e_s n
  have h2 := e_p n
  unfold ms
  rw [writeField_comm (o₁ := pReg n) (n₁ := dk) (o₂ := sReg n) (n₂ := sk) (Or.inr (by omega)),
    writeField_writeField]

theorem ms_setP {n : Nat} (i s p v : Nat) :
    writeField (ms n i s p) (pReg n) dk v = ms n i s v := by
  unfold ms
  rw [writeField_writeField]

theorem ms_id {n i : Nat} (hs : readField i (sReg n) sk = 0) (hp : readField i (pReg n) dk = 0) :
    ms n i 0 0 = i := by
  have e1 : writeField i (sReg n) sk 0 = i := by rw [← hs]; exact writeField_read _ _ _
  unfold ms
  rw [e1, ← hp, writeField_read]

theorem ms_readS0 {n i s p e : Nat} (h : e ≤ sk) :
    readField (ms n i s p) (sReg n) e = s % 2 ^ e := by
  have h2 := ms_readS (n := n) (i := i) (s := s) (p := p) (d := 0) (e := e) (by omega)
  rw [Nat.add_zero, Nat.pow_zero, Nat.div_one] at h2
  exact h2

theorem ms_readP0 {n i s p e : Nat} (h : e ≤ dk) :
    readField (ms n i s p) (pReg n) e = p % 2 ^ e := by
  have h2 := ms_readP (n := n) (i := i) (s := s) (p := p) (d := 0) (e := e) (by omega)
  rw [Nat.add_zero, Nat.pow_zero, Nat.div_one] at h2
  exact h2

/-- One round of the product.  Bit `t` of the second operand gates a copy of
the first, the copy is added into the accumulator at offset `t`, and the copy is
cleared by repeating the same gates: its two controls are untouched by the
addition. -/
theorem mround_act {n : Nat} (hk : k ≤ n) {t i p : Nat} (ht : t < k)
    (hp : p < 2 ^ (k + t)) (hc : bv i (cReg n) = 0) :
    actGates (mround n t) (ms n i 0 p)
      = ms n i 0 (p + bv i (n + t) * readField i 0 k * 2 ^ t) := by
  have h1 := e_s n
  have h2 := e_p n
  have h3 := e_v n
  have h4 := e_q n
  have h5 := e_c n
  have h6 := e_sk
  have h7 := e_dk
  have h8 := e_ws
  have hkp := k_pos
  obtain ⟨A, hA⟩ : ∃ x, readField i 0 k = x := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ x, bv i (n + t) = x := ⟨_, rfl⟩
  have hAk : A < 2 ^ k := hA ▸ readField_lt i 0 k
  have hβ2 : β < 2 := hβ ▸ bv_lt i (n + t)
  have hpk : (0 : Nat) < 2 ^ k := Nat.two_pow_pos k
  have hpt : (0 : Nat) < 2 ^ t := Nat.two_pow_pos t
  have hs : β * A < 2 ^ k := by
    rcases (show β = 0 ∨ β = 1 by omega) with h | h <;> rw [h] <;> omega
  have hsk2 : (2 : Nat) ^ sk = 2 ^ k * 2 := by rw [e_sk, Nat.pow_succ]
  have hpdiv : p / 2 ^ t < 2 ^ k := by
    refine Nat.div_lt_of_lt_mul ?_
    rw [Nat.mul_comm, ← Nat.pow_add]
    exact hp
  have hbvB : ∀ s q : Nat, bv (ms n i s q) (n + t) = β := by
    intro s q
    rw [← readField_one, ms_out (o := n + t) (e := 1) (by omega), readField_one, hβ]
  have hrdA : ∀ s q : Nat, readField (ms n i s q) 0 k = A := by
    intro s q
    rw [ms_out (o := 0) (e := k) (by omega), hA]
  have hbvC : ∀ s q : Nat, bv (ms n i s q) (cReg n) = 0 := by
    intro s q
    rw [← readField_one, ms_above (o := cReg n) (e := 1) (by omega), readField_one, hc]
  -- the gated copy of the first operand
  have step1 : actGates (ccopy (n + t) 0 (sReg n) k) (ms n i 0 p) = ms n i (β * A) p := by
    rw [ccopy_act k 0 (sReg n) (ms n i 0 p) (Or.inl (by omega)) (Or.inl (by omega)),
      ms_readS0 (by omega), hbvB, hrdA, Nat.zero_mod, Nat.zero_xor]
    rw [← ms_setS (n := n) i 0 p (β * A)]
    refine (write_low (K := k) (r := 1) (N := sk) rfl (Nat.mod_eq_of_lt hs) ?_).symm
    rw [Nat.div_eq_of_lt hs, ms_readS (d := k) (e := 1) (by omega)]
    simp
  -- the addition into the accumulator window
  have hmid0 : ∀ j, actGates ([] : List RGate) j
      = writeField j 0 1 ((fun x _ => x) (bv j 0) (bv j (cwire (sReg n) (cReg n) sk))) := by
    intro j
    show j = writeField j 0 1 (bv j 0)
    exact (write_of_bv (by have := bv_lt j 0; omega)).symm
  have step2 : actGates (achain (sReg n) (pReg n + t) (cReg n) [] 0 sk) (ms n i (β * A) p)
      = ms n i (β * A) (p + β * A * 2 ^ t) := by
    have hach := achain_act (A := sReg n) (B := pReg n + t) (c := cReg n) (z := 0) (K := sk)
      (φ := fun x _ => x) (mid := [])
      (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (by omega) hmid0 sk 0 (by omega)
      (ms n i (β * A) p)
    simp only [Nat.add_zero, cwire] at hach
    rw [ms_readS0 (by omega), ms_readP (d := t) (e := sk) (by omega), hbvC] at hach
    have hval : β * A % 2 ^ sk + p / 2 ^ t % 2 ^ sk + 0 = β * A + p / 2 ^ t := by
      rw [Nat.mod_eq_of_lt (show β * A < 2 ^ sk by omega),
        Nat.mod_eq_of_lt (show p / 2 ^ t < 2 ^ sk by omega), Nat.add_zero]
    have hsig : β * A + p / 2 ^ t < 2 ^ sk := by omega
    rw [hval, Nat.mod_eq_of_lt hsig] at hach
    rw [hach]
    have hout : writeField (writeField (ms n i (β * A) p) (pReg n + t) sk
        (β * A + p / 2 ^ t)) 0 1 (bv (ms n i (β * A) p) 0)
        = writeField (ms n i (β * A) p) (pReg n + t) sk (β * A + p / 2 ^ t) := by
      refine write_of_bv ?_
      rw [bv_write_out (Or.inl (by omega))]
      have := bv_lt (ms n i (β * A) p) 0
      omega
    have hwin : writeField (ms n i (β * A) p) (pReg n) dk (p + β * A * 2 ^ t)
        = writeField (ms n i (β * A) p) (pReg n + t) sk (β * A + p / 2 ^ t) := by
      refine write_window (j := t) (K := sk) (r := dk - t - sk) (by omega) ?_ ?_ ?_
      · rw [ms_readP0 (by omega), Nat.add_mul_mod_self_right]
      · rw [Nat.add_mul_div_right _ _ hpt, Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [show pReg n + t + sk = pReg n + (t + sk) from by omega,
          ms_readP (d := t + sk) (e := dk - t - sk) (by omega)]
        have hlt : p + β * A * 2 ^ t < 2 ^ (t + sk) := by
          have e1 : (2 : Nat) ^ (t + sk) = 2 ^ t * 2 ^ k * 2 := by
            rw [Nat.pow_add, hsk2, Nat.mul_assoc]
          have e2 : (2 : Nat) ^ (k + t) = 2 ^ t * 2 ^ k := by rw [Nat.pow_add, Nat.mul_comm]
          have e3 : β * A * 2 ^ t < 2 ^ t * 2 ^ k := by
            rw [Nat.mul_comm (2 ^ t) (2 ^ k)]
            exact Nat.mul_lt_mul_of_lt_of_le hs (Nat.le_refl _) hpt
          omega
        have hlt2 : p < 2 ^ (t + sk) := by
          have : (2 : Nat) ^ (k + t) ≤ 2 ^ (t + sk) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          omega
        rw [Nat.div_eq_of_lt hlt, Nat.div_eq_of_lt hlt2, Nat.zero_mod]
    rw [hout, ← hwin, ms_setP]
  -- clearing the gated copy
  have step3 : actGates (ccopy (n + t) 0 (sReg n) k) (ms n i (β * A) (p + β * A * 2 ^ t))
      = ms n i 0 (p + β * A * 2 ^ t) := by
    rw [ccopy_act k 0 (sReg n) (ms n i (β * A) (p + β * A * 2 ^ t))
        (Or.inl (by omega)) (Or.inl (by omega)),
      ms_readS0 (by omega), hbvB, hrdA, Nat.mod_eq_of_lt hs, Nat.xor_self]
    rw [← ms_setS (n := n) i (β * A) (p + β * A * 2 ^ t) 0]
    refine (write_low (K := k) (r := 1) (N := sk) rfl (by simp) ?_).symm
    rw [Nat.zero_div, ms_readS (d := k) (e := 1) (by omega), Nat.div_eq_of_lt hs,
      Nat.zero_mod]
  show actGates ((ccopy (n + t) 0 (sReg n) k ++ achain (sReg n) (pReg n + t) (cReg n) [] 0 sk)
      ++ ccopy (n + t) 0 (sReg n) k) (ms n i 0 p) = _
  rw [actGates_append, actGates_append, step1, step2, step3, hβ, hA]

/-- The whole product.  After `t` rounds the accumulator holds the first
operand times the low `t` bits of the second, and the shifted addend is
clear. -/
theorem mloop_act {n : Nat} (hk : k ≤ n) {i A B : Nat} (hc : bv i (cReg n) = 0)
    (hA : readField i 0 k = A) (hB : readField i n k = B) : ∀ t, t ≤ k →
    actGates (mloop n t) (ms n i 0 0) = ms n i 0 (A * (B % 2 ^ t)) := by
  have hAk : A < 2 ^ k := hA ▸ readField_lt i 0 k
  intro t
  induction t with
  | zero =>
    intro _
    rw [Nat.pow_zero, Nat.mod_one, Nat.mul_zero]
    rfl
  | succ t ih =>
    intro ht
    have hpt : (0 : Nat) < 2 ^ t := Nat.two_pow_pos t
    have hbit : bv i (n + t) = B / 2 ^ t % 2 := by
      rw [← readField_one, readField_sub_read (off := n) (N := k) (d := t) (e := 1) (by omega),
        hB, Nat.pow_one]
    have hmod : B % 2 ^ (t + 1) = B % 2 ^ t + 2 ^ t * (B / 2 ^ t % 2) := by
      rw [Nat.pow_succ, Nat.mod_mul]
    have hlt : A * (B % 2 ^ t) < 2 ^ (k + t) := by
      have h := Nat.mul_lt_mul_of_lt_of_le hAk (Nat.le_of_lt (Nat.mod_lt B hpt)) hpt
      rw [← Nat.pow_add] at h
      exact h
    have harith : A * (B % 2 ^ (t + 1))
        = A * (B % 2 ^ t) + B / 2 ^ t % 2 * A * 2 ^ t := by
      rw [hmod, Nat.mul_add]
      congr 1
      rw [Nat.mul_comm (2 ^ t) (B / 2 ^ t % 2), ← Nat.mul_assoc,
        Nat.mul_comm A (B / 2 ^ t % 2)]
    rw [show mloop n (t + 1) = mloop n t ++ mround n t from rfl, actGates_append,
      ih (by omega), mround_act hk (by omega) hlt hc, hA, hbit, harith]

/-! ### Reduction semantics

`rt n t i p v f` is the index with the accumulator holding `p`, the constant
register holding `v`, and quotient bit `t` holding `f`.  Those three are the
only registers a reduction step moves, so each of its eight blocks is one
rewrite. -/

def rt (n t i p v f : Nat) : Nat :=
  writeField (writeField (writeField i (pReg n) dk p) (vReg n) dk v) (qReg n + t) 1 f

theorem rt_setP {n t : Nat} (ht : t < k) (i p v f p' : Nat) :
    writeField (rt n t i p v f) (pReg n) dk p' = rt n t i p' v f := by
  have h2 := e_p n
  have h3 := e_v n
  have h4 := e_q n
  have h7 := e_dk
  unfold rt
  rw [writeField_comm (o₁ := qReg n + t) (n₁ := 1) (o₂ := pReg n) (n₂ := dk) (Or.inr (by omega)),
    writeField_comm (o₁ := vReg n) (n₁ := dk) (o₂ := pReg n) (n₂ := dk) (Or.inr (by omega)),
    writeField_writeField]

theorem rt_setV {n t : Nat} (_ht : t < k) (i p v f v' : Nat) :
    writeField (rt n t i p v f) (vReg n) dk v' = rt n t i p v' f := by
  have h3 := e_v n
  have h4 := e_q n
  have h7 := e_dk
  unfold rt
  rw [writeField_comm (o₁ := qReg n + t) (n₁ := 1) (o₂ := vReg n) (n₂ := dk) (Or.inr (by omega)),
    writeField_writeField]

theorem rt_setF {n t : Nat} (i p v f f' : Nat) :
    writeField (rt n t i p v f) (qReg n + t) 1 f' = rt n t i p v f' := by
  unfold rt
  rw [writeField_writeField]

theorem rt_readP {n t : Nat} (ht : t < k) (i p v f : Nat) :
    readField (rt n t i p v f) (pReg n) dk = p % 2 ^ dk := by
  have h2 := e_p n
  have h3 := e_v n
  have h4 := e_q n
  have h7 := e_dk
  unfold rt
  rw [readField_writeField_of_disjoint (Or.inr (by omega)),
    readField_writeField_of_disjoint (Or.inr (by omega)), readField_writeField]

theorem rt_readV {n t : Nat} (_ht : t < k) (i p v f : Nat) :
    readField (rt n t i p v f) (vReg n) dk = v % 2 ^ dk := by
  have h3 := e_v n
  have h4 := e_q n
  have h7 := e_dk
  unfold rt
  rw [readField_writeField_of_disjoint (Or.inr (by omega)), readField_writeField]

theorem rt_readF {n t : Nat} (i p v f : Nat) :
    bv (rt n t i p v f) (qReg n + t) = f % 2 := by
  unfold rt
  rw [← readField_one, readField_writeField, Nat.pow_one]

theorem rt_readC {n t : Nat} (ht : t < k) (i p v f : Nat) :
    bv (rt n t i p v f) (cReg n) = bv i (cReg n) := by
  have h2 := e_p n
  have h3 := e_v n
  have h4 := e_q n
  have h5 := e_c n
  have h7 := e_dk
  unfold rt
  rw [← readField_one, ← readField_one,
    readField_writeField_of_disjoint (Or.inl (by omega)),
    readField_writeField_of_disjoint (Or.inl (by omega)),
    readField_writeField_of_disjoint (Or.inl (by omega))]

theorem rt_id {n t i p : Nat} (hp : readField i (pReg n) dk = p)
    (hv : readField i (vReg n) dk = 0) (hf : bv i (qReg n + t) = 0) :
    rt n t i p 0 0 = i := by
  have e1 : writeField i (pReg n) dk p = i := by rw [← hp]; exact writeField_read _ _ _
  have e2 : writeField i (vReg n) dk 0 = i := by rw [← hv]; exact writeField_read _ _ _
  unfold rt
  rw [e1, e2]
  exact write_of_bv (by rw [hf])

theorem rt_clean {n t : Nat} (_ht : t < k) {i p f : Nat} (hv : readField i (vReg n) dk = 0) :
    rt n t i p 0 f = writeField (writeField i (pReg n) dk p) (qReg n + t) 1 f := by
  have h2 := e_p n
  have h3 := e_v n
  have h7 := e_dk
  have e2 : writeField (writeField i (pReg n) dk p) (vReg n) dk 0
      = writeField i (pReg n) dk p := by
    rw [show (0 : Nat) = readField (writeField i (pReg n) dk p) (vReg n) dk from by
      rw [readField_writeField_of_disjoint (Or.inl (by omega)), hv]]
    exact writeField_read _ _ _
  unfold rt
  rw [e2]

/-- The one split every quotient and remainder by a power of two in the
reduction goes through: below twice the divisor, the quotient is a bit. -/
theorem split_two {K x : Nat} (hK : 0 < K) (h : x < 2 * K) :
    (x < K ∧ x / K = 0 ∧ x % K = x) ∨ (K ≤ x ∧ x / K = 1 ∧ x % K = x - K) := by
  rcases Nat.lt_or_ge x K with h1 | h1
  · exact Or.inl ⟨h1, Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1⟩
  · refine Or.inr ⟨h1, ?_, ?_⟩
    · rw [Nat.div_eq_sub_div hK h1, Nat.div_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

/-- One step of the reduction.  Adding `2 ^ dk - m * 2 ^ t` is subtracting
`m * 2 ^ t` modulo `2 ^ dk`, and its carry out is exactly the comparison the
subtraction should have been conditional on.  The constant is then added back
under the complement of that bit, which leaves the accumulator reduced and the
bit holding the quotient digit. -/
theorem rstep_act {n : Nat} (hk : k ≤ n) {t i p : Nat} (ht : t < k)
    (hp : readField i (pReg n) dk = p) (hv : readField i (vReg n) dk = 0)
    (hf : bv i (qReg n + t) = 0) (hc : bv i (cReg n) = 0)
    (hpm : p < m * 2 ^ (t + 1)) :
    ∃ p' f, p' < m * 2 ^ t ∧ p' % m = p % m ∧ f < 2 ∧
      actGates (rstep n t) i
        = writeField (writeField i (pReg n) dk p') (qReg n + t) 1 f := by
  have h1 := e_s n
  have h2 := e_p n
  have h3 := e_v n
  have h4 := e_q n
  have h5 := e_c n
  have h6 := e_sk
  have h7 := e_dk
  have h8 := e_ws
  have hkp := k_pos
  have hdkp : dk = dkp + 1 := rfl
  -- the constant and its complement
  obtain ⟨C, hCe⟩ : ∃ x, m * 2 ^ t = x := ⟨_, rfl⟩
  obtain ⟨D, hDe⟩ : ∃ x, 2 ^ dk - C = x := ⟨_, rfl⟩
  have hdkpos : (0 : Nat) < 2 ^ dk := Nat.two_pow_pos dk
  have hCpos : 0 < C := by
    rw [← hCe]
    exact Nat.mul_pos m_pos (Nat.two_pow_pos t)
  have hCe2 : m * 2 ^ (t + 1) = 2 * C := by
    rw [Nat.pow_succ, ← Nat.mul_assoc, hCe, Nat.mul_comm]
  have h2C : 2 * C ≤ 2 ^ dk := by
    have e1 : m * 2 ^ (t + 1) < 2 ^ (k + (t + 1)) := by
      rw [Nat.pow_add 2 k (t + 1)]
      exact Nat.mul_lt_mul_of_lt_of_le m_lt (Nat.le_refl _) (Nat.two_pow_pos (t + 1))
    have e2 : (2 : Nat) ^ (k + (t + 1)) ≤ 2 ^ dk := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hCd : C < 2 ^ dk := by omega
  have hDC : D + C = 2 ^ dk := by omega
  have hp2 : p < 2 * C := by omega
  have hpd : p < 2 ^ dk := by omega
  have hi : rt n t i p 0 0 = i := rt_id hp hv hf
  -- the trace
  have hmid1 : ∀ j, actGates [RGate.cx (vReg n + dkp) (qReg n + t)] j
      = writeField j (qReg n + t) 1
        ((fun x y => (x + y) % 2) (bv j (qReg n + t)) (bv j (cwire (vReg n) (cReg n) dk))) := by
    intro j
    rw [cwire_dk]
    show RGate.act (RGate.cx (vReg n + dkp) (qReg n + t)) j = _
    rw [act_cx]
  have hmid0 : ∀ j, actGates ([] : List RGate) j
      = writeField j 0 1 ((fun x _ => x) (bv j 0) (bv j (cwire (vReg n) (cReg n) dk))) := by
    intro j
    show j = writeField j 0 1 (bv j 0)
    exact (write_of_bv (by have := bv_lt j 0; omega)).symm
  have b1 : ∀ q v f : Nat, actGates (loadX (vReg n) dk D) (rt n t i q v f)
      = rt n t i q ((v % 2 ^ dk) ^^^ D) f := by
    intro q v f
    rw [loadX_act, rt_readV ht, rt_setV ht]
  have b4 : ∀ q v f : Nat, actGates [RGate.x (qReg n + t)] (rt n t i q v f)
      = rt n t i q v ((f % 2 + 1) % 2) := by
    intro q v f
    show RGate.act (RGate.x (qReg n + t)) (rt n t i q v f) = _
    rw [act_x, rt_readF, rt_setF]
  have b5 : ∀ q v f w : Nat, actGates (loadC (qReg n + t) (vReg n) dk w) (rt n t i q v f)
      = rt n t i q ((v % 2 ^ dk) ^^^ (f % 2 * w)) f := by
    intro q v f w
    rw [loadC_act dk (vReg n) w (rt n t i q v f) (Or.inr (by omega)), rt_readV ht, rt_readF,
      rt_setV ht]
  -- the subtraction, with its carry out kept
  have b2 : ∀ q v : Nat, v % 2 ^ dk = D → q < 2 ^ dk →
      actGates (achain (vReg n) (pReg n) (cReg n)
          [RGate.cx (vReg n + dkp) (qReg n + t)] 0 dk) (rt n t i q v 0)
        = rt n t i ((D + q) % 2 ^ dk) v ((D + q) / 2 ^ dk % 2) := by
    intro q v hvD hq
    have hach := achain_act (A := vReg n) (B := pReg n) (c := cReg n) (z := qReg n + t)
      (K := dk) (φ := fun x y => (x + y) % 2) (mid := [RGate.cx (vReg n + dkp) (qReg n + t)])
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inr (by omega)) (by omega) hmid1 dk 0 (by omega)
      (rt n t i q v 0)
    simp only [Nat.add_zero, cwire] at hach
    rw [rt_readV ht, rt_readP ht, rt_readC ht, hc, hvD, Nat.mod_eq_of_lt hq, rt_readF,
      Nat.add_zero, Nat.zero_mod, Nat.zero_add] at hach
    rw [hach, rt_setP ht, rt_setF]
  -- the constant added back
  have b6 : ∀ q v f : Nat, q < 2 ^ dk →
      actGates (achain (vReg n) (pReg n) (cReg n) [] 0 dk) (rt n t i q v f)
        = rt n t i ((v % 2 ^ dk + q) % 2 ^ dk) v f := by
    intro q v f hq
    have hach := achain_act (A := vReg n) (B := pReg n) (c := cReg n) (z := 0)
      (K := dk) (φ := fun x _ => x) (mid := [])
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (by omega) hmid0 dk 0 (by omega)
      (rt n t i q v f)
    simp only [Nat.add_zero, cwire] at hach
    rw [rt_readV ht, rt_readP ht, rt_readC ht, hc, Nat.mod_eq_of_lt hq, Nat.add_zero] at hach
    rw [hach]
    have hout : writeField (writeField (rt n t i q v f) (pReg n) dk ((v % 2 ^ dk + q) % 2 ^ dk))
        0 1 (bv (rt n t i q v f) 0)
        = writeField (rt n t i q v f) (pReg n) dk ((v % 2 ^ dk + q) % 2 ^ dk) := by
      refine write_of_bv ?_
      rw [bv_write_out (Or.inl (by omega))]
      have := bv_lt (rt n t i q v f) 0
      omega
    rw [hout, rt_setP ht]
  -- the eight blocks in order
  have hDd : D < 2 ^ dk := by omega
  obtain ⟨g, hgdef⟩ : ∃ x, (D + p) / 2 ^ dk % 2 = x := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ x, (D + p) % 2 ^ dk = x := ⟨_, rfl⟩
  have hP1d : P1 < 2 ^ dk := by rw [← hP1]; exact Nat.mod_lt _ hdkpos
  obtain ⟨g', hg'⟩ : ∃ x, (g % 2 + 1) % 2 = x := ⟨_, rfl⟩
  have hg'2 : g' < 2 := by rw [← hg']; omega
  obtain ⟨V2, hV2⟩ : ∃ x, g' % 2 * C = x := ⟨_, rfl⟩
  have hV2d : V2 < 2 ^ dk := by
    rcases (show g' % 2 = 0 ∨ g' % 2 = 1 by omega) with h | h <;> rw [← hV2, h] <;> omega
  obtain ⟨P2, hP2⟩ : ∃ x, (V2 % 2 ^ dk + P1) % 2 ^ dk = x := ⟨_, rfl⟩
  have c1 : actGates (loadX (vReg n) dk D) (rt n t i p 0 0) = rt n t i p D 0 := by
    rw [b1 p 0 0, Nat.zero_mod, Nat.zero_xor]
  have c2 : actGates (achain (vReg n) (pReg n) (cReg n)
      [RGate.cx (vReg n + dkp) (qReg n + t)] 0 dk) (rt n t i p D 0) = rt n t i P1 D g := by
    rw [b2 p D (Nat.mod_eq_of_lt hDd) hpd, hP1, hgdef]
  have c3 : actGates (loadX (vReg n) dk D) (rt n t i P1 D g) = rt n t i P1 0 g := by
    rw [b1 P1 D g, Nat.mod_eq_of_lt hDd, Nat.xor_self]
  have c4 : actGates [RGate.x (qReg n + t)] (rt n t i P1 0 g) = rt n t i P1 0 g' := by
    rw [b4 P1 0 g, hg']
  have c5 : actGates (loadC (qReg n + t) (vReg n) dk C) (rt n t i P1 0 g')
      = rt n t i P1 V2 g' := by
    rw [b5 P1 0 g' C, Nat.zero_mod, Nat.zero_xor, hV2]
  have c6 : actGates (achain (vReg n) (pReg n) (cReg n) [] 0 dk) (rt n t i P1 V2 g')
      = rt n t i P2 V2 g' := by
    rw [b6 P1 V2 g' hP1d, hP2]
  have c7 : actGates (loadC (qReg n + t) (vReg n) dk C) (rt n t i P2 V2 g')
      = rt n t i P2 0 g' := by
    rw [b5 P2 V2 g' C, Nat.mod_eq_of_lt hV2d, hV2, Nat.xor_self]
  have c8 : actGates [RGate.x (qReg n + t)] (rt n t i P2 0 g')
      = rt n t i P2 0 ((g' % 2 + 1) % 2) := by
    rw [b4 P2 0 g']
  have hall : actGates (rstep n t) i = rt n t i P2 0 ((g' % 2 + 1) % 2) := by
    have hgoal : actGates (rstep n t) i = actGates (rstep n t) (rt n t i p 0 0) := by rw [hi]
    rw [hgoal]
    simp only [rstep, actGates_append]
    rw [hCe, hDe, c1, c2, c3, c4, c5, c6, c7, c8]
  -- what the step computed
  have S1 := split_two (K := 2 ^ dk) (x := D + p) hdkpos (by omega)
  rcases S1 with ⟨d0, d1, d2⟩ | ⟨d0, d1, d2⟩
  · have hgv : g = 0 := by rw [← hgdef, d1]
    have hg'v : g' = 1 := by rw [← hg', hgv]
    have hV2v : V2 = C := by rw [← hV2, hg'v]; omega
    have hP1v : P1 = D + p := by rw [← hP1, d2]
    have hP2v : P2 = p := by
      rw [← hP2, hV2v, hP1v, Nat.mod_eq_of_lt hCd,
        show C + (D + p) = 2 ^ dk + p from by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hpd]
    refine ⟨p, 0, by omega, rfl, by omega, ?_⟩
    rw [hall, hP2v, hg'v, rt_clean ht hv]
  · have hgv : g = 1 := by rw [← hgdef, d1]
    have hg'v : g' = 0 := by rw [← hg', hgv]
    have hV2v : V2 = 0 := by rw [← hV2, hg'v]; simp
    have hP1v : P1 = p - C := by rw [← hP1, d2]; omega
    have hP2v : P2 = p - C := by
      rw [← hP2, hV2v, hP1v, Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    have hmod : (p - C) % m = p % m := by
      have he : p - C + 2 ^ t * m = p := by
        have hcm : C = 2 ^ t * m := by rw [← hCe, Nat.mul_comm]
        omega
      calc (p - C) % m = (p - C + 2 ^ t * m) % m := (Nat.add_mul_mod_self_right _ _ _).symm
        _ = p % m := by rw [he]
    refine ⟨p - C, 1, by omega, hmod, by omega, ?_⟩
    rw [hall, hP2v, hg'v, rt_clean ht hv]

/-- Merging the quotient bit written by a step into the field of the bits the
rest of the loop writes. -/
theorem flag_merge {Y off t z f : Nat} :
    writeField (writeField Y off t z) (off + t) 1 f
      = writeField Y off (t + 1) (z % 2 ^ t + 2 ^ t * f) := by
  have hpt : (0 : Nat) < 2 ^ t := Nat.two_pow_pos t
  have e1 : (z % 2 ^ t + 2 ^ t * f) % 2 ^ t = z % 2 ^ t := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
  have e2 : (z % 2 ^ t + 2 ^ t * f) / 2 ^ t = f := by
    rw [Nat.add_mul_div_left _ _ hpt, Nat.div_eq_of_lt (Nat.mod_lt z hpt), Nat.zero_add]
  rw [writeField_split Y off t 1 (z % 2 ^ t + 2 ^ t * f), e1, e2, writeField_mod]

/-- The whole reduction.  From an accumulator below `m * 2 ^ t` it produces
the residue and `t` quotient bits.  The theorem existentially quantifies the
quotient value.  The reverse pass clears those bits, and correctness depends on
the residue. -/
theorem rloop_act {n : Nat} (hk : k ≤ n) : ∀ t, t ≤ k → ∀ i p : Nat,
    readField i (pReg n) dk = p → p < m * 2 ^ t → readField i (qReg n) t = 0 →
    readField i (vReg n) dk = 0 → bv i (cReg n) = 0 →
    ∃ z, actGates (rloop n t) i
      = writeField (writeField i (pReg n) dk (p % m)) (qReg n) t z := by
  intro t
  induction t with
  | zero =>
    intro _ i p hp hpm _ _ _
    refine ⟨0, ?_⟩
    have hpm' : p < m := by rw [Nat.pow_zero, Nat.mul_one] at hpm; exact hpm
    rw [writeField_zero, Nat.mod_eq_of_lt hpm', ← hp, writeField_read]
    rfl
  | succ t ih =>
    intro ht i p hp hpm hq hv hc
    have h2 := e_p n
    have h3 := e_v n
    have h4 := e_q n
    have h5 := e_c n
    have h7 := e_dk
    have hkp := k_pos
    have hpt : (0 : Nat) < 2 ^ t := Nat.two_pow_pos t
    have hqt : bv i (qReg n + t) = 0 := by
      rw [← readField_one]
      exact readField_sub_zero hq (by omega)
    obtain ⟨p', f, hp'lt, hp'mod, hf2, hact⟩ := rstep_act hk (by omega) hp hv hqt hc hpm
    have hp'd : p' < 2 ^ dk := by
      have e1 : m * 2 ^ t < 2 ^ k * 2 ^ t := Nat.mul_lt_mul_of_lt_of_le m_lt (Nat.le_refl _) hpt
      have e2 : (2 : Nat) ^ k * 2 ^ t = 2 ^ (k + t) := (Nat.pow_add 2 k t).symm
      have e3 : (2 : Nat) ^ (k + t) ≤ 2 ^ dk := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hqlow : readField i (qReg n) t = 0 := by
      have h := readField_sub_zero hq (d := 0) (e := t) (by omega)
      rw [Nat.add_zero] at h
      exact h
    have r1 : readField (writeField (writeField i (pReg n) dk p') (qReg n + t) 1 f)
        (pReg n) dk = p' := by
      rw [readField_writeField_of_disjoint (Or.inr (by omega)), readField_writeField,
        Nat.mod_eq_of_lt hp'd]
    have r2 : readField (writeField (writeField i (pReg n) dk p') (qReg n + t) 1 f)
        (qReg n) t = 0 := by
      rw [readField_writeField_of_disjoint (Or.inr (by omega)),
        readField_writeField_of_disjoint (Or.inl (by omega))]
      exact hqlow
    have r3 : readField (writeField (writeField i (pReg n) dk p') (qReg n + t) 1 f)
        (vReg n) dk = 0 := by
      rw [readField_writeField_of_disjoint (Or.inr (by omega)),
        readField_writeField_of_disjoint (Or.inl (by omega))]
      exact hv
    have r4 : bv (writeField (writeField i (pReg n) dk p') (qReg n + t) 1 f) (cReg n) = 0 := by
      rw [← readField_one, readField_writeField_of_disjoint (Or.inl (by omega)),
        readField_writeField_of_disjoint (Or.inl (by omega)), readField_one]
      exact hc
    obtain ⟨z, hz⟩ := ih (by omega) _ p' r1 hp'lt r2 r3 r4
    refine ⟨z % 2 ^ t + 2 ^ t * f, ?_⟩
    rw [show rloop n (t + 1) = rstep n t ++ rloop n t from rfl, actGates_append, hact, hz,
      writeField_comm (o₁ := qReg n + t) (n₁ := 1) (o₂ := pReg n) (n₂ := dk) (Or.inr (by omega)),
      writeField_writeField,
      writeField_comm (o₁ := qReg n + t) (n₁ := 1) (o₂ := qReg n) (n₂ := t) (Or.inr (by omega)),
      flag_merge, hp'mod]

theorem gates_le : ∀ n : Nat,
    VQ.Circuit.gateCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Mul.gen n)) ≤ 8395520 := by
  intro n
  rw [VQ.Reversible.gateCount_compile]
  show (if k ≤ n then body n else []).length
    + 2 * (if k ≤ n then body n else []).countP RGate.isCcx ≤ 8395520
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    have h1 := (body_counts n).1
    have h2 := (body_counts n).2.1
    have e1 : k = 256 := rfl
    have e2 : sk = 257 := rfl
    have e3 : dk = 512 := rfl
    rw [e1, e2, e3] at h1 h2
    omega
  · rw [if_neg hk]; decide


/-! ### Correctness claim

The forward pass leaves the residue in the low `k` bits of the accumulator and
quotient data in the quotient register.  The residue is copied into the product field,
which the forward pass never names, and the reversed forward pass then restores
every workspace wire and both operands. -/

theorem muls_general : ∀ n : Nat, VQ.Reversible.MulsMod VQ.Curve.PointAddition.Arithmetic.Mul.m VQ.Curve.PointAddition.Arithmetic.Mul.ws n (VQ.Curve.PointAddition.Arithmetic.Mul.gen n) := by
  intro n a b i _hi h0 h1 h2 h3 hm ha hb
  have hk : k ≤ n := k_le hm
  have hkp := k_pos
  have h6 := e_sk
  have h7 := e_dk
  have h8 := e_ws
  have hpp := e_p n
  have hvv := e_v n
  have hqq := e_q n
  have hcc := e_c n
  have hmk : m < 2 ^ k := m_lt
  have hm0 : 0 < m := m_pos
  -- the layout
  have e0 : readField i 0 n = a := h0
  have e1 : readField i n n = b := h1
  have e2' : readField i (n + n) n = 0 := h2
  have e3' : readField i (n + (n + n)) ws = 0 := h3
  have e2 : readField i (2 * n) n = 0 := by
    rw [show 2 * n = n + n from by omega]; exact e2'
  have e3 : readField i (3 * n) ws = 0 := by
    rw [show 3 * n = n + (n + n) from by omega]; exact e3'
  -- the workspace registers are clear
  have wS : readField i (sReg n) sk = 0 := by
    have h := readField_sub_zero e3 (d := 0) (e := sk) (by omega)
    rw [Nat.add_zero] at h
    exact h
  have wP : readField i (pReg n) dk = 0 := by
    have h := readField_sub_zero e3 (d := sk) (e := dk) (by omega)
    rw [show 3 * n + sk = pReg n from by rw [e_p]] at h
    exact h
  have wV : readField i (vReg n) dk = 0 := by
    have h := readField_sub_zero e3 (d := sk + dk) (e := dk) (by omega)
    rw [show 3 * n + (sk + dk) = vReg n from by rw [e_v]; omega] at h
    exact h
  have wQ : readField i (qReg n) k = 0 := by
    have h := readField_sub_zero e3 (d := sk + dk + dk) (e := k) (by omega)
    rw [show 3 * n + (sk + dk + dk) = qReg n from by rw [e_q]; omega] at h
    exact h
  have wC : bv i (cReg n) = 0 := by
    have h := readField_sub_zero e3 (d := sk + dk + dk + k) (e := 1) (by omega)
    rw [show 3 * n + (sk + dk + dk + k) = cReg n from by rw [e_c]; omega, readField_one] at h
    exact h
  -- the operands, read at the width of the modulus
  have ea : readField i 0 k = a := by
    rw [readField_narrow i 0 k n hk, e0, Nat.mod_eq_of_lt (by omega)]
  have eb : readField i n k = b := by
    rw [readField_narrow i n k n hk, e1, Nat.mod_eq_of_lt (by omega)]
  -- the bounds the two phases need
  have hRk : a * b % m < 2 ^ k := by
    have := Nat.mod_lt (a * b) hm0
    omega
  have hdkkk : (2 : Nat) ^ dk = 2 ^ k * 2 ^ k := by
    rw [← Nat.pow_add, show k + k = dk from by omega]
  have habm : a * b < m * 2 ^ k :=
    Nat.mul_lt_mul_of_lt_of_le ha (by omega) (Nat.two_pow_pos k)
  have habd : a * b < 2 ^ dk := by
    have h1' : a * b < 2 ^ k * 2 ^ k :=
      Nat.mul_lt_mul_of_lt_of_le (show a < 2 ^ k by omega) (show b ≤ 2 ^ k by omega)
        (Nat.two_pow_pos k)
    rw [hdkkk]
    exact h1'
  have hact : act (VQ.Curve.PointAddition.Arithmetic.Mul.gen n) i = actGates (body n) i := by
    show actGates (if k ≤ n then body n else []) i = _
    rw [if_pos hk]
  -- the product
  have hmul : actGates (mloop n k) i = writeField i (pReg n) dk (a * b) := by
    have h := mloop_act hk wC ea eb k (Nat.le_refl k)
    rw [ms_id wS wP] at h
    rw [h, Nat.mod_eq_of_lt (show b < 2 ^ k by omega)]
    unfold ms
    rw [show writeField i (sReg n) sk 0 = i from by rw [← wS]; exact writeField_read _ _ _]
  -- the reduction
  have hP1 : readField (writeField i (pReg n) dk (a * b)) (pReg n) dk = a * b := by
    rw [readField_writeField, Nat.mod_eq_of_lt habd]
  have hQ1 : readField (writeField i (pReg n) dk (a * b)) (qReg n) k = 0 := by
    rw [readField_writeField_of_disjoint (Or.inl (by omega))]
    exact wQ
  have hV1 : readField (writeField i (pReg n) dk (a * b)) (vReg n) dk = 0 := by
    rw [readField_writeField_of_disjoint (Or.inl (by omega))]
    exact wV
  have hC1 : bv (writeField i (pReg n) dk (a * b)) (cReg n) = 0 := by
    rw [← readField_one, readField_writeField_of_disjoint (Or.inl (by omega)), readField_one]
    exact wC
  obtain ⟨z, hz⟩ := rloop_act hk k (Nat.le_refl k) _ (a * b) hP1 habm hQ1 hV1 hC1
  have hfwd : actGates (fwd n) i
      = writeField (writeField i (pReg n) dk (a * b % m)) (qReg n) k z := by
    rw [show fwd n = mloop n k ++ rloop n k from rfl, actGates_append, hmul, hz,
      writeField_writeField]
  -- the copy out and the uncomputation
  obtain ⟨J, hJ⟩ : ∃ x, actGates (fwd n) i = x := ⟨_, rfl⟩
  have hJP : readField J (pReg n) k = a * b % m := by
    rw [← hJ, hfwd, readField_writeField_of_disjoint (Or.inr (by omega))]
    have h := readField_write_sub (x := i) (off := pReg n) (N := dk) (v := a * b % m)
      (d := 0) (e := k) (by omega)
    rw [Nat.add_zero, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hRk] at h
    exact h
  have hJ2 : readField J (2 * n) k = 0 := by
    rw [← hJ, hfwd, readField_writeField_of_disjoint (Or.inr (by omega)),
      readField_writeField_of_disjoint (Or.inr (by omega)),
      readField_narrow i (2 * n) k n hk, e2, Nat.zero_mod]
  have hcopy : actGates (pcopy (pReg n) (2 * n) k) J = writeField J (2 * n) k (a * b % m) := by
    rw [pcopy_act k (pReg n) (2 * n) J (Or.inr (by omega)), hJ2, hJP, Nat.zero_xor]
  have hrev : actGates (fwd n).reverse (writeField J (2 * n) k (a * b % m))
      = writeField i (2 * n) k (a * b % m) := by
    rw [actGates_out (fun g hg => fwd_out hk g (List.mem_reverse.mp hg)) J, ← hJ,
      revUndo (fwd_wf hk) i]
  rw [hact]
  show actGates (body n) i = writeField i (n + n) n (a * b % m)
  rw [show body n = (fwd n ++ pcopy (pReg n) (2 * n) k) ++ (fwd n).reverse from rfl,
    actGates_append, actGates_append, hJ, hcopy, hrev, show n + n = 2 * n from by omega]
  exact write_widen hk hRk (by rw [e2]; exact Nat.two_pow_pos k)

/-- Modular multiplication with the modulus and workspace specialized to their fixed values. -/
theorem muls : ∀ n : Nat,
    VQ.Reversible.MulsMod
      115792089237316195423570985008687907853269984665640564039457584007908834671663
      1538 n (VQ.Curve.PointAddition.Arithmetic.Mul.gen n) := muls_general

end Mul
end VQ.Curve.PointAddition.Arithmetic
