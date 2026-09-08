/-
Negation modulo the secp256k1 prime, in place, over
`VQ.Reversible.constLayout n ws`.

`NegatesMod m ws n` asks for one operand field of `n` wires holding `a < m`, a
workspace of `ws` wires starting clear, and the operand replaced by `(m - a) % m`.
That map is not affine over GF(2) and not a constant addition either: every
nonzero residue goes to `m - a`, and zero goes to zero rather than to `m`.
Complementing the low `k` bits of the field and adding the classical constant
`m + 1` modulo `2 ^ k` gives `2 ^ k + (m - a)`, so `m - a`, at every operand the
claim covers.  At `a = 0` this expression equals `m`, which lies outside the
specification.  A negation circuit must therefore distinguish `a = 0`.
`examples/08-modsub` computes `m - a` in a separate register to preserve the
zero case.

The carry out of `(2 ^ k - 1 - a) + 1` provides the zero test without an
additional carry chain.  It is set exactly when `a` is zero, so the first chain
adds the constant `1` to the complement of the field and copies its own carry to
the flag: the field becomes `(2 ^ k - a) % 2 ^ k` and the flag becomes `a = 0`,
with no gate spent beyond the chain and the one `cx` that reads its top carry
wire.  Flipping the flag and adding `m` under its control finishes the value:
`2 ^ k - a + m` reduces to `m - a`, and at `a = 0` nothing is added to a field
already holding zero.  The flag is then cleared by comparing the result against
one.  The carry out of `(2 ^ k - 1) + result` is `result ≠ 0`, hence `a ≠ 0`,
and the comparison's `cx` clears the flag without a correcting `x`.

Three chains of `k` positions use `6 * k` Toffolis.  The construction in
`examples/08-modsub` uses `12 * k` Toffolis because its specification preserves
the input, requiring a second `k`-bit register and a copy.  The workspace here
is one carry ancilla, one flag, and one `k`-bit constant register, so
`ws = k + 2`.

The modulus is fixed and the width `n` is the family
parameter.  The operand the specification covers is below the modulus, so only
its low `k` bits carry information, where `k` is the bit length of the modulus.
The circuit is a gadget of fixed size placed at width-dependent offsets, and
every resource count is a constant.

`kp` is `k - 1`, written so that `k` is syntactically a successor: the carry wire
at the top of a chain of `k` positions is then `A + kp` by definition.
-/
import VQ.Curve.Field
import VQ.Reversible.ArithmeticSpec
import VQ.Reversible.Compile
import VQ.Reversible.Reverse

open VQ VQ.Reversible

namespace VQ.Curve.PointAddition.Arithmetic
namespace Neg

/-- One less than the bit length of the modulus. -/
def kp : Nat := 255

/-- The bit length of the modulus: the number of positions every chain runs
over. -/
def k : Nat := kp + 1

/-- The modulus. -/
def m : Nat := VQ.Curve.p

/-- The workspace: a carry ancilla, a flag, and a `k`-bit constant register. -/
def ws : Nat := k + 2

/-- The carry-in ancilla of every chain. -/
def cw (n : Nat) : Nat := n

/-- The flag wire, which records whether the operand was zero. -/
def fw (n : Nat) : Nat := n + 1

/-- The base of the `k`-bit register the classical constants are loaded into. -/
def vw (n : Nat) : Nat := n + 2

theorem m_pos : 0 < m := by decide

theorem m_lt : m < 2 ^ k := by decide

theorem one_lt : (1 : Nat) < 2 ^ k := by decide

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

/-! ## Circuit construction -/

/-- Cuccaro's MAJ on the carry-in wire `c`, the addend wire `b`, and the augend
wire `a`.  It sends `(c, b, a)` to `(c ^^^ a, b ^^^ a, maj a b c)`, so the carry
out of this position ends up on the augend wire. -/
def maj (c b a : Nat) : List RGate :=
  [RGate.cx a b, RGate.cx a c, RGate.ccx c b a]

/-- Cuccaro's UMA, the two-CNOT form.  It restores `c` and `a` and leaves the
sum bit on `b`. -/
def uma (c b a : Nat) : List RGate :=
  [RGate.ccx c b a, RGate.cx a c, RGate.cx c b]

/-- The reverse of `maj`, which undoes it.  A chain of MAJ steps closed by this
rather than by UMA computes the carry out and changes nothing else, which is a
comparator. -/
def umj (c b a : Nat) : List RGate :=
  [RGate.ccx c b a, RGate.cx a c, RGate.cx a b]

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

/-- The comparison chain: MAJ up the positions, `mid` at the top, MAJ inverted
back down.  Both operand fields come back unchanged.  Only what `mid` writes
survives. -/
def cchain (A B c : Nat) (mid : List RGate) : Nat → Nat → List RGate
  | _, 0 => mid
  | st, p + 1 =>
      maj (cwire A c st) (B + st) (A + st) ++ cchain A B c mid (st + 1) p
        ++ umj (cwire A c st) (B + st) (A + st)

/-- Exclusive-or of the classical constant `v` into the `p`-bit register at `W`,
one `x` gate per set bit. -/
def loadX : Nat → Nat → Nat → List RGate
  | _, 0, _ => []
  | W, p + 1, v => (if v % 2 = 1 then [RGate.x W] else []) ++ loadX (W + 1) p (v / 2)

/-- The same exclusive-or under the control of wire `c`, one CNOT per set bit.
Conditional loading applies a CNOT to each set bit.  The adder remains
uncontrolled. -/
def loadC (c : Nat) : Nat → Nat → Nat → List RGate
  | _, 0, _ => []
  | W, p + 1, v =>
      (if v % 2 = 1 then [RGate.cx c W] else []) ++ loadC c (W + 1) p (v / 2)

/-- Add the augend into the addend and record the carry out on the flag. -/
def blockAdd (A B c z : Nat) : List RGate :=
  achain A B c [RGate.cx (A + kp) z] 0 k

/-- Compare the two fields, leaving both where they were, and record the carry
out on the flag. -/
def blockCmp (A B c z : Nat) : List RGate :=
  cchain A B c [RGate.cx (A + kp) z] 0 k

/-- The whole gadget, at a width that can hold the modulus.

Read left to right: complement the low `k` bits of the operand.  Load `1` and add
it, recording the carry, which is the test for zero.  Unload.  Flip the flag, so
it holds `a ≠ 0`.  Load `m` under the flag, add it, and unload.  Then load the
all-ones pattern and compare, which is the carry out of `(2 ^ k - 1) + result`,
and that is `result ≠ 0`, so it cancels the flag. -/
def gadget (n : Nat) : List RGate :=
  loadX 0 k (2 ^ k - 1)
    ++ loadX (vw n) k 1
    ++ blockAdd (vw n) 0 (cw n) (fw n)
    ++ loadX (vw n) k 1
    ++ [RGate.x (fw n)]
    ++ loadC (fw n) (vw n) k m
    ++ achain (vw n) 0 (cw n) [] 0 k
    ++ loadC (fw n) (vw n) k m
    ++ loadX (vw n) k (2 ^ k - 1)
    ++ blockCmp (vw n) 0 (cw n) (fw n)
    ++ loadX (vw n) k (2 ^ k - 1)

/-- The generator.  Below the bit length of the modulus the operand field cannot
hold it, the clause of `NegatesMod` is vacuous, and the circuit is the
identity. -/
def gen (n : Nat) : RCircuit :=
  { width := n + ws, gates := if k ≤ n then gadget n else [] }

/-! ## Well-formedness

Each chain is one induction over the positions.  The geometric hypotheses are
that the two operand fields are disjoint and that the carry ancilla and the flag
lie outside both.  Everything else is arithmetic. -/

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

/-- The carry wire at the top of a chain of `k` positions. -/
theorem cwire_k (A c : Nat) : cwire A c k = A + kp := rfl

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

theorem umj_wf {w c b a : Nat} (ha : a < w) (hb : b < w) (hc : c < w)
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    (umj c b a).all (RGate.wellFormed w) = true := by
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  simp [umj, RGate.wellFormed, ha, hb, hc, hab, hac, hcb, hba, hca]

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

theorem cchain_wf {A B c w K : Nat} {mid : List RGate}
    (hA : A + K ≤ w) (hB : B + K ≤ w) (hc : c < w) (hK : 0 < K)
    (hAB : A + K ≤ B ∨ B + K ≤ A)
    (hcA : c < A ∨ A + K ≤ c) (hcB : c < B ∨ B + K ≤ c)
    (hmid : mid.all (RGate.wellFormed w) = true) :
    ∀ p st, st + p = K → (cchain A B c mid st p).all (RGate.wellFormed w) = true := by
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
    simp only [cchain, List.all_append, Bool.and_eq_true]
    exact ⟨⟨maj_wf ha hb hcw hab hac hcb, ih (st + 1) (by omega)⟩,
      umj_wf ha hb hcw hab hac hcb⟩

theorem x_wf {w a : Nat} (ha : a < w) : ([RGate.x a]).all (RGate.wellFormed w) = true := by
  simp [RGate.wellFormed, ha]

theorem cx_wf {w a b : Nat} (ha : a < w) (hb : b < w) (hab : a ≠ b) :
    ([RGate.cx a b]).all (RGate.wellFormed w) = true := by
  simp [RGate.wellFormed, ha, hb, hab]

theorem loadX_wf {w : Nat} : ∀ (p W v : Nat), W + p ≤ w →
    (loadX W p v).all (RGate.wellFormed w) = true := by
  intro p
  induction p with
  | zero => intro W v _; rfl
  | succ p ih =>
    intro W v hW
    simp only [loadX, List.all_append, Bool.and_eq_true]
    refine ⟨?_, ih (W + 1) (v / 2) (by omega)⟩
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; exact x_wf (by omega)
    · rw [if_neg hv]; rfl

theorem loadC_wf {w c : Nat} (hc : c < w) : ∀ (p W v : Nat), W + p ≤ w → c < W ∨ W + p ≤ c →
    (loadC c W p v).all (RGate.wellFormed w) = true := by
  intro p
  induction p with
  | zero => intro W v _ _; rfl
  | succ p ih =>
    intro W v hW hcW
    simp only [loadC, List.all_append, Bool.and_eq_true]
    refine ⟨?_, ih (W + 1) (v / 2) (by omega) (by omega)⟩
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; exact cx_wf hc (by omega) (by omega)
    · rw [if_neg hv]; rfl

theorem gadget_wf {n : Nat} (hk : k ≤ n) :
    (gadget n).all (RGate.wellFormed (n + ws)) = true := by
  have hws : ws = k + 2 := rfl
  have hcv : cw n = n := rfl
  have hfv : fw n = n + 1 := rfl
  have hvv : vw n = n + 2 := rfl
  have hkp : k = kp + 1 := rfl
  have hmid : ([RGate.cx (vw n + kp) (fw n)]).all (RGate.wellFormed (n + ws)) = true :=
    cx_wf (by omega) (by omega) (by omega)
  have hla : ∀ v, (loadX 0 k v).all (RGate.wellFormed (n + ws)) = true :=
    fun v => loadX_wf k 0 v (by omega)
  have hlv : ∀ v, (loadX (vw n) k v).all (RGate.wellFormed (n + ws)) = true :=
    fun v => loadX_wf k (vw n) v (by omega)
  have hlc : ∀ v, (loadC (fw n) (vw n) k v).all (RGate.wellFormed (n + ws)) = true :=
    fun v => loadC_wf (by omega) k (vw n) v (by omega) (Or.inl (by omega))
  have hone : ([RGate.x (fw n)]).all (RGate.wellFormed (n + ws)) = true := x_wf (by omega)
  have hc1 : (achain (vw n) 0 (cw n) [RGate.cx (vw n + kp) (fw n)] 0 k).all
      (RGate.wellFormed (n + ws)) = true :=
    achain_wf (A := vw n) (B := 0) (c := cw n) (K := k)
      (by omega) (by omega) (by omega) k_pos
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) hmid k 0 (by omega)
  have hc2 : (achain (vw n) 0 (cw n) [] 0 k).all
      (RGate.wellFormed (n + ws)) = true :=
    achain_wf (A := vw n) (B := 0) (c := cw n) (K := k)
      (by omega) (by omega) (by omega) k_pos
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) rfl k 0 (by omega)
  have hc3 : (cchain (vw n) 0 (cw n) [RGate.cx (vw n + kp) (fw n)] 0 k).all
      (RGate.wellFormed (n + ws)) = true :=
    cchain_wf (A := vw n) (B := 0) (c := cw n) (K := k)
      (by omega) (by omega) (by omega) k_pos
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) hmid k 0 (by omega)
  simp only [gadget, blockAdd, blockCmp, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hla _, hlv _⟩, hc1⟩, hlv _⟩, hone⟩, hlc _⟩, hc2⟩, hlc _⟩, hlv _⟩, hc3⟩, hlv _⟩

theorem wf : ∀ n : Nat, VQ.Reversible.RCircuit.wellFormed (VQ.Curve.PointAddition.Arithmetic.Neg.gen n) = true := by
  intro n
  show (if k ≤ n then gadget n else []).all (RGate.wellFormed (n + ws)) = true
  by_cases hk : k ≤ n
  · rw [if_pos hk]; exact gadget_wf hk
  · rw [if_neg hk]; rfl

/-! ## Resource bounds

Every count is a constant.  The gate list does not grow with the width: it is
one gadget of `k` positions placed at width-dependent offsets, and it is empty
below the width that can hold the modulus.

The Toffoli count is exact, at `6 * k`.  The other two are bounds and are loose,
because `loadX_length` and `loadC_length` charge each load its full `k` gates
while `loadX (vw n) k 1` emits one and `loadC` emits one per set bit of the
modulus.  Measured at `n = 256`: 5881 gates in the gate list against the bound
`25 * k + 3 = 6403`, 3574 CNOTs against `14 * k + 2 = 3586`, and 8953 gates
after compilation against `37 * k + 3 = 9475`.  An exact count would require a
kernel computation of the prime's population count. -/

theorem achain_length (A B c : Nat) (mid : List RGate) (p st : Nat) :
    (achain A B c mid st p).length = 6 * p + mid.length := by
  induction p generalizing st with
  | zero => simp [achain]
  | succ p ih =>
    simp only [achain, List.length_append, ih (st + 1), maj, uma, List.length_cons,
      List.length_nil]
    omega

theorem cchain_length (A B c : Nat) (mid : List RGate) (p st : Nat) :
    (cchain A B c mid st p).length = 6 * p + mid.length := by
  induction p generalizing st with
  | zero => simp [cchain]
  | succ p ih =>
    simp only [cchain, List.length_append, ih (st + 1), maj, umj, List.length_cons,
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

theorem cchain_ccx (A B c : Nat) (mid : List RGate) (p st : Nat) :
    (cchain A B c mid st p).countP RGate.isCcx = 2 * p + mid.countP RGate.isCcx := by
  induction p generalizing st with
  | zero => simp [cchain]
  | succ p ih =>
    have hm : (maj (cwire A c st) (B + st) (A + st)).countP RGate.isCcx = 1 := rfl
    have hu : (umj (cwire A c st) (B + st) (A + st)).countP RGate.isCcx = 1 := rfl
    simp only [cchain, List.countP_append, ih (st + 1), hm, hu]
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

theorem cchain_cx (A B c : Nat) (mid : List RGate) (p st : Nat) :
    (cchain A B c mid st p).countP RGate.isCx = 4 * p + mid.countP RGate.isCx := by
  induction p generalizing st with
  | zero => simp [cchain]
  | succ p ih =>
    have hm : (maj (cwire A c st) (B + st) (A + st)).countP RGate.isCx = 2 := rfl
    have hu : (umj (cwire A c st) (B + st) (A + st)).countP RGate.isCx = 2 := rfl
    simp only [cchain, List.countP_append, ih (st + 1), hm, hu]
    omega

theorem loadX_length : ∀ (p W v : Nat), (loadX W p v).length ≤ p := by
  intro p
  induction p with
  | zero => intro W v; simp [loadX]
  | succ p ih =>
    intro W v
    have := ih (W + 1) (v / 2)
    simp only [loadX, List.length_append]
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; simp only [List.length_cons, List.length_nil]; omega
    · rw [if_neg hv]; simp only [List.length_nil]; omega

theorem loadC_length : ∀ (p c W v : Nat), (loadC c W p v).length ≤ p := by
  intro p
  induction p with
  | zero => intro c W v; simp [loadC]
  | succ p ih =>
    intro c W v
    have := ih c (W + 1) (v / 2)
    simp only [loadC, List.length_append]
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; simp only [List.length_cons, List.length_nil]; omega
    · rw [if_neg hv]; simp only [List.length_nil]; omega

theorem loadX_ccx : ∀ (p W v : Nat), (loadX W p v).countP RGate.isCcx = 0 := by
  intro p
  induction p with
  | zero => intro W v; rfl
  | succ p ih =>
    intro W v
    have := ih (W + 1) (v / 2)
    simp only [loadX, List.countP_append, this]
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; rfl
    · rw [if_neg hv]; rfl

theorem loadX_cx : ∀ (p W v : Nat), (loadX W p v).countP RGate.isCx = 0 := by
  intro p
  induction p with
  | zero => intro W v; rfl
  | succ p ih =>
    intro W v
    have := ih (W + 1) (v / 2)
    simp only [loadX, List.countP_append, this]
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; rfl
    · rw [if_neg hv]; rfl

theorem loadC_ccx : ∀ (p c W v : Nat), (loadC c W p v).countP RGate.isCcx = 0 := by
  intro p
  induction p with
  | zero => intro c W v; rfl
  | succ p ih =>
    intro c W v
    have := ih c (W + 1) (v / 2)
    simp only [loadC, List.countP_append, this]
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; rfl
    · rw [if_neg hv]; rfl

theorem loadC_cx : ∀ (p c W v : Nat), (loadC c W p v).countP RGate.isCx ≤ p := by
  intro p
  induction p with
  | zero => intro c W v; simp [loadC]
  | succ p ih =>
    intro c W v
    have := ih c (W + 1) (v / 2)
    simp only [loadC, List.countP_append]
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]
      have h1 : ([RGate.cx c W]).countP RGate.isCx = 1 := rfl
      omega
    · rw [if_neg hv]
      have h1 : ([] : List RGate).countP RGate.isCx = 0 := rfl
      omega

theorem gadget_ccx (n : Nat) : (gadget n).countP RGate.isCcx = 6 * k := by
  have e1 : ([RGate.cx (vw n + kp) (fw n)]).countP RGate.isCcx = 0 := rfl
  have e2 : ([RGate.x (fw n)]).countP RGate.isCcx = 0 := rfl
  have e3 : ([] : List RGate).countP RGate.isCcx = 0 := rfl
  simp only [gadget, blockAdd, blockCmp, List.countP_append, achain_ccx, cchain_ccx,
    loadX_ccx, loadC_ccx, e1, e2, e3]
  omega

theorem gadget_cx (n : Nat) : (gadget n).countP RGate.isCx ≤ 14 * k + 2 := by
  have l1 := loadC_cx k (fw n) (vw n) m
  have e1 : ([RGate.cx (vw n + kp) (fw n)]).countP RGate.isCx = 1 := rfl
  have e2 : ([RGate.x (fw n)]).countP RGate.isCx = 0 := rfl
  have e3 : ([] : List RGate).countP RGate.isCx = 0 := rfl
  simp only [gadget, blockAdd, blockCmp, List.countP_append, achain_cx, cchain_cx,
    loadX_cx, e1, e2, e3]
  omega

theorem gadget_len (n : Nat) : (gadget n).length ≤ 25 * k + 3 := by
  have l1 := loadX_length k 0 (2 ^ k - 1)
  have l2 := loadX_length k (vw n) 1
  have l3 := loadX_length k (vw n) (2 ^ k - 1)
  have l4 := loadC_length k (fw n) (vw n) m
  simp only [gadget, blockAdd, blockCmp, List.length_append, achain_length, cchain_length,
    List.length_cons, List.length_nil]
  omega

theorem toffoli_le : ∀ n : Nat,
    VQ.Circuit.toffoliCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Neg.gen n)) ≤ 1536 := by
  intro n
  rw [VQ.Reversible.toffoliCount_compile]
  show (if k ≤ n then gadget n else []).countP RGate.isCcx ≤ 1536
  by_cases hk : k ≤ n
  · rw [if_pos hk, gadget_ccx]; decide
  · rw [if_neg hk]; decide

theorem cnot_le : ∀ n : Nat,
    VQ.Circuit.cnotCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Neg.gen n)) ≤ 3586 := by
  intro n
  rw [VQ.Reversible.cnotCount_compile]
  show (if k ≤ n then gadget n else []).countP RGate.isCx ≤ 3586
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    have := gadget_cx n
    have hkv : k = 256 := rfl
    omega
  · rw [if_neg hk]; decide

theorem gates_le : ∀ n : Nat,
    VQ.Circuit.gateCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Neg.gen n)) ≤ 9475 := by
  intro n
  rw [VQ.Reversible.gateCount_compile]
  show (if k ≤ n then gadget n else []).length
    + 2 * (if k ≤ n then gadget n else []).countP RGate.isCcx ≤ 9475
  by_cases hk : k ≤ n
  · rw [if_pos hk, gadget_ccx]
    have := gadget_len n
    have hkv : k = 256 := rfl
    omega
  · rw [if_neg hk]; decide

/-! ### Wire bounds

`usedWires` counts the distinct wires a gate list names, which is not a count
over the gates, so the bound goes through `usedWires_compile_le_of_mem`: name
the wires the gadget can touch as a list, show every gate stays inside it, and
the count is at most its length. -/

/-- The wires the gadget names: the low `k` of the operand field and the whole
workspace. -/
def uw (n : Nat) : List Nat :=
  List.range k ++ (List.range (k + 2)).map (fun j => n + j)

theorem uw_length (n : Nat) : (uw n).length = 2 * k + 2 := by
  simp only [uw, List.length_append, List.length_map, List.length_range]
  omega

theorem mem_uw_a {n j : Nat} (h : j < k) : j ∈ uw n := by
  simp only [uw, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl h

theorem mem_uw_w {n j : Nat} (h : j < k + 2) : n + j ∈ uw n := by
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

theorem cchain_mem {A B c K : Nat} {mid : List RGate} {P : Nat → Prop}
    (hA : ∀ j, j < K → P (A + j)) (hB : ∀ j, j < K → P (B + j)) (hc : P c)
    (hmid : ∀ g ∈ mid, ∀ q ∈ g.wires, P q) :
    ∀ p st, st + p = K → ∀ g ∈ cchain A B c mid st p, ∀ q ∈ g.wires, P q := by
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
    simp only [cchain, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · simp only [maj, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;>
        · simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl <;> assumption
    · exact ih (st + 1) (by omega) g hg q hq
    · simp only [umj, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;>
        · simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl <;> assumption

theorem loadX_mem {P : Nat → Prop} : ∀ (p W v : Nat), (∀ j, j < p → P (W + j)) →
    ∀ g ∈ loadX W p v, ∀ q ∈ g.wires, P q := by
  intro p
  induction p with
  | zero => intro W v _ g hg; simp [loadX] at hg
  | succ p ih =>
    intro W v hW g hg q hq
    simp only [loadX, List.mem_append] at hg
    rcases hg with hg | hg
    · have h0 : P W := by have := hW 0 (by omega); simpa using this
      by_cases hv : v % 2 = 1
      · rw [if_pos hv] at hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        subst hg
        simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        exact h0
      · rw [if_neg hv] at hg; simp at hg
    · exact ih (W + 1) (v / 2) (fun j hj => by
        have := hW (j + 1) (by omega)
        have he : W + 1 + j = W + (j + 1) := by omega
        rw [he]; exact this) g hg q hq

theorem loadC_mem {P : Nat → Prop} {c : Nat} (hc : P c) :
    ∀ (p W v : Nat), (∀ j, j < p → P (W + j)) → ∀ g ∈ loadC c W p v, ∀ q ∈ g.wires, P q := by
  intro p
  induction p with
  | zero => intro W v _ g hg; simp [loadC] at hg
  | succ p ih =>
    intro W v hW g hg q hq
    simp only [loadC, List.mem_append] at hg
    rcases hg with hg | hg
    · have h0 : P W := by have := hW 0 (by omega); simpa using this
      by_cases hv : v % 2 = 1
      · rw [if_pos hv] at hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        subst hg
        simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hc
        · exact h0
      · rw [if_neg hv] at hg; simp at hg
    · exact ih (W + 1) (v / 2) (fun j hj => by
        have := hW (j + 1) (by omega)
        have he : W + 1 + j = W + (j + 1) := by omega
        rw [he]; exact this) g hg q hq

/-- The four wire families the gadget names, collected once. -/
theorem uw_parts (n : Nat) :
    (∀ j, j < k → (0 + j) ∈ uw n) ∧ (∀ j, j < k → (vw n + j) ∈ uw n) ∧
      cw n ∈ uw n ∧ fw n ∈ uw n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj; simpa using mem_uw_a (n := n) hj
  · intro j hj
    have he : vw n + j = n + (j + 2) := by show n + 2 + j = _; omega
    rw [he]
    exact mem_uw_w (by omega)
  · have he : cw n = n + 0 := by show n = _; omega
    rw [he]; exact mem_uw_w (by omega)
  · have he : fw n = n + 1 := rfl
    rw [he]; exact mem_uw_w (by omega)

theorem gadget_mem (n : Nat) : ∀ g ∈ gadget n, ∀ q ∈ g.wires, q ∈ uw n := by
  obtain ⟨hA, hV, hcm, hfm⟩ := uw_parts n
  have hkp : k = kp + 1 := rfl
  have hmid : ∀ g ∈ [RGate.cx (vw n + kp) (fw n)], ∀ q ∈ g.wires, q ∈ uw n := by
    intro g hg q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hV kp (by omega)
    · exact hfm
  have hx : ∀ g ∈ [RGate.x (fw n)], ∀ q ∈ g.wires, q ∈ uw n := by
    intro g hg q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact hfm
  have h1 := achain_mem (K := k) hV hA hcm hmid k 0 (by omega)
  have h2 := achain_mem (K := k) (mid := []) hV hA hcm (by intro g hg; cases hg) k 0 (by omega)
  have h3 := cchain_mem (K := k) hV hA hcm hmid k 0 (by omega)
  have h4 : ∀ v, ∀ g ∈ loadX 0 k v, ∀ q ∈ g.wires, q ∈ uw n :=
    fun v => loadX_mem k 0 v hA
  have h5 : ∀ v, ∀ g ∈ loadX (vw n) k v, ∀ q ∈ g.wires, q ∈ uw n :=
    fun v => loadX_mem k (vw n) v hV
  have h6 : ∀ v, ∀ g ∈ loadC (fw n) (vw n) k v, ∀ q ∈ g.wires, q ∈ uw n :=
    fun v => loadC_mem hfm k (vw n) v hV
  intro g hg
  simp only [gadget, blockAdd, blockCmp, List.mem_append] at hg
  rcases hg with (((((((((hg | hg) | hg) | hg) | hg) | hg) | hg) | hg) | hg) | hg) | hg
  · exact h4 _ g hg
  · exact h5 _ g hg
  · exact h1 g hg
  · exact h5 _ g hg
  · exact hx g hg
  · exact h6 _ g hg
  · exact h2 g hg
  · exact h6 _ g hg
  · exact h5 _ g hg
  · exact h3 g hg
  · exact h5 _ g hg

/-- The qubit count: the low `k` bits of the operand field and the `k + 2`
workspace wires, whatever the declared width. -/
theorem wires_le : ∀ n : Nat,
    VQ.Circuit.usedWires (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Neg.gen n)) ≤ 514 := by
  intro n
  have hsub : ∀ g ∈ (VQ.Curve.PointAddition.Arithmetic.Neg.gen n).gates, ∀ q ∈ g.wires, q ∈ uw n := by
    intro g hg
    have hg' : g ∈ (if k ≤ n then gadget n else []) := hg
    by_cases hk : k ≤ n
    · rw [if_pos hk] at hg'; exact gadget_mem n g hg'
    · rw [if_neg hk] at hg'; exact absurd hg' (by simp)
  have h := VQ.Reversible.usedWires_compile_le_of_mem hsub
  rw [uw_length] at h
  have hkv : k = 256 := rfl
  omega

/-! ## Correctness

The proof evaluates one basis index at a time.  `bv i q` gives the value on wire
`q`, and `readField i off len` gives the value of a contiguous wire range.  Each
gate action is a single-wire write on `Nat`, reducing correctness to arithmetic
on basis indices.  The lemmas through `VQ.Curve.PointAddition.Arithmetic.Neg.loadC_act` establish the required
loading and bit-level gate semantics. -/

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

/-- A clear field has clear sub-runs, so the single workspace hypothesis
applies to each workspace register. -/
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
theorem readField_low (i off p q : Nat) (h : p ≤ q) :
    readField i off p = readField i off q % 2 ^ p := by
  show (i >>> off) % 2 ^ p = ((i >>> off) % 2 ^ q) % 2 ^ p
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]

/-- If a wide field contains a narrow value, writing another narrow value to it
equals a narrow-field write.  A gadget that acts on only the low `k` bits of the operand
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

theorem umj_write {c b a z v i : Nat} (ha : a ≠ z) (hb : b ≠ z) (hc : c ≠ z) :
    actGates (umj c b a) (writeField i z 1 v)
      = writeField (actGates (umj c b a) i) z 1 v := by
  show RGate.act (RGate.cx a b) (RGate.act (RGate.cx a c)
      (RGate.act (RGate.ccx c b a) (writeField i z 1 v)))
    = writeField (RGate.act (RGate.cx a b) (RGate.act (RGate.cx a c)
      (RGate.act (RGate.ccx c b a) i))) z 1 v
  rw [act_ccx_write hc hb ha, act_cx_write ha hc, act_cx_write ha hb]

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

theorem cx_gwf {w a b : Nat} (ha : a < w) (hb : b < w) (hab : a ≠ b) :
    (RGate.cx a b).wellFormed w = true := by simp [RGate.wellFormed, ha, hb, hab]

theorem ccx_gwf {w a b c : Nat} (ha : a < w) (hb : b < w) (hc : c < w)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (RGate.ccx a b c).wellFormed w = true := by
  simp [RGate.wellFormed, ha, hb, hc, hab, hbc, hac]

/-- The reverse of MAJ undoes it because each gate is an involution. -/
theorem umj_maj {c b a : Nat} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (i : Nat) :
    actGates (umj c b a) (actGates (maj c b a) i) = i := by
  have h1 : (RGate.cx a b).wellFormed (a + b + c + 1) = true :=
    cx_gwf (by omega) (by omega) hab
  have h2 : (RGate.cx a c).wellFormed (a + b + c + 1) = true :=
    cx_gwf (by omega) (by omega) hac
  have h3 : (RGate.ccx c b a).wellFormed (a + b + c + 1) = true :=
    ccx_gwf (by omega) (by omega) (by omega) hcb (Ne.symm hab) (Ne.symm hac)
  show RGate.act (RGate.cx a b) (RGate.act (RGate.cx a c) (RGate.act (RGate.ccx c b a)
      (RGate.act (RGate.ccx c b a) (RGate.act (RGate.cx a c) (RGate.act (RGate.cx a b) i))))) = i
  rw [RGate.act_act h3, RGate.act_act h2, RGate.act_act h1]

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
addend field.  Disjoint operand fields suffice, so the lemma applies in both
directions. -/
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

/-- One position of the comparator.  The MAJ half and its inverse leave both
operand fields where they were.  Only the carry out survives, on `z`. -/
theorem cchain_step {a b c z p : Nat} {φ : Nat → Nat → Nat} (gs : List RGate) (i : Nat)
    (hab : a + 1 + p ≤ b ∨ b + 1 + p ≤ a)
    (hca : c + 1 ≤ a ∨ a + 1 + p ≤ c)
    (hcb : c + 1 ≤ b ∨ b + 1 + p ≤ c)
    (hza : z < a ∨ a + 1 + p ≤ z)
    (hzb : z < b ∨ b + 1 + p ≤ z)
    (hzc : z ≠ c)
    (hinner : ∀ j, actGates gs j =
      writeField j z 1 (φ (bv j z)
        ((readField j (a + 1) p + readField j (b + 1) p + bv j a) / 2 ^ p))) :
    actGates (maj c b a ++ gs ++ umj c b a) i =
      writeField i z 1 (φ (bv i z)
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
  have hmaj := act_maj' hab' hac' hcb' hA hB hC
  rw [readField_succ i a p, readField_succ i b p, hA, hB, hC, hA', hB']
  rw [actGates_append, actGates_append, hmaj,
    hinner (majState i a b c A B C),
    readField_majState (o := a + 1) (len := p) (by omega) (by omega) (by omega),
    readField_majState (o := b + 1) (len := p) (by omega) (by omega) (by omega),
    bv_majState_a hA2 hB2 hC2, bv_majState_out (Ne.symm haz) (Ne.symm hbz) (Ne.symm hcz),
    hA', hB', umj_write haz hbz hcz, ← hmaj, umj_maj hab' hac' hcb']
  have hpow : (2 : Nat) ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ]; omega
  have hW : (A + 2 * A' + (B + 2 * B') + C) / 2 ^ (p + 1)
      = (A' + B' + (A + B + C) / 2) / 2 ^ p := by
    rw [hpow, ← Nat.div_div_eq_div_mul]
    have h2 : (A + 2 * A' + (B + 2 * B') + C) / 2 = A' + B' + (A + B + C) / 2 := by omega
    rw [h2]
  rw [hW]

/-! ### Carry-chain composition -/

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

theorem cchain_act {A B c z K : Nat} {φ : Nat → Nat → Nat} {mid : List RGate}
    (hAB : A + K ≤ B ∨ B + K ≤ A)
    (hcA : c < A ∨ A + K ≤ c) (hcB : c < B ∨ B + K ≤ c)
    (hzA : z < A ∨ A + K ≤ z) (hzB : z < B ∨ B + K ≤ z) (hzc : z ≠ c)
    (hmid : ∀ j, actGates mid j = writeField j z 1 (φ (bv j z) (bv j (cwire A c K)))) :
    ∀ p st, st + p = K → ∀ i,
      actGates (cchain A B c mid st p) i =
        writeField i z 1 (φ (bv i z)
          ((readField i (A + st) p + readField i (B + st) p + bv i (cwire A c st)) / 2 ^ p)) := by
  intro p
  induction p with
  | zero =>
    intro st hst i
    have hs : st = K := by omega
    subst hs
    rw [show cchain A B c mid st 0 = mid from rfl, hmid i, readField_size_zero,
      readField_size_zero]
    simp
  | succ p ih =>
    intro st hst i
    have hlt : st < K := by omega
    have hcc := cwire_cases (A := A) (c := c) (K := K) hlt
    exact cchain_step (a := A + st) (b := B + st) (c := cwire A c st) (p := p) (φ := φ)
      (cchain A B c mid (st + 1) p) i
      (by omega) (by rcases hcc with h | h <;> omega) (by rcases hcc with h | h <;> omega)
      (by omega) (by omega) (by rcases hcc with h | h <;> omega)
      (fun j => ih (st + 1) (by omega) j)

/-! ### Classical-constant loading

Both loads exclusive-or a constant into a register, one gate per set bit, so
their effect is stated with `Nat.xor` and the two bit identities below are what
carries the induction. -/

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

/-- Exclusive-or with the all-ones pattern is complementation. -/
theorem xor_ones : ∀ (p x : Nat), x < 2 ^ p → x ^^^ (2 ^ p - 1) = 2 ^ p - 1 - x := by
  intro p
  induction p with
  | zero =>
    intro x hx
    have h0 : x = 0 := by simpa using hx
    subst h0
    rfl
  | succ p ih =>
    intro x hx
    have hpow : (2 : Nat) ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ]; omega
    have hppos : 0 < (2 : Nat) ^ p := Nat.two_pow_pos p
    have h1 : (x ^^^ (2 ^ (p + 1) - 1)) % 2 = (x % 2 + (2 ^ (p + 1) - 1) % 2) % 2 := xor_bit _ _
    have h2 : (x ^^^ (2 ^ (p + 1) - 1)) / 2 = (x / 2) ^^^ ((2 ^ (p + 1) - 1) / 2) :=
      xor_div_two _ _
    have h3 : (2 ^ (p + 1) - 1) / 2 = 2 ^ p - 1 := by omega
    rw [h3, ih (x / 2) (by omega)] at h2
    omega

theorem loadX_act : ∀ (p W v i : Nat),
    actGates (loadX W p v) i = writeField i W p ((readField i W p) ^^^ v) := by
  intro p
  induction p with
  | zero => intro W v i; rw [writeField_zero]; rfl
  | succ p ih =>
    intro W v i
    have hbw := bv_lt i W
    have hr := readField_succ i W p
    have hhead : actGates (if v % 2 = 1 then [RGate.x W] else []) i
        = writeField i W 1 ((bv i W + v % 2) % 2) := by
      by_cases hv : v % 2 = 1
      · rw [if_pos hv]
        show RGate.act (RGate.x W) i = _
        rw [act_x, hv]
      · rw [if_neg hv]
        have hv0 : v % 2 = 0 := by omega
        rw [hv0]
        show i = writeField i W 1 ((bv i W + 0) % 2)
        exact (write_of_bv (by omega)).symm
    have hα : ((readField i W (p + 1)) ^^^ v) % 2 = (bv i W + v % 2) % 2 := by
      rw [xor_bit]
      have : readField i W (p + 1) % 2 = bv i W := by omega
      rw [this]
    have hβ : ((readField i W (p + 1)) ^^^ v) / 2 = (readField i (W + 1) p) ^^^ (v / 2) := by
      rw [xor_div_two]
      have : readField i W (p + 1) / 2 = readField i (W + 1) p := by omega
      rw [this]
    rw [loadX, actGates_append, hhead, ih (W + 1) (v / 2),
      readField_writeField_of_disjoint (Or.inl (by omega)),
      writeField_succ i W p ((readField i W (p + 1)) ^^^ v), hα, hβ]

theorem loadC_act {c : Nat} : ∀ (p W v i : Nat), (c < W ∨ W + p ≤ c) →
    actGates (loadC c W p v) i = writeField i W p ((readField i W p) ^^^ (bv i c * v)) := by
  intro p
  induction p with
  | zero => intro W v i _; rw [writeField_zero]; rfl
  | succ p ih =>
    intro W v i hcW
    have hbw := bv_lt i W
    have hbc := bv_lt i c
    have hr := readField_succ i W p
    have ht : bv i c = 0 ∨ bv i c = 1 := by omega
    have hcne : c ≠ W := by omega
    have hhead : actGates (if v % 2 = 1 then [RGate.cx c W] else []) i
        = writeField i W 1 ((bv i W + bv i c * (v % 2)) % 2) := by
      by_cases hv : v % 2 = 1
      · rw [if_pos hv]
        show RGate.act (RGate.cx c W) i = _
        rw [act_cx, hv]
        exact write_congr (by omega)
      · rw [if_neg hv]
        have hv0 : v % 2 = 0 := by omega
        rw [hv0]
        show i = writeField i W 1 ((bv i W + bv i c * 0) % 2)
        exact (write_of_bv (by omega)).symm
    have hbc1 : bv (writeField i W 1 ((bv i W + bv i c * (v % 2)) % 2)) c = bv i c :=
      bv_write_ne hcne
    have hmul2 : (bv i c * v) % 2 = (bv i c * (v % 2)) % 2 := by
      rcases ht with ht | ht <;> rw [ht] <;> omega
    have hmuld : (bv i c * v) / 2 = bv i c * (v / 2) := by
      rcases ht with ht | ht <;> rw [ht] <;> omega
    have hα : ((readField i W (p + 1)) ^^^ (bv i c * v)) % 2
        = (bv i W + bv i c * (v % 2)) % 2 := by
      rw [xor_bit, hmul2]
      have : readField i W (p + 1) % 2 = bv i W := by omega
      rw [this]
      omega
    have hβ : ((readField i W (p + 1)) ^^^ (bv i c * v)) / 2
        = (readField i (W + 1) p) ^^^ (bv i c * (v / 2)) := by
      rw [xor_div_two, hmuld]
      have : readField i W (p + 1) / 2 = readField i (W + 1) p := by omega
      rw [this]
    rw [loadC, actGates_append, hhead, ih (W + 1) (v / 2) _ (by omega), hbc1,
      readField_writeField_of_disjoint (Or.inl (by omega)),
      writeField_succ i W p ((readField i W (p + 1)) ^^^ (bv i c * v)), hα, hβ]

/-! ### Gadget state

The moving registers are the low `k` bits of the operand field, the flag, and
the constant register.  `stt n i b f v` names the index with those values,
permitting direct composition of the block equations.  Every chain returns the
carry ancilla to zero, so it remains part of `i`. -/

def stt (n i b f v : Nat) : Nat :=
  writeField (writeField (writeField i 0 k b) (fw n) 1 f) (vw n) k v

theorem stt_eq {n i b f v b' f' v' : Nat} (hb : b % 2 ^ k = b' % 2 ^ k)
    (hf : f % 2 = f' % 2) (hv : v % 2 ^ k = v' % 2 ^ k) :
    stt n i b f v = stt n i b' f' v' := by
  have e1 : writeField i 0 k b = writeField i 0 k b' := by
    rw [← writeField_mod i 0 k b, ← writeField_mod i 0 k b', hb]
  have e3 : ∀ X, writeField X (vw n) k v = writeField X (vw n) k v' := by
    intro X
    rw [← writeField_mod X (vw n) k v, ← writeField_mod X (vw n) k v', hv]
  unfold stt
  rw [e1, write_congr hf, e3]

theorem stt_setB {n : Nat} (hk : k ≤ n) (i b f v b' : Nat) :
    writeField (stt n i b f v) 0 k b' = stt n i b' f v := by
  have hfv : fw n = n + 1 := rfl
  have hvv : vw n = n + 2 := rfl
  unfold stt
  rw [writeField_comm (o₁ := vw n) (n₁ := k) (o₂ := 0) (n₂ := k) (by omega),
    writeField_comm (o₁ := fw n) (n₁ := 1) (o₂ := 0) (n₂ := k) (by omega),
    writeField_writeField]

theorem stt_setF {n : Nat} (i b f v f' : Nat) :
    writeField (stt n i b f v) (fw n) 1 f' = stt n i b f' v := by
  have hfv : fw n = n + 1 := rfl
  have hvv : vw n = n + 2 := rfl
  unfold stt
  rw [writeField_comm (o₁ := vw n) (n₁ := k) (o₂ := fw n) (n₂ := 1) (by omega),
    writeField_writeField]

theorem stt_setV {n : Nat} (i b f v v' : Nat) :
    writeField (stt n i b f v) (vw n) k v' = stt n i b f v' := by
  unfold stt
  rw [writeField_writeField]

theorem stt_readB {n : Nat} (hk : k ≤ n) (i b f v : Nat) :
    readField (stt n i b f v) 0 k = b % 2 ^ k := by
  have hfv : fw n = n + 1 := rfl
  have hvv : vw n = n + 2 := rfl
  unfold stt
  rw [readField_writeField_of_disjoint (by omega), readField_writeField_of_disjoint (by omega),
    readField_writeField]

theorem stt_readF {n : Nat} (i b f v : Nat) : bv (stt n i b f v) (fw n) = f % 2 := by
  have hfv : fw n = n + 1 := rfl
  have hvv : vw n = n + 2 := rfl
  unfold stt
  rw [bv_write_out (by omega), bv_write_self]

theorem stt_readV {n : Nat} (i b f v : Nat) :
    readField (stt n i b f v) (vw n) k = v % 2 ^ k := by
  unfold stt
  rw [readField_writeField]

theorem stt_readC {n : Nat} (hk : k ≤ n) (i b f v : Nat) :
    bv (stt n i b f v) (cw n) = bv i (cw n) := by
  have hcv : cw n = n := rfl
  have hfv : fw n = n + 1 := rfl
  have hvv : vw n = n + 2 := rfl
  unfold stt
  rw [bv_write_out (by omega), bv_write_ne (by omega), bv_write_out (by omega)]

theorem stt_id {n b i : Nat} (hb : readField i 0 k = b) (hf : bv i (fw n) = 0)
    (hv : readField i (vw n) k = 0) : stt n i b 0 0 = i := by
  have e1 : writeField i 0 k b = i := by rw [← hb]; exact writeField_read i 0 k
  have e2 : writeField i (fw n) 1 0 = i := write_of_bv (by rw [hf])
  have e3 : writeField i (vw n) k 0 = i := by rw [← hv]; exact writeField_read i (vw n) k
  unfold stt
  rw [e1, e2, e3]

theorem stt_clean {n : Nat} (hk : k ≤ n) {i r : Nat} (hfz : bv i (fw n) = 0)
    (hvz : readField i (vw n) k = 0) :
    stt n i r 0 0 = writeField i 0 k r := by
  have hfv : fw n = n + 1 := rfl
  have hvv : vw n = n + 2 := rfl
  have e1 : bv (writeField i 0 k r) (fw n) = 0 := by rw [bv_write_out (by omega), hfz]
  have e2 : readField (writeField i 0 k r) (vw n) k = 0 := by
    rw [readField_writeField_of_disjoint (by omega), hvz]
  have f2 : writeField (writeField i 0 k r) (fw n) 1 0 = writeField i 0 k r :=
    write_of_bv (by rw [e1])
  have f3 : ∀ X : Nat, readField X (vw n) k = 0 → writeField X (vw n) k 0 = X := by
    intro X hX; rw [← hX]; exact writeField_read X (vw n) k
  unfold stt
  rw [f2, f3 _ e2]

/-! ### Block semantics -/

theorem act_loadA {n : Nat} (hk : k ≤ n) (i b f v c : Nat) :
    actGates (loadX 0 k c) (stt n i b f v) = stt n i ((b % 2 ^ k) ^^^ c) f v := by
  rw [loadX_act, stt_readB hk, stt_setB hk]

theorem act_loadV {n : Nat} (i b f v c : Nat) :
    actGates (loadX (vw n) k c) (stt n i b f v) = stt n i b f ((v % 2 ^ k) ^^^ c) := by
  rw [loadX_act, stt_readV, stt_setV]

theorem act_loadC {n : Nat} (i b f v c : Nat) :
    actGates (loadC (fw n) (vw n) k c) (stt n i b f v)
      = stt n i b f ((v % 2 ^ k) ^^^ (f % 2 * c)) := by
  have hfv : fw n = n + 1 := rfl
  have hvv : vw n = n + 2 := rfl
  rw [loadC_act k (vw n) c (stt n i b f v) (Or.inl (by omega)), stt_readV, stt_readF, stt_setV]

theorem act_flip {n : Nat} (i b f v : Nat) :
    actGates [RGate.x (fw n)] (stt n i b f v) = stt n i b ((f % 2 + 1) % 2) v := by
  show RGate.act (RGate.x (fw n)) (stt n i b f v) = _
  rw [act_x, stt_readF, stt_setF]

/-- The constant register into the operand field, with the carry out on the
flag. -/
theorem act_addV {n : Nat} (hk : k ≤ n) {i b f v : Nat} (hb : b < 2 ^ k) (hf : f < 2)
    (hv : v < 2 ^ k) (hc : bv i (cw n) = 0) :
    actGates (blockAdd (vw n) 0 (cw n) (fw n)) (stt n i b f v)
      = stt n i ((v + b) % 2 ^ k) ((f + (v + b) / 2 ^ k) % 2) v := by
  have hcv : cw n = n := rfl
  have hfv : fw n = n + 1 := rfl
  have hvv : vw n = n + 2 := rfl
  have hmid : ∀ j, actGates [RGate.cx (vw n + kp) (fw n)] j
      = writeField j (fw n) 1
        ((fun x y => (x + y) % 2) (bv j (fw n)) (bv j (cwire (vw n) (cw n) k))) := by
    intro j
    rw [cwire_k]
    show RGate.act (RGate.cx (vw n + kp) (fw n)) j = _
    rw [act_cx]
  have h := achain_act (A := vw n) (B := 0) (c := cw n) (z := fw n) (K := k)
    (φ := fun x y => (x + y) % 2) (mid := [RGate.cx (vw n + kp) (fw n)])
    (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
    (Or.inl (by omega)) (Or.inr (by omega)) (by omega) hmid k 0 (by omega) (stt n i b f v)
  simp only [Nat.add_zero, cwire] at h
  rw [stt_readV, stt_readB hk, stt_readC hk, hc, stt_readF, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hv, Nat.add_zero, stt_setB hk, stt_setF] at h
  show actGates (achain (vw n) 0 (cw n) [RGate.cx (vw n + kp) (fw n)] 0 k) (stt n i b f v) = _
  exact h

/-- The constant register into the operand field with the carry discarded, which
is the conditional add-back of the modulus. -/
theorem act_addV0 {n : Nat} (hk : k ≤ n) {i b f v : Nat} (hb : b < 2 ^ k) (hf : f < 2)
    (hv : v < 2 ^ k) (hc : bv i (cw n) = 0) :
    actGates (achain (vw n) 0 (cw n) [] 0 k) (stt n i b f v)
      = stt n i ((v + b) % 2 ^ k) f v := by
  have hcv : cw n = n := rfl
  have hfv : fw n = n + 1 := rfl
  have hvv : vw n = n + 2 := rfl
  have hmid : ∀ j, actGates ([] : List RGate) j
      = writeField j (fw n) 1
        ((fun x _ => x) (bv j (fw n)) (bv j (cwire (vw n) (cw n) k))) := by
    intro j
    show j = writeField j (fw n) 1 (bv j (fw n))
    exact (write_of_bv (by have := bv_lt j (fw n); omega)).symm
  have h := achain_act (A := vw n) (B := 0) (c := cw n) (z := fw n) (K := k)
    (φ := fun x _ => x) (mid := [])
    (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
    (Or.inl (by omega)) (Or.inr (by omega)) (by omega) hmid k 0 (by omega) (stt n i b f v)
  simp only [Nat.add_zero, cwire] at h
  rw [stt_readV, stt_readB hk, stt_readC hk, hc, stt_readF, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hv, Nat.add_zero, stt_setB hk, stt_setF] at h
  exact h

/-- The comparison of the operand field against the constant register, which is
what clears the flag. -/
theorem act_cmpV {n : Nat} (hk : k ≤ n) {i b f v : Nat} (hb : b < 2 ^ k) (hf : f < 2)
    (hv : v < 2 ^ k) (hc : bv i (cw n) = 0) :
    actGates (blockCmp (vw n) 0 (cw n) (fw n)) (stt n i b f v)
      = stt n i b ((f + (v + b) / 2 ^ k) % 2) v := by
  have hcv : cw n = n := rfl
  have hfv : fw n = n + 1 := rfl
  have hvv : vw n = n + 2 := rfl
  have hmid : ∀ j, actGates [RGate.cx (vw n + kp) (fw n)] j
      = writeField j (fw n) 1
        ((fun x y => (x + y) % 2) (bv j (fw n)) (bv j (cwire (vw n) (cw n) k))) := by
    intro j
    rw [cwire_k]
    show RGate.act (RGate.cx (vw n + kp) (fw n)) j = _
    rw [act_cx]
  have h := cchain_act (A := vw n) (B := 0) (c := cw n) (z := fw n) (K := k)
    (φ := fun x y => (x + y) % 2) (mid := [RGate.cx (vw n + kp) (fw n)])
    (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
    (Or.inl (by omega)) (Or.inr (by omega)) (by omega) hmid k 0 (by omega) (stt n i b f v)
  simp only [Nat.add_zero, cwire] at h
  rw [stt_readV, stt_readB hk, stt_readC hk, hc, stt_readF, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hv, Nat.add_zero, stt_setF] at h
  show actGates (cchain (vw n) 0 (cw n) [RGate.cx (vw n + kp) (fw n)] 0 k) (stt n i b f v) = _
  exact h

/-! ### Arithmetic semantics

Every quotient and remainder by `2 ^ k` in the trace is settled by this one
split, which turns a division by a power the tactics cannot see into a linear
fact. -/

theorem split_two {K x : Nat} (hK : 0 < K) (h : x < 2 * K) :
    (x < K ∧ x / K = 0 ∧ x % K = x) ∨ (K ≤ x ∧ x / K = 1 ∧ x % K = x - K) := by
  rcases Nat.lt_or_ge x K with h1 | h1
  · exact Or.inl ⟨h1, Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1⟩
  · refine Or.inr ⟨h1, ?_, ?_⟩
    · rw [Nat.div_eq_sub_div hK h1, Nat.div_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

/-! ### Gadget block semantics

`b1` and `b2` are the successive values of the operand field, `c1` the carry
that tests for zero, `f2` the flag it becomes, and `c4` the carry of the closing
comparison.  The flag returns to zero because `c4` is `1` exactly where `f2` is,
so the comparison needs no correcting `x`. -/

theorem gadget_act {n : Nat} (hk : k ≤ n) {i a : Nat} (ha : readField i 0 k = a)
    (hcz : bv i (cw n) = 0) (hfz : bv i (fw n) = 0) (hvz : readField i (vw n) k = 0)
    (ham : a < m) :
    actGates (gadget n) i = stt n i ((m - a) % m) 0 0 := by
  have hK : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
  have hmK : m < 2 ^ k := m_lt
  have hm0 : 0 < m := m_pos
  have h1K : (1 : Nat) < 2 ^ k := one_lt
  have haK : a < 2 ^ k := by omega
  have hi : stt n i a 0 0 = i := stt_id ha hfz hvz
  obtain ⟨b1, hb1⟩ : ∃ x, (1 + (2 ^ k - 1 - a)) % 2 ^ k = x := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ x, (1 + (2 ^ k - 1 - a)) / 2 ^ k = x := ⟨_, rfl⟩
  have S1 := split_two hK (show 1 + (2 ^ k - 1 - a) < 2 * 2 ^ k by omega)
  rw [hb1, hc1] at S1
  have hb1K : b1 < 2 ^ k := by rw [← hb1]; exact Nat.mod_lt _ hK
  have hc1lt : c1 < 2 := by rcases S1 with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega
  obtain ⟨f2, hf2⟩ : ∃ x, (c1 + 1) % 2 = x := ⟨_, rfl⟩
  have hf2lt : f2 < 2 := by omega
  have hfm : f2 * m < 2 ^ k := by
    rcases (show f2 = 0 ∨ f2 = 1 by omega) with h | h <;> subst h <;> omega
  obtain ⟨b2, hb2⟩ : ∃ x, (f2 * m + b1) % 2 ^ k = x := ⟨_, rfl⟩
  have hb2K : b2 < 2 ^ k := by rw [← hb2]; exact Nat.mod_lt _ hK
  obtain ⟨c4, hc4⟩ : ∃ x, (2 ^ k - 1 + b2) / 2 ^ k = x := ⟨_, rfl⟩
  have key : b2 = (m - a) % m ∧ (f2 + c4) % 2 = 0 := by
    have S2 := split_two hK (show f2 * m + b1 < 2 * 2 ^ k by omega)
    rw [hb2] at S2
    have S4 := split_two hK (show 2 ^ k - 1 + b2 < 2 * 2 ^ k by omega)
    rw [hc4] at S4
    have SM := split_two hm0 (show m - a < 2 * m by omega)
    rcases (show f2 = 0 ∨ f2 = 1 by omega) with hf | hf <;> subst hf <;>
      rcases S1 with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;>
      rcases S2 with ⟨d1, d2, d3⟩ | ⟨d1, d2, d3⟩ <;>
      rcases S4 with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ <;>
      rcases SM with ⟨j1, j2, j3⟩ | ⟨j1, j2, j3⟩ <;>
      exact ⟨by omega, by omega⟩
  have t1 : actGates (loadX 0 k (2 ^ k - 1)) i = stt n i (2 ^ k - 1 - a) 0 0 := by
    have h := act_loadA (n := n) hk i a 0 0 (2 ^ k - 1)
    rw [hi] at h
    rw [h, Nat.mod_eq_of_lt haK, xor_ones k a haK]
  have t2 : actGates (loadX (vw n) k 1) (stt n i (2 ^ k - 1 - a) 0 0)
      = stt n i (2 ^ k - 1 - a) 0 1 := by
    rw [act_loadV, Nat.zero_mod, Nat.zero_xor]
  have t3 : actGates (blockAdd (vw n) 0 (cw n) (fw n)) (stt n i (2 ^ k - 1 - a) 0 1)
      = stt n i b1 c1 1 := by
    have h := act_addV (n := n) hk (b := 2 ^ k - 1 - a) (f := 0) (v := 1)
      (by omega) (by omega) (by omega) hcz
    rw [hb1, hc1] at h
    rw [h]
    exact stt_eq rfl (by omega) rfl
  have t4 : actGates (loadX (vw n) k 1) (stt n i b1 c1 1) = stt n i b1 c1 0 := by
    rw [act_loadV, Nat.mod_eq_of_lt h1K, Nat.xor_self]
  have t5 : actGates [RGate.x (fw n)] (stt n i b1 c1 0) = stt n i b1 f2 0 := by
    rw [act_flip]
    exact stt_eq rfl (by omega) rfl
  have t6 : actGates (loadC (fw n) (vw n) k m) (stt n i b1 f2 0)
      = stt n i b1 f2 (f2 * m) := by
    rw [act_loadC, Nat.zero_mod, Nat.zero_xor, Nat.mod_eq_of_lt hf2lt]
  have t7 : actGates (achain (vw n) 0 (cw n) [] 0 k) (stt n i b1 f2 (f2 * m))
      = stt n i b2 f2 (f2 * m) := by
    rw [act_addV0 hk hb1K hf2lt hfm hcz, hb2]
  have t8 : actGates (loadC (fw n) (vw n) k m) (stt n i b2 f2 (f2 * m))
      = stt n i b2 f2 0 := by
    rw [act_loadC, Nat.mod_eq_of_lt hfm, Nat.mod_eq_of_lt hf2lt, Nat.xor_self]
  have t9 : actGates (loadX (vw n) k (2 ^ k - 1)) (stt n i b2 f2 0)
      = stt n i b2 f2 (2 ^ k - 1) := by
    rw [act_loadV, Nat.zero_mod, Nat.zero_xor]
  have t10 : actGates (blockCmp (vw n) 0 (cw n) (fw n)) (stt n i b2 f2 (2 ^ k - 1))
      = stt n i b2 ((f2 + c4) % 2) (2 ^ k - 1) := by
    rw [act_cmpV hk hb2K hf2lt (by omega) hcz, hc4]
  have t11 : actGates (loadX (vw n) k (2 ^ k - 1))
      (stt n i b2 ((f2 + c4) % 2) (2 ^ k - 1)) = stt n i ((m - a) % m) 0 0 := by
    have hkey := key.2
    rw [act_loadV, Nat.mod_eq_of_lt (show (2 : Nat) ^ k - 1 < 2 ^ k by omega), Nat.xor_self,
      key.1]
    exact stt_eq rfl (by omega) rfl
  simp only [gadget, actGates_append]
  rw [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]

/-! ### Correctness claim -/

theorem negs_general : ∀ n : Nat, VQ.Reversible.NegatesMod VQ.Curve.PointAddition.Arithmetic.Neg.m VQ.Curve.PointAddition.Arithmetic.Neg.ws n (VQ.Curve.PointAddition.Arithmetic.Neg.gen n) := by
  intro n a i _ h0 h1 hm ha
  have hk : k ≤ n := k_le hm
  have hmK : m < 2 ^ k := m_lt
  have hm0 : 0 < m := m_pos
  have hwsv : ws = k + 2 := rfl
  have e0 : readField i 0 n = a := h0
  have e1 : readField i (n + 0) ws = 0 := h1
  rw [Nat.add_zero] at e1
  have ea : readField i 0 k = a := by
    rw [readField_low i 0 k n hk, e0, Nat.mod_eq_of_lt (by omega)]
  have ec : bv i (cw n) = 0 := by
    rw [← readField_one]
    have h := readField_sub_zero e1 (d := 0) (e := 1) (by omega)
    rw [show cw n = n + 0 from by show n = _; omega]
    exact h
  have ef : bv i (fw n) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero e1 (d := 1) (e := 1) (by omega)
  have ev : readField i (vw n) k = 0 :=
    readField_sub_zero e1 (d := 2) (e := k) (by omega)
  have hact : act (VQ.Curve.PointAddition.Arithmetic.Neg.gen n) i = actGates (gadget n) i := by
    show actGates (if k ≤ n then gadget n else []) i = _
    rw [if_pos hk]
  show act (VQ.Curve.PointAddition.Arithmetic.Neg.gen n) i = writeField i 0 n ((m - a) % m)
  rw [hact, gadget_act hk ea ec ef ev ha, stt_clean hk ef ev]
  exact write_widen hk (by have := Nat.mod_lt (m - a) hm0; omega) (by rw [e0]; omega)

/-- Modular negation with the modulus and workspace specialized to their fixed values. -/
theorem negs : ∀ n : Nat,
    VQ.Reversible.NegatesMod
      115792089237316195423570985008687907853269984665640564039457584007908834671663
      258 n (VQ.Curve.PointAddition.Arithmetic.Neg.gen n) := negs_general

end Neg
end VQ.Curve.PointAddition.Arithmetic
