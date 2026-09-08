import VQ

open VQ VQ.Reversible

namespace VQ.Curve.PointAddition.Arithmetic
namespace Subt

/-! ## Circuit construction

Subtraction of `a` from `b` modulo `m` is addition of `m - a`, and `m - a` is
computable from `a` by a constant adder: complement `a` in `k` bits and add
`m + 1` modulo `2 ^ k`, which is `2 ^ k + (m - a)` and so `m - a`.  The circuit
computes that into a workspace register, runs the modular adder of
`examples/06-modadd-p` with the register as its augend field, and runs the
negation backwards to clear the register.  The adder does not read the first
operand field after the negation copies it.  The comparison that uncomputes the
reduction flag compares against the register.

Choosing this over an in-place modular negation of the target is what avoids an
exceptional input.  Negation modulo `m` maps zero to zero and every other
residue to `m - a`, so a circuit for it needs the `k`-input test for zero, at
`k - 2` Toffolis and an ancilla, or an exceptional branch the specification does
not allow.  The register form has no such branch: `m - a` runs over `[1, m]`
rather than over the residues, and the adder is correct on an augend of `m`,
since `m + b` reduces to `b` and the flag is uncomputed by a comparison that
still discriminates.  The one adaptation from `examples/06-modadd-p` is that its
augend hypothesis weakens from below the modulus to at most the modulus.

The modulus is fixed and the width `n` is the family
parameter.  Both operands the specification covers are below the modulus, so
only the low `k` bits of each carry information, where `k` is the bit length of
the modulus.  The circuit is therefore a gadget of fixed size placed at
width-dependent offsets, and every resource count is a constant.

`kp` is `k - 1`, written so that `k` is syntactically a successor: the carry
wire at the top of a chain of `k` positions is then `A + kp` by definition. -/

/-- One less than the bit length of the modulus. -/
def kp : Nat := 255

/-- The bit length of the modulus: the number of positions every chain runs
over. -/
def k : Nat := kp + 1

/-- The modulus. -/
def m : Nat := VQ.Curve.p

/-- The workspace: a carry ancilla, a flag, a `k`-bit constant register, and a
`k`-bit register for the negated first operand. -/
def ws : Nat := 2 * k + 2

/-- The carry-in ancilla of every chain. -/
def cw (n : Nat) : Nat := 2 * n

/-- The flag wire records whether the reduction was applied. -/
def fw (n : Nat) : Nat := 2 * n + 1

/-- The base of the `k`-bit register the classical constants are loaded into. -/
def vw (n : Nat) : Nat := 2 * n + 2

/-- The base of the `k`-bit register holding `m - a`, which is the field the
adder adds from. -/
def aw (n : Nat) : Nat := 2 * n + 2 + k

theorem m_pos : 0 < m := by decide

theorem m_lt : m < 2 ^ k := by decide

/-- The negation constant fits the register it is loaded into. -/
theorem m_succ_lt : m + 1 < 2 ^ k := by decide

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

/-- Exclusive-or of the `p`-bit field at `S` into the `p`-bit field at `T`, one
CNOT per position.  The two fields have to be disjoint. -/
def copyR : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | S, T, p + 1 => [RGate.cx S T] ++ copyR (S + 1) (T + 1) p

/-- Add the augend into the addend and record the carry out on the flag. -/
def blockAdd (A B c z : Nat) : List RGate :=
  achain A B c [RGate.cx (A + kp) z] 0 k

/-- The negation constant, loaded into and unloaded from the constant register
by the same gates. -/
def loadV (n : Nat) : List RGate := loadX (vw n) k (m + 1)

/-- Write `m - a` into the negation register: copy the first operand in,
complement it, and add `m + 1` modulo `2 ^ k`. -/
def negA (n : Nat) : List RGate :=
  copyR 0 (aw n) k
    ++ loadX (aw n) k (2 ^ k - 1)
    ++ loadV n
    ++ achain (vw n) (aw n) (cw n) [] 0 k
    ++ loadV n

/-- Clear the negation register, by the same three steps in the other order:
complement `m - a`, add `m + 1` modulo `2 ^ k` to reach `a`, and cancel the
copy. -/
def unnegA (n : Nat) : List RGate :=
  loadX (aw n) k (2 ^ k - 1)
    ++ loadV n
    ++ achain (vw n) (aw n) (cw n) [] 0 k
    ++ loadV n
    ++ copyR 0 (aw n) k

/-- The modular adder, with the negation register as its augend field.

Read left to right: add the register into `b` and record the carry.  Add
`2 ^ k - m` and record its carry, which leaves the flag holding
`a' + b ≥ m`.  Flip the flag.  Load the modulus under the flag, add it back, and
unload it.  Then compare the result against the register and clear the flag.  The
comparison requires the register and `b` to be at most the modulus.  The
`SubsMod` value clause supplies both bounds. -/
def madd (n : Nat) : List RGate :=
  blockAdd (aw n) n (cw n) (fw n)
    ++ loadX (vw n) k (2 ^ k - m)
    ++ blockAdd (vw n) n (cw n) (fw n)
    ++ loadX (vw n) k (2 ^ k - m)
    ++ [RGate.x (fw n)]
    ++ loadC (fw n) (vw n) k m
    ++ achain (vw n) n (cw n) [] 0 k
    ++ loadC (fw n) (vw n) k m
    ++ loadX n k (2 ^ k - 1)
    ++ cchain (aw n) n (cw n) [RGate.cx (aw n + kp) (fw n)] 0 k
    ++ loadX n k (2 ^ k - 1)
    ++ [RGate.x (fw n)]

/-- The whole gadget, at a width that can hold the modulus. -/
def gadget (n : Nat) : List RGate := negA n ++ madd n ++ unnegA n

/-- The generator.  Below the bit length of the modulus the register cannot hold
it, the clause of `SubsMod` is vacuous, and the circuit is the identity. -/
def gen (n : Nat) : RCircuit :=
  { width := 2 * n + ws, gates := if k ≤ n then gadget n else [] }

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

theorem copyR_wf {w : Nat} : ∀ (p S T : Nat), S + p ≤ w → T + p ≤ w → (T + p ≤ S ∨ S + p ≤ T) →
    (copyR S T p).all (RGate.wellFormed w) = true := by
  intro p
  induction p with
  | zero => intro S T _ _ _; rfl
  | succ p ih =>
    intro S T hS hT hd
    simp only [copyR, List.all_append, Bool.and_eq_true]
    exact ⟨cx_wf (by omega) (by omega) (by omega),
      ih (S + 1) (T + 1) (by omega) (by omega) (by omega)⟩

theorem negA_wf {n : Nat} (hk : k ≤ n) :
    (negA n).all (RGate.wellFormed (2 * n + ws)) = true := by
  have hws : ws = 2 * k + 2 := rfl
  have hcv : cw n = 2 * n := rfl
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  have hcp : (copyR 0 (aw n) k).all (RGate.wellFormed (2 * n + ws)) = true :=
    copyR_wf k 0 (aw n) (by omega) (by omega) (Or.inr (by omega))
  have hla : ∀ v, (loadX (aw n) k v).all (RGate.wellFormed (2 * n + ws)) = true :=
    fun v => loadX_wf k (aw n) v (by omega)
  have hlv : ∀ v, (loadX (vw n) k v).all (RGate.wellFormed (2 * n + ws)) = true :=
    fun v => loadX_wf k (vw n) v (by omega)
  have hch : (achain (vw n) (aw n) (cw n) [] 0 k).all
      (RGate.wellFormed (2 * n + ws)) = true :=
    achain_wf (A := vw n) (B := aw n) (c := cw n) (K := k)
      (by omega) (by omega) (by omega) k_pos
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) rfl k 0 (by omega)
  simp only [negA, loadV, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨hcp, hla _⟩, hlv _⟩, hch⟩, hlv _⟩

theorem unnegA_wf {n : Nat} (hk : k ≤ n) :
    (unnegA n).all (RGate.wellFormed (2 * n + ws)) = true := by
  have hws : ws = 2 * k + 2 := rfl
  have hcv : cw n = 2 * n := rfl
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  have hcp : (copyR 0 (aw n) k).all (RGate.wellFormed (2 * n + ws)) = true :=
    copyR_wf k 0 (aw n) (by omega) (by omega) (Or.inr (by omega))
  have hla : ∀ v, (loadX (aw n) k v).all (RGate.wellFormed (2 * n + ws)) = true :=
    fun v => loadX_wf k (aw n) v (by omega)
  have hlv : ∀ v, (loadX (vw n) k v).all (RGate.wellFormed (2 * n + ws)) = true :=
    fun v => loadX_wf k (vw n) v (by omega)
  have hch : (achain (vw n) (aw n) (cw n) [] 0 k).all
      (RGate.wellFormed (2 * n + ws)) = true :=
    achain_wf (A := vw n) (B := aw n) (c := cw n) (K := k)
      (by omega) (by omega) (by omega) k_pos
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) rfl k 0 (by omega)
  simp only [unnegA, loadV, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨hla _, hlv _⟩, hch⟩, hlv _⟩, hcp⟩

theorem madd_wf {n : Nat} (hk : k ≤ n) :
    (madd n).all (RGate.wellFormed (2 * n + ws)) = true := by
  have hws : ws = 2 * k + 2 := rfl
  have hkp : k = kp + 1 := rfl
  have hcv : cw n = 2 * n := rfl
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  have hone : ∀ z, z < 2 * n + ws → ([RGate.x z]).all (RGate.wellFormed (2 * n + ws)) = true :=
    fun z hz => x_wf hz
  have hmida : ([RGate.cx (aw n + kp) (fw n)]).all (RGate.wellFormed (2 * n + ws)) = true :=
    cx_wf (by omega) (by omega) (by omega)
  have hmidv : ([RGate.cx (vw n + kp) (fw n)]).all (RGate.wellFormed (2 * n + ws)) = true :=
    cx_wf (by omega) (by omega) (by omega)
  have hc1 : (achain (aw n) n (cw n) [RGate.cx (aw n + kp) (fw n)] 0 k).all
      (RGate.wellFormed (2 * n + ws)) = true :=
    achain_wf (A := aw n) (B := n) (c := cw n) (K := k)
      (by omega) (by omega) (by omega) k_pos
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      hmida k 0 (by omega)
  have hc2 : (achain (vw n) n (cw n) [RGate.cx (vw n + kp) (fw n)] 0 k).all
      (RGate.wellFormed (2 * n + ws)) = true :=
    achain_wf (A := vw n) (B := n) (c := cw n) (K := k)
      (by omega) (by omega) (by omega) k_pos
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) hmidv k 0 (by omega)
  have hc3 : (achain (vw n) n (cw n) [] 0 k).all
      (RGate.wellFormed (2 * n + ws)) = true :=
    achain_wf (A := vw n) (B := n) (c := cw n) (K := k)
      (by omega) (by omega) (by omega) k_pos
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) rfl k 0 (by omega)
  have hc4 : (cchain (aw n) n (cw n) [RGate.cx (aw n + kp) (fw n)] 0 k).all
      (RGate.wellFormed (2 * n + ws)) = true :=
    cchain_wf (A := aw n) (B := n) (c := cw n) (K := k)
      (by omega) (by omega) (by omega) k_pos
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      hmida k 0 (by omega)
  have hlv : ∀ v, (loadX (vw n) k v).all (RGate.wellFormed (2 * n + ws)) = true :=
    fun v => loadX_wf k (vw n) v (by omega)
  have hln : ∀ v, (loadX n k v).all (RGate.wellFormed (2 * n + ws)) = true :=
    fun v => loadX_wf k n v (by omega)
  have hlc : ∀ v, (loadC (fw n) (vw n) k v).all (RGate.wellFormed (2 * n + ws)) = true :=
    fun v => loadC_wf (by omega) k (vw n) v (by omega) (Or.inl (by omega))
  simp only [madd, blockAdd, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc1, hlv _⟩, hc2⟩, hlv _⟩, hone _ (by omega)⟩, hlc _⟩, hc3⟩,
    hlc _⟩, hln _⟩, hc4⟩, hln _⟩, hone _ (by omega)⟩

theorem gadget_wf {n : Nat} (hk : k ≤ n) :
    (gadget n).all (RGate.wellFormed (2 * n + ws)) = true := by
  simp only [gadget, List.all_append, Bool.and_eq_true]
  exact ⟨⟨negA_wf hk, madd_wf hk⟩, unnegA_wf hk⟩

/-! ## Resource bounds

Every count is a constant.  The gate list does not grow with the width: it is
one gadget of `k` positions placed at width-dependent offsets, and it is empty
below the width that can hold the modulus. -/

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

theorem copyR_length : ∀ (p S T : Nat), (copyR S T p).length = p := by
  intro p
  induction p with
  | zero => intro S T; rfl
  | succ p ih =>
    intro S T
    simp only [copyR, List.length_append, ih (S + 1) (T + 1), List.length_cons,
      List.length_nil]
    omega

theorem copyR_ccx : ∀ (p S T : Nat), (copyR S T p).countP RGate.isCcx = 0 := by
  intro p
  induction p with
  | zero => intro S T; rfl
  | succ p ih =>
    intro S T
    have h1 : ([RGate.cx S T]).countP RGate.isCcx = 0 := rfl
    simp only [copyR, List.countP_append, ih (S + 1) (T + 1), h1]

theorem copyR_cx : ∀ (p S T : Nat), (copyR S T p).countP RGate.isCx = p := by
  intro p
  induction p with
  | zero => intro S T; rfl
  | succ p ih =>
    intro S T
    have h1 : ([RGate.cx S T]).countP RGate.isCx = 1 := rfl
    simp only [copyR, List.countP_append, ih (S + 1) (T + 1), h1]
    omega

theorem negA_ccx (n : Nat) : (negA n).countP RGate.isCcx = 2 * k := by
  have e4 : ([] : List RGate).countP RGate.isCcx = 0 := rfl
  simp only [negA, loadV, List.countP_append, achain_ccx, loadX_ccx, copyR_ccx, e4]
  omega

theorem unnegA_ccx (n : Nat) : (unnegA n).countP RGate.isCcx = 2 * k := by
  have e4 : ([] : List RGate).countP RGate.isCcx = 0 := rfl
  simp only [unnegA, loadV, List.countP_append, achain_ccx, loadX_ccx, copyR_ccx, e4]
  omega

theorem negA_cx (n : Nat) : (negA n).countP RGate.isCx = 5 * k := by
  have e4 : ([] : List RGate).countP RGate.isCx = 0 := rfl
  simp only [negA, loadV, List.countP_append, achain_cx, loadX_cx, copyR_cx, e4]
  omega

theorem unnegA_cx (n : Nat) : (unnegA n).countP RGate.isCx = 5 * k := by
  have e4 : ([] : List RGate).countP RGate.isCx = 0 := rfl
  simp only [unnegA, loadV, List.countP_append, achain_cx, loadX_cx, copyR_cx, e4]
  omega

theorem negA_len (n : Nat) : (negA n).length ≤ 10 * k := by
  have l1 := loadX_length k (aw n) (2 ^ k - 1)
  have l2 := loadX_length k (vw n) (m + 1)
  simp only [negA, loadV, List.length_append, achain_length, copyR_length, List.length_nil]
  omega

theorem unnegA_len (n : Nat) : (unnegA n).length ≤ 10 * k := by
  have l1 := loadX_length k (aw n) (2 ^ k - 1)
  have l2 := loadX_length k (vw n) (m + 1)
  simp only [unnegA, loadV, List.length_append, achain_length, copyR_length, List.length_nil]
  omega

theorem madd_ccx (n : Nat) : (madd n).countP RGate.isCcx = 8 * k := by
  simp only [madd, blockAdd, List.countP_append, achain_ccx, cchain_ccx, loadX_ccx,
    loadC_ccx]
  have e1 : ([RGate.cx (aw n + kp) (fw n)]).countP RGate.isCcx = 0 := rfl
  have e2 : ([RGate.cx (vw n + kp) (fw n)]).countP RGate.isCcx = 0 := rfl
  have e3 : ([RGate.x (fw n)]).countP RGate.isCcx = 0 := rfl
  have e4 : ([] : List RGate).countP RGate.isCcx = 0 := rfl
  rw [e1, e2, e3, e4]
  omega

theorem madd_cx (n : Nat) : (madd n).countP RGate.isCx ≤ 18 * k + 3 := by
  have l1 := loadC_cx k (fw n) (vw n) m
  simp only [madd, blockAdd, List.countP_append, achain_cx, cchain_cx, loadX_cx]
  have e1 : ([RGate.cx (aw n + kp) (fw n)]).countP RGate.isCx = 1 := rfl
  have e2 : ([RGate.cx (vw n + kp) (fw n)]).countP RGate.isCx = 1 := rfl
  have e3 : ([RGate.x (fw n)]).countP RGate.isCx = 0 := rfl
  have e4 : ([] : List RGate).countP RGate.isCx = 0 := rfl
  rw [e1, e2, e3, e4]
  omega

theorem madd_len (n : Nat) : (madd n).length ≤ 30 * k + 5 := by
  have l1 := loadX_length k (vw n) (2 ^ k - m)
  have l2 := loadC_length k (fw n) (vw n) m
  have l3 := loadX_length k n (2 ^ k - 1)
  simp only [madd, blockAdd, List.length_append, achain_length, cchain_length,
    List.length_cons, List.length_nil]
  omega

theorem gadget_ccx (n : Nat) : (gadget n).countP RGate.isCcx = 12 * k := by
  simp only [gadget, List.countP_append, negA_ccx, unnegA_ccx, madd_ccx]
  omega

theorem gadget_cx (n : Nat) : (gadget n).countP RGate.isCx ≤ 28 * k + 3 := by
  have l1 := madd_cx n
  simp only [gadget, List.countP_append, negA_cx, unnegA_cx]
  omega

theorem gadget_len (n : Nat) : (gadget n).length ≤ 50 * k + 5 := by
  have l1 := negA_len n
  have l2 := unnegA_len n
  have l3 := madd_len n
  simp only [gadget, List.length_append]
  omega

theorem toffoli_le : ∀ n : Nat,
    VQ.Circuit.toffoliCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Subt.gen n)) ≤ 3072 := by
  intro n
  rw [VQ.Reversible.toffoliCount_compile]
  show (if k ≤ n then gadget n else []).countP RGate.isCcx ≤ 3072
  by_cases hk : k ≤ n
  · rw [if_pos hk, gadget_ccx]; decide
  · rw [if_neg hk]; decide

theorem cnot_le : ∀ n : Nat,
    VQ.Circuit.cnotCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Subt.gen n)) ≤ 7171 := by
  intro n
  rw [VQ.Reversible.cnotCount_compile]
  show (if k ≤ n then gadget n else []).countP RGate.isCx ≤ 7171
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    have := gadget_cx n
    have hkv : k = 256 := rfl
    omega
  · rw [if_neg hk]; decide

theorem gates_le : ∀ n : Nat,
    VQ.Circuit.gateCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Subt.gen n)) ≤ 18949 := by
  intro n
  rw [VQ.Reversible.gateCount_compile]
  show (if k ≤ n then gadget n else []).length
    + 2 * (if k ≤ n then gadget n else []).countP RGate.isCcx ≤ 18949
  by_cases hk : k ≤ n
  · rw [if_pos hk, gadget_ccx]
    have := gadget_len n
    have hkv : k = 256 := rfl
    omega
  · rw [if_neg hk]; decide

/-! ### Wire bounds

`usedWires` counts the distinct wires a gate list names, which is the length of
a deduplicated list rather than a count over the gates, so the bound goes
through a pigeonhole: a deduplicated list whose entries all lie in a list of
`3 * k + 2` wires has at most that many entries. -/

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

/-- The wires the gadget names: the low `k` of each operand field and the whole
workspace. -/
def uw (n : Nat) : List Nat :=
  List.range k ++ (List.range k).map (fun j => n + j)
    ++ (List.range (2 * k + 2)).map (fun j => 2 * n + j)

theorem uw_length (n : Nat) : (uw n).length = 4 * k + 2 := by
  simp only [uw, List.length_append, List.length_map, List.length_range]
  omega

theorem mem_uw_a {n j : Nat} (h : j < k) : j ∈ uw n := by
  simp only [uw, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl h)

theorem mem_uw_b {n j : Nat} (h : j < k) : n + j ∈ uw n := by
  simp only [uw, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨j, h, rfl⟩)

theorem mem_uw_w {n j : Nat} (h : j < 2 * k + 2) : 2 * n + j ∈ uw n := by
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

theorem copyR_mem {P : Nat → Prop} : ∀ (p S T : Nat), (∀ j, j < p → P (S + j)) →
    (∀ j, j < p → P (T + j)) → ∀ g ∈ copyR S T p, ∀ q ∈ g.wires, P q := by
  intro p
  induction p with
  | zero => intro S T _ _ g hg; simp [copyR] at hg
  | succ p ih =>
    intro S T hS hT g hg q hq
    simp only [copyR, List.mem_append] at hg
    rcases hg with hg | hg
    · have h0 : P S := by have := hS 0 (by omega); simpa using this
      have h1 : P T := by have := hT 0 (by omega); simpa using this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact h0
      · exact h1
    · refine ih (S + 1) (T + 1) (fun j hj => ?_) (fun j hj => ?_) g hg q hq
      · have := hS (j + 1) (by omega)
        have he : S + 1 + j = S + (j + 1) := by omega
        rw [he]; exact this
      · have := hT (j + 1) (by omega)
        have he : T + 1 + j = T + (j + 1) := by omega
        rw [he]; exact this

/-- The six wire families the three parts name, collected once. -/
theorem uw_parts (n : Nat) :
    (∀ j, j < k → (0 + j) ∈ uw n) ∧ (∀ j, j < k → (n + j) ∈ uw n) ∧
      (∀ j, j < k → (vw n + j) ∈ uw n) ∧ (∀ j, j < k → (aw n + j) ∈ uw n) ∧
      cw n ∈ uw n ∧ fw n ∈ uw n := by
  refine ⟨?_, fun j hj => mem_uw_b hj, ?_, ?_, ?_, ?_⟩
  · intro j hj; simpa using mem_uw_a (n := n) hj
  · intro j hj
    have he : vw n + j = 2 * n + (j + 2) := by show 2 * n + 2 + j = _; omega
    rw [he]
    exact mem_uw_w (by omega)
  · intro j hj
    have he : aw n + j = 2 * n + (j + 2 + k) := by show 2 * n + 2 + k + j = _; omega
    rw [he]
    exact mem_uw_w (by omega)
  · have he : cw n = 2 * n + 0 := by show 2 * n = _; omega
    rw [he]; exact mem_uw_w (by omega)
  · have he : fw n = 2 * n + 1 := rfl
    rw [he]; exact mem_uw_w (by omega)

theorem negA_mem (n : Nat) : ∀ g ∈ negA n, ∀ q ∈ g.wires, q ∈ uw n := by
  obtain ⟨hA, hB, hV, hW, hcm, hfm⟩ := uw_parts n
  have h1 := achain_mem (K := k) (mid := []) hV hW hcm (by intro g hg; cases hg) k 0 (by omega)
  have h2 : ∀ v, ∀ g ∈ loadX (vw n) k v, ∀ q ∈ g.wires, q ∈ uw n :=
    fun v => loadX_mem k (vw n) v hV
  have h3 : ∀ v, ∀ g ∈ loadX (aw n) k v, ∀ q ∈ g.wires, q ∈ uw n :=
    fun v => loadX_mem k (aw n) v hW
  have h4 : ∀ g ∈ copyR 0 (aw n) k, ∀ q ∈ g.wires, q ∈ uw n := copyR_mem k 0 (aw n) hA hW
  intro g hg
  simp only [negA, loadV, List.mem_append] at hg
  rcases hg with (((hg | hg) | hg) | hg) | hg
  · exact h4 g hg
  · exact h3 _ g hg
  · exact h2 _ g hg
  · exact h1 g hg
  · exact h2 _ g hg

theorem unnegA_mem (n : Nat) : ∀ g ∈ unnegA n, ∀ q ∈ g.wires, q ∈ uw n := by
  obtain ⟨hA, hB, hV, hW, hcm, hfm⟩ := uw_parts n
  have h1 := achain_mem (K := k) (mid := []) hV hW hcm (by intro g hg; cases hg) k 0 (by omega)
  have h2 : ∀ v, ∀ g ∈ loadX (vw n) k v, ∀ q ∈ g.wires, q ∈ uw n :=
    fun v => loadX_mem k (vw n) v hV
  have h3 : ∀ v, ∀ g ∈ loadX (aw n) k v, ∀ q ∈ g.wires, q ∈ uw n :=
    fun v => loadX_mem k (aw n) v hW
  have h4 : ∀ g ∈ copyR 0 (aw n) k, ∀ q ∈ g.wires, q ∈ uw n := copyR_mem k 0 (aw n) hA hW
  intro g hg
  simp only [unnegA, loadV, List.mem_append] at hg
  rcases hg with (((hg | hg) | hg) | hg) | hg
  · exact h3 _ g hg
  · exact h2 _ g hg
  · exact h1 g hg
  · exact h2 _ g hg
  · exact h4 g hg

theorem madd_mem (n : Nat) : ∀ g ∈ madd n, ∀ q ∈ g.wires, q ∈ uw n := by
  obtain ⟨hA, hB, hV, hW, hcm, hfm⟩ := uw_parts n
  have hmida : ∀ g ∈ [RGate.cx (aw n + kp) (fw n)], ∀ q ∈ g.wires, q ∈ uw n := by
    intro g hg q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hW kp (by show kp < kp + 1; omega)
    · exact hfm
  have hmidv : ∀ g ∈ [RGate.cx (vw n + kp) (fw n)], ∀ q ∈ g.wires, q ∈ uw n := by
    intro g hg q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hV kp (by show kp < kp + 1; omega)
    · exact hfm
  have hx : ∀ g ∈ [RGate.x (fw n)], ∀ q ∈ g.wires, q ∈ uw n := by
    intro g hg q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact hfm
  have h1 := achain_mem (K := k) hW hB hcm hmida k 0 (by omega)
  have h2 := achain_mem (K := k) hV hB hcm hmidv k 0 (by omega)
  have h3 := achain_mem (K := k) (mid := []) hV hB hcm (by intro g hg; cases hg) k 0 (by omega)
  have h4 := cchain_mem (K := k) hW hB hcm hmida k 0 (by omega)
  have h5 : ∀ v, ∀ g ∈ loadX (vw n) k v, ∀ q ∈ g.wires, q ∈ uw n :=
    fun v => loadX_mem k (vw n) v hV
  have h6 : ∀ v, ∀ g ∈ loadX n k v, ∀ q ∈ g.wires, q ∈ uw n :=
    fun v => loadX_mem k n v hB
  have h7 : ∀ v, ∀ g ∈ loadC (fw n) (vw n) k v, ∀ q ∈ g.wires, q ∈ uw n :=
    fun v => loadC_mem hfm k (vw n) v hV
  intro g hg
  simp only [madd, blockAdd, List.mem_append] at hg
  rcases hg with ((((((((((hg | hg) | hg) | hg) | hg) | hg) | hg) | hg) | hg) | hg) | hg) | hg
  · exact h1 g hg
  · exact h5 _ g hg
  · exact h2 g hg
  · exact h5 _ g hg
  · exact hx g hg
  · exact h7 _ g hg
  · exact h3 g hg
  · exact h7 _ g hg
  · exact h6 _ g hg
  · exact h4 g hg
  · exact h6 _ g hg
  · exact hx g hg

theorem gadget_mem (n : Nat) :
    ∀ g ∈ gadget n, ∀ q ∈ g.wires, q ∈ uw n := by
  intro g hg
  simp only [gadget, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact negA_mem n g hg
  · exact madd_mem n g hg
  · exact unnegA_mem n g hg

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
    VQ.Circuit.usedWires (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Subt.gen n)) ≤ 1026 := by
  intro n
  by_cases hk : k ≤ n
  · have hsub : ∀ q ∈ (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Subt.gen n)).gates.flatMap Gate.wires,
        q ∈ uw n := by
      intro q hq
      obtain ⟨pg, hp, hqp⟩ := List.exists_of_mem_flatMap hq
      have hp' : pg ∈ (VQ.Curve.PointAddition.Arithmetic.Subt.gen n).gates.flatMap VQ.Reversible.compileGate := hp
      obtain ⟨g, hg, hpg⟩ := List.exists_of_mem_flatMap hp'
      have hg' : g ∈ gadget n := by
        have : (VQ.Curve.PointAddition.Arithmetic.Subt.gen n).gates = if k ≤ n then gadget n else [] := rfl
        rw [this, if_pos hk] at hg
        exact hg
      exact gadget_mem n g hg' q (compileGate_wires hpg hqp)
    have h := dedup_le (4 * k + 2) (uw n)
      ((VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Subt.gen n)).gates.flatMap Gate.wires)
      (Nat.le_of_eq (uw_length n)) hsub
    rw [uw_length] at h
    show ((VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Subt.gen n)).gates.flatMap Gate.wires).eraseDups.length ≤ 1026
    have hkv : k = 256 := rfl
    omega
  · show ((VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Subt.gen n)).gates.flatMap Gate.wires).eraseDups.length ≤ 1026
    have he : (VQ.Curve.PointAddition.Arithmetic.Subt.gen n).gates = [] := by
      have : (VQ.Curve.PointAddition.Arithmetic.Subt.gen n).gates = if k ≤ n then gadget n else [] := rfl
      rw [this, if_neg hk]
    have : (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Subt.gen n)).gates = [] := by
      show (VQ.Curve.PointAddition.Arithmetic.Subt.gen n).gates.flatMap VQ.Reversible.compileGate = []
      rw [he]; rfl
    rw [this]
    simp

theorem wf : ∀ n : Nat, VQ.Reversible.RCircuit.wellFormed (VQ.Curve.PointAddition.Arithmetic.Subt.gen n) = true := by
  intro n
  show (if k ≤ n then gadget n else []).all (RGate.wellFormed (2 * n + ws)) = true
  by_cases hk : k ≤ n
  · rw [if_pos hk]; exact gadget_wf hk
  · rw [if_neg hk]; rfl

/-! ## Correctness

The proof evaluates one basis index at a time.  `bv i q` gives the value on wire
`q`, and `readField i off len` gives the value of a contiguous wire range.  Each
gate action is a single-wire write on `Nat`, reducing correctness to arithmetic
on basis indices.  The lemmas through `VQ.Curve.PointAddition.Arithmetic.Subt.loadC_act` establish the required
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

/-- A clear workspace field makes each workspace register clear. -/
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
equals a narrow-field write.  A gadget that acts on only the low `k` bits of the target
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
addend field.  Disjoint operand fields suffice, so the lemma applies to the
operand adder and the constant adder. -/
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

/-! ### Field-copy semantics

The negation register is loaded from the first operand field by one CNOT per
position, which is exclusive-or of the source into the target.  The two fields
have to be disjoint, or a CNOT would read a bit an earlier one wrote. -/

theorem copyR_act : ∀ (p S T i : Nat), T + p ≤ S ∨ S + p ≤ T →
    actGates (copyR S T p) i = writeField i T p ((readField i T p) ^^^ (readField i S p)) := by
  intro p
  induction p with
  | zero => intro S T i _; rw [writeField_zero]; rfl
  | succ p ih =>
    intro S T i hd
    have hbT := bv_lt i T
    have hbS := bv_lt i S
    have hrT := readField_succ i T p
    have hrS := readField_succ i S p
    have hhead : actGates [RGate.cx S T] i = writeField i T 1 ((bv i T + bv i S) % 2) := by
      show RGate.act (RGate.cx S T) i = _
      rw [act_cx]
    have hα : ((readField i T (p + 1)) ^^^ (readField i S (p + 1))) % 2
        = (bv i T + bv i S) % 2 := by
      rw [xor_bit]
      have h1 : readField i T (p + 1) % 2 = bv i T := by omega
      have h2 : readField i S (p + 1) % 2 = bv i S := by omega
      rw [h1, h2]
    have hβ : ((readField i T (p + 1)) ^^^ (readField i S (p + 1))) / 2
        = (readField i (T + 1) p) ^^^ (readField i (S + 1) p) := by
      rw [xor_div_two]
      have h1 : readField i T (p + 1) / 2 = readField i (T + 1) p := by omega
      have h2 : readField i S (p + 1) / 2 = readField i (S + 1) p := by omega
      rw [h1, h2]
    rw [copyR, actGates_append, hhead, ih (S + 1) (T + 1) _ (by omega),
      readField_writeField_of_disjoint (Or.inl (by omega)),
      readField_writeField_of_disjoint (by omega),
      writeField_succ i T p ((readField i T (p + 1)) ^^^ (readField i S (p + 1))), hα, hβ]

/-! ### Gadget state

The moving registers are the low `k` bits of the target, the flag, the
constant register, and the negation register.  `stt n i b f v w` names the
index with those values, permitting direct composition of the block equations.
The copy reads the first operand without changing it, so that field remains
part of `i`. -/

def stt (n i b f v w : Nat) : Nat :=
  writeField (writeField (writeField (writeField i n k b) (fw n) 1 f) (vw n) k v) (aw n) k w

theorem stt_eq {n i b f v w b' f' v' w' : Nat} (hb : b % 2 ^ k = b' % 2 ^ k)
    (hf : f % 2 = f' % 2) (hv : v % 2 ^ k = v' % 2 ^ k) (hw : w % 2 ^ k = w' % 2 ^ k) :
    stt n i b f v w = stt n i b' f' v' w' := by
  have e1 : writeField i n k b = writeField i n k b' := by
    rw [← writeField_mod i n k b, ← writeField_mod i n k b', hb]
  have e3 : ∀ X, writeField X (vw n) k v = writeField X (vw n) k v' := by
    intro X
    rw [← writeField_mod X (vw n) k v, ← writeField_mod X (vw n) k v', hv]
  have e4 : ∀ X, writeField X (aw n) k w = writeField X (aw n) k w' := by
    intro X
    rw [← writeField_mod X (aw n) k w, ← writeField_mod X (aw n) k w', hw]
  unfold stt
  rw [e1, write_congr hf, e3, e4]

theorem stt_setB {n : Nat} (hk : k ≤ n) (i b f v w b' : Nat) :
    writeField (stt n i b f v w) n k b' = stt n i b' f v w := by
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  unfold stt
  rw [writeField_comm (o₁ := aw n) (n₁ := k) (o₂ := n) (n₂ := k) (by omega),
    writeField_comm (o₁ := vw n) (n₁ := k) (o₂ := n) (n₂ := k) (by omega),
    writeField_comm (o₁ := fw n) (n₁ := 1) (o₂ := n) (n₂ := k) (by omega),
    writeField_writeField]

theorem stt_setF {n : Nat} (_hk : k ≤ n) (i b f v w f' : Nat) :
    writeField (stt n i b f v w) (fw n) 1 f' = stt n i b f' v w := by
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  unfold stt
  rw [writeField_comm (o₁ := aw n) (n₁ := k) (o₂ := fw n) (n₂ := 1) (by omega),
    writeField_comm (o₁ := vw n) (n₁ := k) (o₂ := fw n) (n₂ := 1) (by omega),
    writeField_writeField]

theorem stt_setV {n : Nat} (i b f v w v' : Nat) :
    writeField (stt n i b f v w) (vw n) k v' = stt n i b f v' w := by
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  unfold stt
  rw [writeField_comm (o₁ := aw n) (n₁ := k) (o₂ := vw n) (n₂ := k) (by omega),
    writeField_writeField]

theorem stt_setW {n : Nat} (i b f v w w' : Nat) :
    writeField (stt n i b f v w) (aw n) k w' = stt n i b f v w' := by
  unfold stt
  rw [writeField_writeField]

theorem stt_readA {n : Nat} (hk : k ≤ n) (i b f v w : Nat) :
    readField (stt n i b f v w) 0 k = readField i 0 k := by
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  unfold stt
  rw [readField_writeField_of_disjoint (by omega), readField_writeField_of_disjoint (by omega),
    readField_writeField_of_disjoint (by omega), readField_writeField_of_disjoint (by omega)]

theorem stt_readB {n : Nat} (hk : k ≤ n) (i b f v w : Nat) :
    readField (stt n i b f v w) n k = b % 2 ^ k := by
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  unfold stt
  rw [readField_writeField_of_disjoint (by omega), readField_writeField_of_disjoint (by omega),
    readField_writeField_of_disjoint (by omega), readField_writeField]

theorem stt_readF {n : Nat} (i b f v w : Nat) : bv (stt n i b f v w) (fw n) = f % 2 := by
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  unfold stt
  rw [bv_write_out (by omega), bv_write_out (by omega), bv_write_self]

theorem stt_readV {n : Nat} (i b f v w : Nat) :
    readField (stt n i b f v w) (vw n) k = v % 2 ^ k := by
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  unfold stt
  rw [readField_writeField_of_disjoint (by omega), readField_writeField]

theorem stt_readW {n : Nat} (i b f v w : Nat) :
    readField (stt n i b f v w) (aw n) k = w % 2 ^ k := by
  unfold stt
  rw [readField_writeField]

theorem stt_readC {n : Nat} (hk : k ≤ n) (i b f v w : Nat) :
    bv (stt n i b f v w) (cw n) = bv i (cw n) := by
  have hcv : cw n = 2 * n := rfl
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  unfold stt
  rw [bv_write_out (by omega), bv_write_out (by omega), bv_write_ne (by omega),
    bv_write_out (by omega)]

theorem stt_id {n b i : Nat} (hb : readField i n k = b) (hf : bv i (fw n) = 0)
    (hv : readField i (vw n) k = 0) (hw : readField i (aw n) k = 0) : stt n i b 0 0 0 = i := by
  have e1 : writeField i n k b = i := by rw [← hb]; exact writeField_read i n k
  have e2 : writeField i (fw n) 1 0 = i := write_of_bv (by rw [hf])
  have e3 : writeField i (vw n) k 0 = i := by rw [← hv]; exact writeField_read i (vw n) k
  have e4 : writeField i (aw n) k 0 = i := by rw [← hw]; exact writeField_read i (aw n) k
  unfold stt
  rw [e1, e2, e3, e4]

theorem stt_clean {n : Nat} (hk : k ≤ n) {i r : Nat} (hfz : bv i (fw n) = 0)
    (hvz : readField i (vw n) k = 0) (hwz : readField i (aw n) k = 0) :
    stt n i r 0 0 0 = writeField i n k r := by
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  have e1 : bv (writeField i n k r) (fw n) = 0 := by rw [bv_write_out (by omega), hfz]
  have e2 : readField (writeField i n k r) (vw n) k = 0 := by
    rw [readField_writeField_of_disjoint (by omega), hvz]
  have e3 : readField (writeField i n k r) (aw n) k = 0 := by
    rw [readField_writeField_of_disjoint (by omega), hwz]
  have f2 : writeField (writeField i n k r) (fw n) 1 0 = writeField i n k r :=
    write_of_bv (by rw [e1])
  have f3 : ∀ X : Nat, readField X (vw n) k = 0 → writeField X (vw n) k 0 = X := by
    intro X hX; rw [← hX]; exact writeField_read X (vw n) k
  have f4 : ∀ X : Nat, readField X (aw n) k = 0 → writeField X (aw n) k 0 = X := by
    intro X hX; rw [← hX]; exact writeField_read X (aw n) k
  unfold stt
  rw [f2, f3 _ e2, f4 _ e3]

/-! ### Block semantics -/

theorem act_copyA {n : Nat} (hk : k ≤ n) (i b f v w : Nat) :
    actGates (copyR 0 (aw n) k) (stt n i b f v w)
      = stt n i b f v ((w % 2 ^ k) ^^^ readField i 0 k) := by
  have hav : aw n = 2 * n + 2 + k := rfl
  rw [copyR_act k 0 (aw n) (stt n i b f v w) (Or.inr (by omega)), stt_readW, stt_readA hk,
    stt_setW]

theorem act_loadaw {n : Nat} (i b f v w c : Nat) :
    actGates (loadX (aw n) k c) (stt n i b f v w) = stt n i b f v ((w % 2 ^ k) ^^^ c) := by
  rw [loadX_act, stt_readW, stt_setW]

theorem act_loadv {n : Nat} (i b f v w c : Nat) :
    actGates (loadX (vw n) k c) (stt n i b f v w) = stt n i b f ((v % 2 ^ k) ^^^ c) w := by
  rw [loadX_act, stt_readV, stt_setV]

theorem act_loadb {n : Nat} (hk : k ≤ n) (i b f v w c : Nat) :
    actGates (loadX n k c) (stt n i b f v w) = stt n i ((b % 2 ^ k) ^^^ c) f v w := by
  rw [loadX_act, stt_readB hk, stt_setB hk]

theorem act_loadc {n : Nat} (i b f v w c : Nat) :
    actGates (loadC (fw n) (vw n) k c) (stt n i b f v w)
      = stt n i b f ((v % 2 ^ k) ^^^ (f % 2 * c)) w := by
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  rw [loadC_act k (vw n) c (stt n i b f v w) (Or.inl (by omega)), stt_readV, stt_readF, stt_setV]

theorem act_flip {n : Nat} (hk : k ≤ n) (i b f v w : Nat) :
    actGates [RGate.x (fw n)] (stt n i b f v w) = stt n i b ((f % 2 + 1) % 2) v w := by
  show RGate.act (RGate.x (fw n)) (stt n i b f v w) = _
  rw [act_x, stt_readF, stt_setF hk]

/-- The constant register into the negation register, modulo `2 ^ k`.  The flag
is the carry wire the chain is given, and this chain discards its carry, so the
flag comes back unchanged. -/
theorem act_negadd {n : Nat} (hk : k ≤ n) {i b f v w : Nat} (hf : f < 2) (hv : v < 2 ^ k)
    (hw : w < 2 ^ k) (hc : bv i (cw n) = 0) :
    actGates (achain (vw n) (aw n) (cw n) [] 0 k) (stt n i b f v w)
      = stt n i b f v ((v + w) % 2 ^ k) := by
  have hcv : cw n = 2 * n := rfl
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  have hmid : ∀ j, actGates ([] : List RGate) j
      = writeField j (fw n) 1
        ((fun x _ => x) (bv j (fw n)) (bv j (cwire (vw n) (cw n) k))) := by
    intro j
    show j = writeField j (fw n) 1 (bv j (fw n))
    exact (write_of_bv (by have := bv_lt j (fw n); omega)).symm
  have h := achain_act (A := vw n) (B := aw n) (c := cw n) (z := fw n) (K := k)
    (φ := fun x _ => x) (mid := [])
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    (Or.inl (by omega)) (Or.inl (by omega)) (by omega) hmid k 0 (by omega) (stt n i b f v w)
  simp only [Nat.add_zero, cwire] at h
  rw [stt_readV, stt_readW, stt_readC hk, hc, stt_readF, Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hf, Nat.add_zero, stt_setW, stt_setF hk] at h
  exact h

/-- The negation register into the target, with the carry out on the flag. -/
theorem act_addaw {n : Nat} (hk : k ≤ n) {i b f v w : Nat} (hb : b < 2 ^ k) (hf : f < 2)
    (hw : w < 2 ^ k) (hc : bv i (cw n) = 0) :
    actGates (blockAdd (aw n) n (cw n) (fw n)) (stt n i b f v w)
      = stt n i ((w + b) % 2 ^ k) ((f + (w + b) / 2 ^ k) % 2) v w := by
  have hcv : cw n = 2 * n := rfl
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  have hmid : ∀ j, actGates [RGate.cx (aw n + kp) (fw n)] j
      = writeField j (fw n) 1
        ((fun x y => (x + y) % 2) (bv j (fw n)) (bv j (cwire (aw n) (cw n) k))) := by
    intro j
    rw [cwire_k]
    show RGate.act (RGate.cx (aw n + kp) (fw n)) j = _
    rw [act_cx]
  have h := achain_act (A := aw n) (B := n) (c := cw n) (z := fw n) (K := k)
    (φ := fun x y => (x + y) % 2) (mid := [RGate.cx (aw n + kp) (fw n)])
    (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
    (Or.inl (by omega)) (Or.inr (by omega)) (by omega) hmid k 0 (by omega) (stt n i b f v w)
  simp only [Nat.add_zero, cwire] at h
  rw [stt_readW, stt_readB hk, stt_readC hk, hc, stt_readF, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hw, Nat.add_zero, stt_setB hk, stt_setF hk] at h
  show actGates (achain (aw n) n (cw n) [RGate.cx (aw n + kp) (fw n)] 0 k) (stt n i b f v w) = _
  exact h

/-- The constant register into the target, with the carry out on the flag. -/
theorem act_addv {n : Nat} (hk : k ≤ n) {i b f v w : Nat} (hb : b < 2 ^ k) (hf : f < 2)
    (hv : v < 2 ^ k) (hc : bv i (cw n) = 0) :
    actGates (blockAdd (vw n) n (cw n) (fw n)) (stt n i b f v w)
      = stt n i ((v + b) % 2 ^ k) ((f + (v + b) / 2 ^ k) % 2) v w := by
  have hcv : cw n = 2 * n := rfl
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  have hmid : ∀ j, actGates [RGate.cx (vw n + kp) (fw n)] j
      = writeField j (fw n) 1
        ((fun x y => (x + y) % 2) (bv j (fw n)) (bv j (cwire (vw n) (cw n) k))) := by
    intro j
    rw [cwire_k]
    show RGate.act (RGate.cx (vw n + kp) (fw n)) j = _
    rw [act_cx]
  have h := achain_act (A := vw n) (B := n) (c := cw n) (z := fw n) (K := k)
    (φ := fun x y => (x + y) % 2) (mid := [RGate.cx (vw n + kp) (fw n)])
    (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
    (Or.inl (by omega)) (Or.inr (by omega)) (by omega) hmid k 0 (by omega) (stt n i b f v w)
  simp only [Nat.add_zero, cwire] at h
  rw [stt_readV, stt_readB hk, stt_readC hk, hc, stt_readF, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hv, Nat.add_zero, stt_setB hk, stt_setF hk] at h
  show actGates (achain (vw n) n (cw n) [RGate.cx (vw n + kp) (fw n)] 0 k) (stt n i b f v w) = _
  exact h

/-- The constant register into the target with the carry discarded, which is the
add-back of the modulus. -/
theorem act_addv0 {n : Nat} (hk : k ≤ n) {i b f v w : Nat} (hb : b < 2 ^ k) (hf : f < 2)
    (hv : v < 2 ^ k) (hc : bv i (cw n) = 0) :
    actGates (achain (vw n) n (cw n) [] 0 k) (stt n i b f v w)
      = stt n i ((v + b) % 2 ^ k) f v w := by
  have hcv : cw n = 2 * n := rfl
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  have hmid : ∀ j, actGates ([] : List RGate) j
      = writeField j (fw n) 1
        ((fun x _ => x) (bv j (fw n)) (bv j (cwire (vw n) (cw n) k))) := by
    intro j
    show j = writeField j (fw n) 1 (bv j (fw n))
    exact (write_of_bv (by have := bv_lt j (fw n); omega)).symm
  have h := achain_act (A := vw n) (B := n) (c := cw n) (z := fw n) (K := k)
    (φ := fun x _ => x) (mid := [])
    (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
    (Or.inl (by omega)) (Or.inr (by omega)) (by omega) hmid k 0 (by omega) (stt n i b f v w)
  simp only [Nat.add_zero, cwire] at h
  rw [stt_readV, stt_readB hk, stt_readC hk, hc, stt_readF, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hv, Nat.add_zero, stt_setB hk, stt_setF hk] at h
  exact h

/-- Comparing the target against the negation register clears the flag. -/
theorem act_cmp {n : Nat} (hk : k ≤ n) {i b f v w : Nat} (hb : b < 2 ^ k) (hf : f < 2)
    (hw : w < 2 ^ k) (hc : bv i (cw n) = 0) :
    actGates (cchain (aw n) n (cw n) [RGate.cx (aw n + kp) (fw n)] 0 k) (stt n i b f v w)
      = stt n i b ((f + (w + b) / 2 ^ k) % 2) v w := by
  have hcv : cw n = 2 * n := rfl
  have hfv : fw n = 2 * n + 1 := rfl
  have hvv : vw n = 2 * n + 2 := rfl
  have hav : aw n = 2 * n + 2 + k := rfl
  have hmid : ∀ j, actGates [RGate.cx (aw n + kp) (fw n)] j
      = writeField j (fw n) 1
        ((fun x y => (x + y) % 2) (bv j (fw n)) (bv j (cwire (aw n) (cw n) k))) := by
    intro j
    rw [cwire_k]
    show RGate.act (RGate.cx (aw n + kp) (fw n)) j = _
    rw [act_cx]
  have h := cchain_act (A := aw n) (B := n) (c := cw n) (z := fw n) (K := k)
    (φ := fun x y => (x + y) % 2) (mid := [RGate.cx (aw n + kp) (fw n)])
    (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
    (Or.inl (by omega)) (Or.inr (by omega)) (by omega) hmid k 0 (by omega) (stt n i b f v w)
  simp only [Nat.add_zero, cwire] at h
  rw [stt_readW, stt_readB hk, stt_readC hk, hc, stt_readF, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hw, Nat.add_zero, stt_setF hk] at h
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

/-! ### Modular negation

Five blocks each way.  `m + 1` added to the complement of `a` is
`2 ^ k + (m - a)`, which reduces to `m - a` because `a` is below the modulus,
and the same constant added to the complement of `m - a` is `2 ^ k + a`, which
brings the register back to the value the copy put there. -/

theorem negA_act {n : Nat} (hk : k ≤ n) {i a b : Nat} (ha : readField i 0 k = a)
    (ham : a < m) (hc : bv i (cw n) = 0) :
    actGates (negA n) (stt n i b 0 0 0) = stt n i b 0 0 (m - a) := by
  have hK : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
  have hmK : m < 2 ^ k := m_lt
  have hm1 : m + 1 < 2 ^ k := m_succ_lt
  have haK : a < 2 ^ k := by omega
  have t1 : actGates (copyR 0 (aw n) k) (stt n i b 0 0 0) = stt n i b 0 0 a := by
    rw [act_copyA hk, ha, Nat.zero_mod, Nat.zero_xor]
  have t2 : actGates (loadX (aw n) k (2 ^ k - 1)) (stt n i b 0 0 a)
      = stt n i b 0 0 (2 ^ k - 1 - a) := by
    rw [act_loadaw, Nat.mod_eq_of_lt haK, xor_ones k a haK]
  have t3 : actGates (loadV n) (stt n i b 0 0 (2 ^ k - 1 - a))
      = stt n i b 0 (m + 1) (2 ^ k - 1 - a) := by
    rw [loadV, act_loadv, Nat.zero_mod, Nat.zero_xor]
  have t4 : actGates (achain (vw n) (aw n) (cw n) [] 0 k)
      (stt n i b 0 (m + 1) (2 ^ k - 1 - a)) = stt n i b 0 (m + 1) (m - a) := by
    have he : (m + 1 + (2 ^ k - 1 - a)) % 2 ^ k = m - a := by
      have S := split_two hK (show m + 1 + (2 ^ k - 1 - a) < 2 * 2 ^ k by omega)
      rcases S with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega
    rw [act_negadd hk (by omega) hm1 (by omega) hc, he]
  have t5 : actGates (loadV n) (stt n i b 0 (m + 1) (m - a)) = stt n i b 0 0 (m - a) := by
    rw [loadV, act_loadv, Nat.mod_eq_of_lt hm1, Nat.xor_self]
  simp only [negA, actGates_append]
  rw [t1, t2, t3, t4, t5]

theorem unnegA_act {n : Nat} (hk : k ≤ n) {i a r : Nat} (ha : readField i 0 k = a)
    (ham : a < m) (hc : bv i (cw n) = 0) :
    actGates (unnegA n) (stt n i r 0 0 (m - a)) = stt n i r 0 0 0 := by
  have hK : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
  have hmK : m < 2 ^ k := m_lt
  have hm1 : m + 1 < 2 ^ k := m_succ_lt
  have haK : a < 2 ^ k := by omega
  have hdK : m - a < 2 ^ k := by omega
  have t1 : actGates (loadX (aw n) k (2 ^ k - 1)) (stt n i r 0 0 (m - a))
      = stt n i r 0 0 (2 ^ k - 1 - (m - a)) := by
    rw [act_loadaw, Nat.mod_eq_of_lt hdK, xor_ones k (m - a) hdK]
  have t2 : actGates (loadV n) (stt n i r 0 0 (2 ^ k - 1 - (m - a)))
      = stt n i r 0 (m + 1) (2 ^ k - 1 - (m - a)) := by
    rw [loadV, act_loadv, Nat.zero_mod, Nat.zero_xor]
  have t3 : actGates (achain (vw n) (aw n) (cw n) [] 0 k)
      (stt n i r 0 (m + 1) (2 ^ k - 1 - (m - a))) = stt n i r 0 (m + 1) a := by
    have he : (m + 1 + (2 ^ k - 1 - (m - a))) % 2 ^ k = a := by
      have S := split_two hK (show m + 1 + (2 ^ k - 1 - (m - a)) < 2 * 2 ^ k by omega)
      rcases S with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega
    rw [act_negadd hk (by omega) hm1 (by omega) hc, he]
  have t4 : actGates (loadV n) (stt n i r 0 (m + 1) a) = stt n i r 0 0 a := by
    rw [loadV, act_loadv, Nat.mod_eq_of_lt hm1, Nat.xor_self]
  have t5 : actGates (copyR 0 (aw n) k) (stt n i r 0 0 a) = stt n i r 0 0 0 := by
    rw [act_copyA hk, ha, Nat.mod_eq_of_lt haK, Nat.xor_self]
  simp only [unnegA, actGates_append]
  rw [t1, t2, t3, t4, t5]

/-! ### Adder block semantics

`b1`, `b3`, `b7`, `b9` are the successive values of the target field and `c1`,
`c2`, `c4` the three carries the flag is built from.  The augend is the negation
register, whose value runs over `[1, m]` rather than over the residues, so the
hypothesis here is that it is at most the modulus.  That is all the twelve
blocks need: the two adds and the comparison are correct at the endpoint, where
`m + b` reduces to `b` and the comparison still discriminates. -/

theorem madd_act {n : Nat} (hk : k ≤ n) {i b w : Nat}
    (hc : bv i (cw n) = 0) (hwm : w ≤ m) (hbm : b < m) :
    actGates (madd n) (stt n i b 0 0 w) = stt n i ((w + b) % m) 0 0 w := by
  have hK : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
  have hmK : m < 2 ^ k := m_lt
  have hm0 : 0 < m := m_pos
  have hwK : w < 2 ^ k := by omega
  have hbK : b < 2 ^ k := by omega
  obtain ⟨c1, hc1⟩ : ∃ x, (w + b) / 2 ^ k = x := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ x, (w + b) % 2 ^ k = x := ⟨_, rfl⟩
  have hb1K : b1 < 2 ^ k := by rw [← hb1]; exact Nat.mod_lt _ hK
  have S1 := split_two hK (show w + b < 2 * 2 ^ k by omega)
  rw [hc1, hb1] at S1
  have hc1lt : c1 < 2 := by rcases S1 with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega
  obtain ⟨c2, hc2⟩ : ∃ x, (2 ^ k - m + b1) / 2 ^ k = x := ⟨_, rfl⟩
  obtain ⟨b3, hb3⟩ : ∃ x, (2 ^ k - m + b1) % 2 ^ k = x := ⟨_, rfl⟩
  have hb3K : b3 < 2 ^ k := by rw [← hb3]; exact Nat.mod_lt _ hK
  have S2 := split_two hK (show 2 ^ k - m + b1 < 2 * 2 ^ k by omega)
  rw [hc2, hb3] at S2
  have hc2lt : c2 < 2 := by rcases S2 with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega
  obtain ⟨ff3, hff3⟩ : ∃ x, (c1 + c2) % 2 = x := ⟨_, rfl⟩
  have hff3lt : ff3 < 2 := by omega
  obtain ⟨g, hg⟩ : ∃ x, (ff3 + 1) % 2 = x := ⟨_, rfl⟩
  have hglt : g < 2 := by omega
  have hgm : g * m < 2 ^ k := by
    rcases (show g = 0 ∨ g = 1 by omega) with h | h <;> rw [h] <;> omega
  obtain ⟨b7, hb7⟩ : ∃ x, (g * m + b3) % 2 ^ k = x := ⟨_, rfl⟩
  have hb7K : b7 < 2 ^ k := by rw [← hb7]; exact Nat.mod_lt _ hK
  have S3 := split_two hK (show g * m + b3 < 2 * 2 ^ k by omega)
  rw [hb7] at S3
  obtain ⟨b9, hb9⟩ : ∃ x, 2 ^ k - 1 - b7 = x := ⟨_, rfl⟩
  have hb9K : b9 < 2 ^ k := by omega
  obtain ⟨c4, hc4⟩ : ∃ x, (w + b9) / 2 ^ k = x := ⟨_, rfl⟩
  have S4 := split_two hK (show w + b9 < 2 * 2 ^ k by omega)
  rw [hc4] at S4
  have SM := split_two hm0 (show w + b < 2 * m by omega)
  have key : b7 = (w + b) % m ∧ ((g + c4) % 2 % 2 + 1) % 2 = 0 := by
    have hgcase : g = 0 ∨ g = 1 := by omega
    rcases hgcase with hg0 | hg0 <;> subst hg0 <;>
      rcases S1 with ⟨e0, e1, e2⟩ | ⟨e1, e2, e3⟩ <;>
      rcases S2 with ⟨d0, e4, e5⟩ | ⟨e4, e5, e6⟩ <;>
      rcases S3 with ⟨c0, e7, e8⟩ | ⟨e7, e8, e9⟩ <;>
      rcases S4 with ⟨a0, f1, f2⟩ | ⟨f1, f2, f3⟩ <;>
      rcases SM with ⟨b0, h1, h2⟩ | ⟨h1, h2, h3⟩ <;>
      exact ⟨by omega, by omega⟩
  have hz0 : (0 % 2 ^ k) ^^^ (2 ^ k - m) = 2 ^ k - m := by rw [Nat.zero_mod, Nat.zero_xor]
  have hz1 : (((2 : Nat) ^ k - m) % 2 ^ k) ^^^ (2 ^ k - m) = 0 := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.xor_self]
  have hz2 : (0 % 2 ^ k) ^^^ (g % 2 * m) = g * m := by
    rw [Nat.zero_mod, Nat.zero_xor, Nat.mod_eq_of_lt hglt]
  have hz3 : ((g * m) % 2 ^ k) ^^^ (g % 2 * m) = 0 := by
    rw [Nat.mod_eq_of_lt hgm, Nat.mod_eq_of_lt hglt, Nat.xor_self]
  have hz4 : (b7 % 2 ^ k) ^^^ (2 ^ k - 1) = b9 := by
    rw [Nat.mod_eq_of_lt hb7K, xor_ones k b7 hb7K, hb9]
  have hz5 : (b9 % 2 ^ k) ^^^ (2 ^ k - 1) = b7 := by
    rw [Nat.mod_eq_of_lt hb9K, xor_ones k b9 hb9K]
    omega
  have t1 : actGates (blockAdd (aw n) n (cw n) (fw n)) (stt n i b 0 0 w)
      = stt n i b1 c1 0 w := by
    have h := act_addaw (n := n) hk (i := i) (b := b) (f := 0) (v := 0) (w := w)
      hbK (by omega) hwK hc
    rw [hc1, hb1] at h
    rw [h]
    exact stt_eq rfl (by omega) rfl rfl
  have t2 : actGates (loadX (vw n) k (2 ^ k - m)) (stt n i b1 c1 0 w)
      = stt n i b1 c1 (2 ^ k - m) w := by rw [act_loadv, hz0]
  have t3 : actGates (blockAdd (vw n) n (cw n) (fw n)) (stt n i b1 c1 (2 ^ k - m) w)
      = stt n i b3 ff3 (2 ^ k - m) w := by
    rw [act_addv hk hb1K hc1lt (by omega) hc, hc2, hb3, hff3]
  have t4 : actGates (loadX (vw n) k (2 ^ k - m)) (stt n i b3 ff3 (2 ^ k - m) w)
      = stt n i b3 ff3 0 w := by rw [act_loadv, hz1]
  have t5 : actGates [RGate.x (fw n)] (stt n i b3 ff3 0 w) = stt n i b3 g 0 w := by
    rw [act_flip hk]
    exact stt_eq rfl (by omega) rfl rfl
  have t6 : actGates (loadC (fw n) (vw n) k m) (stt n i b3 g 0 w)
      = stt n i b3 g (g * m) w := by rw [act_loadc, hz2]
  have t7 : actGates (achain (vw n) n (cw n) [] 0 k) (stt n i b3 g (g * m) w)
      = stt n i b7 g (g * m) w := by
    rw [act_addv0 hk hb3K hglt hgm hc, hb7]
  have t8 : actGates (loadC (fw n) (vw n) k m) (stt n i b7 g (g * m) w)
      = stt n i b7 g 0 w := by rw [act_loadc, hz3]
  have t9 : actGates (loadX n k (2 ^ k - 1)) (stt n i b7 g 0 w) = stt n i b9 g 0 w := by
    rw [act_loadb hk, hz4]
  have t10 : actGates (cchain (aw n) n (cw n) [RGate.cx (aw n + kp) (fw n)] 0 k)
      (stt n i b9 g 0 w) = stt n i b9 ((g + c4) % 2) 0 w := by
    rw [act_cmp hk hb9K hglt hwK hc, hc4]
  have t11 : actGates (loadX n k (2 ^ k - 1)) (stt n i b9 ((g + c4) % 2) 0 w)
      = stt n i b7 ((g + c4) % 2) 0 w := by
    rw [act_loadb hk, hz5]
  have t12 : actGates [RGate.x (fw n)] (stt n i b7 ((g + c4) % 2) 0 w)
      = stt n i ((w + b) % m) 0 0 w := by
    rw [act_flip hk, key.1]
    exact stt_eq rfl (by omega) rfl rfl
  simp only [madd, actGates_append]
  rw [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12]

/-! ### Circuit components -/

theorem gadget_act {n : Nat} (hk : k ≤ n) {i a b : Nat}
    (ha : readField i 0 k = a) (hbr : readField i n k = b)
    (hcz : bv i (cw n) = 0) (hfz : bv i (fw n) = 0)
    (hvz : readField i (vw n) k = 0) (hwz : readField i (aw n) k = 0)
    (ham : a < m) (hbm : b < m) :
    actGates (gadget n) i = stt n i ((b + (m - a)) % m) 0 0 0 := by
  have hi : stt n i b 0 0 0 = i := stt_id hbr hfz hvz hwz
  have hmm : m - a ≤ m := by omega
  have hsum : (m - a + b) % m = (b + (m - a)) % m := by rw [Nat.add_comm (m - a) b]
  have e1 : actGates (negA n) i = stt n i b 0 0 (m - a) := by
    have h := negA_act (n := n) hk (i := i) (a := a) (b := b) ha ham hcz
    rw [hi] at h
    exact h
  have e2 := madd_act (n := n) hk (i := i) (b := b) (w := m - a) hcz hmm hbm
  have e3 := unnegA_act (n := n) hk (i := i) (a := a) (r := (m - a + b) % m) ha ham hcz
  simp only [gadget, actGates_append]
  rw [e1, e2, e3, hsum]

/-! ### Correctness claim -/

theorem subs_general : ∀ n : Nat, VQ.Reversible.SubsMod VQ.Curve.PointAddition.Arithmetic.Subt.m VQ.Curve.PointAddition.Arithmetic.Subt.ws n (VQ.Curve.PointAddition.Arithmetic.Subt.gen n) := by
  intro n a b i _ h0 h1 h2
  have hmain : m ≤ 2 ^ n → a < m → b < m →
      act (VQ.Curve.PointAddition.Arithmetic.Subt.gen n) i = writeField i n n ((b + (m - a)) % m) := by
    intro hm ha hb
    have hk : k ≤ n := k_le hm
    have hmK : m < 2 ^ k := m_lt
    have hm0 : 0 < m := m_pos
    have hK : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
    have hwsv : ws = 2 * k + 2 := rfl
    have e0 : readField i 0 n = a := h0
    have e1 : readField i n n = b := h1
    have e2 : readField i (2 * n) ws = 0 := by
      have h : readField i (n + n) ws = 0 := h2
      rw [show 2 * n = n + n from by omega]
      exact h
    have ea : readField i 0 k = a := by
      rw [readField_narrow i 0 k n hk, e0, Nat.mod_eq_of_lt (by omega)]
    have eb : readField i n k = b := by
      rw [readField_narrow i n k n hk, e1, Nat.mod_eq_of_lt (by omega)]
    have ec : bv i (cw n) = 0 := by
      rw [← readField_one]
      have := readField_sub_zero e2 (d := 0) (e := 1) (by omega)
      rw [show cw n = 2 * n + 0 from by simp [cw]]
      exact this
    have ef : bv i (fw n) = 0 := by
      rw [← readField_one]
      exact readField_sub_zero e2 (d := 1) (e := 1) (by omega)
    have ev : readField i (vw n) k = 0 :=
      readField_sub_zero e2 (d := 2) (e := k) (by omega)
    have ew : readField i (aw n) k = 0 := by
      have h := readField_sub_zero e2 (d := 2 + k) (e := k) (by omega)
      rw [show aw n = 2 * n + (2 + k) from by show 2 * n + 2 + k = _; omega]
      exact h
    have hact : act (VQ.Curve.PointAddition.Arithmetic.Subt.gen n) i = actGates (gadget n) i := by
      show actGates (if k ≤ n then gadget n else []) i = _
      rw [if_pos hk]
    rw [hact, gadget_act hk ea eb ec ef ev ew ha hb, stt_clean hk ef ev ew]
    exact write_widen hk (by have := Nat.mod_lt (b + (m - a)) hm0; omega) (by rw [e1]; omega)
  intro hm ha hb
  show act (VQ.Curve.PointAddition.Arithmetic.Subt.gen n) i = writeField i (n + 0) n ((b + (m - a)) % m)
  rw [Nat.add_zero]
  exact hmain hm ha hb

/-- Modular subtraction with the modulus and workspace specialized to their fixed values. -/
theorem subs : ∀ n : Nat,
    VQ.Reversible.SubsMod
      115792089237316195423570985008687907853269984665640564039457584007908834671663
      514 n (VQ.Curve.PointAddition.Arithmetic.Subt.gen n) := subs_general

end Subt
end VQ.Curve.PointAddition.Arithmetic
