import VQ.Curve.PointAddition.Arithmetic.Inv.Add
import VQ.Reversible.Reverse

/-!
# Load and copy circuits

Three gadgets the round needs beside the adder.

`loadX` exclusive-ors a classical constant into a field, one X gate per set bit.
The comparison uses it with the all-ones pattern, which complements the field.

`copyC` copies a quantum field into another under the control of one wire, one
Toffoli per bit.  This is how a conditional addition is built: a Cuccaro adder
cannot take an extra control, since its Toffolis are already at two, so the
addend is copied into scratch under the control and the adder runs
unconditionally.

The exclusive-or lemmas are the arithmetic those two need, and `act_x` is the
single-gate fact.  All of this except `copyC` is `examples/06-modadd-p` verbatim.
-/

namespace VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible VQ.Curve.PointAddition.Arithmetic.Inv.Add

theorem act_x (q i : Nat) :
    RGate.act (RGate.x q) i = writeField i q 1 ((bv i q + 1) % 2) := flip_eq i q

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

/-- A single bit as a shift and a remainder. -/
theorem bv_shift (i q : Nat) : bv i q = i >>> q % 2 := by
  rw [← readField_one]
  show (i >>> q) % 2 ^ 1 = _
  rw [Nat.pow_one]

/-- The top bit of a field is the bit at its top wire. -/
theorem readField_top (i off k : Nat) :
    readField i off (k + 1) / 2 ^ k % 2 = bv i (off + k) := by
  have hpow : (2 : Nat) ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
  show ((i >>> off) % 2 ^ (k + 1)) / 2 ^ k % 2 = _
  rw [hpow, Nat.mod_mul_right_div_self, bv_shift, Nat.shiftRight_add,
    Nat.shiftRight_eq_div_pow]
  omega

/-- Gates that avoid a field leave it as they found it. -/
theorem readField_actGates_outside {gs : List RGate} {off len i : Nat}
    (h : ∀ g ∈ gs, ∀ q ∈ g.wires, q < off ∨ off + len ≤ q) :
    readField (actGates gs i) off len = readField i off len := by
  have hw : writeField i off len (readField i off len) = i := Reversible.writeField_read i off len
  have e := actGates_write_of_outside h (v := readField i off len) i
  rw [hw] at e
  rw [e, readField_writeField, Nat.mod_eq_of_lt (readField_lt i off len)]

/-- Writing a short value into a wider field, when the field's high bits are
already clear. -/
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

/-- A value whose top bit is clear fits in one bit fewer. -/
theorem lt_of_top_bit_zero {x k : Nat} (hx : x < 2 ^ (k + 1)) (h : x / 2 ^ k % 2 = 0) :
    x < 2 ^ k := by
  have hpos := Nat.two_pow_pos k
  have hq : x / 2 ^ k < 2 := by
    refine Nat.div_lt_of_lt_mul ?_
    rw [← Nat.pow_succ]
    exact hx
  have hd : x / 2 ^ k = 0 := by
    match hval : x / 2 ^ k with
    | 0 => rfl
    | 1 => rw [hval] at h; simp at h
    | t + 2 => rw [hval] at hq; omega
  exact Nat.lt_of_div_eq_zero hpos hd

/-- Reading a narrower field out of a written one. -/
theorem readField_writeField_narrow {i o m n v : Nat} (h : m ≤ n) :
    readField (writeField i o n v) o m = v % 2 ^ m := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  rw [testBit_readField, Nat.testBit_mod_two_pow]
  by_cases hb : b < m
  · rw [testBit_writeField_inside (by omega) (by omega)]
    simp [hb]
  · simp [hb]

/-- Writing one bit into a field already written: the low bit changes and the
rest stays. -/
theorem writeField_low {i o m v u : Nat} :
    writeField (writeField i o (m + 1) v) o 1 u
      = writeField i o (m + 1) (u % 2 + 2 * (v / 2)) := by
  rw [writeField_succ i o m v, writeField_succ i o m (u % 2 + 2 * (v / 2))]
  have h1 : (u % 2 + 2 * (v / 2)) % 2 = u % 2 := by omega
  have h2 : (u % 2 + 2 * (v / 2)) / 2 = v / 2 := by omega
  rw [h1, h2, writeField_comm (i := writeField i o 1 (v % 2)) (o₁ := o + 1) (n₁ := m)
    (v := v / 2) (o₂ := o) (n₂ := 1) (u := u) (by omega), writeField_writeField]
  exact congrArg (fun z => writeField z (o + 1) m (v / 2)) (write_congr (by omega))

/-- Exclusive-or a classical constant into a field, one X gate per set bit. -/
def loadX : Nat → Nat → Nat → List RGate
  | _, 0, _ => []
  | W, p + 1, v => (if v % 2 = 1 then [RGate.x W] else []) ++ loadX (W + 1) p (v / 2)

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

/-- Load a classical constant under a control.

A copy from a register costs one Toffoli per bit.  When the source is a
constant known when the circuit is built, the same effect is one CNOT from the
control per set bit of that constant, and no Toffoli at all. -/
def loadCX (c : Nat) : Nat → Nat → Nat → List RGate
  | _, 0, _ => []
  | W, p + 1, v => (if v % 2 = 1 then [RGate.cx c W] else []) ++ loadCX c (W + 1) p (v / 2)

theorem loadCX_act {c : Nat} : ∀ (p W v i : Nat), (c < W ∨ W + p ≤ c) →
    actGates (loadCX c W p v) i = writeField i W p ((readField i W p) ^^^ (bv i c * v)) := by
  intro p
  induction p with
  | zero => intro W v i _; rw [writeField_zero]; rfl
  | succ p ih =>
    intro W v i hc
    have hcW : c < W ∨ W + 1 ≤ c := by omega
    have hbc := bv_lt i c
    have hbw := bv_lt i W
    have hhead : actGates (if v % 2 = 1 then [RGate.cx c W] else []) i
        = writeField i W 1 ((bv i W + bv i c * (v % 2)) % 2) := by
      by_cases hv : v % 2 = 1
      · rw [if_pos hv]
        show RGate.act (RGate.cx c W) i = _
        rw [act_cx, hv, Nat.mul_one]
      · rw [if_neg hv]
        have hv0 : v % 2 = 0 := by omega
        rw [hv0, Nat.mul_zero]
        show i = writeField i W 1 ((bv i W + 0) % 2)
        exact (write_of_bv (by omega)).symm
    have hmod : (bv i c * v) % 2 = bv i c * (v % 2) % 2 := by
      rcases (by omega : bv i c = 0 ∨ bv i c = 1) with h | h <;> rw [h] <;> simp
    have hdiv : (bv i c * v) / 2 = bv i c * (v / 2) := by
      rcases (by omega : bv i c = 0 ∨ bv i c = 1) with h | h <;> rw [h] <;> simp
    have hα : ((readField i W (p + 1)) ^^^ (bv i c * v)) % 2
        = (bv i W + bv i c * (v % 2)) % 2 := by
      rw [xor_bit, hmod]
      have hr : readField i W (p + 1) % 2 = bv i W := by
        have := readField_succ i W p; omega
      rw [hr]
      omega
    have hβ : ((readField i W (p + 1)) ^^^ (bv i c * v)) / 2
        = (readField i (W + 1) p) ^^^ (bv i c * (v / 2)) := by
      rw [xor_div_two, hdiv]
      have hr : readField i W (p + 1) / 2 = readField i (W + 1) p := by
        have := readField_succ i W p; omega
      rw [hr]
    have hbvc : bv (writeField i W 1 ((bv i W + bv i c * (v % 2)) % 2)) c = bv i c := by
      rw [← readField_one, readField_writeField_of_disjoint (by omega), readField_one]
    rw [loadCX, actGates_append, hhead, ih (W + 1) (v / 2) _ (by omega),
      readField_writeField_of_disjoint (Or.inl (by omega)), hbvc,
      writeField_succ i W p ((readField i W (p + 1)) ^^^ (bv i c * v)), hα, hβ]

theorem loadCX_wires {c : Nat} : ∀ (p W v : Nat), ∀ g ∈ loadCX c W p v, ∀ q ∈ g.wires,
    q = c ∨ (W ≤ q ∧ q < W + p) := by
  intro p
  induction p with
  | zero => intro W v g hg; simp [loadCX] at hg
  | succ p ih =>
    intro W v g hg q hq
    rw [loadCX, List.mem_append] at hg
    cases hg with
    | inl h =>
      by_cases hv : v % 2 = 1
      · rw [if_pos hv] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        subst h
        simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨Nat.le_refl _, by omega⟩
      · rw [if_neg hv] at h; simp at h
    | inr h =>
      have := ih (W + 1) (v / 2) g h q hq
      omega

theorem loadCX_ccx (c : Nat) : ∀ (p W v : Nat), (loadCX c W p v).countP RGate.isCcx = 0
  | 0, _, _ => rfl
  | p + 1, W, v => by
    rw [loadCX, List.countP_append, loadCX_ccx c p (W + 1) (v / 2)]
    by_cases h : v % 2 = 1
    · rw [if_pos h]; rfl
    · rw [if_neg h]; rfl

theorem loadCX_len (c : Nat) : ∀ (p W v : Nat), (loadCX c W p v).length ≤ p
  | 0, _, _ => Nat.le_refl 0
  | p + 1, W, v => by
    rw [loadCX, List.length_append]
    have h := loadCX_len c p (W + 1) (v / 2)
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; simp only [List.length_cons, List.length_nil]; omega
    · rw [if_neg hv]; simp only [List.length_nil]; omega

/-- Every gate of a load touches only the field it writes. -/
theorem loadX_wires : ∀ (p W v : Nat), ∀ g ∈ loadX W p v, ∀ q ∈ g.wires, W ≤ q ∧ q < W + p := by
  intro p
  induction p with
  | zero => intro W v g hg; simp [loadX] at hg
  | succ p ih =>
    intro W v g hg q hq
    rw [loadX, List.mem_append] at hg
    cases hg with
    | inl h =>
      by_cases hv : v % 2 = 1
      · rw [if_pos hv] at h
        simp only [List.mem_singleton] at h
        subst h
        simp only [RGate.wires, List.mem_singleton] at hq
        omega
      · rw [if_neg hv] at h; simp at h
    | inr h =>
      have := ih (W + 1) (v / 2) g h q hq
      omega

/-- Complementing a field: `loadX` with the all-ones pattern. -/
theorem loadX_ones (p W i : Nat) :
    actGates (loadX W p (2 ^ p - 1)) i = writeField i W p (2 ^ p - 1 - readField i W p) := by
  rw [loadX_act, xor_ones p (readField i W p) (readField_lt i W p)]

/-- Every gate of a load is well formed at any width the field fits in. -/
theorem loadX_wf : ∀ (p W v Wd : Nat), W + p ≤ Wd →
    (loadX W p v).all (RGate.wellFormed Wd) = true := by
  intro p
  induction p with
  | zero => intro W v Wd _; simp [loadX]
  | succ p ih =>
    intro W v Wd h
    rw [loadX, List.all_append, Bool.and_eq_true]
    refine ⟨?_, ih (W + 1) (v / 2) Wd (by omega)⟩
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; simp [RGate.wellFormed]; omega
    · rw [if_neg hv]; simp

theorem loadCX_wf (c : Nat) : ∀ (p W v Wd : Nat), (c < W ∨ W + p ≤ c) → c < Wd →
    W + p ≤ Wd → (loadCX c W p v).all (RGate.wellFormed Wd) = true := by
  intro p
  induction p with
  | zero => intro W v Wd _ _ _; simp [loadCX]
  | succ p ih =>
    intro W v Wd hc hcw h
    rw [loadCX, List.all_append, Bool.and_eq_true]
    refine ⟨?_, ih (W + 1) (v / 2) Wd (by omega) hcw (by omega)⟩
    by_cases hv : v % 2 = 1
    · rw [if_pos hv]; simp [RGate.wellFormed]; omega
    · rw [if_neg hv]; simp

/-- Copy one field into another under the control of wire `c`, one Toffoli per
bit.  The source field is read and the target is exclusive-ored. -/
def copyC (c : Nat) : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | src, dst, p + 1 => RGate.ccx c src dst :: copyC c (src + 1) (dst + 1) p

theorem copyC_act {c : Nat} : ∀ (p src dst i : Nat),
    (dst + p ≤ src ∨ src + p ≤ dst) → (c < dst ∨ dst + p ≤ c) →
    actGates (copyC c src dst p) i
      = writeField i dst p ((readField i dst p) ^^^ (bv i c * readField i src p)) := by
  intro p
  induction p with
  | zero => intro src dst i _ _; rw [writeField_zero]; rfl
  | succ p ih =>
    intro src dst i hsd hcd
    have hbd := bv_lt i dst
    have hbs := bv_lt i src
    have hbc := bv_lt i c
    have hrd := readField_succ i dst p
    have hrs := readField_succ i src p
    have ht : bv i c = 0 ∨ bv i c = 1 := by omega
    have hcne : c ≠ dst := by omega
    have hsne : src ≠ dst := by omega
    have hhead : actGates [RGate.ccx c src dst] i
        = writeField i dst 1 ((bv i dst + bv i c * bv i src) % 2) := by
      show RGate.act (RGate.ccx c src dst) i = _
      rw [act_ccx]
    have hbc1 : bv (writeField i dst 1 ((bv i dst + bv i c * bv i src) % 2)) c = bv i c :=
      bv_write_ne hcne
    have hmul2 : (bv i c * readField i src (p + 1)) % 2 = (bv i c * bv i src) % 2 := by
      cases ht with
      | inl h => rw [h]; omega
      | inr h => rw [h]; omega
    have hmuld : (bv i c * readField i src (p + 1)) / 2 = bv i c * readField i (src + 1) p := by
      cases ht with
      | inl h => rw [h]; omega
      | inr h => rw [h]; omega
    have hα : ((readField i dst (p + 1)) ^^^ (bv i c * readField i src (p + 1))) % 2
        = (bv i dst + bv i c * bv i src) % 2 := by
      rw [xor_bit, hmul2]
      have : readField i dst (p + 1) % 2 = bv i dst := by omega
      rw [this]
      omega
    have hβ : ((readField i dst (p + 1)) ^^^ (bv i c * readField i src (p + 1))) / 2
        = (readField i (dst + 1) p) ^^^ (bv i c * readField i (src + 1) p) := by
      rw [xor_div_two, hmuld]
      have : readField i dst (p + 1) / 2 = readField i (dst + 1) p := by omega
      rw [this]
    have hsrc1 : readField (writeField i dst 1 ((bv i dst + bv i c * bv i src) % 2))
        (src + 1) p = readField i (src + 1) p :=
      readField_writeField_of_disjoint (by omega)
    show actGates (RGate.ccx c src dst :: copyC c (src + 1) (dst + 1) p) i = _
    rw [show (RGate.ccx c src dst :: copyC c (src + 1) (dst + 1) p)
          = [RGate.ccx c src dst] ++ copyC c (src + 1) (dst + 1) p from rfl,
      actGates_append, hhead, ih (src + 1) (dst + 1) _ (by omega) (by omega), hbc1, hsrc1,
      readField_writeField_of_disjoint (Or.inl (by omega)),
      writeField_succ i dst p
        ((readField i dst (p + 1)) ^^^ (bv i c * readField i src (p + 1))), hα, hβ]


/-! ## Zero-test circuit

A general comparator decides `v ≠ 0` at four adders' worth of Toffolis, two to
compute the difference and two to undo it.  The question is the or of the
register's bits, and an or-ladder answers it at one Toffoli per bit, with its
own uncomputation, using one scratch wire per bit. -/

/-- A field is zero exactly when every one of its bits is. -/
theorem readField_eq_zero_iff (i off w : Nat) :
    readField i off w = 0 ↔ ∀ b, b < w → i.testBit (off + b) = false := by
  constructor
  · intro h b hb
    have := testBit_readField i off w b
    rw [h] at this
    simp only [Nat.zero_testBit, decide_eq_true_eq] at this
    simpa [hb] using this.symm
  · intro h
    refine Nat.eq_of_testBit_eq fun b => ?_
    rw [testBit_readField, Nat.zero_testBit]
    by_cases hb : b < w
    · simp [hb, h b hb]
    · simp [hb]

/-- `dst ^= a ∨ b`, correct when `dst` starts clear. -/
def orInto (a b dst : Nat) : List RGate :=
  [RGate.cx a dst, RGate.cx b dst, RGate.ccx a b dst]

theorem bv_write_ne {j q d v : Nat} (h : q ≠ d) : bv (writeField j d 1 v) q = bv j q := by
  rw [← readField_one, readField_writeField_of_disjoint (by omega), readField_one]

/-- Off the target, the three gates change nothing. -/
theorem orInto_outside {a b dst : Nat} : ∀ (i q : Nat), q ≠ dst →
    bv (actGates (orInto a b dst) i) q = bv i q := by
  intro i q h
  show bv (RGate.act (RGate.ccx a b dst) (RGate.act (RGate.cx b dst)
    (RGate.act (RGate.cx a dst) i))) q = bv i q
  rw [act_ccx, bv_write_ne h, act_cx, bv_write_ne h, act_cx, bv_write_ne h]

/-- A clear target ends holding the or. -/
theorem orInto_act {a b dst : Nat} (hda : a ≠ dst) (hdb : b ≠ dst) : ∀ (i : Nat),
    bv i dst = 0 →
    bv (actGates (orInto a b dst) i) dst = (if bv i a = 0 ∧ bv i b = 0 then 0 else 1) := by
  intro i h0
  have ha := bv_lt i a
  have hb := bv_lt i b
  show bv (RGate.act (RGate.ccx a b dst) (RGate.act (RGate.cx b dst)
    (RGate.act (RGate.cx a dst) i))) dst = _
  rw [act_ccx, bv_write_self, act_cx, bv_write_self, act_cx, bv_write_self]
  simp only [bv_write_ne hda, bv_write_ne hdb, h0]
  rcases (by omega : bv i a = 0 ∨ bv i a = 1) with h | h <;>
    rcases (by omega : bv i b = 0 ∨ bv i b = 1) with h' | h' <;> simp [h, h']

/-- The running or of a field's low bits, one scratch wire per bit.  Wire
`sc + w - 1` ends holding the or of `src` through `src + w - 1`. -/
def orLadder (src sc : Nat) : Nat → List RGate
  | 0 => []
  | 1 => [RGate.cx src sc]
  | k + 2 => orLadder src sc (k + 1) ++ orInto (sc + k) (src + k + 1) (sc + k + 1)

/-- The ladder touches only the scratch wires it uses and the field it reads. -/
theorem orLadder_wires (src sc : Nat) : ∀ (w : Nat), ∀ g ∈ orLadder src sc w, ∀ q ∈ g.wires,
    (sc ≤ q ∧ q < sc + w) ∨ (src ≤ q ∧ q < src + w)
  | 0 => by intro g hg; simp [orLadder] at hg
  | 1 => by
      intro g hg q hq
      simp only [orLadder, List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact Or.inr ⟨Nat.le_refl _, by omega⟩
      · exact Or.inl ⟨Nat.le_refl _, by omega⟩
  | k + 2 => by
      intro g hg q hq
      rw [show orLadder src sc (k + 2)
        = orLadder src sc (k + 1) ++ orInto (sc + k) (src + k + 1) (sc + k + 1) from rfl,
        List.mem_append] at hg
      cases hg with
      | inl h => have := orLadder_wires src sc (k + 1) g h q hq; omega
      | inr h =>
        simp only [orInto, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl <;>
          simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;> omega

/-- The ladder writes only the `w` scratch wires it uses. -/
theorem orLadder_outside (src sc : Nat) :
    ∀ (w i q : Nat), (q < sc ∨ sc + w ≤ q) →
      bv (actGates (orLadder src sc w) i) q = bv i q
  | 0, _, _, _ => rfl
  | 1, i, q, hq => by
      show bv (RGate.act (RGate.cx src sc) i) q = bv i q
      rw [act_cx, bv_write_ne (by omega)]
  | k + 2, i, q, hq => by
      show bv (actGates (orLadder src sc (k + 1)
        ++ orInto (sc + k) (src + k + 1) (sc + k + 1)) i) q = bv i q
      rw [actGates_append, orInto_outside _ q (by omega),
        orLadder_outside src sc (k + 1) i q (by omega)]

/-- The ladder's top wire is the or of the field's bits. -/
theorem orLadder_top (src sc W : Nat) (hd : src + W ≤ sc ∨ sc + W ≤ src) :
    ∀ (w i : Nat), 0 < w → w ≤ W → readField i sc W = 0 →
      bv (actGates (orLadder src sc w) i) (sc + w - 1)
        = (if readField i src w = 0 then 0 else 1)
  | 0, _, h, _, _ => absurd h (Nat.lt_irrefl 0)
  | 1, i, _, hw, hsc => by
      have hz : bv i sc = 0 := by
        have h0 := (readField_eq_zero_iff i sc W).mp hsc 0 (by omega)
        rw [Nat.add_zero] at h0
        simp [bv, h0]
      have hb := bv_lt i src
      show bv (RGate.act (RGate.cx src sc) i) (sc + 1 - 1) = _
      rw [act_cx, show sc + 1 - 1 = sc from by omega, bv_write_self, hz, Nat.zero_add,
        readField_one]
      rcases (by omega : bv i src = 0 ∨ bv i src = 1) with h | h <;> simp [h]
  | k + 2, i, _, hw, hsc => by
      have hih := orLadder_top src sc W hd (k + 1) i (by omega) (by omega) hsc
      have hout := orLadder_outside src sc (k + 1) i
      have hsrcb : bv (actGates (orLadder src sc (k + 1)) i) (src + k + 1) = bv i (src + k + 1) :=
        hout (src + k + 1) (by omega)
      have hdstz : bv (actGates (orLadder src sc (k + 1)) i) (sc + k + 1) = 0 := by
        rw [hout (sc + k + 1) (by omega)]
        have h0 := (readField_eq_zero_iff i sc W).mp hsc (k + 1) (by omega)
        rw [show sc + (k + 1) = sc + k + 1 from by omega] at h0
        simp [bv, h0]
      have hacc : bv (actGates (orLadder src sc (k + 1)) i) (sc + k)
          = (if readField i src (k + 1) = 0 then 0 else 1) := by
        rw [show sc + k = sc + (k + 1) - 1 from by omega]; exact hih
      have hsplit : readField i src (k + 2) = 0
          ↔ readField i src (k + 1) = 0 ∧ i.testBit (src + (k + 1)) = false := by
        rw [readField_eq_zero_iff, readField_eq_zero_iff]
        constructor
        · intro h
          exact ⟨fun b hb => h b (by omega), h (k + 1) (by omega)⟩
        · intro ⟨h1, h2⟩ b hb
          rcases (by omega : b < k + 1 ∨ b = k + 1) with hb' | rfl
          · exact h1 b hb'
          · exact h2
      have hsrceq : bv i (src + k + 1) = if i.testBit (src + (k + 1)) then 1 else 0 := by
        simp only [bv, show src + k + 1 = src + (k + 1) from by omega]
      show bv (actGates (orLadder src sc (k + 1)
        ++ orInto (sc + k) (src + k + 1) (sc + k + 1)) i) (sc + (k + 2) - 1) = _
      rw [actGates_append, show sc + (k + 2) - 1 = sc + k + 1 from by omega,
        orInto_act (by omega) (by omega) _ hdstz, hacc, hsrcb, hsrceq]
      by_cases h1 : readField i src (k + 1) = 0 <;>
        by_cases h2 : i.testBit (src + (k + 1)) <;>
        simp [h1, h2, hsplit]

/-- The zero test: one Toffoli per bit, and its uncomputation. -/
def nzTest (src sc tgt w : Nat) : List RGate :=
  orLadder src sc w ++ [RGate.cx (sc + w - 1) tgt] ++ (orLadder src sc w).reverse

theorem orLadder_ccx (src sc : Nat) : ∀ (w : Nat),
    (orLadder src sc w).countP RGate.isCcx = w - 1
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    show (orLadder src sc (k + 1) ++ orInto (sc + k) (src + k + 1) (sc + k + 1)).countP _ = _
    rw [List.countP_append, orLadder_ccx src sc (k + 1),
      show List.countP RGate.isCcx (orInto (sc + k) (src + k + 1) (sc + k + 1)) = 1 from rfl]
    omega

theorem orLadder_len (src sc : Nat) : ∀ (w : Nat), (orLadder src sc w).length = 3 * w - 2
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    show (orLadder src sc (k + 1) ++ orInto (sc + k) (src + k + 1) (sc + k + 1)).length = _
    rw [List.length_append, orLadder_len src sc (k + 1),
      show (orInto (sc + k) (src + k + 1) (sc + k + 1)).length = 3 from rfl]
    omega

theorem orLadder_wf (src sc : Nat) : ∀ (w Wd : Nat), (src + w ≤ sc ∨ sc + w ≤ src) →
    src + w ≤ Wd → sc + w ≤ Wd → (orLadder src sc w).all (RGate.wellFormed Wd) = true
  | 0, _, _, _, _ => by simp [orLadder]
  | 1, Wd, hd, h1, h2 => by
      show ([RGate.cx src sc]).all _ = true
      simp [RGate.wellFormed]
      omega
  | k + 2, Wd, hd, h1, h2 => by
      show (orLadder src sc (k + 1) ++ orInto (sc + k) (src + k + 1) (sc + k + 1)).all _ = true
      rw [List.all_append, Bool.and_eq_true]
      refine ⟨orLadder_wf src sc (k + 1) Wd (by omega) (by omega) (by omega), ?_⟩
      show ([RGate.cx (sc + k) (sc + k + 1), RGate.cx (src + k + 1) (sc + k + 1),
        RGate.ccx (sc + k) (src + k + 1) (sc + k + 1)]).all _ = true
      simp [RGate.wellFormed]
      omega

theorem nzTest_wires (src sc tgt : Nat) : ∀ (w : Nat), 0 < w →
    ∀ g ∈ nzTest src sc tgt w, ∀ q ∈ g.wires,
    q = tgt ∨ (sc ≤ q ∧ q < sc + w) ∨ (src ≤ q ∧ q < src + w) := by
  intro w hw g hg q hq
  have hg' : g ∈ orLadder src sc w ++ [RGate.cx (sc + w - 1) tgt]
    ++ (orLadder src sc w).reverse := hg
  rw [List.mem_append, List.mem_append] at hg'
  rcases hg' with (h | h) | h
  · exact Or.inr (orLadder_wires src sc w g h q hq)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inl rfl
  · exact Or.inr (orLadder_wires src sc w g (List.mem_reverse.mp h) q hq)

theorem nzTest_wf (src sc tgt w Wd : Nat) (hw : 0 < w) (hd : src + w ≤ sc ∨ sc + w ≤ src)
    (hts : tgt < sc ∨ sc + w ≤ tgt)
    (h1 : src + w ≤ Wd) (h2 : sc + w ≤ Wd) (h3 : tgt < Wd) :
    (nzTest src sc tgt w).all (RGate.wellFormed Wd) = true := by
  have hlad := orLadder_wf src sc w Wd hd h1 h2
  show (orLadder src sc w ++ [RGate.cx (sc + w - 1) tgt]
    ++ (orLadder src sc w).reverse).all _ = true
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨hlad, ?_⟩, List.all_eq_true.mpr fun g hg =>
    List.all_eq_true.mp hlad g (List.mem_reverse.mp hg)⟩
  simp [RGate.wellFormed]
  omega

/-- The zero test writes `v ≠ 0` and leaves the scratch clear. -/
theorem nzTest_act {src sc tgt w Wd : Nat} (hw : 0 < w)
    (hd : src + w ≤ sc ∨ sc + w ≤ src) (hts : tgt < sc ∨ sc + w ≤ tgt)
    (htr : tgt < src ∨ src + w ≤ tgt)
    (h1 : src + w ≤ Wd) (h2 : sc + w ≤ Wd) (h3 : tgt < Wd)
    (i : Nat) (hsc : readField i sc w = 0) :
    actGates (nzTest src sc tgt w) i
      = writeField i tgt 1 ((bv i tgt + if readField i src w = 0 then 0 else 1) % 2) := by
  have hcp : ∀ j, actGates [RGate.cx (sc + w - 1) tgt] j
      = writeField j tgt 1 ((bv j tgt + bv j (sc + w - 1)) % 2) := by
    intro j
    show RGate.act (RGate.cx (sc + w - 1) tgt) j = _
    rw [act_cx]
  have hout : ∀ g ∈ orLadder src sc w, ∀ q ∈ g.wires, q < tgt ∨ tgt + 1 ≤ q := by
    intro g hg q hq
    have := orLadder_wires src sc w g hg q hq
    omega
  have hmain := actGates_compute_use_uncompute (gs := orLadder src sc w)
    (cp := [RGate.cx (sc + w - 1) tgt]) (w := Wd) (off := tgt) (len := 1)
    (orLadder_wf src sc w Wd hd h1 h2) hout hcp i
  show actGates (orLadder src sc w ++ [RGate.cx (sc + w - 1) tgt]
    ++ (orLadder src sc w).reverse) i = _
  rw [hmain, orLadder_outside src sc w i tgt (by omega),
    orLadder_top src sc w hd w i hw (Nat.le_refl _) hsc]

theorem nzTest_ccx (src sc tgt w : Nat) :
    (nzTest src sc tgt w).countP RGate.isCcx = 2 * (w - 1) := by
  show (orLadder src sc w ++ [RGate.cx (sc + w - 1) tgt]
    ++ (orLadder src sc w).reverse).countP _ = _
  rw [List.countP_append, List.countP_append, List.countP_reverse,
    orLadder_ccx src sc w,
    show List.countP RGate.isCcx [RGate.cx (sc + w - 1) tgt] = 0 from rfl]
  omega

theorem nzTest_len (src sc tgt w : Nat) (hw : 0 < w) :
    (nzTest src sc tgt w).length = 6 * w - 3 := by
  show (orLadder src sc w ++ [RGate.cx (sc + w - 1) tgt]
    ++ (orLadder src sc w).reverse).length = _
  rw [List.length_append, List.length_append, List.length_reverse,
    orLadder_len src sc w]
  simp only [List.length_cons, List.length_nil]
  omega


end VQ.Curve.PointAddition.Arithmetic.Inv
