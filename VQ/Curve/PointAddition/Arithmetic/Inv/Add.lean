import VQ.Reversible.ArithmeticSpec
import VQ.Reversible.Compile

/-!
# Wrap-around adder component

Cuccaro, Draper, Kutin, and Moulton's ripple-carry adder, `quant-ph/0410184`,
with its `AddsWrap` proof.

Kaliski's round uses its addition, subtraction, and controlled-addition forms.
Subtraction is the adder run backwards, since `act` of a reversed circuit
inverts the action.  Comparison is the carry out of a subtraction, kept while
the subtraction is undone.
-/

open VQ VQ.Reversible

namespace VQ.Curve.PointAddition.Arithmetic.Inv.Add

/-! ## Circuit construction -/

/-- The wire carrying the carry into bit position `st`.  Position zero takes it
from the workspace wire `2 * n`.  Every later position takes it from the `a` wire
below, which the MAJ step has overwritten with that position's carry out. -/
def carryWire (n : Nat) : Nat → Nat
  | 0 => 2 * n
  | k + 1 => k

theorem carryWire_zero (n : Nat) : carryWire n 0 = 2 * n := rfl

theorem carryWire_succ (n k : Nat) : carryWire n (k + 1) = k := rfl

/-- Cuccaro's MAJ on the carry-in wire `c`, the addend wire `b`, and the augend
wire `a`.  It sends `(c, b, a)` to `(c ^^^ a, b ^^^ a, m)` with `m` the majority
of the three, which is the carry out of this position. -/
def maj (c b a : Nat) : List RGate :=
  [RGate.cx a b, RGate.cx a c, RGate.ccx c b a]

/-- Cuccaro's UMA, the two-CNOT form.  Run on the output of `maj` it restores
`c` and `a` and leaves the sum bit `a ^^^ b ^^^ c` on `b`. -/
def uma (c b a : Nat) : List RGate :=
  [RGate.ccx c b a, RGate.cx a c, RGate.cx c b]

/-- The MAJ/UMA chain over `m` bit positions starting at position `st`, on the
layout `[n, n, 1]`: augend bit `k` is wire `k`, addend bit `k` is wire `n + k`,
and the workspace is wire `2 * n`.  Structural recursion on the number of
positions.  Nesting the recursive call between the two halves supports a
single inductive correctness proof. -/
def body (n : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | st, m + 1 =>
    maj (carryWire n st) (n + st) st ++ body n (st + 1) m ++ uma (carryWire n st) (n + st) st

/-- The `n`-bit adder: two `n`-bit operands and one workspace wire. -/
def gen (n : Nat) : RCircuit := { width := 2 * n + 1, gates := body n 0 n }

/-! ## Well-formedness -/

theorem carry_lt {n st : Nat} (h : st < n) : carryWire n st < 2 * n + 1 := by
  cases st with
  | zero => rw [carryWire_zero]; omega
  | succ k => rw [carryWire_succ]; omega

theorem carry_ne_a {n st : Nat} (h : st < n) : carryWire n st ≠ st := by
  cases st with
  | zero => rw [carryWire_zero]; omega
  | succ k => rw [carryWire_succ]; omega

theorem carry_ne_b {n st : Nat} (h : st < n) : carryWire n st ≠ n + st := by
  cases st with
  | zero => rw [carryWire_zero]; omega
  | succ k => rw [carryWire_succ]; omega

theorem maj_wf {w c b a : Nat} (ha : a < w) (hb : b < w) (hc : c < w)
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    (maj c b a).all (RGate.wellFormed w) = true := by
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  have hbc : b ≠ c := Ne.symm hcb
  simp [maj, RGate.wellFormed, ha, hb, hc, hab, hac, hcb, hba, hca]

theorem uma_wf {w c b a : Nat} (ha : a < w) (hb : b < w) (hc : c < w)
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
    (uma c b a).all (RGate.wellFormed w) = true := by
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  have hbc : b ≠ c := Ne.symm hcb
  simp [uma, RGate.wellFormed, ha, hb, hc, hac, hcb, hba, hca]

theorem body_wf (n : Nat) : ∀ (m st : Nat), st + m ≤ n →
    (body n st m).all (RGate.wellFormed (2 * n + 1)) = true := by
  intro m
  induction m with
  | zero => intro st _; rfl
  | succ m ih =>
    intro st hst
    have hlt : st < n := by omega
    have ha : st < 2 * n + 1 := by omega
    have hb : n + st < 2 * n + 1 := by omega
    have hc := carry_lt hlt
    have hab : st ≠ n + st := by omega
    have hac : st ≠ carryWire n st := fun e => carry_ne_a hlt e.symm
    have hcb := carry_ne_b hlt
    simp only [body, List.all_append, Bool.and_eq_true]
    exact ⟨⟨maj_wf ha hb hc hab hac hcb, ih (st + 1) (by omega)⟩,
      uma_wf ha hb hc hab hac hcb⟩

theorem wf : ∀ n : Nat, VQ.Reversible.RCircuit.wellFormed (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen n) = true := by
  intro n
  exact body_wf n n 0 (by omega)

/-! ## Resource bounds

Each count is one induction over the chain.  `maj` and `uma` are three gates
each, one of them a Toffoli, so a chain of `m` positions is `6 * m` gates with
`2 * m` Toffolis and `4 * m` CNOTs, and the compiled circuit's counts follow
from the identities in `VQ.Reversible.Compile`. -/

theorem length_body (n : Nat) : ∀ (m st : Nat), (body n st m).length = 6 * m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
    intro st
    simp only [body, List.length_append, ih (st + 1), maj, uma, List.length_cons,
      List.length_nil]
    omega

theorem ccx_body (n : Nat) : ∀ (m st : Nat),
    (body n st m).countP RGate.isCcx = 2 * m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
    intro st
    have hm : (maj (carryWire n st) (n + st) st).countP RGate.isCcx = 1 := rfl
    have hu : (uma (carryWire n st) (n + st) st).countP RGate.isCcx = 1 := rfl
    simp only [body, List.countP_append, ih (st + 1), hm, hu]
    omega

theorem cx_body (n : Nat) : ∀ (m st : Nat),
    (body n st m).countP RGate.isCx = 4 * m := by
  intro m
  induction m with
  | zero => intro st; rfl
  | succ m ih =>
    intro st
    have hm : (maj (carryWire n st) (n + st) st).countP RGate.isCx = 2 := rfl
    have hu : (uma (carryWire n st) (n + st) st).countP RGate.isCx = 2 := rfl
    simp only [body, List.countP_append, ih (st + 1), hm, hu]
    omega

theorem toffoli_le : ∀ n : Nat,
    VQ.Circuit.toffoliCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen n)) ≤ 0 + n * 2 := by
  intro n
  rw [VQ.Reversible.toffoliCount_compile]
  show (body n 0 n).countP RGate.isCcx ≤ 0 + n * 2
  rw [ccx_body]
  omega

theorem cnot_le : ∀ n : Nat,
    VQ.Circuit.cnotCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen n)) ≤ 0 + n * 4 := by
  intro n
  rw [VQ.Reversible.cnotCount_compile]
  show (body n 0 n).countP RGate.isCx ≤ 0 + n * 4
  rw [cx_body]
  omega

theorem gates_le : ∀ n : Nat,
    VQ.Circuit.gateCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen n)) ≤ 0 + n * 10 := by
  intro n
  rw [VQ.Reversible.gateCount_compile]
  show (body n 0 n).length + 2 * (body n 0 n).countP RGate.isCcx ≤ 0 + n * 10
  rw [length_body, ccx_body]
  omega

/-! ### Wire bounds

`usedWires` counts the distinct wires a gate list names, which is the length of
a deduplicated list rather than a count over the gates, so the bound goes
through a pigeonhole: a deduplicated list whose entries all lie below `w` has at
most `w` entries. -/

theorem dedup_le : ∀ (k : Nat) (s l : List Nat), s.length ≤ k → (∀ x ∈ l, x ∈ s) →
    l.eraseDups.length ≤ s.length := by
  intro k
  induction k with
  | zero =>
    intro s l hs hl
    cases l with
    | nil => simp
    | cons a as =>
      have hnil : s = [] := List.eq_nil_of_length_eq_zero (by omega)
      have := hl a List.mem_cons_self
      rw [hnil] at this
      exact absurd this (by simp)
  | succ k ih =>
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

theorem compileGate_wires {g : RGate} {w : Nat} (h : g.wellFormed w = true) :
    ∀ p ∈ VQ.Reversible.compileGate g, ∀ q ∈ p.wires, q < w := by
  cases g <;>
    simp_all [VQ.Reversible.compileGate, VQ.Circuit.ccx, Gate.wires, RGate.wellFormed] <;>
    omega

theorem compile_wires_lt (n : Nat) :
    ∀ q ∈ (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen n)).gates.flatMap Gate.wires, q < 2 * n + 1 := by
  intro q hq
  obtain ⟨p, hp, hqp⟩ := List.exists_of_mem_flatMap hq
  have hp' : p ∈ (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen n).gates.flatMap VQ.Reversible.compileGate := hp
  obtain ⟨g, hg, hpg⟩ := List.exists_of_mem_flatMap hp'
  exact compileGate_wires (RCircuit.wellFormed_mem (wf n) hg) p hpg q hqp

theorem wires_le : ∀ n : Nat,
    VQ.Circuit.usedWires (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen n)) ≤ 1 + n * 2 := by
  intro n
  have h := dedup_le (2 * n + 1) (List.range (2 * n + 1))
    ((VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen n)).gates.flatMap Gate.wires)
    (by simp) (fun x hx => List.mem_range.mpr (compile_wires_lt n x hx))
  rw [List.length_range] at h
  show ((VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen n)).gates.flatMap Gate.wires).eraseDups.length ≤ 1 + n * 2
  omega

/-! ## Correctness

The proof runs on one basis index at a time.  `bv i q` is the value on wire `q`,
`readField i off len` is the value of a run of wires, and every gate's action is
a single-wire write, so the whole argument is arithmetic on `Nat` with no state
vector anywhere. -/

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

theorem readField_succ (i off m : Nat) :
    readField i off (m + 1) = bv i off + 2 * readField i (off + 1) m := by
  rw [← readField_one]
  show (i >>> off) % 2 ^ (m + 1) = (i >>> off) % 2 ^ 1 + 2 * ((i >>> (off + 1)) % 2 ^ m)
  rw [Nat.pow_one, Nat.pow_succ', Nat.mod_mul, Nat.shiftRight_add]
  simp [Nat.shiftRight_eq_div_pow]

theorem writeField_succ (i off m v : Nat) :
    writeField i off (m + 1) v = writeField (writeField i off 1 (v % 2)) (off + 1) m (v / 2) := by
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
    · by_cases h3 : b < off + (m + 1)
      · rw [testBit_writeField_inside (by omega) h3,
          testBit_writeField_inside (by omega) (by omega), Nat.testBit_div_two]
        congr 1
        omega
      · rw [testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_outside (Or.inr (by omega)),
          testBit_writeField_outside (Or.inr (by omega))]

/-! ### Single-gate write semantics

`x` never appears, and the other two gates write one wire each.  Neither
identity needs the wires to be distinct: a `cx` whose control is its target
writes the value the definition of `act` gives it either way. -/

theorem flip_eq (i q : Nat) : i ^^^ (1 <<< q) = writeField i q 1 ((bv i q + 1) % 2) := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases hb : b = q
  · subst hb
    rw [testBit_writeField_inside (Nat.le_refl _) (by omega), Nat.sub_self,
      Nat.one_shiftLeft, Nat.testBit_xor, Nat.testBit_two_pow_self]
    cases h : i.testBit b <;> simp [bv, h]
  · rw [testBit_writeField_outside (by omega), RGate.testBit_xor_of_ne hb]

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

/-! ### Full-adder halves

`maj` writes the three wires it names and nothing else, and the value it leaves
on the augend wire is the carry out, which for bit values is `(A + B + C) / 2`.
`uma` reverses the first two writes, restores the carry-in and augend, and
leaves the sum bit `(A + B + C) % 2` on the addend wire. -/

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

/-! ### Ripple-step semantics

`majState` names the index the MAJ half produces, so the rest of the step is
stated about a term of three writes rather than about the gate list. -/

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

/-- The three writes the UMA half adds on top of the inner chain collapse: the
augend wire and the carry-in wire are restored to what they held on entry, and
the addend wire keeps the sum bit. -/
theorem uma_collapse {i a b c A B C X m : Nat} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (hm : a + 1 + m ≤ b) (hc : c + 1 ≤ a ∨ b + 1 + m ≤ c)
    (hA : bv i a = A) (hA2 : A < 2) (hC : bv i c = C) (hC2 : C < 2) :
    writeField (writeField (writeField (writeField (majState i a b c A B C) (b + 1) m X)
        a 1 A) c 1 C) b 1 ((A + B + C) % 2)
      = writeField (writeField i b 1 ((A + B + C) % 2)) (b + 1) m X := by
  rw [writeField_comm (i := majState i a b c A B C) (o₁ := b + 1) (n₁ := m) (v := X)
        (o₂ := a) (n₂ := 1) (u := A) (Or.inr (by omega)),
    majState_restore_a hab hac hA hA2,
    writeField_comm (i := writeField (writeField i b 1 ((B + A) % 2)) c 1 ((C + A) % 2))
      (o₁ := b + 1) (n₁ := m) (v := X) (o₂ := c) (n₂ := 1) (u := C) (by omega),
    majState_restore_c hcb hC hC2,
    writeField_comm (i := writeField i b 1 ((B + A) % 2)) (o₁ := b + 1) (n₁ := m) (v := X)
      (o₂ := b) (n₂ := 1) (u := (A + B + C) % 2) (Or.inr (by omega)),
    writeField_writeField]

/-- One position of the ripple carry.  Given that the inner chain adds the
`m` positions above this one, the MAJ and UMA halves around it add `m + 1`
positions: the carry wire and the augend field come back unchanged, and the
addend field holds the sum modulo `2 ^ (m + 1)`.

`hm` places the augend field strictly below the addend field.  `hc` places the
carry-in wire below the augend field or above the addend field, making it
disjoint from both. -/
theorem adder_step {a b c m : Nat} (gs : List RGate) (i : Nat)
    (hm : a + 1 + m ≤ b) (hc : c + 1 ≤ a ∨ b + 1 + m ≤ c)
    (hinner : ∀ j, actGates gs j =
      writeField j (b + 1) m ((readField j (a + 1) m + readField j (b + 1) m + bv j a) % 2 ^ m)) :
    actGates (maj c b a ++ gs ++ uma c b a) i =
      writeField i b (m + 1)
        ((readField i a (m + 1) + readField i b (m + 1) + bv i c) % 2 ^ (m + 1)) := by
  have hab : a ≠ b := by omega
  have hac : a ≠ c := by omega
  have hcb : c ≠ b := by omega
  obtain ⟨A, hA⟩ : ∃ x, bv i a = x := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ x, bv i b = x := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ x, bv i c = x := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ x, readField i (a + 1) m = x := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ x, readField i (b + 1) m = x := ⟨_, rfl⟩
  have hA2 : A < 2 := hA ▸ bv_lt i a
  have hB2 : B < 2 := hB ▸ bv_lt i b
  have hC2 : C < 2 := hC ▸ bv_lt i c
  rw [readField_succ i a m, readField_succ i b m, hA, hB, hC, hA', hB']
  rw [actGates_append, actGates_append, act_maj' hab hac hcb hA hB hC,
    hinner (majState i a b c A B C),
    readField_majState (o := a + 1) (len := m) (by omega) (by omega) (by omega),
    readField_majState (o := b + 1) (len := m) (by omega) (by omega) (by omega),
    bv_majState_a hA2 hB2 hC2, hA', hB']
  obtain ⟨X, hX⟩ : ∃ x, (A' + B' + (A + B + C) / 2) % 2 ^ m = x := ⟨_, rfl⟩
  rw [hX]
  have hja : bv (writeField (majState i a b c A B C) (b + 1) m X) a = (A + B + C) / 2 := by
    rw [bv_write_out (Or.inl (by omega)), bv_majState_a hA2 hB2 hC2]
  have hjb : bv (writeField (majState i a b c A B C) (b + 1) m X) b = (B + A) % 2 := by
    rw [bv_write_out (Or.inl (by omega)), bv_majState_b hab hcb]
  have hjc : bv (writeField (majState i a b c A B C) (b + 1) m X) c = (C + A) % 2 := by
    rw [bv_write_out (by omega), bv_majState_c hac]
  have hpow : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
  have hV : (A + 2 * A' + (B + 2 * B') + C) % 2 ^ (m + 1) = (A + B + C) % 2 + 2 * X := by
    rw [hpow, Nat.mod_mul]
    have h1 : (A + 2 * A' + (B + 2 * B') + C) % 2 = (A + B + C) % 2 := by omega
    have h2 : (A + 2 * A' + (B + 2 * B') + C) / 2 = (A + B + C) / 2 + A' + B' := by omega
    have h3 : (A + B + C) / 2 + A' + B' = A' + B' + (A + B + C) / 2 := by omega
    rw [h1, h2, h3, hX]
  rw [act_uma hab hac hcb hA2 hB2 hC2 hja hjb hjc,
    uma_collapse hab hac hcb hm hc hA hA2 hC hC2,
    writeField_succ i b m ((A + 2 * A' + (B + 2 * B') + C) % 2 ^ (m + 1)), hV,
    show ((A + B + C) % 2 + 2 * X) % 2 = (A + B + C) % 2 by omega,
    show ((A + B + C) % 2 + 2 * X) / 2 = X by omega]

/-! ### Carry-chain semantics

One induction on the number of positions.  `adder_step` is the whole inductive
step, and the induction hypothesis is what it takes as `hinner`. -/

theorem body_act (n : Nat) : ∀ (m st i : Nat), st + m ≤ n →
    actGates (body n st m) i =
      writeField i (n + st) m
        ((readField i st m + readField i (n + st) m + bv i (carryWire n st)) % 2 ^ m) := by
  intro m
  induction m with
  | zero =>
    intro st i _
    rw [show body n st 0 = [] from rfl, actGates_nil, writeField_zero]
  | succ m ih =>
    intro st i hst
    have hc : carryWire n st + 1 ≤ st ∨ n + st + 1 + m ≤ carryWire n st := by
      cases st with
      | zero => right; rw [carryWire_zero]; omega
      | succ k => left; rw [carryWire_succ]; exact Nat.le_refl _
    exact adder_step (a := st) (b := n + st) (c := carryWire n st) (m := m)
      (body n (st + 1) m) i (by omega) hc (fun j => ih (st + 1) j (by omega))

theorem adds : ∀ n : Nat, VQ.Reversible.AddsWrap 1 n (VQ.Curve.PointAddition.Arithmetic.Inv.Add.gen n) := by
  intro n a b i _ h0 h1 h2
  have e0 : readField i 0 n = a := h0
  have e1 : readField i (n + 0) n = b := h1
  have e2 : readField i (2 * n) 1 = 0 := by
    have hoff : n + (n + 0) = 2 * n := by omega
    have : readField i (n + (n + 0)) 1 = 0 := h2
    rwa [hoff] at this
  have hc : bv i (carryWire n 0) = 0 := by
    rw [carryWire_zero, ← readField_one]
    exact e2
  have key := body_act n n 0 i (by omega)
  rw [hc, e0, e1] at key
  exact key

end VQ.Curve.PointAddition.Arithmetic.Inv.Add
