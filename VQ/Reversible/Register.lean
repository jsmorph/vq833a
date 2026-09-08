/-
Registers inside a basis index.

A basis index is one natural number and a specification talks about registers,
so every point-addition claim passes through a decoding.  A field is a
contiguous run of `n` bits of the index starting at bit `off`.  `readField` and
`writeField` are the two directions of that decoding, and they take the offset
and the width as arguments so that neither commits to a particular assignment of
registers to bit ranges.  Both are built from shifts, masks, and `|||` rather
than from division, because every lemma here is proved bitwise through
`Nat.eq_of_testBit_eq`, and because the bitwise form reduces in the kernel on
concrete arguments.

A `Layout` fixes one assignment: it is the list of field widths from bit zero
upward, so an offset is a partial sum and the fields are disjoint and contiguous
by construction.  Disjointness is then a theorem rather than a hypothesis a
caller supplies and could get wrong, which is the reason for deriving offsets
instead of listing explicit ranges.  The cost is that a layout cannot leave a
gap between two registers.  A gap is expressed as a field nothing reads.

`testBit_writeField_outside` states that writing a field preserves every bit
outside it.  `Layout.ext` derives equality of indices from agreement on every
field.  `Layout.pack_lt` bounds an index assembled from field values below
`2 ^ width` because `pack` reduces each value to its field width.  Since
`readField` is a remainder, every decoded field value satisfies its range bound
without a hypothesis on the index.
-/
import VQ.Reversible.Act

namespace VQ
namespace Reversible

/-! ## Fields at an explicit offset -/

/-- The value held by the `n` bits of `i` starting at bit `off`. -/
def readField (i off n : Nat) : Nat := (i >>> off) % 2 ^ n

/-- `i` with the `n` bits starting at bit `off` replaced by the low `n` bits of
`v`.  The three parts are the bits below the field, the bits above it, and the
new value shifted into place. -/
def writeField (i off n v : Nat) : Nat :=
  (i % 2 ^ off ||| (i >>> (off + n)) <<< (off + n)) ||| (v % 2 ^ n) <<< off

/-! ### The bits of a field operation

The read and write bit lemmas support the remaining field identities through
`Nat.eq_of_testBit_eq`. -/

/-- Bit `b` of a field is bit `off + b` of the index, and the field has no bits
at or above its width. -/
theorem testBit_readField (i off n b : Nat) :
    (readField i off n).testBit b = (decide (b < n) && i.testBit (off + b)) := by
  simp [readField]

/-- Inside the field, a write shows the value written. -/
theorem testBit_writeField_inside {i off n v b : Nat} (hlo : off ≤ b) (hhi : b < off + n) :
    (writeField i off n v).testBit b = v.testBit (b - off) := by
  have hb : ¬ b < off := by omega
  have hab : ¬ off + n ≤ b := by omega
  have hsub : b - off < n := by omega
  simp [writeField, hb, hab, hsub, hlo]

/-- Outside the field, a write changes nothing.  This is the statement a
correctness claim uses for "every bit outside the two registers is
unchanged". -/
theorem testBit_writeField_outside {i off n v b : Nat} (h : b < off ∨ off + n ≤ b) :
    (writeField i off n v).testBit b = i.testBit b := by
  rcases h with h | h
  · have hab : ¬ off + n ≤ b := by omega
    have hoff : ¬ off ≤ b := by omega
    simp [writeField, h, hab, hoff]
  · have hb : ¬ b < off := by omega
    have hsub : ¬ b - off < n := by omega
    have hoff : off ≤ b := by omega
    have hcancel : off + n + (b - (off + n)) = b := by omega
    simp [writeField, hb, hsub, hoff, h, hcancel]

/-! ### Reading a field -/

/-- A field is below its own width, whatever the index.  There is no hypothesis
to discharge here: `readField` is a remainder. -/
theorem readField_lt (i off n : Nat) : readField i off n < 2 ^ n :=
  Nat.mod_lt _ (Nat.two_pow_pos n)

/-- Reading a field after shifting `i` skips the preceding field, supporting
induction over the remaining layout. -/
theorem readField_shiftRight (i a b n : Nat) :
    readField i (a + b) n = readField (i >>> a) b n := by
  rw [readField, readField, Nat.shiftRight_add]

/-- Reading at offset zero is a remainder. -/
theorem readField_zero (i n : Nat) : readField i 0 n = i % 2 ^ n := rfl

/-- A one-wire field is the natural-number encoding of that wire's Boolean
value.  This connects register specifications using `0` and `1` to coherent
control theorems stated with `testBit`.  The equality holds at every index and
offset without a width hypothesis. -/
theorem readField_one_eq_if (i q : Nat) :
    readField i q 1 = if i.testBit q then 1 else 0 := by
  have h : (i >>> q).testBit 0 = i.testBit q := by simp
  show (i >>> q) % 2 ^ 1 = if i.testBit q then 1 else 0
  rw [Nat.pow_one, ← h, Nat.testBit_zero]
  by_cases hx : (i >>> q) % 2 = 1 <;> simp [hx] <;> omega

/-- An empty field holds nothing. -/
theorem readField_size_zero (i off : Nat) : readField i off 0 = 0 := by
  rw [readField, Nat.pow_zero, Nat.mod_one]

/-! ### Writing a field -/

/-- Reading a field immediately after writing it gives the value reduced modulo
the field width. -/
theorem readField_writeField (i off n v : Nat) :
    readField (writeField i off n v) off n = v % 2 ^ n := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  rw [testBit_readField, Nat.testBit_mod_two_pow]
  by_cases hb : b < n
  · rw [testBit_writeField_inside (Nat.le_add_right off b) (by omega)]
    simp [hb]
  · simp [hb]

/-- Writing a field back the value it already holds changes nothing.
`readField` extracts exactly the bits that `writeField` replaces.  The identity
holds for every offset and length. -/
theorem writeField_read (i off len : Nat) :
    writeField i off len (readField i off len) = i := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases hlo : off ≤ b
  · by_cases hhi : b < off + len
    · rw [testBit_writeField_inside hlo hhi, testBit_readField]
      simp [show b - off < len by omega, show off + (b - off) = b by omega]
    · rw [testBit_writeField_outside (Or.inr (by omega))]
  · rw [testBit_writeField_outside (Or.inl (by omega))]

/-- A clear field stays clear when read at a narrower width.  This transfers an
assembly's shared-workspace condition to each component's workspace prefix. -/
theorem readField_narrow {i off w w' : Nat} (h : w' ≤ w) (hz : readField i off w = 0) :
    readField i off w' = 0 := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, Nat.zero_testBit]
  by_cases hb : b < w'
  · have hb' : b < w := by omega
    have hbit := congrArg (fun j => Nat.testBit j b) hz
    simp only [testBit_readField, hb', decide_true, Bool.true_and, Nat.zero_testBit] at hbit
    simp [hb, hbit]
  · simp [hb]

/-- A wide field is clear exactly when its two halves are.  An assembly's
workspace is one field of the claim's layout and several of its own, and this is
what carries the workspace clause across. -/
theorem readField_split {i off a b : Nat} :
    readField i off (a + b) = 0 ↔ readField i off a = 0 ∧ readField i (off + a) b = 0 := by
  constructor
  · intro h
    refine ⟨readField_narrow (by omega) h, ?_⟩
    refine Nat.eq_of_testBit_eq fun k => ?_
    rw [testBit_readField, Nat.zero_testBit]
    by_cases hk : k < b
    · have hb := congrArg (fun j => Nat.testBit j (a + k)) h
      simp only [testBit_readField, Nat.zero_testBit, show a + k < a + b by omega,
        decide_true, Bool.true_and] at hb
      simp only [hk, decide_true, Bool.true_and, show off + a + k = off + (a + k) by omega]
      exact hb
    · simp [hk]
  · intro hpair
    refine Nat.eq_of_testBit_eq fun k => ?_
    rw [testBit_readField, Nat.zero_testBit]
    by_cases hk : k < a + b
    · by_cases hk2 : k < a
      · have hb := congrArg (fun j => Nat.testBit j k) hpair.1
        simp only [testBit_readField, Nat.zero_testBit, hk2, decide_true, Bool.true_and] at hb
        simp only [hk, decide_true, Bool.true_and]
        exact hb
      · have hb := congrArg (fun j => Nat.testBit j (k - a)) hpair.2
        simp only [testBit_readField, Nat.zero_testBit, show k - a < b by omega,
          decide_true, Bool.true_and, show off + a + (k - a) = off + k by omega] at hb
        simp only [hk, decide_true, Bool.true_and]
        exact hb
    · simp [hk]

/-- A sub-range of a clear field is clear.  An assembly whose workspace is one
field of the claim and many of its own uses this once per block, and there may be
hundreds of them, so it has to be a lemma rather than a chain of splits. -/
theorem readField_sub_zero {i off len o l : Nat} (h1 : off ≤ o) (h2 : o + l ≤ off + len)
    (hz : readField i off len = 0) : readField i o l = 0 := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, Nat.zero_testBit]
  by_cases hb : b < l
  · have hbit := congrArg (fun j => Nat.testBit j (o - off + b)) hz
    simp only [testBit_readField, Nat.zero_testBit,
      show o - off + b < len by omega, decide_true, Bool.true_and,
      show off + (o - off + b) = o + b by omega] at hbit
    simp [hb, hbit]
  · simp [hb]

/-- Writing the whole of an `n`-bit register replaces it.  A component whose
layout has one field at offset zero ends every correctness proof here. -/
theorem writeField_zero_eq {i n v : Nat} (hi : i < 2 ^ n) (hv : v < 2 ^ n) :
    writeField i 0 n v = v := by
  simp [writeField, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hi,
    Nat.mod_eq_of_lt hv, Nat.mod_one]

/-- Reading back a field immediately after writing it gives the value, when it
fits. -/
theorem readField_writeField_self {i off n v : Nat} (hv : v < 2 ^ n) :
    readField (writeField i off n v) off n = v := by
  rw [readField_writeField, Nat.mod_eq_of_lt hv]

/-- A write to one field is invisible to a field disjoint from it.  The
hypothesis is that the two bit ranges do not meet. -/
theorem readField_writeField_of_disjoint {i o₁ n₁ v o₂ n₂ : Nat}
    (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) :
    readField (writeField i o₁ n₁ v) o₂ n₂ = readField i o₂ n₂ := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  rw [testBit_readField, testBit_readField]
  by_cases hb : b < n₂
  · rw [testBit_writeField_outside (i := i) (off := o₁) (n := n₁) (v := v) (b := o₂ + b)
      (by omega)]
  · simp [hb]

/-- Reading a subfield immediately after writing the containing field gives the corresponding
subfield of the value. -/
theorem readField_writeField_subfield {i off width v inner len : Nat}
    (hfit : inner + len ≤ width) :
    readField (writeField i off width v) (off + inner) len =
      readField v inner len := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, testBit_readField]
  by_cases hb : b < len
  · simp only [hb, decide_true, Bool.true_and]
    rw [testBit_writeField_inside (by omega) (by omega)]
    congr 1
    omega
  · simp [hb]

/-- Two writes to the same field keep the second. -/
theorem writeField_writeField (i off n v u : Nat) :
    writeField (writeField i off n v) off n u = writeField i off n u := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases hlo : off ≤ b
  · by_cases hhi : b < off + n
    · rw [testBit_writeField_inside hlo hhi, testBit_writeField_inside hlo hhi]
    · rw [testBit_writeField_outside (Or.inr (by omega)),
        testBit_writeField_outside (Or.inr (by omega)),
        testBit_writeField_outside (Or.inr (by omega))]
  · rw [testBit_writeField_outside (Or.inl (by omega)),
      testBit_writeField_outside (Or.inl (by omega)),
      testBit_writeField_outside (Or.inl (by omega))]

/-- Writes to disjoint fields commute. -/
theorem writeField_comm {i o₁ n₁ v o₂ n₂ u : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) :
    writeField (writeField i o₁ n₁ v) o₂ n₂ u = writeField (writeField i o₂ n₂ u) o₁ n₁ v := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases h₁ : o₁ ≤ b ∧ b < o₁ + n₁
  · rw [testBit_writeField_outside (by omega), testBit_writeField_inside h₁.1 h₁.2,
      testBit_writeField_inside h₁.1 h₁.2]
  · by_cases h₂ : o₂ ≤ b ∧ b < o₂ + n₂
    · rw [testBit_writeField_inside h₂.1 h₂.2, testBit_writeField_outside (by omega),
        testBit_writeField_inside h₂.1 h₂.2]
    · rw [testBit_writeField_outside (by omega), testBit_writeField_outside (by omega),
        testBit_writeField_outside (by omega), testBit_writeField_outside (by omega)]

theorem writeField_overwrite_of_disjoint
    {i o₁ n₁ v o₂ n₂ u v' : Nat}
    (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) :
    writeField (writeField (writeField i o₁ n₁ v) o₂ n₂ u) o₁ n₁ v' =
      writeField (writeField i o₂ n₂ u) o₁ n₁ v' := by
  rw [writeField_comm (i := i) (o₁ := o₁) (n₁ := n₁)
    (o₂ := o₂) (n₂ := n₂) h, writeField_writeField]

theorem writeField_overwrite_two_of_disjoint
    {i o₁ n₁ v₁ o₂ n₂ v₂ u₁ u₂ : Nat}
    (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) :
    writeField
        (writeField (writeField (writeField i o₁ n₁ v₁) o₂ n₂ v₂)
          o₂ n₂ u₂)
        o₁ n₁ u₁ =
      writeField (writeField i o₂ n₂ u₂) o₁ n₁ u₁ := by
  rw [writeField_writeField, writeField_overwrite_of_disjoint h]

theorem writeField_overwrite_alternating_of_disjoint
    {i o₁ n₁ v₁ o₂ n₂ v₂ u₁ u₂ : Nat}
    (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) :
    writeField
        (writeField
          (writeField (writeField i o₁ n₁ v₁) o₂ n₂ v₂)
          o₁ n₁ u₁)
        o₂ n₂ u₂ =
      writeField (writeField i o₁ n₁ u₁) o₂ n₂ u₂ := by
  have h' : o₂ + n₂ ≤ o₁ ∨ o₁ + n₁ ≤ o₂ := h.elim Or.inr Or.inl
  rw [writeField_overwrite_of_disjoint (i := i) (o₁ := o₁) (n₁ := n₁)
    (o₂ := o₂) (n₂ := n₂) h,
    writeField_overwrite_of_disjoint (i := i) (o₁ := o₂) (n₁ := n₂)
      (o₂ := o₁) (n₂ := n₁) h']

/-- Replacing a subfield equals replacing its enclosing field with the same
subfield update applied to the enclosing value. -/
theorem writeField_subfield
    {i outerOffset outerWidth innerOffset innerWidth value : Nat}
    (hfit : innerOffset + innerWidth ≤ outerWidth) :
    writeField i (outerOffset + innerOffset) innerWidth value =
      writeField i outerOffset outerWidth
        (writeField (readField i outerOffset outerWidth)
          innerOffset innerWidth value) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases houter : outerOffset ≤ b ∧ b < outerOffset + outerWidth
  · rw [testBit_writeField_inside houter.1 houter.2]
    by_cases hinner : outerOffset + innerOffset ≤ b ∧
        b < outerOffset + innerOffset + innerWidth
    · rw [testBit_writeField_inside hinner.1 hinner.2,
        testBit_writeField_inside (by omega) (by omega)]
      congr 1
      omega
    · rw [testBit_writeField_outside (by omega),
        testBit_writeField_outside (by omega), testBit_readField]
      simp [show b - outerOffset < outerWidth by omega,
        show outerOffset + (b - outerOffset) = b by omega]
  · rw [testBit_writeField_outside (by omega),
      testBit_writeField_outside (by omega)]

theorem eq_write_three_fields
    {i j o₁ n₁ o₂ n₂ o₃ n₃ : Nat}
    (h₁₂ : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁)
    (h₁₃ : o₁ + n₁ ≤ o₃ ∨ o₃ + n₃ ≤ o₁)
    (h₂₃ : o₂ + n₂ ≤ o₃ ∨ o₃ + n₃ ≤ o₂)
    (hout : ∀ b,
      (b < o₁ ∨ o₁ + n₁ ≤ b) →
      (b < o₂ ∨ o₂ + n₂ ≤ b) →
      (b < o₃ ∨ o₃ + n₃ ≤ b) →
      j.testBit b = i.testBit b) :
    j = writeField
      (writeField
        (writeField i o₁ n₁ (readField j o₁ n₁))
        o₂ n₂ (readField j o₂ n₂))
      o₃ n₃ (readField j o₃ n₃) := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases h₁ : o₁ ≤ b ∧ b < o₁ + n₁
  · rw [testBit_writeField_outside (by rcases h₁₃ with h | h <;> omega),
      testBit_writeField_outside (by rcases h₁₂ with h | h <;> omega),
      testBit_writeField_inside h₁.1 h₁.2, testBit_readField]
    simp [show b - o₁ < n₁ by omega, show o₁ + (b - o₁) = b by omega]
  · by_cases h₂ : o₂ ≤ b ∧ b < o₂ + n₂
    · rw [testBit_writeField_outside (by rcases h₂₃ with h | h <;> omega),
        testBit_writeField_inside h₂.1 h₂.2, testBit_readField]
      simp [show b - o₂ < n₂ by omega,
        show o₂ + (b - o₂) = b by omega]
    · by_cases h₃ : o₃ ≤ b ∧ b < o₃ + n₃
      · rw [testBit_writeField_inside h₃.1 h₃.2, testBit_readField]
        simp [show b - o₃ < n₃ by omega,
          show o₃ + (b - o₃) = b by omega]
      · rw [testBit_writeField_outside (by omega),
          testBit_writeField_outside (by omega),
          testBit_writeField_outside (by omega)]
        exact hout b (by omega) (by omega) (by omega)

/-- Bits at or above `w` determine whether an index reaches `2 ^ w`.  An index
with all those bits false lies below that bound.  This is the converse direction
of `Nat.testBit_lt_two_pow`. -/
theorem lt_two_pow_of_testBit {x w : Nat} (h : ∀ b, w ≤ b → x.testBit b = false) : x < 2 ^ w := by
  rcases Nat.lt_or_ge x (2 ^ w) with hlt | hge
  · exact hlt
  · obtain ⟨b, hb, hbt⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow hge
    rw [h b hb] at hbt
    exact Bool.noConfusion hbt

/-- A write inside the addressed block stays inside it.  This is the bound a
claim about a fixed-width register needs. -/
theorem writeField_lt {i off n v w : Nat} (hw : off + n ≤ w) (hi : i < 2 ^ w) :
    writeField i off n v < 2 ^ w := by
  refine lt_two_pow_of_testBit (fun b hb => ?_)
  rw [testBit_writeField_outside (Or.inr (by omega))]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) hb))

/-! ## A layout

A layout is the list of field widths from bit zero upward.  Field `k` occupies
the bits from `offset k` to `offset k + size k`, and both are read off the list,
so no arithmetic relation between the fields has to be assumed. -/

/-- The widths of the fields of a basis index, from bit zero upward. -/
abbrev Layout := List Nat

namespace Layout

/-- The number of bits the layout addresses. -/
def width : Layout → Nat
  | [] => 0
  | n :: rest => n + width rest

/-- The first bit of field `k`.  A field past the end of the layout starts at
the top of it and is empty. -/
def offset : Layout → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | n :: rest, k + 1 => n + offset rest k

/-- The width of field `k`, and zero past the end of the layout. -/
def size : Layout → Nat → Nat
  | [], _ => 0
  | n :: _, 0 => n
  | _ :: rest, k + 1 => size rest k

/-- The value field `k` holds in the basis index `i`. -/
def read (l : Layout) (i k : Nat) : Nat := readField i (l.offset k) (l.size k)

/-- The basis index `i` with field `k` set to `v`. -/
def write (l : Layout) (i k v : Nat) : Nat := writeField i (l.offset k) (l.size k) v

/-- The index whose fields are `vs`, with each value reduced to its own field
and every bit above the layout zero. -/
def pack : Layout → List Nat → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | n :: rest, v :: vs => v % 2 ^ n ||| pack rest vs <<< n

/-- The fields of an index, in layout order. -/
def fields : Layout → Nat → List Nat
  | [], _ => []
  | n :: rest, i => i % 2 ^ n :: fields rest (i >>> n)

/-! ### Offsets and sizes -/

/-- The head of a layout occupies the low bits, so the widths add. -/
theorem width_cons (n : Nat) (rest : Layout) : width (n :: rest) = n + width rest := rfl

/-- Field zero is the low bits of the index. -/
theorem read_zero (n : Nat) (rest : Layout) (i : Nat) : read (n :: rest) i 0 = i % 2 ^ n := rfl

/-- Field `k + 1` of a layout is field `k` of its tail, read from the shifted
index.  Every induction over a layout runs through this. -/
theorem read_succ (n : Nat) (rest : Layout) (i k : Nat) :
    read (n :: rest) i (k + 1) = read rest (i >>> n) k :=
  readField_shiftRight i n (rest.offset k) (rest.size k)

/-- A field ends where the layout ends or earlier. -/
theorem offset_add_size_le_width (l : Layout) (k : Nat) : l.offset k + l.size k ≤ l.width := by
  induction l generalizing k with
  | nil => exact Nat.le_refl 0
  | cons n rest ih =>
    cases k with
    | zero =>
      show 0 + n ≤ n + Layout.width rest
      omega
    | succ k =>
      show n + Layout.offset rest k + Layout.size rest k ≤ n + Layout.width rest
      have := ih k
      omega

/-- An earlier field ends before a later field starts, so layout fields are
pairwise disjoint. -/
theorem offset_add_size_le_offset {l : Layout} {j k : Nat} (h : j < k) :
    l.offset j + l.size j ≤ l.offset k := by
  induction l generalizing j k with
  | nil => exact Nat.le_refl 0
  | cons n rest ih =>
    cases k with
    | zero => exact absurd h (Nat.not_lt_zero j)
    | succ k =>
      cases j with
      | zero =>
        show 0 + n ≤ n + Layout.offset rest k
        omega
      | succ j =>
        show n + Layout.offset rest j + Layout.size rest j ≤ n + Layout.offset rest k
        have := ih (Nat.lt_of_succ_lt_succ h)
        omega

/-- Two distinct fields of a layout do not meet. -/
theorem disjoint {l : Layout} {j k : Nat} (h : j ≠ k) :
    l.offset j + l.size j ≤ l.offset k ∨ l.offset k + l.size k ≤ l.offset j := by
  rcases Nat.lt_or_ge j k with hjk | hjk
  · exact Or.inl (offset_add_size_le_offset hjk)
  · exact Or.inr (offset_add_size_le_offset (by omega))

/-! ### Reading and writing a field of a layout -/

theorem read_lt (l : Layout) (i k : Nat) : l.read i k < 2 ^ l.size k := readField_lt _ _ _

theorem read_write_self {l : Layout} {i k v : Nat} (hv : v < 2 ^ l.size k) :
    l.read (l.write i k v) k = v := readField_writeField_self hv

theorem read_write_ne {l : Layout} {i j k v : Nat} (h : j ≠ k) :
    l.read (l.write i k v) j = l.read i j :=
  readField_writeField_of_disjoint (disjoint (Ne.symm h))

theorem write_read (l : Layout) (i k : Nat) : l.write i k (l.read i k) = i :=
  writeField_read _ _ _

theorem write_write_self (l : Layout) (i k v u : Nat) :
    l.write (l.write i k v) k u = l.write i k u := writeField_writeField _ _ _ _ _

theorem write_comm {l : Layout} {i j k v u : Nat} (h : j ≠ k) :
    l.write (l.write i j v) k u = l.write (l.write i k u) j v := writeField_comm (disjoint h)

/-- Writing a field of an index inside the layout's block keeps it inside. -/
theorem write_lt {l : Layout} {i k v : Nat} (hi : i < 2 ^ l.width) :
    l.write i k v < 2 ^ l.width := writeField_lt (offset_add_size_le_width l k) hi

/-! ### The layout addresses exactly `width` bits -/

/-- An assembled index is inside the block the layout addresses, whatever the
values assembled, because `pack` reduces each value to its own field. -/
theorem pack_lt (l : Layout) (vs : List Nat) : pack l vs < 2 ^ l.width := by
  induction l generalizing vs with
  | nil => exact Nat.two_pow_pos _
  | cons n rest ih =>
    cases vs with
    | nil => exact Nat.two_pow_pos _
    | cons v vs =>
      show (v % 2 ^ n ||| pack rest vs <<< n) < 2 ^ (n + Layout.width rest)
      refine Nat.or_lt_two_pow ?_ ?_
      · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos n))
          (Nat.pow_le_pow_right (by omega) (Nat.le_add_right n (Layout.width rest)))
      · rw [Nat.shiftLeft_eq, Nat.pow_add' 2 n (Layout.width rest)]
        exact (Nat.mul_lt_mul_right (Nat.two_pow_pos n)).mpr (ih vs)

theorem pack_cons_mod (n : Nat) (rest : Layout) (v : Nat) (vs : List Nat) :
    pack (n :: rest) (v :: vs) % 2 ^ n = v % 2 ^ n := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  simp only [pack, Nat.testBit_mod_two_pow, Nat.testBit_or,
    Nat.testBit_shiftLeft]
  by_cases hb : b < n
  · simp [hb, Nat.not_le.mpr hb]
  · simp [hb]

theorem pack_cons_shiftRight
    (n : Nat) (rest : Layout) (v : Nat) (vs : List Nat) :
    pack (n :: rest) (v :: vs) >>> n = pack rest vs := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  simp only [Nat.testBit_shiftRight, pack, Nat.testBit_or,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  simp [Nat.not_lt_of_ge (Nat.le_add_right n b)]

/-- Reading a packed field returns the corresponding list entry, reduced to
that field's width. -/
theorem read_pack (l : Layout) (vs : List Nat) (k : Nat) :
    l.read (l.pack vs) k = vs.getD k 0 % 2 ^ l.size k := by
  induction l generalizing vs k with
  | nil =>
      change 0 = vs.getD k 0 % 1
      rw [Nat.mod_one]
  | cons n rest ih =>
      cases vs with
      | nil => simp [pack, read, readField]
      | cons v vs =>
          cases k with
          | zero => exact pack_cons_mod n rest v vs
          | succ k =>
              rw [read_succ, pack_cons_shiftRight]
              exact ih vs k

/-- Splitting an index at bit `n` and putting it back together. -/
theorem mod_or_shiftLeft_shiftRight (a n : Nat) : a % 2 ^ n ||| (a >>> n) <<< n = a := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases h : b < n
  · simp [h, Nat.not_le.mpr h]
  · have hle : n ≤ b := Nat.le_of_not_lt h
    simp [h, hle, Nat.add_sub_cancel' hle]

/-- Field `k` of an index is entry `k` of its list of fields. -/
theorem getD_fields (l : Layout) (i k : Nat) : (l.fields i).getD k 0 = l.read i k := by
  induction l generalizing i k with
  | nil => exact (readField_size_zero i 0).symm
  | cons n rest ih =>
    cases k with
    | zero => rfl
    | succ k => rw [read_succ]; exact ih (i >>> n) k

/-- An index inside the block the layout addresses is the assembly of its own
fields.  With `pack_lt` this says the layout and the block determine each
other: `pack` and `fields` are mutually inverse between the indices below
`2 ^ width` and the field values. -/
theorem pack_fields {l : Layout} {i : Nat} (hi : i < 2 ^ l.width) : pack l (l.fields i) = i := by
  induction l generalizing i with
  | nil =>
    have h1 : i < 1 := hi
    show 0 = i
    omega
  | cons n rest ih =>
    have hi' : i < 2 ^ n * 2 ^ Layout.width rest := by rw [← Nat.pow_add]; exact hi
    have hshift : i >>> n < 2 ^ Layout.width rest := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_of_lt_mul hi'
    show (i % 2 ^ n) % 2 ^ n ||| pack rest (Layout.fields rest (i >>> n)) <<< n = i
    rw [Nat.mod_mod, ih hshift, mod_or_shiftLeft_shiftRight]

/-- The block the layout addresses is exactly the assembled indices.  This
is the bound in both directions: an index below `2 ^ width` is assembled from
field values, and anything assembled from field values is below `2 ^ width`.
Every value is reduced to its field by `pack`, so "the values are in range" is
not a hypothesis here. -/
theorem lt_width_iff_pack {l : Layout} {i : Nat} : i < 2 ^ l.width ↔ ∃ vs, pack l vs = i :=
  ⟨fun h => ⟨l.fields i, pack_fields h⟩, fun ⟨vs, hv⟩ => hv ▸ pack_lt l vs⟩

/-- Two indices inside the block agree exactly when every field agrees.  This
converts a register-level specification into an equation between basis
indices. -/
theorem ext {l : Layout} {i j : Nat} (hi : i < 2 ^ l.width) (hj : j < 2 ^ l.width)
    (h : ∀ k, k < l.length → l.read i k = l.read j k) : i = j := by
  induction l generalizing i j with
  | nil =>
    have hi' : i < 1 := hi
    have hj' : j < 1 := hj
    omega
  | cons n rest ih =>
    have hlow : i % 2 ^ n = j % 2 ^ n := h 0 (Nat.zero_lt_succ _)
    have hbound : ∀ x : Nat, x < 2 ^ (n + Layout.width rest) →
        x >>> n < 2 ^ Layout.width rest := by
      intro x hx
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hx)
    have hhigh : i >>> n = j >>> n := by
      refine ih (hbound i hi) (hbound j hj) (fun k hk => ?_)
      have := h (k + 1) (Nat.succ_lt_succ hk)
      rwa [read_succ, read_succ] at this
    calc i = 2 ^ n * (i / 2 ^ n) + i % 2 ^ n := (Nat.div_add_mod i (2 ^ n)).symm
      _ = 2 ^ n * (j / 2 ^ n) + j % 2 ^ n := by
          rw [hlow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, hhigh]
      _ = j := Nat.div_add_mod j (2 ^ n)

end Layout

/-! ## Carrying a register statement to a basis index

A correctness claim says that the action of a circuit on `i` leaves stated
values in two registers and everything else untouched, which as one equation
between basis indices is `act r i = l.write (l.write i k₁ v₁) k₂ v₂`.  The three
theorems here are what that equation yields: the values of the two registers,
the values of every other field, and the bits belonging to no field at all.  The
last of them is stated over bit ranges rather than over the layout, since
"outside the registers" has to mean every bit and not only the bits some field
names. -/

/-- A circuit's action written as two field writes determines every field of the
result.  The two registers hold what was written, and no other field moves. -/
theorem read_write_two {l : Layout} {i k₁ v₁ k₂ v₂ : Nat} (hk : k₁ ≠ k₂)
    (h₁ : v₁ < 2 ^ l.size k₁) (h₂ : v₂ < 2 ^ l.size k₂) :
    l.read (l.write (l.write i k₁ v₁) k₂ v₂) k₁ = v₁ ∧
      l.read (l.write (l.write i k₁ v₁) k₂ v₂) k₂ = v₂ ∧
      ∀ k, k ≠ k₁ → k ≠ k₂ → l.read (l.write (l.write i k₁ v₁) k₂ v₂) k = l.read i k :=
  ⟨by rw [Layout.read_write_ne hk, Layout.read_write_self h₁],
   Layout.read_write_self h₂,
   fun k h h' => by rw [Layout.read_write_ne h', Layout.read_write_ne h]⟩

/-- Every bit outside two fields is unchanged by writing them. -/
theorem testBit_write_two_outside {i o₁ n₁ v₁ o₂ n₂ v₂ b : Nat}
    (h₁ : b < o₁ ∨ o₁ + n₁ ≤ b) (h₂ : b < o₂ ∨ o₂ + n₂ ≤ b) :
    (writeField (writeField i o₁ n₁ v₁) o₂ n₂ v₂).testBit b = i.testBit b := by
  rw [testBit_writeField_outside h₂, testBit_writeField_outside h₁]

/-- The fields determine the action of a well-formed circuit when the layout
covers its width.  A claim proved register by register can therefore compose
with claims stated through `act`. -/
theorem act_eq_of_read {r : RCircuit} {l : Layout} (hw : l.width = r.width)
    (hr : r.wellFormed = true) {i j : Nat} (hi : i < 2 ^ r.width) (hj : j < 2 ^ l.width)
    (h : ∀ k, k < l.length → l.read (act r i) k = l.read j k) : act r i = j :=
  Layout.ext (hw ▸ act_lt hr hi) hj h

end Reversible
end VQ
