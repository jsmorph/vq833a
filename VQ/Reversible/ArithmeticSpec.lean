/-
Specifications for generic reversible arithmetic circuits.
The declarations fix layouts, value domains, output values, and cleanup conditions.
-/
import VQ.Reversible.Register

namespace VQ
namespace Reversible

/-- Two `n`-bit operands and a workspace.  The second operand is the target: it
is the field the result is written into. -/
def adderLayout (n ws : Nat) : Layout := [n, n, ws]

/-- The circuit adds the first operand into the second, modulo `m`, over
`adderLayout n ws`.

The operands are reduced because addition modulo `m` is the group operation on
that domain.  The basis-index equation fixes the first operand and workspace
while updating the target, so one clause states both the value and cleanup
conditions.  A modular adder may clear its reduction flag by comparing against
an operand, and that comparison also requires reduced operands.

An assembly using the adder must prove that each intermediate operand remains
below the modulus.  `AddsPoint` retains separate value and workspace domains:
its workspace condition also covers points below the prime that lie off the
curve.  Its documentation states the two exclusions from that domain.

The condition `m ≤ 2 ^ n` ensures that every residue fits in the target field.
At a smaller width, every representable operand can lie below `m` while the
required residue lies outside the field.  The specification therefore includes
the width condition in the value clause. -/
def AddsMod (m ws n : Nat) (r : RCircuit) : Prop :=
  ∀ a b i, i < 2 ^ (adderLayout n ws).width →
    (adderLayout n ws).read i 0 = a →
    (adderLayout n ws).read i 1 = b →
    (adderLayout n ws).read i 2 = 0 →
    m ≤ 2 ^ n → a < m → b < m →
      act r i = (adderLayout n ws).write i 1 ((a + b) % m)

/-- `AddsMod` yields the sum in the target field while preserving the first
operand and clearing the workspace. -/
theorem addsMod_read {m ws n : Nat} {r : RCircuit} (h : AddsMod m ws n r)
    {a b i : Nat} (hi : i < 2 ^ (adderLayout n ws).width)
    (h₀ : (adderLayout n ws).read i 0 = a)
    (h₁ : (adderLayout n ws).read i 1 = b)
    (h₂ : (adderLayout n ws).read i 2 = 0)
    (ha : a < m) (hb : b < m) (hm : m ≤ 2 ^ n) :
    (adderLayout n ws).read (act r i) 0 = a ∧
      (adderLayout n ws).read (act r i) 1 = (a + b) % m ∧
      (adderLayout n ws).read (act r i) 2 = 0 := by
  have hsum : (a + b) % m < 2 ^ (adderLayout n ws).size 1 :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a) ha))
      hm) (Nat.le_refl _)
  have heq := h a b i hi h₀ h₁ h₂ hm ha hb
  refine ⟨?_, ?_, ?_⟩
  · rw [heq, Layout.read_write_ne (by decide), h₀]
  · rw [heq, Layout.read_write_self hsum]
  · rw [heq, Layout.read_write_ne (by decide), h₂]

/-- The circuit subtracts the first operand from the second, modulo `m`, over
`adderLayout n ws`.  The basis-index equation fixes the preserved first
operand, updated second operand, and workspace in one clause.  The affine
addition formula uses the differences `y - b` and `x - x₃`.
`SubsMod` states those operations directly.  Expressing either through
`AddsMod` would require a separate modular-negation circuit. -/
def SubsMod (m ws n : Nat) (r : RCircuit) : Prop :=
  ∀ a b i, i < 2 ^ (adderLayout n ws).width →
    (adderLayout n ws).read i 0 = a →
    (adderLayout n ws).read i 1 = b →
    (adderLayout n ws).read i 2 = 0 →
    m ≤ 2 ^ n → a < m → b < m →
      act r i = (adderLayout n ws).write i 1 ((b + (m - a)) % m)

/-- `SubsMod` preserves the first operand.  The target contains the modular
difference, and the workspace remains zero.  The difference is written
`(b + (m - a)) % m` rather than with subtraction,
because `Nat` subtraction truncates and `b - a` would be zero wherever `a`
exceeds `b`.  On reduced operands the two agree with the field difference. -/
theorem subsMod_read {m ws n : Nat} {r : RCircuit} (h : SubsMod m ws n r)
    {a b i : Nat} (hi : i < 2 ^ (adderLayout n ws).width)
    (h₀ : (adderLayout n ws).read i 0 = a)
    (h₁ : (adderLayout n ws).read i 1 = b)
    (h₂ : (adderLayout n ws).read i 2 = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) (hb : b < m) :
    (adderLayout n ws).read (act r i) 0 = a ∧
      (adderLayout n ws).read (act r i) 1 = (b + (m - a)) % m ∧
      (adderLayout n ws).read (act r i) 2 = 0 := by
  have hdiff : (b + (m - a)) % m < 2 ^ (adderLayout n ws).size 1 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a) ha)) hm
  have heq := h a b i hi h₀ h₁ h₂ hm ha hb
  refine ⟨?_, ?_, ?_⟩
  · rw [heq, Layout.read_write_ne (by decide), h₀]
  · rw [heq, Layout.read_write_self hdiff]
  · rw [heq, Layout.read_write_ne (by decide), h₂]

/-- The circuit adds the first operand into the second modulo `2 ^ n`, over
`adderLayout n ws`: an `n`-bit adder with the carry out discarded.

`AddsWrap` specializes modular addition to the width-dependent modulus
`2 ^ n` and serves as a component of modular adders.  Every `n`-bit operand
lies below that modulus, and the reduced sum fits in the target field, so its
value clause requires no range guard. -/
def AddsWrap (ws n : Nat) (r : RCircuit) : Prop :=
  ∀ a b i, i < 2 ^ (adderLayout n ws).width →
    (adderLayout n ws).read i 0 = a →
    (adderLayout n ws).read i 1 = b →
    (adderLayout n ws).read i 2 = 0 →
    act r i = (adderLayout n ws).write i 1 ((a + b) % 2 ^ n)

/-- `AddsWrap` preserves the first operand.  The target contains the wrapped
sum.  The workspace remains zero. -/
theorem addsWrap_read {ws n : Nat} {r : RCircuit} (h : AddsWrap ws n r)
    {a b i : Nat} (hi : i < 2 ^ (adderLayout n ws).width)
    (h₀ : (adderLayout n ws).read i 0 = a)
    (h₁ : (adderLayout n ws).read i 1 = b)
    (h₂ : (adderLayout n ws).read i 2 = 0) :
    (adderLayout n ws).read (act r i) 0 = a ∧
      (adderLayout n ws).read (act r i) 1 = (a + b) % 2 ^ n ∧
      (adderLayout n ws).read (act r i) 2 = 0 := by
  have hsum : (a + b) % 2 ^ n < 2 ^ (adderLayout n ws).size 1 :=
    Nat.mod_lt _ (Nat.two_pow_pos n)
  have heq := h a b i hi h₀ h₁ h₂
  refine ⟨?_, ?_, ?_⟩
  · rw [heq, Layout.read_write_ne (by decide), h₀]
  · rw [heq, Layout.read_write_self hsum]
  · rw [heq, Layout.read_write_ne (by decide), h₂]

/-- Two operands, the source circuit's workspace, one coherent control, and one
control-decomposition wire.  The fields occur in that order so an existing
adder occupies the low `2 * n + ws` wires without relabelling.  Both one-bit
fields belong to the quantum circuit rather than to `Program`'s classical data. -/
def controlledAdderLayout (n ws : Nat) : Layout := [n, n, ws, 1, 1]

/-- A coherently controlled modular adder.  A clear control fixes the complete
basis index, while a set control adds the source into the target modulo `m`.
Both operands must be reduced, and both workspace fields return to zero. -/
def ControlledAddsMod (m ws n : Nat) (r : RCircuit) : Prop :=
  ∀ (enabled : Bool) a b i, i < 2 ^ (controlledAdderLayout n ws).width →
    (controlledAdderLayout n ws).read i 0 = a →
    (controlledAdderLayout n ws).read i 1 = b →
    (controlledAdderLayout n ws).read i 2 = 0 →
    (controlledAdderLayout n ws).read i 3 =
      (if enabled = true then 1 else 0) →
    (controlledAdderLayout n ws).read i 4 = 0 →
    m ≤ 2 ^ n → a < m → b < m →
    act r i = if enabled = true then
      (controlledAdderLayout n ws).write i 1 ((a + b) % m)
    else i

/-- A coherently controlled modular subtractor.  A clear control fixes the
complete basis index, while a set control subtracts the source from the target
modulo `m`.  Both operands must be reduced, and both workspace fields return to
zero. -/
def ControlledSubsMod (m ws n : Nat) (r : RCircuit) : Prop :=
  ∀ (enabled : Bool) a b i, i < 2 ^ (controlledAdderLayout n ws).width →
    (controlledAdderLayout n ws).read i 0 = a →
    (controlledAdderLayout n ws).read i 1 = b →
    (controlledAdderLayout n ws).read i 2 = 0 →
    (controlledAdderLayout n ws).read i 3 =
      (if enabled = true then 1 else 0) →
    (controlledAdderLayout n ws).read i 4 = 0 →
    m ≤ 2 ^ n → a < m → b < m →
    act r i = if enabled = true then
      (controlledAdderLayout n ws).write i 1 ((b + (m - a)) % m)
    else i

/-- The field form of `ControlledAddsMod`.  It states the conditional modular
sum while retaining the reduced-input domain.  The remaining conjuncts state
source preservation, control preservation, and cleanup of both workspaces. -/
theorem controlledAddsMod_read {m ws n : Nat} {r : RCircuit}
    (h : ControlledAddsMod m ws n r) {enabled : Bool} {a b i : Nat}
    (hi : i < 2 ^ (controlledAdderLayout n ws).width)
    (h₀ : (controlledAdderLayout n ws).read i 0 = a)
    (h₁ : (controlledAdderLayout n ws).read i 1 = b)
    (h₂ : (controlledAdderLayout n ws).read i 2 = 0)
    (h₃ : (controlledAdderLayout n ws).read i 3 = if enabled = true then 1 else 0)
    (h₄ : (controlledAdderLayout n ws).read i 4 = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) (hb : b < m) :
    (controlledAdderLayout n ws).read (act r i) 0 = a ∧
      (controlledAdderLayout n ws).read (act r i) 1 =
        (if enabled = true then (a + b) % m else b) ∧
      (controlledAdderLayout n ws).read (act r i) 2 = 0 ∧
      (controlledAdderLayout n ws).read (act r i) 3 =
        (if enabled = true then 1 else 0) ∧
      (controlledAdderLayout n ws).read (act r i) 4 = 0 := by
  have heq := h enabled a b i hi h₀ h₁ h₂ h₃ h₄ hm ha hb
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at heq h₃ ⊢
      rw [heq, h₀, h₁, h₂, h₃, h₄]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | true =>
      have hsum : (a + b) % m < 2 ^ (controlledAdderLayout n ws).size 1 := by
        change (a + b) % m < 2 ^ n
        exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hm
      simp only [if_true] at heq h₃ ⊢
      rw [heq, Layout.read_write_ne (by decide), h₀,
        Layout.read_write_self hsum, Layout.read_write_ne (by decide), h₂,
        Layout.read_write_ne (by decide), h₃,
        Layout.read_write_ne (by decide), h₄]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A coherently controlled wrapped adder.  A clear control fixes the complete
basis index, while a set control adds the source into the target modulo `2 ^ n`.
Both clauses preserve the control and return the source workspace and the
control-decomposition wire to zero because the equation fixes every field. -/
def ControlledAddsWrap (ws n : Nat) (r : RCircuit) : Prop :=
  ∀ (enabled : Bool) a b i, i < 2 ^ (controlledAdderLayout n ws).width →
    (controlledAdderLayout n ws).read i 0 = a →
    (controlledAdderLayout n ws).read i 1 = b →
    (controlledAdderLayout n ws).read i 2 = 0 →
    (controlledAdderLayout n ws).read i 3 = (if enabled = true then 1 else 0) →
    (controlledAdderLayout n ws).read i 4 = 0 →
    act r i = (if enabled = true then
      (controlledAdderLayout n ws).write i 1 ((a + b) % 2 ^ n)
    else i)

/-- The field form of `ControlledAddsWrap`.  It states identity and wrapped
addition through one Boolean expression while retaining both clean-workspace
facts.  The final two conjuncts state preservation of the quantum control and
cleanup of the decomposition wire. -/
theorem controlledAddsWrap_read {ws n : Nat} {r : RCircuit}
    (h : ControlledAddsWrap ws n r) {enabled : Bool} {a b i : Nat}
    (hi : i < 2 ^ (controlledAdderLayout n ws).width)
    (h₀ : (controlledAdderLayout n ws).read i 0 = a)
    (h₁ : (controlledAdderLayout n ws).read i 1 = b)
    (h₂ : (controlledAdderLayout n ws).read i 2 = 0)
    (h₃ : (controlledAdderLayout n ws).read i 3 = if enabled = true then 1 else 0)
    (h₄ : (controlledAdderLayout n ws).read i 4 = 0) :
    (controlledAdderLayout n ws).read (act r i) 0 = a ∧
      (controlledAdderLayout n ws).read (act r i) 1 =
        (if enabled = true then (a + b) % 2 ^ n else b) ∧
      (controlledAdderLayout n ws).read (act r i) 2 = 0 ∧
      (controlledAdderLayout n ws).read (act r i) 3 =
        (if enabled = true then 1 else 0) ∧
      (controlledAdderLayout n ws).read (act r i) 4 = 0 := by
  have heq := h enabled a b i hi h₀ h₁ h₂ h₃ h₄
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at heq h₃ ⊢
      rw [heq, h₀, h₁, h₂, h₃, h₄]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | true =>
      have hsum : (a + b) % 2 ^ n < 2 ^ (controlledAdderLayout n ws).size 1 := by
        change (a + b) % 2 ^ n < 2 ^ n
        exact Nat.mod_lt (a + b) (Nat.two_pow_pos n)
      simp only [if_true] at heq h₃ ⊢
      rw [heq, Layout.read_write_ne (by decide), h₀,
        Layout.read_write_self hsum, Layout.read_write_ne (by decide), h₂,
        Layout.read_write_ne (by decide), h₃,
        Layout.read_write_ne (by decide), h₄]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Two `n`-bit operands, an `n`-bit product field, and a workspace.

The product needs a field of its own.  At `a = 0`, writing `a * b` over `b`
maps every value of `b` to zero and fails injectivity.  A reversible multiplier
therefore writes into a separate field that starts clear. -/
def mulLayout (n ws : Nat) : Layout := [n, n, n, ws]

/-- The circuit writes the product of the two operands modulo `m` into the third
field, over `mulLayout n ws`.

One clause, like `AddsWrap` and unlike the two `AddsMod` carries: the hypotheses
that make the product defined are the same ones that make the workspace
statement meaningful, so a single equation between basis indices says both.  It
fixes the two operands and the workspace as tightly as it fixes the product.

`m ≤ 2 ^ n` guards the same thing it guards in `AddsMod`: a residue has to fit
the field it is written into. -/
def MulsMod (m ws n : Nat) (r : RCircuit) : Prop :=
  ∀ a b i, i < 2 ^ (mulLayout n ws).width →
    (mulLayout n ws).read i 0 = a →
    (mulLayout n ws).read i 1 = b →
    (mulLayout n ws).read i 2 = 0 →
    (mulLayout n ws).read i 3 = 0 →
    m ≤ 2 ^ n → a < m → b < m →
    act r i = (mulLayout n ws).write i 2 (a * b % m)

/-- `MulsMod` preserves both operands.  The third field contains their modular
product.  The workspace remains zero. -/
theorem mulsMod_read {m ws n : Nat} {r : RCircuit} (h : MulsMod m ws n r)
    {a b i : Nat} (hi : i < 2 ^ (mulLayout n ws).width)
    (h₀ : (mulLayout n ws).read i 0 = a)
    (h₁ : (mulLayout n ws).read i 1 = b)
    (h₂ : (mulLayout n ws).read i 2 = 0)
    (h₃ : (mulLayout n ws).read i 3 = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) (hb : b < m) :
    (mulLayout n ws).read (act r i) 0 = a ∧
      (mulLayout n ws).read (act r i) 1 = b ∧
      (mulLayout n ws).read (act r i) 2 = a * b % m ∧
      (mulLayout n ws).read (act r i) 3 = 0 := by
  have hprod : a * b % m < 2 ^ (mulLayout n ws).size 2 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a) ha)) hm
  have heq := h a b i hi h₀ h₁ h₂ h₃ hm ha hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq, Layout.read_write_ne (by decide), h₀]
  · rw [heq, Layout.read_write_ne (by decide), h₁]
  · rw [heq, Layout.read_write_self hprod]
  · rw [heq, Layout.read_write_ne (by decide), h₃]

/-! ## Classical operands

`AddsConstMod` carries a fixed operand as a specification parameter.
`AddsMod` instead represents both operands as quantum fields.
`examples/06-modadd-p` therefore uses 256 of its 770 wires to hold the fixed
value.  `AddsPoint` uses the same parameterized form for its offset.

Constant subtraction uses addition by `m - c`, with the negation computed
before circuit construction.  `SubsMod` covers the distinct case in which both
operands occupy quantum fields. -/

/-- One operand and a workspace.  The other operand is classical. -/
def constLayout (n ws : Nat) : Layout := [n, ws]

/-- One operand, the source circuit's workspace, one coherent control, and one
control-decomposition wire. -/
def controlledConstLayout (n ws : Nat) : Layout := [n, ws, 1, 1]

/-- The circuit adds the classical value `c` to the operand, modulo `m`, over
`constLayout n ws`.

The basis-index equation fixes the workspace and sum in one clause.  The
hypothesis `c < m` permits a generator to reject an unreduced constant or to
reduce it before constructing the circuit. -/
def AddsConstMod (m ws n c : Nat) (r : RCircuit) : Prop :=
  ∀ a i, i < 2 ^ (constLayout n ws).width →
    (constLayout n ws).read i 0 = a →
    (constLayout n ws).read i 1 = 0 →
    m ≤ 2 ^ n → a < m → c < m →
      act r i = (constLayout n ws).write i 0 ((a + c) % m)

/-- `AddsConstMod` replaces the operand with the modular sum.  The workspace
remains zero.  The theorem applies to a reduced constant and operand. -/
theorem addsConstMod_read {m ws n c : Nat} {r : RCircuit} (h : AddsConstMod m ws n c r)
    {a i : Nat} (hi : i < 2 ^ (constLayout n ws).width)
    (h₀ : (constLayout n ws).read i 0 = a)
    (h₁ : (constLayout n ws).read i 1 = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) (hc : c < m) :
    (constLayout n ws).read (act r i) 0 = (a + c) % m ∧
      (constLayout n ws).read (act r i) 1 = 0 := by
  have hsum : (a + c) % m < 2 ^ (constLayout n ws).size 0 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a) ha)) hm
  have heq := h a i hi h₀ h₁ hm ha hc
  exact ⟨by rw [heq, Layout.read_write_self hsum],
         by rw [heq, Layout.read_write_ne (by decide), h₁]⟩

/-! ## Unary arithmetic -/

/-- The circuit replaces one reduced operand with twice that operand modulo
`m`, over `constLayout n ws`.  Its workspace starts and ends clear.  A circuit
construction must separately establish the arithmetic conditions that make the
reduced-domain map reversible. -/
def DoublesMod (m ws n : Nat) (r : RCircuit) : Prop :=
  ∀ a i, i < 2 ^ (constLayout n ws).width →
    (constLayout n ws).read i 0 = a →
    (constLayout n ws).read i 1 = 0 →
    m ≤ 2 ^ n → a < m →
      act r i = (constLayout n ws).write i 0 (2 * a % m)

/-- `DoublesMod` replaces the operand with its reduced double.  The workspace
remains zero.  The theorem applies to a reduced operand that fits the field. -/
theorem doublesMod_read {m ws n : Nat} {r : RCircuit} (h : DoublesMod m ws n r)
    {a i : Nat} (hi : i < 2 ^ (constLayout n ws).width)
    (h₀ : (constLayout n ws).read i 0 = a)
    (h₁ : (constLayout n ws).read i 1 = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) :
    (constLayout n ws).read (act r i) 0 = 2 * a % m ∧
      (constLayout n ws).read (act r i) 1 = 0 := by
  have hv : 2 * a % m < 2 ^ (constLayout n ws).size 0 :=
    Nat.lt_of_lt_of_le
      (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a) ha)) hm
  have heq := h a i hi h₀ h₁ hm ha
  exact ⟨by rw [heq, Layout.read_write_self hv],
         by rw [heq, Layout.read_write_ne (by decide), h₁]⟩

/-- One input field, one output field, and a workspace.  The shape `MulsMod`
has, with one operand instead of two. -/
def unaryLayout (n ws : Nat) : Layout := [n, n, ws]

/-- The circuit writes the square of the first field modulo `m` into the second,
over `unaryLayout n ws`.  `SquaresMod` uses one input field, while `MulsMod`
reads two fields.  A multiplication assembly that copies its input into a
second field adds `n` wires and the copy gates. -/
def SquaresMod (m ws n : Nat) (r : RCircuit) : Prop :=
  ∀ a i, i < 2 ^ (unaryLayout n ws).width →
    (unaryLayout n ws).read i 0 = a →
    (unaryLayout n ws).read i 1 = 0 →
    (unaryLayout n ws).read i 2 = 0 →
    m ≤ 2 ^ n → a < m →
      act r i = (unaryLayout n ws).write i 1 (a * a % m)

/-- `SquaresMod` preserves the input field.  The output field contains its
modular square.  The workspace remains zero. -/
theorem squaresMod_read {m ws n : Nat} {r : RCircuit} (h : SquaresMod m ws n r)
    {a i : Nat} (hi : i < 2 ^ (unaryLayout n ws).width)
    (h₀ : (unaryLayout n ws).read i 0 = a)
    (h₁ : (unaryLayout n ws).read i 1 = 0)
    (h₂ : (unaryLayout n ws).read i 2 = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) :
    (unaryLayout n ws).read (act r i) 0 = a ∧
      (unaryLayout n ws).read (act r i) 1 = a * a % m ∧
      (unaryLayout n ws).read (act r i) 2 = 0 := by
  have hv : a * a % m < 2 ^ (unaryLayout n ws).size 1 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a) ha)) hm
  have heq := h a i hi h₀ h₁ h₂ hm ha
  refine ⟨?_, ?_, ?_⟩
  · rw [heq, Layout.read_write_ne (by decide), h₀]
  · rw [heq, Layout.read_write_self hv]
  · rw [heq, Layout.read_write_ne (by decide), h₂]

/-- The circuit replaces the field with its negation modulo `m`, over
`constLayout n ws`.

The circuit updates the field in place, as required by step 15 of the published
algorithm.  `SubsMod` reads two fields, preserves its source, and writes the
difference into its target, requiring an additional field in the assembly.
`(m - a) % m` sends zero to zero because `m % m = 0`. -/
def NegatesMod (m ws n : Nat) (r : RCircuit) : Prop :=
  ∀ a i, i < 2 ^ (constLayout n ws).width →
    (constLayout n ws).read i 0 = a →
    (constLayout n ws).read i 1 = 0 →
    m ≤ 2 ^ n → a < m →
      act r i = (constLayout n ws).write i 0 ((m - a) % m)

/-- A coherently controlled modular negator.  A clear control fixes the complete
basis index, while a set control negates the operand modulo `m`.  The source
workspace and control-decomposition wire return to zero. -/
def ControlledNegatesMod (m ws n : Nat) (r : RCircuit) : Prop :=
  ∀ (enabled : Bool) a i, i < 2 ^ (controlledConstLayout n ws).width →
    (controlledConstLayout n ws).read i 0 = a →
    (controlledConstLayout n ws).read i 1 = 0 →
    (controlledConstLayout n ws).read i 2 =
      (if enabled = true then 1 else 0) →
    (controlledConstLayout n ws).read i 3 = 0 →
    m ≤ 2 ^ n → a < m →
    act r i = if enabled = true then
      (controlledConstLayout n ws).write i 0 ((m - a) % m)
    else i

/-- `NegatesMod` replaces the operand with its modular negation.  The workspace
remains zero.  The theorem applies to a reduced operand that fits the field. -/
theorem negatesMod_read {m ws n : Nat} {r : RCircuit} (h : NegatesMod m ws n r)
    {a i : Nat} (hi : i < 2 ^ (constLayout n ws).width)
    (h₀ : (constLayout n ws).read i 0 = a)
    (h₁ : (constLayout n ws).read i 1 = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) :
    (constLayout n ws).read (act r i) 0 = (m - a) % m ∧
      (constLayout n ws).read (act r i) 1 = 0 := by
  have hv : (m - a) % m < 2 ^ (constLayout n ws).size 0 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le a) ha)) hm
  have heq := h a i hi h₀ h₁ hm ha
  exact ⟨by rw [heq, Layout.read_write_self hv],
         by rw [heq, Layout.read_write_ne (by decide), h₁]⟩

/-- The field form of `ControlledNegatesMod`. -/
theorem controlledNegatesMod_read {m ws n : Nat} {r : RCircuit}
    (h : ControlledNegatesMod m ws n r) {enabled : Bool} {a i : Nat}
    (hi : i < 2 ^ (controlledConstLayout n ws).width)
    (h₀ : (controlledConstLayout n ws).read i 0 = a)
    (h₁ : (controlledConstLayout n ws).read i 1 = 0)
    (h₂ : (controlledConstLayout n ws).read i 2 =
      if enabled = true then 1 else 0)
    (h₃ : (controlledConstLayout n ws).read i 3 = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) :
    (controlledConstLayout n ws).read (act r i) 0 =
        (if enabled = true then (m - a) % m else a) ∧
      (controlledConstLayout n ws).read (act r i) 1 = 0 ∧
      (controlledConstLayout n ws).read (act r i) 2 =
        (if enabled = true then 1 else 0) ∧
      (controlledConstLayout n ws).read (act r i) 3 = 0 := by
  have heq := h enabled a i hi h₀ h₁ h₂ h₃ hm ha
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at heq h₂ ⊢
      rw [heq, h₀, h₁, h₂, h₃]
      exact ⟨rfl, rfl, rfl, rfl⟩
  | true =>
      have hneg : (m - a) % m < 2 ^
          (controlledConstLayout n ws).size 0 := by
        change (m - a) % m < 2 ^ n
        exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hm
      simp only [if_true] at heq h₂ ⊢
      rw [heq, Layout.read_write_self hneg,
        Layout.read_write_ne (by decide), h₁,
        Layout.read_write_ne (by decide), h₂,
        Layout.read_write_ne (by decide), h₃]
      exact ⟨rfl, rfl, rfl, rfl⟩

end Reversible
end VQ
