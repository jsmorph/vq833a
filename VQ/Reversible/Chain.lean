/-
Composition of a multiplier and an adder.

Each component specification uses a local layout starting at wire zero.  This
module places both components in one register and proves composition from
`MulsMod` and `AddsMod`.  Any circuits satisfying those specifications may
replace the components without changing the composition proof.

Each component's workspace follows its data fields, so components placed at
different offsets occupy disjoint blocks.  The composition copies the product
from the multiplier block into the adder operand, then reverses the multiplier
to clear its workspace.  `actGates_compute_use_uncompute` proves this sequence,
with `cp` as the intervening copy.
-/
import VQ.Reversible.Compile
import VQ.Reversible.Place
import VQ.Reversible.ArithmeticSpec

namespace VQ
namespace Reversible

/-! ## Block preservation lemmas

Both lemmas read a subfield after placing a component at an offset. -/

/-- Reading a field of a block is reading it of the whole index, shifted by
where the block starts. -/
theorem readField_readField {i D off len W : Nat} (h : off + len ≤ W) :
    readField (readField i D W) off len = readField i (D + off) len := by
  refine Nat.eq_of_testBit_eq fun b => ?_
  rw [testBit_readField, testBit_readField, testBit_readField]
  by_cases hb : b < len
  · have hlt : off + b < W := by omega
    simp only [hb, decide_true, Bool.true_and, hlt, Nat.add_assoc]
  · simp only [hb, decide_false, Bool.false_and]

/-- Reading a field of the low block is reading it of the index. -/
theorem readField_readField_zero {i off len W : Nat} (h : off + len ≤ W) :
    readField (readField i 0 W) off len = readField i off len := by
  rw [readField_readField h, Nat.zero_add]

/-- Shifting every wire by zero changes nothing. -/
@[simp] theorem RGate.map_add_zero (g : RGate) : g.map (· + 0) = g := by
  cases g <;> simp [RGate.map]

@[simp] theorem gates_map_add_zero (gs : List RGate) :
    gs.map (RGate.map (· + 0)) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [List.map_cons, RGate.map_add_zero, ih]

/-- A gate list whose wires all lie below `W` acts on the low `W`-bit block the
way it acts on an index that is only that block.  This is
`readField_actGates_map` at offset zero, which is where a component sits when
the assembly puts it first. -/
theorem readField_actGates_low {gs : List RGate} {W : Nat}
    (h : ∀ g ∈ gs, ∀ q ∈ g.wires, q < W) (i : Nat) :
    readField (actGates gs i) 0 W = actGates gs (readField i 0 W) := by
  have := readField_actGates_map (δ := 0) (w := W) h i
  rwa [gates_map_add_zero] at this


/-! ## Component chain

Seven fields: two multiplier operands, the product, the multiplier's workspace,
the adder's addend, the adder's target, and the adder's workspace.  The first
four are the multiplier's own layout and the last three are the adder's, so each
component sits on a contiguous block and neither can reach the other's.
-/

/-- The assembled layout. -/
def chainLayout (n wm wa : Nat) : Layout := [n, n, n, wm, n, n, wa]

/-- Where the adder's block begins. -/
def addOffset (n wm : Nat) : Nat := 3 * n + wm

theorem chainLayout_width (n wm wa : Nat) :
    (chainLayout n wm wa).width = addOffset n wm + (adderLayout n wa).width := by
  simp [chainLayout, addOffset, adderLayout, Layout.width]
  omega

/-! The adder's three fields, named by where they sit in the assembled
register rather than by their index in the layout. -/

theorem chainLayout_read4 (n wm wa i : Nat) :
    (chainLayout n wm wa).read i 4 = readField i (addOffset n wm) n := by
  have ho : (chainLayout n wm wa).offset 4 = addOffset n wm := by
    simp [chainLayout, addOffset, Layout.offset]; omega
  have hs : (chainLayout n wm wa).size 4 = n := rfl
  simp only [Layout.read, ho, hs]

theorem chainLayout_read5 (n wm wa i : Nat) :
    (chainLayout n wm wa).read i 5 = readField i (addOffset n wm + n) n := by
  have ho : (chainLayout n wm wa).offset 5 = addOffset n wm + n := by
    simp [chainLayout, addOffset, Layout.offset]; omega
  have hs : (chainLayout n wm wa).size 5 = n := rfl
  simp only [Layout.read, ho, hs]

theorem chainLayout_read6 (n wm wa i : Nat) :
    (chainLayout n wm wa).read i 6 = readField i (addOffset n wm + (n + n)) wa := by
  have ho : (chainLayout n wm wa).offset 6 = addOffset n wm + (n + n) := by
    simp [chainLayout, addOffset, Layout.offset]; omega
  have hs : (chainLayout n wm wa).size 6 = wa := rfl
  simp only [Layout.read, ho, hs]

/-- The assembled circuit: multiply, copy the product into the adder's addend,
uncompute the multiplier, add.

The copy is a parameter rather than a construction, for the same reason the
components are: this theorem is about composition, and what the copy circuit is
belongs to its own proof. -/
def chain (n wm wa : Nat) (mul cp add : RCircuit) : RCircuit :=
  { width := (chainLayout n wm wa).width,
    gates := mul.gates ++ cp.gates ++ mul.gates.reverse
      ++ add.gates.map (RGate.map (· + addOffset n wm)) }

theorem chain_gates (n wm wa : Nat) (mul cp add : RCircuit) :
    (chain n wm wa mul cp add).gates
      = (mul.gates ++ cp.gates ++ mul.gates.reverse)
          ++ add.gates.map (RGate.map (· + addOffset n wm)) := rfl

/-! ## Chain composition -/

/-- Two components compose.

Given any multiplier satisfying `MulsMod`, any adder satisfying `AddsMod`, and a
copy circuit that exchanges the adder's addend field for its exclusive-or with
the product field, the assembled circuit writes `(a * b + c) % m` into the
adder's target.

Each hypothesis concerns a component specification, so any conforming
multiplier or adder can replace the corresponding component. -/
theorem chain_correct {m n wm wa : Nat} {mul cp add : RCircuit}
    (hmulwf : mul.wellFormed = true)
    (hmulw : ∀ g ∈ mul.gates, ∀ q ∈ g.wires, q < (mulLayout n wm).width)
    (haddw : ∀ g ∈ add.gates, ∀ q ∈ g.wires, q < (adderLayout n wa).width)
    (hmul : MulsMod m wm n mul)
    (hadd : AddsMod m wa n add)
    (hcp : ∀ j, actGates cp.gates j
      = writeField j (addOffset n wm) n
          ((readField j (addOffset n wm) n) ^^^ (readField j (2 * n) n)))
    (a b c i : Nat)
    (h0 : (chainLayout n wm wa).read i 0 = a)
    (h1 : (chainLayout n wm wa).read i 1 = b)
    (h2 : (chainLayout n wm wa).read i 2 = 0)
    (h3 : (chainLayout n wm wa).read i 3 = 0)
    (h4 : (chainLayout n wm wa).read i 4 = 0)
    (h5 : (chainLayout n wm wa).read i 5 = c)
    (h6 : (chainLayout n wm wa).read i 6 = 0)
    (hm : m ≤ 2 ^ n) (ha : a < m) (hb : b < m) (hc : c < m) :
    (chainLayout n wm wa).read (act (chain n wm wa mul cp add) i) 5 = (a * b + c) % m := by
  have hmpos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le a) ha
  have hpm : a * b % m < m := Nat.mod_lt _ hmpos
  have hpn : a * b % m < 2 ^ n := Nat.lt_of_lt_of_le hpm hm
  have hWm : (mulLayout n wm).width = addOffset n wm := by
    simp [mulLayout, addOffset, Layout.width]; omega
  have hmulD : ∀ g ∈ mul.gates, ∀ q ∈ g.wires, q < addOffset n wm := by
    intro g hg q hq; rw [← hWm]; exact hmulw g hg q hq
  have hmulOut : ∀ g ∈ mul.gates, ∀ q ∈ g.wires,
      q < addOffset n wm ∨ addOffset n wm + n ≤ q :=
    fun g hg q hq => Or.inl (hmulD g hg q hq)
  -- The multiplier's block, and what it holds before and after.
  have hblk : readField (actGates mul.gates i) 0 (mulLayout n wm).width
      = act mul (readField i 0 (mulLayout n wm).width) :=
    readField_actGates_low hmulw i
  have hf0 : (mulLayout n wm).read (readField i 0 (mulLayout n wm).width) 0 = a := by
    show readField (readField i 0 (mulLayout n wm).width) 0 n = a
    rw [readField_readField_zero (by rw [hWm]; simp [addOffset]; omega)]
    exact h0
  have hf1 : (mulLayout n wm).read (readField i 0 (mulLayout n wm).width) 1 = b := by
    show readField (readField i 0 (mulLayout n wm).width) n n = b
    rw [readField_readField_zero (by rw [hWm]; simp [addOffset]; omega)]
    exact h1
  have hf2 : (mulLayout n wm).read (readField i 0 (mulLayout n wm).width) 2 = 0 := by
    show readField (readField i 0 (mulLayout n wm).width) (n + n) n = 0
    rw [readField_readField_zero (by rw [hWm]; simp [addOffset]; omega)]
    exact h2
  have hf3 : (mulLayout n wm).read (readField i 0 (mulLayout n wm).width) 3 = 0 := by
    show readField (readField i 0 (mulLayout n wm).width) (n + (n + n)) wm = 0
    rw [readField_readField_zero (by rw [hWm]; simp [addOffset]; omega)]
    exact h3
  have hmulapp := hmul a b (readField i 0 (mulLayout n wm).width)
    (readField_lt _ _ _) hf0 hf1 hf2 hf3 hm ha hb
  -- The product, read out of the block after the multiplier has run.
  have hprod : readField (actGates mul.gates i) (2 * n) n = a * b % m := by
    have hin : readField (actGates mul.gates i) (2 * n) n
        = readField (readField (actGates mul.gates i) 0 (mulLayout n wm).width) (2 * n) n := by
      rw [readField_readField_zero (by rw [hWm]; simp [addOffset]; omega)]
    rw [hin, hblk, hmulapp, Nat.two_mul]
    exact readField_writeField_self hpn
  -- The adder's addend is untouched by the multiplier, so it is still clear.
  have hclear : readField (actGates mul.gates i) (addOffset n wm) n = 0 := by
    rw [readField_actGates_of_outside hmulOut, ← chainLayout_read4 n wm wa]
    exact h4
  -- Multiply, copy, uncompute: the register as it was, with the product in the
  -- adder's addend.
  have step1 : actGates (mul.gates ++ cp.gates ++ mul.gates.reverse) i
      = writeField i (addOffset n wm) n (a * b % m) := by
    rw [actGates_compute_use_uncompute hmulwf hmulOut hcp i, hclear, hprod, Nat.zero_xor]
  have hstate : act (chain n wm wa mul cp add) i
      = actGates (add.gates.map (RGate.map (· + addOffset n wm)))
          (writeField i (addOffset n wm) n (a * b % m)) := by
    show actGates ((mul.gates ++ cp.gates ++ mul.gates.reverse) ++ _) i = _
    rw [actGates_append, step1]
  -- The adder's block, on the state the copy left behind.
  have hWa : n + n ≤ (adderLayout n wa).width := by
    simp [adderLayout, Layout.width]
  have hWa2 : n + n + wa ≤ (adderLayout n wa).width := by
    simp [adderLayout, Layout.width]; omega
  have hg0 : (adderLayout n wa).read
      (readField (writeField i (addOffset n wm) n (a * b % m))
        (addOffset n wm) (adderLayout n wa).width) 0 = a * b % m := by
    show readField (readField _ (addOffset n wm) (adderLayout n wa).width) 0 n = _
    rw [readField_readField (by omega), Nat.add_zero]
    exact readField_writeField_self hpn
  have hg1 : (adderLayout n wa).read
      (readField (writeField i (addOffset n wm) n (a * b % m))
        (addOffset n wm) (adderLayout n wa).width) 1 = c := by
    show readField (readField _ (addOffset n wm) (adderLayout n wa).width) n n = _
    rw [readField_readField hWa,
      readField_writeField_of_disjoint (Or.inl (Nat.le_refl _)),
      ← chainLayout_read5 n wm wa]
    exact h5
  have hg2 : (adderLayout n wa).read
      (readField (writeField i (addOffset n wm) n (a * b % m))
        (addOffset n wm) (adderLayout n wa).width) 2 = 0 := by
    show readField (readField _ (addOffset n wm) (adderLayout n wa).width) (n + n) wa = _
    rw [readField_readField hWa2,
      readField_writeField_of_disjoint (Or.inl (by omega)),
      ← chainLayout_read6 n wm wa]
    exact h6
  have haddapp := hadd (a * b % m) c _ (readField_lt _ _ _) hg0 hg1 hg2 hm hpm hc
  -- Read the adder's target out of the assembled register.
  rw [chainLayout_read5, hstate, ← readField_readField hWa,
    readField_actGates_map haddw]
  show (adderLayout n wa).read (act add _) 1 = _
  rw [haddapp, Layout.read_write_self (by
    show (a * b % m + c) % m < 2 ^ (adderLayout n wa).size 1
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hmpos) hm), Nat.mod_add_mod]

/-! ## Assembly resources

`chain_correct` proves the circuit's functional action.  Resource counts are
additive with the multiplier doubled because reversal preserves each count and
placement preserves each gate kind.  A composed bound is therefore the sum of
the component bounds. -/

theorem chain_countP (n wm wa : Nat) (mul cp add : RCircuit) {p : RGate → Bool}
    (hp : ∀ g, p (RGate.map (· + addOffset n wm) g) = p g) :
    (chain n wm wa mul cp add).gates.countP p
      = 2 * mul.gates.countP p + cp.gates.countP p + add.gates.countP p := by
  rw [chain_gates, List.countP_append, List.countP_append, List.countP_append,
    List.countP_reverse, countP_map_gates hp]
  omega

theorem chain_length (n wm wa : Nat) (mul cp add : RCircuit) :
    (chain n wm wa mul cp add).gates.length
      = 2 * mul.gates.length + cp.gates.length + add.gates.length := by
  rw [chain_gates, List.length_append, List.length_append, List.length_append,
    List.length_reverse, List.length_map]
  omega

theorem chain_toffoliCount (n wm wa : Nat) (mul cp add : RCircuit) :
    Circuit.toffoliCount (compile (chain n wm wa mul cp add))
      = 2 * Circuit.toffoliCount (compile mul) + Circuit.toffoliCount (compile cp)
        + Circuit.toffoliCount (compile add) := by
  rw [toffoliCount_compile, toffoliCount_compile, toffoliCount_compile,
    toffoliCount_compile, chain_countP _ _ _ _ _ _ (RGate.isCcx_map _)]

theorem chain_cnotCount (n wm wa : Nat) (mul cp add : RCircuit) :
    Circuit.cnotCount (compile (chain n wm wa mul cp add))
      = 2 * Circuit.cnotCount (compile mul) + Circuit.cnotCount (compile cp)
        + Circuit.cnotCount (compile add) := by
  rw [cnotCount_compile, cnotCount_compile, cnotCount_compile, cnotCount_compile,
    chain_countP _ _ _ _ _ _ (RGate.isCx_map _)]

theorem chain_gateCount (n wm wa : Nat) (mul cp add : RCircuit) :
    Circuit.gateCount (compile (chain n wm wa mul cp add))
      = 2 * Circuit.gateCount (compile mul) + Circuit.gateCount (compile cp)
        + Circuit.gateCount (compile add) := by
  rw [gateCount_compile, gateCount_compile, gateCount_compile, gateCount_compile,
    chain_length, chain_countP _ _ _ _ _ _ (RGate.isCcx_map _)]
  omega

/-! ## Assembly register

Every gate lies inside the chain layout, so the circuit is well formed at its
declared width and uses no more wires than the layout has. -/

theorem chain_wires {n wm wa : Nat} {mul cp add : RCircuit}
    (hmulw : ∀ g ∈ mul.gates, ∀ q ∈ g.wires, q < (mulLayout n wm).width)
    (haddw : ∀ g ∈ add.gates, ∀ q ∈ g.wires, q < (adderLayout n wa).width)
    (hcpw : ∀ g ∈ cp.gates, ∀ q ∈ g.wires, q < (chainLayout n wm wa).width) :
    ∀ g ∈ (chain n wm wa mul cp add).gates, ∀ q ∈ g.wires,
      q < (chainLayout n wm wa).width := by
  have hWm : (mulLayout n wm).width = addOffset n wm := by
    simp [mulLayout, addOffset, Layout.width]; omega
  have hW := chainLayout_width n wm wa
  intro g hg q hq
  rw [chain_gates] at hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · have := hmulw g hg q hq; omega
      · exact hcpw g hg q hq
    · have := hmulw g (List.mem_reverse.mp hg) q hq; omega
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    rw [RGate.wires_map, List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    have := haddw g' hg' q' hq'
    omega

theorem chain_wellFormed {n wm wa : Nat} {mul cp add : RCircuit}
    (hmulwf : mul.gates.all (RGate.wellFormed (mulLayout n wm).width) = true)
    (haddwf : add.gates.all (RGate.wellFormed (adderLayout n wa).width) = true)
    (hcpwf : cp.gates.all (RGate.wellFormed (chainLayout n wm wa).width) = true) :
    (chain n wm wa mul cp add).wellFormed = true := by
  have hWm : (mulLayout n wm).width = addOffset n wm := by
    simp [mulLayout, addOffset, Layout.width]; omega
  have hW := chainLayout_width n wm wa
  have hmul := List.all_eq_true.mp hmulwf
  have hadd := List.all_eq_true.mp haddwf
  have hcp := List.all_eq_true.mp hcpwf
  show (chain n wm wa mul cp add).gates.all
    (RGate.wellFormed (chainLayout n wm wa).width) = true
  refine List.all_eq_true.mpr (fun g hg => ?_)
  rw [chain_gates] at hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact RGate.wellFormed_mono (by omega) (hmul g hg)
      · exact hcp g hg
    · exact RGate.wellFormed_mono (by omega) (hmul g (List.mem_reverse.mp hg))
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact RGate.wellFormed_map_add (by omega) (hadd g' hg')

theorem chain_usedWires {n wm wa : Nat} {mul cp add : RCircuit}
    (hmulw : ∀ g ∈ mul.gates, ∀ q ∈ g.wires, q < (mulLayout n wm).width)
    (haddw : ∀ g ∈ add.gates, ∀ q ∈ g.wires, q < (adderLayout n wa).width)
    (hcpw : ∀ g ∈ cp.gates, ∀ q ∈ g.wires, q < (chainLayout n wm wa).width) :
    Circuit.usedWires (compile (chain n wm wa mul cp add))
      ≤ (chainLayout n wm wa).width :=
  usedWires_compile_le_of_lt (chain_wires hmulw haddw hcpw)

end Reversible
end VQ
