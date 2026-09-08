/-
A register of many equal blocks.

`VQ.Reversible.Assembly` fixes four data blocks for point addition.  Fermat
inversion requires a construction-dependent number of blocks.  This module
therefore parameterizes the block count and represents the state as a function
of the block index.
-/
import VQ.Reversible.Wiring
import VQ.Reversible.ArithmeticSpec

namespace VQ
namespace Reversible

/-! ## Block register -/

/-- `b` blocks of `n` wires, then one shared component workspace of `cw`. -/
def blockLayout (b n cw : Nat) : Layout := List.replicate b n ++ [cw]

@[simp] theorem blockLayout_length (b n cw : Nat) : (blockLayout b n cw).length = b + 1 := by
  simp [blockLayout]

theorem blockLayout_width (b n cw : Nat) : (blockLayout b n cw).width = b * n + cw := by
  induction b with
  | zero => simp [blockLayout, Layout.width]
  | succ b ih =>
    show n + Layout.width (List.replicate b n ++ [cw]) = (b + 1) * n + cw
    rw [show Layout.width (List.replicate b n ++ [cw]) = b * n + cw from ih,
      Nat.succ_mul]
    omega

theorem blockLayout_size {b n cw j : Nat} (hj : j < b) : (blockLayout b n cw).size j = n := by
  induction b generalizing j with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ b ih =>
    cases j with
    | zero => rfl
    | succ j =>
      show Layout.size (List.replicate b n ++ [cw]) j = n
      exact ih (Nat.lt_of_succ_lt_succ hj)

theorem blockLayout_size_ws (b n cw : Nat) : (blockLayout b n cw).size b = cw := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show Layout.size (List.replicate b n ++ [cw]) b = cw
    exact ih

theorem blockLayout_offset {b n cw j : Nat} (hj : j ≤ b) :
    (blockLayout b n cw).offset j = j * n := by
  induction b generalizing j with
  | zero =>
    have hz : j = 0 := by omega
    subst hz
    show (0 : Nat) = 0 * n
    omega
  | succ b ih =>
    cases j with
    | zero => show (0 : Nat) = 0 * n; omega
    | succ j =>
      show n + Layout.offset (List.replicate b n ++ [cw]) j = (j + 1) * n
      rw [show Layout.offset (List.replicate b n ++ [cw]) j = j * n from
        ih (Nat.le_of_succ_le_succ hj), Nat.succ_mul]
      omega

/-- Reading a data block. -/
theorem blk_read {b n cw j I : Nat} (hj : j < b) :
    (blockLayout b n cw).read I j = readField I (j * n) n := by
  show readField I ((blockLayout b n cw).offset j) ((blockLayout b n cw).size j) = _
  rw [blockLayout_offset (Nat.le_of_lt hj), blockLayout_size hj]

/-- Reading the shared workspace. -/
theorem blk_read_ws (b n cw I : Nat) :
    (blockLayout b n cw).read I b = readField I (b * n) cw := by
  show readField I ((blockLayout b n cw).offset b) ((blockLayout b n cw).size b) = _
  rw [blockLayout_offset (Nat.le_refl b), blockLayout_size_ws]

/-! ## Block arithmetic

Two facts about the offsets discharge every wiring condition, as they do for the
four-block register. -/

theorem blk_le {b n j : Nat} (hj : j < b) : j * n + n ≤ b * n := by
  have h1 : j * n + n = (j + 1) * n := (Nat.succ_mul j n).symm
  have h2 : (j + 1) * n ≤ b * n := Nat.mul_le_mul_right n (by omega)
  omega

theorem blk_ne {n j k : Nat} (hne : j ≠ k) :
    j * n + n ≤ k * n ∨ k * n + n ≤ j * n := by
  rcases Nat.lt_or_ge j k with h | h
  · refine Or.inl ?_
    have h1 : j * n + n = (j + 1) * n := (Nat.succ_mul j n).symm
    have h2 : (j + 1) * n ≤ k * n := Nat.mul_le_mul_right n (by omega)
    omega
  · refine Or.inr ?_
    have h1 : k * n + n = (k + 1) * n := (Nat.succ_mul k n).symm
    have h2 : (k + 1) * n ≤ j * n := Nat.mul_le_mul_right n (by omega)
    omega

/-! ## Block state

A function from the block index to its value, and the workspace clear.  A chain
of a few hundred steps changes one entry at a time, so the state has to be a
function rather than a tuple. -/

/-- The state with block `k` set to `x`.  Core Lean has no `Function.update`. -/
def setBlk (v : Nat → Nat) (k x : Nat) : Nat → Nat := fun j => if j = k then x else v j

@[simp] theorem setBlk_self (v : Nat → Nat) (k x : Nat) : setBlk v k x k = x := by
  simp [setBlk]

theorem setBlk_ne {v : Nat → Nat} {k x j : Nat} (h : j ≠ k) : setBlk v k x j = v j := by
  simp [setBlk, h]

/-- Block `j` holds `v j`, and the workspace is clear. -/
structure BSt (b n cw I : Nat) (v : Nat → Nat) : Prop where
  blk : ∀ j, j < b → (blockLayout b n cw).read I j = v j
  ws : (blockLayout b n cw).read I b = 0

/-- Writing block `k` advances the state at that index and leaves the rest. -/
theorem BSt.write {b n cw I : Nat} {v : Nat → Nat} (h : BSt b n cw I v) {k x : Nat}
    (hk : k < b) (hx : x < 2 ^ n) :
    BSt b n cw ((blockLayout b n cw).write I k x) (setBlk v k x) where
  blk := by
    intro j hj
    by_cases hjk : j = k
    · subst hjk
      rw [Layout.read_write_self (by rw [blockLayout_size hj]; exact hx), setBlk_self]
    · rw [Layout.read_write_ne hjk, h.blk j hj, setBlk_ne hjk]
  ws := by
    rw [Layout.read_write_ne (by omega), h.ws]

/-! ## Block wirings

The workspace offset is `b * n`, so the disjointness conditions are the
four-block ones with that in place of `4 * n`. -/

/-- A one-operand component on block `j`, workspace at `W`. -/
def bw1 (n W j : Nat) : Wiring := [j * n, W]

/-- A two-operand component on blocks `j` and `k`. -/
def bw2 (n W j k : Nat) : Wiring := [j * n, k * n, W]

/-- A three-operand component on blocks `j`, `k`, and `l`. -/
def bw3 (n W j k l : Nat) : Wiring := [j * n, k * n, l * n, W]

theorem bdisjoint2 {n ws' o W : Nat} (ho : o + n ≤ W) :
    Wiring.Disjoint [n, ws'] [o, W] := by
  intro j k hj hk hne
  have hj' : j = 0 ∨ j = 1 := by simp at hj; omega
  have hk' : k = 0 ∨ k = 1 := by simp at hk; omega
  rcases hj' with rfl | rfl <;> rcases hk' with rfl | rfl
  · exact absurd rfl hne
  · exact Or.inl ho
  · exact Or.inr ho
  · exact absurd rfl hne

theorem bdisjoint3 {n ws' o₀ o₁ W : Nat}
    (h₀ : o₀ + n ≤ W) (h₁ : o₁ + n ≤ W)
    (h01 : o₀ + n ≤ o₁ ∨ o₁ + n ≤ o₀) :
    Wiring.Disjoint [n, n, ws'] [o₀, o₁, W] := by
  intro j k hj hk hne
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by simp at hj; omega
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by simp at hk; omega
  rcases hj' with rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact h01
  · exact Or.inl h₀
  · exact h01.symm
  · exact absurd rfl hne
  · exact Or.inl h₁
  · exact Or.inr h₀
  · exact Or.inr h₁
  · exact absurd rfl hne

theorem bdisjoint4 {n ws' o₀ o₁ o₂ W : Nat}
    (h₀ : o₀ + n ≤ W) (h₁ : o₁ + n ≤ W) (h₂ : o₂ + n ≤ W)
    (h01 : o₀ + n ≤ o₁ ∨ o₁ + n ≤ o₀)
    (h02 : o₀ + n ≤ o₂ ∨ o₂ + n ≤ o₀)
    (h12 : o₁ + n ≤ o₂ ∨ o₂ + n ≤ o₁) :
    Wiring.Disjoint [n, n, n, ws'] [o₀, o₁, o₂, W] := by
  intro j k hj hk hne
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp at hj; omega
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by simp at hk; omega
  rcases hj' with rfl | rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl | rfl
  · exact absurd rfl hne
  · exact h01
  · exact h02
  · exact Or.inl h₀
  · exact h01.symm
  · exact absurd rfl hne
  · exact h12
  · exact Or.inl h₁
  · exact h02.symm
  · exact h12.symm
  · exact absurd rfl hne
  · exact Or.inl h₂
  · exact Or.inr h₀
  · exact Or.inr h₁
  · exact Or.inr h₂
  · exact absurd rfl hne

/-! ## Range conditions -/

theorem bW2 {b n cw ws' j k : Nat} (hj : j < b) (hk : k < b) (hws : ws' ≤ cw) :
    ∀ i, i < (unaryLayout n ws').length →
      (bw2 n (b * n) j k).getD i 0 + Layout.size (unaryLayout n ws') i
        ≤ (blockLayout b n cw).width := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by simp [unaryLayout] at hi; omega
  rw [blockLayout_width]
  rcases hi' with rfl | rfl | rfl
  · show j * n + n ≤ b * n + cw
    have := blk_le (n := n) hj; omega
  · show k * n + n ≤ b * n + cw
    have := blk_le (n := n) hk; omega
  · show b * n + ws' ≤ b * n + cw
    omega

theorem bW3 {b n cw ws' j k l : Nat} (hj : j < b) (hk : k < b) (hl : l < b)
    (hws : ws' ≤ cw) :
    ∀ i, i < (mulLayout n ws').length →
      (bw3 n (b * n) j k l).getD i 0 + Layout.size (mulLayout n ws') i
        ≤ (blockLayout b n cw).width := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp [mulLayout] at hi; omega
  rw [blockLayout_width]
  rcases hi' with rfl | rfl | rfl | rfl
  · show j * n + n ≤ b * n + cw
    have := blk_le (n := n) hj; omega
  · show k * n + n ≤ b * n + cw
    have := blk_le (n := n) hk; omega
  · show l * n + n ≤ b * n + cw
    have := blk_le (n := n) hl; omega
  · show b * n + ws' ≤ b * n + cw
    omega

/-- A component's own workspace is clear when the shared one is. -/
theorem bws_narrow {b n cw ws' I : Nat} (hws : ws' ≤ cw)
    (hz : (blockLayout b n cw).read I b = 0) : readField I (b * n) ws' = 0 :=
  readField_narrow hws (by rw [← blk_read_ws]; exact hz)

/-! ## Steps -/

theorem bstep_write {L : Layout} {W : Wiring} {r : RCircuit} {k v I b n cw j : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length) (hk : k < L.length)
    (hwf : ∀ g ∈ r.gates, g.wellFormed L.width = true)
    (hoff : W.getD k 0 = (blockLayout b n cw).offset j)
    (hsize : Layout.size L k = (blockLayout b n cw).size j)
    (h : act r (gatherBits (place L W) L.width I)
       = L.write (gatherBits (place L W) L.width I) k v) :
    actGates (r.gates.map (RGate.map (place L W))) I
      = (blockLayout b n cw).write I j v := by
  rw [actGates_placed_write hd hlen hk hwf h, hoff, hsize]
  rfl

/-- A step that squares one block into another. -/
theorem bstep_square {m ws' b n cw j k I : Nat} {r : RCircuit}
    (hcomp : SquaresMod m ws' n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (unaryLayout n ws').width = true)
    (hws : ws' ≤ cw) (hj : j < b) (hk : k < b) (hjk : j ≠ k) (hm : m ≤ 2 ^ n)
    (ha : (blockLayout b n cw).read I j < m)
    (hout : (blockLayout b n cw).read I k = 0)
    (hz : (blockLayout b n cw).read I b = 0) :
    actGates (r.gates.map (RGate.map (place (unaryLayout n ws') (bw2 n (b * n) j k)))) I
      = (blockLayout b n cw).write I k
          ((blockLayout b n cw).read I j * (blockLayout b n cw).read I j % m) := by
  refine bstep_write (k := 1) (j := k)
    (bdisjoint3 (by have := blk_le (n := n) hj; omega)
      (by have := blk_le (n := n) hk; omega) (blk_ne hjk))
    (by simp [bw2, unaryLayout]) (by simp [unaryLayout]) hwf ?_ ?_ ?_
  · show (bw2 n (b * n) j k).getD 1 0 = _
    rw [blockLayout_offset (Nat.le_of_lt hk)]; rfl
  · show (unaryLayout n ws').size 1 = _
    rw [blockLayout_size hk]; rfl
  · refine hcomp _ _ (gatherBits_lt _ _ _) ?_ ?_ ?_ hm ha
    · rw [read_gatherBits (unaryLayout n ws') (bw2 n (b * n) j k) 0 I (by simp [bw2])]
      show readField I (j * n) n = _
      rw [← blk_read hj]
    · rw [read_gatherBits (unaryLayout n ws') (bw2 n (b * n) j k) 1 I (by simp [bw2])]
      show readField I (k * n) n = _
      rw [← blk_read hk]; exact hout
    · rw [read_gatherBits (unaryLayout n ws') (bw2 n (b * n) j k) 2 I (by simp [bw2])]
      show readField I (b * n) ws' = _
      exact bws_narrow hws hz

/-- A step that multiplies two blocks into a third. -/
theorem bstep_mul {m ws' b n cw j k l I : Nat} {r : RCircuit}
    (hcomp : MulsMod m ws' n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (mulLayout n ws').width = true)
    (hws : ws' ≤ cw) (hj : j < b) (hk : k < b) (hl : l < b)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (hm : m ≤ 2 ^ n)
    (ha : (blockLayout b n cw).read I j < m)
    (hb : (blockLayout b n cw).read I k < m)
    (hout : (blockLayout b n cw).read I l = 0)
    (hz : (blockLayout b n cw).read I b = 0) :
    actGates (r.gates.map (RGate.map (place (mulLayout n ws') (bw3 n (b * n) j k l)))) I
      = (blockLayout b n cw).write I l
          ((blockLayout b n cw).read I j * (blockLayout b n cw).read I k % m) := by
  refine bstep_write (k := 2) (j := l)
    (bdisjoint4 (by have := blk_le (n := n) hj; omega)
      (by have := blk_le (n := n) hk; omega) (by have := blk_le (n := n) hl; omega)
      (blk_ne hjk) (blk_ne hjl) (blk_ne hkl))
    (by simp [bw3, mulLayout]) (by simp [mulLayout]) hwf ?_ ?_ ?_
  · show (bw3 n (b * n) j k l).getD 2 0 = _
    rw [blockLayout_offset (Nat.le_of_lt hl)]; rfl
  · show (mulLayout n ws').size 2 = _
    rw [blockLayout_size hl]; rfl
  · refine hcomp _ _ _ (gatherBits_lt _ _ _) ?_ ?_ ?_ ?_ hm ha hb
    · rw [read_gatherBits (mulLayout n ws') (bw3 n (b * n) j k l) 0 I (by simp [bw3])]
      show readField I (j * n) n = _
      rw [← blk_read hj]
    · rw [read_gatherBits (mulLayout n ws') (bw3 n (b * n) j k l) 1 I (by simp [bw3])]
      show readField I (k * n) n = _
      rw [← blk_read hk]
    · rw [read_gatherBits (mulLayout n ws') (bw3 n (b * n) j k l) 2 I (by simp [bw3])]
      show readField I (l * n) n = _
      rw [← blk_read hl]; exact hout
    · rw [read_gatherBits (mulLayout n ws') (bw3 n (b * n) j k l) 3 I (by simp [bw3])]
      show readField I (b * n) ws' = _
      exact bws_narrow hws hz

/-! ## Copying a field

An assembly that uncomputes its whole chain has to copy the answer out first, and
the copy is the `cp` that `actGates_compute_use_uncompute` takes.  A CNOT per bit
position exchanges the destination for its exclusive-or with the source, which is
the shape that theorem's hypothesis wants. -/

/-- `len` CNOTs copying the field at `s` into the field at `d`. -/
def copyField (s d len : Nat) : List RGate :=
  (List.range len).map (fun t => RGate.cx (s + t) (d + t))

theorem copyField_succ (s d len : Nat) :
    copyField s d (len + 1) = copyField s d len ++ [RGate.cx (s + len) (d + len)] := by
  rw [copyField, copyField, List.range_succ, List.map_append]
  rfl

theorem copyField_wires {s d len : Nat} :
    ∀ g ∈ copyField s d len, ∀ q ∈ g.wires,
      (s ≤ q ∧ q < s + len) ∨ (d ≤ q ∧ q < d + len) := by
  intro g hg q hq
  rw [copyField, List.mem_map] at hg
  obtain ⟨t, ht, rfl⟩ := hg
  rw [List.mem_range] at ht
  simp only [RGate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

theorem testBit_copyField {s d : Nat} : ∀ (len : Nat), (s + len ≤ d ∨ d + len ≤ s) →
    ∀ (I q : Nat), (actGates (copyField s d len) I).testBit q
      = if d ≤ q ∧ q < d + len then I.testBit q ^^ I.testBit (s + (q - d))
        else I.testBit q := by
  intro len
  induction len with
  | zero =>
    intro _ I q
    show (actGates (copyField s d 0) I).testBit q = _
    rw [show copyField s d 0 = [] from rfl, if_neg (by omega : ¬(d ≤ q ∧ q < d + 0))]
    rfl
  | succ len ih =>
    intro hdis I q
    have hdis' : s + len ≤ d ∨ d + len ≤ s := by
      rcases hdis with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hprev := ih hdis' I
    rw [copyField_succ, actGates_append]
    show (RGate.act (RGate.cx (s + len) (d + len))
      (actGates (copyField s d len) I)).testBit q = _
    have hsrc : (actGates (copyField s d len) I).testBit (s + len) = I.testBit (s + len) := by
      rw [hprev (s + len),
        if_neg (by rcases hdis with h | h <;> omega : ¬(d ≤ s + len ∧ s + len < d + len))]
    simp only [RGate.act, hsrc]
    by_cases hb : I.testBit (s + len)
    · rw [if_pos hb, Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow, hprev q]
      by_cases hq : d + len = q
      · subst hq
        rw [if_neg (by omega : ¬(d ≤ d + len ∧ d + len < d + len)),
          if_pos (by omega : d ≤ d + len ∧ d + len < d + (len + 1)),
          show d + len - d = len by omega]
        simp [hb]
      · rw [show (decide (d + len = q)) = false from by simp [hq], Bool.xor_false]
        by_cases h2 : d ≤ q ∧ q < d + len
        · rw [if_pos h2, if_pos (by omega : d ≤ q ∧ q < d + (len + 1))]
        · rw [if_neg h2, if_neg (by omega : ¬(d ≤ q ∧ q < d + (len + 1)))]
    · rw [if_neg hb, hprev q]
      simp only [Bool.not_eq_true] at hb
      by_cases hq : d + len = q
      · subst hq
        rw [if_neg (by omega : ¬(d ≤ d + len ∧ d + len < d + len)),
          if_pos (by omega : d ≤ d + len ∧ d + len < d + (len + 1)),
          show d + len - d = len by omega]
        simp [hb]
      · by_cases h2 : d ≤ q ∧ q < d + len
        · rw [if_pos h2, if_pos (by omega : d ≤ q ∧ q < d + (len + 1))]
        · rw [if_neg h2, if_neg (by omega : ¬(d ≤ q ∧ q < d + (len + 1)))]

/-- The copy exchanges the destination for its exclusive-or with the source. -/
theorem actGates_copyField {s d len : Nat} (hdis : s + len ≤ d ∨ d + len ≤ s) (I : Nat) :
    actGates (copyField s d len) I
      = writeField I d len ((readField I d len) ^^^ (readField I s len)) := by
  refine Nat.eq_of_testBit_eq fun q => ?_
  rw [testBit_copyField len hdis I q]
  by_cases hin : d ≤ q ∧ q < d + len
  · rw [if_pos hin, testBit_writeField_inside hin.1 hin.2, Nat.testBit_xor,
      testBit_readField, testBit_readField]
    have hlt : q - d < len := by omega
    simp only [hlt, decide_true, Bool.true_and,
      show d + (q - d) = q by omega]
  · rw [if_neg hin, testBit_writeField_outside (by omega)]

/-- Each gate in a field copy and the wire-distinctness facts needed for
well-formedness. -/
theorem copyField_mem {s d len : Nat} {g : RGate} (hg : g ∈ copyField s d len) :
    ∃ t, t < len ∧ g = RGate.cx (s + t) (d + t) := by
  rw [copyField, List.mem_map] at hg
  obtain ⟨t, ht, rfl⟩ := hg
  exact ⟨t, List.mem_range.mp ht, rfl⟩

theorem copyFieldBlock_wf {s d len width : Nat}
    (hdis : s + len ≤ d ∨ d + len ≤ s)
    (hsource : s + len ≤ width) (hdestination : d + len ≤ width) :
    (copyField s d len).all (RGate.wellFormed width) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨t, ht, rfl⟩ := copyField_mem hg
  simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨by omega, by omega⟩, by rcases hdis with h | h <;> omega⟩

theorem copyField_length (s d len : Nat) : (copyField s d len).length = len := by
  rw [copyField, List.length_map, List.length_range]

theorem copyField_no_ccx (s d len : Nat) : (copyField s d len).countP RGate.isCcx = 0 := by
  rw [copyField]
  induction len with
  | zero => rfl
  | succ len ih =>
    rw [List.range_succ, List.map_append, List.countP_append, ih]
    rfl

theorem copyField_cx (s d len : Nat) : (copyField s d len).countP RGate.isCx = len := by
  rw [copyField]
  induction len with
  | zero => rfl
  | succ len ih =>
    rw [List.range_succ, List.map_append, List.countP_append, ih]
    rfl

/-! ## Swapping two fields -/

/-- Exchange two disjoint fields with three CNOTs per bit. -/
def swapFields (a b len : Nat) : List RGate :=
  copyField a b len ++ copyField b a len ++ copyField a b len

theorem swapFields_wf {a b len width : Nat}
    (hdis : a + len ≤ b ∨ b + len ≤ a)
    (ha : a + len ≤ width) (hb : b + len ≤ width) :
    (swapFields a b len).all (RGate.wellFormed width) = true := by
  rw [swapFields, List.all_append, List.all_append]
  have hdis' : b + len ≤ a ∨ a + len ≤ b := hdis.elim Or.inr Or.inl
  rw [copyFieldBlock_wf hdis ha hb, copyFieldBlock_wf hdis' hb ha]
  rfl

/-- The three-copy construction exchanges the fields and changes no other bit. -/
theorem actGates_swapFields {a b len : Nat}
    (hdis : a + len ≤ b ∨ b + len ≤ a) (I : Nat) :
    actGates (swapFields a b len) I =
      writeField (writeField I a len (readField I b len))
        b len (readField I a len) := by
  have hdis' : b + len ≤ a ∨ a + len ≤ b := hdis.elim Or.inr Or.inl
  have ha : readField I a len < 2 ^ len := readField_lt I a len
  have hb : readField I b len < 2 ^ len := readField_lt I b len
  have hxor : readField I b len ^^^ readField I a len < 2 ^ len :=
    Nat.xor_lt_two_pow hb ha
  have hfirst : readField I a len ^^^ (readField I b len ^^^ readField I a len) =
      readField I b len := by
    rw [← Nat.xor_assoc, Nat.xor_comm (readField I a len) (readField I b len),
      Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  have hsecond : (readField I b len ^^^ readField I a len) ^^^ readField I b len =
      readField I a len := by
    rw [Nat.xor_assoc, Nat.xor_comm (readField I a len) (readField I b len),
      ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have h1 : actGates (copyField a b len) I =
      writeField I b len (readField I b len ^^^ readField I a len) :=
    actGates_copyField hdis I
  have h2 : actGates (copyField b a len) (actGates (copyField a b len) I) =
      writeField (writeField I b len (readField I b len ^^^ readField I a len))
        a len (readField I b len) := by
    rw [h1, actGates_copyField hdis',
      readField_writeField_of_disjoint hdis', readField_writeField_self hxor, hfirst]
  rw [swapFields, actGates_append, actGates_append, h2,
    actGates_copyField hdis,
    readField_writeField_of_disjoint hdis,
    readField_writeField_self hxor, readField_writeField_self hb,
    hsecond, writeField_comm hdis', writeField_writeField]

theorem swapFields_length (a b len : Nat) : (swapFields a b len).length = 3 * len := by
  simp [swapFields, copyField_length]
  omega

theorem swapFields_no_ccx (a b len : Nat) :
    (swapFields a b len).countP RGate.isCcx = 0 := by
  simp [swapFields, copyField_no_ccx]

theorem swapFields_cx (a b len : Nat) :
    (swapFields a b len).countP RGate.isCx = 3 * len := by
  simp [swapFields, copyField_cx]
  omega

end Reversible
end VQ
