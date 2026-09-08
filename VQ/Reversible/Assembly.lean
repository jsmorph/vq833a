/-
The point addition assembly.

The assembly places seventeen component calls on one register, following
Algorithm 1 of Roetteler, Naehrig, Svore, and Lauter with its control bit
removed because `AddsPoint` is uncontrolled.  Each hypothesis is a component
specification, allowing any conforming implementation to replace that
component without changing the assembly proof.

The register is four `n`-wide fields and a shared workspace:

    asmLayout n ws = [n, n, n, n, ws]

holding `x`, `y`, `t`, and the slope, with the workspace last.  Each component's
own workspace field maps to the front of the shared one.  The components run
in sequence and each returns its workspace to zero, which its specification's
equation between basis indices forces, so sharing is sound.

The wirings are not contiguous and not in each component's layout order — step 5
multiplies the slope by `x` and writes `y`, step 8 subtracts `t` from `x` — which
is why this is built on `VQ.Reversible.Wiring` rather than on
`VQ.Reversible.Place`.
-/
import VQ.Reversible.Blocks
import VQ.Reversible.Compile
import VQ.Curve.ReversibleSpec

namespace VQ
namespace Reversible

/-! ## Point-addition register -/

/-- Four `n`-wide registers and a shared workspace. -/
def asmLayout (n ws : Nat) : Layout := [n, n, n, n, ws]

@[simp] theorem asmLayout_width (n ws : Nat) :
    (asmLayout n ws).width = 4 * n + ws := by
  simp [asmLayout, Layout.width]; omega

@[simp] theorem asmLayout_size_lt (n ws j : Nat) (hj : j < 4) :
    (asmLayout n ws).size j = n := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rfl

theorem asmLayout_offset (n ws j : Nat) (hj : j < 4) :
    (asmLayout n ws).offset j = j * n := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    (show _ = _; simp [asmLayout, Layout.offset]; try omega)

theorem asmLayout_offset_ws (n ws : Nat) : (asmLayout n ws).offset 4 = 4 * n := by
  show _ = _
  simp [asmLayout, Layout.offset]
  omega

/-! ## Component wirings

A component's data fields go to blocks below `4 * n` and its workspace to the
front of the shared one.  Disjointness is the only condition, and for these
shapes it is arithmetic in the offsets: a data block is disjoint from the
workspace because it ends at or before `4 * n`, and two data blocks are disjoint
because their offsets differ by at least `n`. -/

/-- A one-operand component: the operand block and the workspace. -/
theorem disjoint2 {n ws' o : Nat} (ho : o + n ≤ 4 * n) :
    Wiring.Disjoint [n, ws'] [o, 4 * n] := by
  intro j k hj hk hne
  have hj' : j = 0 ∨ j = 1 := by simp at hj; omega
  have hk' : k = 0 ∨ k = 1 := by simp at hk; omega
  rcases hj' with rfl | rfl <;> rcases hk' with rfl | rfl
  · exact absurd rfl hne
  · exact Or.inl ho
  · exact Or.inr ho
  · exact absurd rfl hne

/-- A two-operand component. -/
theorem disjoint3 {n ws' o₀ o₁ : Nat}
    (h₀ : o₀ + n ≤ 4 * n) (h₁ : o₁ + n ≤ 4 * n)
    (h01 : o₀ + n ≤ o₁ ∨ o₁ + n ≤ o₀) :
    Wiring.Disjoint [n, n, ws'] [o₀, o₁, 4 * n] := by
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

/-- A three-operand component. -/
theorem disjoint4 {n ws' o₀ o₁ o₂ : Nat}
    (h₀ : o₀ + n ≤ 4 * n) (h₁ : o₁ + n ≤ 4 * n) (h₂ : o₂ + n ≤ 4 * n)
    (h01 : o₀ + n ≤ o₁ ∨ o₁ + n ≤ o₀)
    (h02 : o₀ + n ≤ o₂ ∨ o₂ + n ≤ o₀)
    (h12 : o₁ + n ≤ o₂ ∨ o₂ + n ≤ o₁) :
    Wiring.Disjoint [n, n, n, ws'] [o₀, o₁, o₂, 4 * n] := by
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

/-! ## Block arithmetic

The four data blocks sit at `0`, `n`, `2n`, and `3n`, and the shared workspace at
`4n`.  `blk_le` and `blk_ne` in `VQ.Reversible.Blocks` are the general form and
discharge every wiring condition here at `b = 4`. -/

/-! ## Wirings, by component shape -/

/-- A one-operand component on block `j`. -/
def w1 (n j : Nat) : Wiring := [j * n, 4 * n]

/-- A two-operand component on blocks `j` and `k`. -/
def w2 (n j k : Nat) : Wiring := [j * n, k * n, 4 * n]

/-- A three-operand component on blocks `j`, `k`, and `l`. -/
def w3 (n j k l : Nat) : Wiring := [j * n, k * n, l * n, 4 * n]

/-! ## Assembly step

`step_write` transfers a component write from layout field `k` to assembly block
`j` through the specified wiring, while preserving every other block. -/

theorem step_write {L : Layout} {W : Wiring} {r : RCircuit} {k v I n ws j : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length) (hk : k < L.length)
    (hwf : ∀ g ∈ r.gates, g.wellFormed L.width = true)
    (hoff : W.getD k 0 = (asmLayout n ws).offset j)
    (hsize : Layout.size L k = (asmLayout n ws).size j)
    (h : act r (gatherBits (place L W) L.width I)
       = L.write (gatherBits (place L W) L.width I) k v) :
    actGates (r.gates.map (RGate.map (place L W))) I = (asmLayout n ws).write I j v := by
  rw [actGates_placed_write hd hlen hk hwf h, hoff, hsize]
  rfl

/-! ## Unary component step

`AddsConstMod` and `NegatesMod` share this shape, and the assembly uses it at
steps 1, 2, 9, 15, 16, and 17. -/

theorem gather_field1 {n ws' j I : Nat} :
    (constLayout n ws').read (gatherBits (place (constLayout n ws') (w1 n j))
        (constLayout n ws').width I) 0
      = readField I (j * n) n := by
  have := read_gatherBits (constLayout n ws') (w1 n j) 0 I (by simp [w1])
  simpa [w1, constLayout, Layout.size] using this

theorem gather_ws1 {n ws' j I : Nat} :
    (constLayout n ws').read (gatherBits (place (constLayout n ws') (w1 n j))
        (constLayout n ws').width I) 1
      = readField I (4 * n) ws' := by
  have := read_gatherBits (constLayout n ws') (w1 n j) 1 I (by simp [w1])
  simpa [w1, constLayout, Layout.size] using this

/-- Reading block `j` of the assembly. -/
theorem asm_read {n ws j I : Nat} (hj : j < 4) :
    (asmLayout n ws).read I j = readField I (j * n) n := by
  show readField I ((asmLayout n ws).offset j) ((asmLayout n ws).size j) = _
  rw [asmLayout_offset n ws j hj, asmLayout_size_lt n ws j hj]

/-- Reading the shared workspace. -/
theorem asm_read_ws {n ws I : Nat} :
    (asmLayout n ws).read I 4 = readField I (4 * n) ws := by
  show readField I ((asmLayout n ws).offset 4) ((asmLayout n ws).size 4) = _
  rw [asmLayout_offset_ws]
  rfl

/-- A component's own workspace field is clear when the shared one is. -/
theorem asm_ws_narrow {n ws ws' I : Nat} (hws : ws' ≤ ws)
    (hz : (asmLayout n ws).read I 4 = 0) : readField I (4 * n) ws' = 0 :=
  readField_narrow hws (by rw [← asm_read_ws]; exact hz)

/-- A step that adds a classical value to one block.  Steps 1, 2, 9, 16, and
17 of the assembly. -/
theorem step_addConst {m ws' n ws j c I : Nat} {r : RCircuit}
    (hcomp : AddsConstMod m ws' n c r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (constLayout n ws').width = true)
    (hws : ws' ≤ ws) (hj : j < 4) (hm : m ≤ 2 ^ n) (hc : c < m)
    (ha : (asmLayout n ws).read I j < m)
    (hz : (asmLayout n ws).read I 4 = 0) :
    actGates (r.gates.map (RGate.map (place (constLayout n ws') (w1 n j)))) I
      = (asmLayout n ws).write I j (((asmLayout n ws).read I j + c) % m) := by
  refine step_write (k := 0) (j := j) (disjoint2 (blk_le hj))
    (by simp [w1, constLayout]) (by simp [constLayout]) hwf ?_ ?_ ?_
  · show (w1 n j).getD 0 0 = _
    rw [asmLayout_offset n ws j hj]; rfl
  · show (constLayout n ws').size 0 = _
    rw [asmLayout_size_lt n ws j hj]; rfl
  · refine hcomp _ _ (gatherBits_lt _ _ _) ?_ ?_ hm ?_ hc
    · rw [gather_field1, ← asm_read hj]
    · rw [gather_ws1]; exact asm_ws_narrow hws hz
    · exact ha

/-- A step that negates one block.  Step 15. -/
theorem step_negate {m ws' n ws j I : Nat} {r : RCircuit}
    (hcomp : NegatesMod m ws' n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (constLayout n ws').width = true)
    (hws : ws' ≤ ws) (hj : j < 4) (hm : m ≤ 2 ^ n)
    (ha : (asmLayout n ws).read I j < m)
    (hz : (asmLayout n ws).read I 4 = 0) :
    actGates (r.gates.map (RGate.map (place (constLayout n ws') (w1 n j)))) I
      = (asmLayout n ws).write I j ((m - (asmLayout n ws).read I j) % m) := by
  refine step_write (k := 0) (j := j) (disjoint2 (blk_le hj))
    (by simp [w1, constLayout]) (by simp [constLayout]) hwf ?_ ?_ ?_
  · show (w1 n j).getD 0 0 = _
    rw [asmLayout_offset n ws j hj]; rfl
  · show (constLayout n ws').size 0 = _
    rw [asmLayout_size_lt n ws j hj]; rfl
  · refine hcomp _ _ (gatherBits_lt _ _ _) ?_ ?_ hm ?_
    · rw [gather_field1, ← asm_read hj]
    · rw [gather_ws1]; exact asm_ws_narrow hws hz
    · exact ha

/-! ## Binary component steps

`InvertsField`, `SquaresMod`, and `SubsMod` share the layout `[n, n, ws]`.  The
first two write their second field and `SubsMod` writes its second field too, so
all three place the same way.  What differs is the value written and the
hypotheses. -/

/-- A step that inverts one block into another.  Steps 3 and 12. -/
theorem step_invert {ws' n ws j k I : Nat} {r : RCircuit}
    (hcomp : InvertsField ws' n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (unaryLayout n ws').width = true)
    (hws : ws' ≤ ws) (hj : j < 4) (hk : k < 4) (hjk : j ≠ k)
    (hp : Curve.p ≤ 2 ^ n)
    (ha : (asmLayout n ws).read I j < Curve.p)
    (hout : (asmLayout n ws).read I k = 0)
    (hz : (asmLayout n ws).read I 4 = 0) :
    actGates (r.gates.map (RGate.map (place (unaryLayout n ws') (w2 n j k)))) I
      = (asmLayout n ws).write I k (Curve.inv ((asmLayout n ws).read I j)) := by
  refine step_write (k := 1) (j := k) (disjoint3 (blk_le hj) (blk_le hk) (blk_ne hjk))
    (by simp [w2, unaryLayout]) (by simp [unaryLayout]) hwf ?_ ?_ ?_
  · show (w2 n j k).getD 1 0 = _
    rw [asmLayout_offset n ws k hk]; rfl
  · show (unaryLayout n ws').size 1 = _
    rw [asmLayout_size_lt n ws k hk]; rfl
  · refine hcomp _ _ (gatherBits_lt _ _ _) ?_ ?_ ?_ hp ha
    · rw [read_gatherBits (unaryLayout n ws') (w2 n j k) 0 I (by simp [w2])]
      show readField I (j * n) n = _
      rw [← asm_read hj]
    · rw [read_gatherBits (unaryLayout n ws') (w2 n j k) 1 I (by simp [w2])]
      show readField I (k * n) n = _
      rw [← asm_read hk]; exact hout
    · rw [read_gatherBits (unaryLayout n ws') (w2 n j k) 2 I (by simp [w2])]
      show readField I (4 * n) ws' = _
      exact asm_ws_narrow hws hz

/-- A step that squares one block into another.  Step 7. -/
theorem step_square {m ws' n ws j k I : Nat} {r : RCircuit}
    (hcomp : SquaresMod m ws' n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (unaryLayout n ws').width = true)
    (hws : ws' ≤ ws) (hj : j < 4) (hk : k < 4) (hjk : j ≠ k)
    (hm : m ≤ 2 ^ n)
    (ha : (asmLayout n ws).read I j < m)
    (hout : (asmLayout n ws).read I k = 0)
    (hz : (asmLayout n ws).read I 4 = 0) :
    actGates (r.gates.map (RGate.map (place (unaryLayout n ws') (w2 n j k)))) I
      = (asmLayout n ws).write I k
          ((asmLayout n ws).read I j * (asmLayout n ws).read I j % m) := by
  refine step_write (k := 1) (j := k) (disjoint3 (blk_le hj) (blk_le hk) (blk_ne hjk))
    (by simp [w2, unaryLayout]) (by simp [unaryLayout]) hwf ?_ ?_ ?_
  · show (w2 n j k).getD 1 0 = _
    rw [asmLayout_offset n ws k hk]; rfl
  · show (unaryLayout n ws').size 1 = _
    rw [asmLayout_size_lt n ws k hk]; rfl
  · refine hcomp _ _ (gatherBits_lt _ _ _) ?_ ?_ ?_ hm ha
    · rw [read_gatherBits (unaryLayout n ws') (w2 n j k) 0 I (by simp [w2])]
      show readField I (j * n) n = _
      rw [← asm_read hj]
    · rw [read_gatherBits (unaryLayout n ws') (w2 n j k) 1 I (by simp [w2])]
      show readField I (k * n) n = _
      rw [← asm_read hk]; exact hout
    · rw [read_gatherBits (unaryLayout n ws') (w2 n j k) 2 I (by simp [w2])]
      show readField I (4 * n) ws' = _
      exact asm_ws_narrow hws hz

/-- A step that subtracts one block from another, in place.  Step 8.
`SubsMod` writes its second field, so the block being reduced is `k`. -/
theorem step_sub {m ws' n ws j k I : Nat} {r : RCircuit}
    (hcomp : SubsMod m ws' n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (adderLayout n ws').width = true)
    (hws : ws' ≤ ws) (hj : j < 4) (hk : k < 4) (hjk : j ≠ k)
    (hm : m ≤ 2 ^ n)
    (ha : (asmLayout n ws).read I j < m)
    (hb : (asmLayout n ws).read I k < m)
    (hz : (asmLayout n ws).read I 4 = 0) :
    actGates (r.gates.map (RGate.map (place (adderLayout n ws') (w2 n j k)))) I
      = (asmLayout n ws).write I k
          (((asmLayout n ws).read I k + (m - (asmLayout n ws).read I j)) % m) := by
  refine step_write (k := 1) (j := k) (disjoint3 (blk_le hj) (blk_le hk) (blk_ne hjk))
    (by simp [w2, adderLayout]) (by simp [adderLayout]) hwf ?_ ?_ ?_
  · show (w2 n j k).getD 1 0 = _
    rw [asmLayout_offset n ws k hk]; rfl
  · show (adderLayout n ws').size 1 = _
    rw [asmLayout_size_lt n ws k hk]; rfl
  · refine hcomp _ _ _ (gatherBits_lt _ _ _) ?_ ?_ ?_ hm ha hb
    · rw [read_gatherBits (adderLayout n ws') (w2 n j k) 0 I (by simp [w2])]
      show readField I (j * n) n = _
      rw [← asm_read hj]
    · rw [read_gatherBits (adderLayout n ws') (w2 n j k) 1 I (by simp [w2])]
      show readField I (k * n) n = _
      rw [← asm_read hk]
    · rw [read_gatherBits (adderLayout n ws') (w2 n j k) 2 I (by simp [w2])]
      show readField I (4 * n) ws' = _
      exact asm_ws_narrow hws hz

/-! ## Ternary component step

`MulsMod` reads two blocks and writes a third.  Steps 4, 5, 11, and 13 are this
step, two of them run backwards. -/

/-- A step that multiplies two blocks into a third. -/
theorem step_mul {m ws' n ws j k l I : Nat} {r : RCircuit}
    (hcomp : MulsMod m ws' n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (mulLayout n ws').width = true)
    (hws : ws' ≤ ws) (hj : j < 4) (hk : k < 4) (hl : l < 4)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hm : m ≤ 2 ^ n)
    (ha : (asmLayout n ws).read I j < m)
    (hb : (asmLayout n ws).read I k < m)
    (hout : (asmLayout n ws).read I l = 0)
    (hz : (asmLayout n ws).read I 4 = 0) :
    actGates (r.gates.map (RGate.map (place (mulLayout n ws') (w3 n j k l)))) I
      = (asmLayout n ws).write I l
          ((asmLayout n ws).read I j * (asmLayout n ws).read I k % m) := by
  refine step_write (k := 2) (j := l)
    (disjoint4 (blk_le hj) (blk_le hk) (blk_le hl)
      (blk_ne hjk) (blk_ne hjl) (blk_ne hkl))
    (by simp [w3, mulLayout]) (by simp [mulLayout]) hwf ?_ ?_ ?_
  · show (w3 n j k l).getD 2 0 = _
    rw [asmLayout_offset n ws l hl]; rfl
  · show (mulLayout n ws').size 2 = _
    rw [asmLayout_size_lt n ws l hl]; rfl
  · refine hcomp _ _ _ (gatherBits_lt _ _ _) ?_ ?_ ?_ ?_ hm ha hb
    · rw [read_gatherBits (mulLayout n ws') (w3 n j k l) 0 I (by simp [w3])]
      show readField I (j * n) n = _
      rw [← asm_read hj]
    · rw [read_gatherBits (mulLayout n ws') (w3 n j k l) 1 I (by simp [w3])]
      show readField I (k * n) n = _
      rw [← asm_read hk]
    · rw [read_gatherBits (mulLayout n ws') (w3 n j k l) 2 I (by simp [w3])]
      show readField I (l * n) n = _
      rw [← asm_read hl]; exact hout
    · rw [read_gatherBits (mulLayout n ws') (w3 n j k l) 3 I (by simp [w3])]
      show readField I (4 * n) ws' = _
      exact asm_ws_narrow hws hz

/-! ## Reversed component step

Steps 5 and 13 run a multiplier backwards, and steps 6, 10, and 14 run an
inverter or a squarer backwards.  Each is the same lemma: if the forward step
takes `J` to the current state, the reversed step takes the current state back to
`J`.  What has to be supplied is the `J`, which the arithmetic determines. -/

theorem step_reverse {L : Layout} {W : Wiring} {gs : List RGate} {n ws I J : Nat}
    (hd : Wiring.Disjoint L W) (hlen : L.length ≤ W.length)
    (hW : ∀ j, j < L.length → W.getD j 0 + Layout.size L j ≤ (asmLayout n ws).width)
    (hwf : ∀ g ∈ gs, g.wellFormed L.width = true)
    (hfwd : actGates (gs.map (RGate.map (place L W))) J = I) :
    actGates (gs.map (RGate.map (place L W))).reverse I = J := by
  rw [← hfwd]
  exact actGates_placed_reverse (Wd := (asmLayout n ws).width) hd hlen hW hwf J

/-! ## Point-addition state

Seventeen steps means seventeen intermediate registers, and each step's
hypotheses are the previous register's field values.  `St` bundles them so a step
is one line and the register itself never has to be named. -/

/-- The four blocks hold `x`, `y`, `t`, and `l`, and the workspace is clear. -/
structure St (n ws I x y t l : Nat) : Prop where
  f0 : (asmLayout n ws).read I 0 = x
  f1 : (asmLayout n ws).read I 1 = y
  f2 : (asmLayout n ws).read I 2 = t
  f3 : (asmLayout n ws).read I 3 = l
  f4 : (asmLayout n ws).read I 4 = 0

/-- Writing block `j` advances the state. -/
theorem St.write0 {n ws I x y t l v : Nat} (h : St n ws I x y t l)
    (hv : v < 2 ^ (asmLayout n ws).size 0) :
    St n ws ((asmLayout n ws).write I 0 v) v y t l where
  f0 := Layout.read_write_self hv
  f1 := by rw [Layout.read_write_ne (by decide), h.f1]
  f2 := by rw [Layout.read_write_ne (by decide), h.f2]
  f3 := by rw [Layout.read_write_ne (by decide), h.f3]
  f4 := by rw [Layout.read_write_ne (by decide), h.f4]

theorem St.write1 {n ws I x y t l v : Nat} (h : St n ws I x y t l)
    (hv : v < 2 ^ (asmLayout n ws).size 1) :
    St n ws ((asmLayout n ws).write I 1 v) x v t l where
  f0 := by rw [Layout.read_write_ne (by decide), h.f0]
  f1 := Layout.read_write_self hv
  f2 := by rw [Layout.read_write_ne (by decide), h.f2]
  f3 := by rw [Layout.read_write_ne (by decide), h.f3]
  f4 := by rw [Layout.read_write_ne (by decide), h.f4]

theorem St.write2 {n ws I x y t l v : Nat} (h : St n ws I x y t l)
    (hv : v < 2 ^ (asmLayout n ws).size 2) :
    St n ws ((asmLayout n ws).write I 2 v) x y v l where
  f0 := by rw [Layout.read_write_ne (by decide), h.f0]
  f1 := by rw [Layout.read_write_ne (by decide), h.f1]
  f2 := Layout.read_write_self hv
  f3 := by rw [Layout.read_write_ne (by decide), h.f3]
  f4 := by rw [Layout.read_write_ne (by decide), h.f4]

theorem St.write3 {n ws I x y t l v : Nat} (h : St n ws I x y t l)
    (hv : v < 2 ^ (asmLayout n ws).size 3) :
    St n ws ((asmLayout n ws).write I 3 v) x y t v where
  f0 := by rw [Layout.read_write_ne (by decide), h.f0]
  f1 := by rw [Layout.read_write_ne (by decide), h.f1]
  f2 := by rw [Layout.read_write_ne (by decide), h.f2]
  f3 := Layout.read_write_self hv
  f4 := by rw [Layout.read_write_ne (by decide), h.f4]

/-- A value below the prime fits a block, when the block is wide enough for the
prime. -/
theorem fits {n ws j v : Nat} (hj : j < 4) (hp : Curve.p ≤ 2 ^ n) (hv : v < Curve.p) :
    v < 2 ^ (asmLayout n ws).size j := by
  rw [asmLayout_size_lt n ws j hj]
  exact Nat.lt_of_lt_of_le hv hp

/-! ## Range conditions for the reversed steps

`step_reverse` needs every block the wiring names to lie inside the assembly's
register.  One lemma per component shape. -/

theorem wW1 {n ws ws' j : Nat} (hj : j < 4) (hws : ws' ≤ ws) :
    ∀ i, i < (constLayout n ws').length →
      (w1 n j).getD i 0 + Layout.size (constLayout n ws') i ≤ (asmLayout n ws).width := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by simp [constLayout] at hi; omega
  rw [asmLayout_width]
  rcases hi' with rfl | rfl
  · show j * n + n ≤ 4 * n + ws
    have := blk_le (n := n) hj; omega
  · show 4 * n + ws' ≤ 4 * n + ws
    omega

theorem wW2 {n ws ws' j k : Nat} (hj : j < 4) (hk : k < 4) (hws : ws' ≤ ws) :
    ∀ i, i < (unaryLayout n ws').length →
      (w2 n j k).getD i 0 + Layout.size (unaryLayout n ws') i ≤ (asmLayout n ws).width := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by simp [unaryLayout] at hi; omega
  rw [asmLayout_width]
  rcases hi' with rfl | rfl | rfl
  · show j * n + n ≤ 4 * n + ws
    have := blk_le (n := n) hj; omega
  · show k * n + n ≤ 4 * n + ws
    have := blk_le (n := n) hk; omega
  · show 4 * n + ws' ≤ 4 * n + ws
    omega

theorem wW3 {n ws ws' j k l : Nat} (hj : j < 4) (hk : k < 4) (hl : l < 4) (hws : ws' ≤ ws) :
    ∀ i, i < (mulLayout n ws').length →
      (w3 n j k l).getD i 0 + Layout.size (mulLayout n ws') i ≤ (asmLayout n ws).width := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp [mulLayout] at hi; omega
  rw [asmLayout_width]
  rcases hi' with rfl | rfl | rfl | rfl
  · show j * n + n ≤ 4 * n + ws
    have := blk_le (n := n) hj; omega
  · show k * n + n ≤ 4 * n + ws
    have := blk_le (n := n) hk; omega
  · show l * n + n ≤ 4 * n + ws
    have := blk_le (n := n) hl; omega
  · show 4 * n + ws' ≤ 4 * n + ws
    omega

/-! ## Point-addition schedule

The gate lists, and then the trace.  Blocks: `x` is 0, `y` is 1, `t` is 2, and
the slope is 3. -/

/-- The assembled circuit.  Each component is a parameter, so any circuit
satisfying the corresponding specification can replace it. -/
def pointAdd (n ws wa wn wi wq wu wm ax ay : Nat)
    (addc : Nat → RCircuit) (negc invc sqc subc mulc : RCircuit) : RCircuit :=
  let A := fun (c j : Nat) => (addc c).gates.map (RGate.map (place (constLayout n wa) (w1 n j)))
  let N := fun (j : Nat) => negc.gates.map (RGate.map (place (constLayout n wn) (w1 n j)))
  let V := fun (j k : Nat) => invc.gates.map (RGate.map (place (unaryLayout n wi) (w2 n j k)))
  let Q := fun (j k : Nat) => sqc.gates.map (RGate.map (place (unaryLayout n wq) (w2 n j k)))
  let S := fun (j k : Nat) => subc.gates.map (RGate.map (place (adderLayout n wu) (w2 n j k)))
  let M := fun (j k l : Nat) => mulc.gates.map (RGate.map (place (mulLayout n wm) (w3 n j k l)))
  { width := (asmLayout n ws).width,
    gates :=
      A (Curve.neg ax) 0 ++ A (Curve.neg ay) 1 ++ V 0 2 ++ M 1 2 3
        ++ (M 3 0 1).reverse ++ (V 0 2).reverse ++ Q 3 2 ++ S 2 0
        ++ A (Curve.mul 3 ax) 0 ++ (Q 3 2).reverse ++ M 3 0 1 ++ V 0 2
        ++ (M 2 1 3).reverse ++ (V 0 2).reverse ++ N 0
        ++ A (Curve.neg ay) 1 ++ A ax 0 }

/-! ## Reversed schedule

Steps 5, 6, 10, 13, and 14 undo a component.  Each is the same argument: the
block the component writes already holds what the component would write, so
running the component on the state with that block cleared reproduces the current
state, and the reversed component therefore clears it. -/

theorem step_mul_rev {m ws' n ws j k l I : Nat} {r : RCircuit}
    (hcomp : MulsMod m ws' n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (mulLayout n ws').width = true)
    (hws : ws' ≤ ws) (hj : j < 4) (hk : k < 4) (hl : l < 4)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (hm : m ≤ 2 ^ n)
    (haj : (asmLayout n ws).read I j < m) (hak : (asmLayout n ws).read I k < m)
    (hz : (asmLayout n ws).read I 4 = 0)
    (hprod : (asmLayout n ws).read I j * (asmLayout n ws).read I k % m
               = (asmLayout n ws).read I l) :
    actGates (r.gates.map (RGate.map (place (mulLayout n ws') (w3 n j k l)))).reverse I
      = (asmLayout n ws).write I l 0 := by
  refine step_reverse (n := n) (ws := ws)
    (disjoint4 (blk_le hj) (blk_le hk) (blk_le hl) (blk_ne hjk) (blk_ne hjl) (blk_ne hkl))
    (by simp [w3, mulLayout]) (wW3 hj hk hl hws) hwf ?_
  rw [step_mul hcomp hwf hws hj hk hl hjk hjl hkl hm
    (by rw [Layout.read_write_ne hjl]; exact haj)
    (by rw [Layout.read_write_ne hkl]; exact hak)
    (Layout.read_write_self (Nat.two_pow_pos _))
    (by rw [Layout.read_write_ne (show (4 : Nat) ≠ l by omega)]; exact hz)]
  rw [Layout.read_write_ne hjl, Layout.read_write_ne hkl, hprod,
    Layout.write_write_self, Layout.write_read]

theorem step_invert_rev {ws' n ws j k I : Nat} {r : RCircuit}
    (hcomp : InvertsField ws' n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (unaryLayout n ws').width = true)
    (hws : ws' ≤ ws) (hj : j < 4) (hk : k < 4) (hjk : j ≠ k)
    (hp : Curve.p ≤ 2 ^ n)
    (haj : (asmLayout n ws).read I j < Curve.p)
    (hz : (asmLayout n ws).read I 4 = 0)
    (hval : Curve.inv ((asmLayout n ws).read I j) = (asmLayout n ws).read I k) :
    actGates (r.gates.map (RGate.map (place (unaryLayout n ws') (w2 n j k)))).reverse I
      = (asmLayout n ws).write I k 0 := by
  refine step_reverse (n := n) (ws := ws)
    (disjoint3 (blk_le hj) (blk_le hk) (blk_ne hjk))
    (by simp [w2, unaryLayout]) (wW2 hj hk hws) hwf ?_
  rw [step_invert hcomp hwf hws hj hk hjk hp
    (by rw [Layout.read_write_ne hjk]; exact haj)
    (Layout.read_write_self (Nat.two_pow_pos _))
    (by rw [Layout.read_write_ne (show (4 : Nat) ≠ k by omega)]; exact hz)]
  rw [Layout.read_write_ne hjk, hval, Layout.write_write_self, Layout.write_read]

theorem step_square_rev {m ws' n ws j k I : Nat} {r : RCircuit}
    (hcomp : SquaresMod m ws' n r)
    (hwf : ∀ g ∈ r.gates, g.wellFormed (unaryLayout n ws').width = true)
    (hws : ws' ≤ ws) (hj : j < 4) (hk : k < 4) (hjk : j ≠ k) (hm : m ≤ 2 ^ n)
    (haj : (asmLayout n ws).read I j < m)
    (hz : (asmLayout n ws).read I 4 = 0)
    (hval : (asmLayout n ws).read I j * (asmLayout n ws).read I j % m
              = (asmLayout n ws).read I k) :
    actGates (r.gates.map (RGate.map (place (unaryLayout n ws') (w2 n j k)))).reverse I
      = (asmLayout n ws).write I k 0 := by
  refine step_reverse (n := n) (ws := ws)
    (disjoint3 (blk_le hj) (blk_le hk) (blk_ne hjk))
    (by simp [w2, unaryLayout]) (wW2 hj hk hws) hwf ?_
  rw [step_square hcomp hwf hws hj hk hjk hm
    (by rw [Layout.read_write_ne hjk]; exact haj)
    (Layout.read_write_self (Nat.two_pow_pos _))
    (by rw [Layout.read_write_ne (show (4 : Nat) ≠ k by omega)]; exact hz)]
  rw [Layout.read_write_ne hjk, hval, Layout.write_write_self, Layout.write_read]

/-! ## Arithmetic state trace

The seventeen steps, in order.  Each is one rewrite with the step lemma above and
one advance of the state, and the arithmetic identities enter at steps 5, 9, 11,
13, 15, 16, and 17. -/

set_option maxHeartbeats 1000000 in
theorem pointAdd_trace {n ws wa wn wi wq wu wm : Nat} {addc : Nat → RCircuit}
    {negc invc sqc subc mulc : RCircuit}
    (hlaw : Curve.InverseLaw) (halgl : Curve.Alg1Law)
    (hadd : ∀ c, AddsConstMod Curve.p wa n c (addc c))
    (haddwf : ∀ c, ∀ g ∈ (addc c).gates, g.wellFormed (constLayout n wa).width = true)
    (hneg : NegatesMod Curve.p wn n negc)
    (hnegwf : ∀ g ∈ negc.gates, g.wellFormed (constLayout n wn).width = true)
    (hinv : InvertsField wi n invc)
    (hinvwf : ∀ g ∈ invc.gates, g.wellFormed (unaryLayout n wi).width = true)
    (hsq : SquaresMod Curve.p wq n sqc)
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout n wq).width = true)
    (hsub : SubsMod Curve.p wu n subc)
    (hsubwf : ∀ g ∈ subc.gates, g.wellFormed (adderLayout n wu).width = true)
    (hmul : MulsMod Curve.p wm n mulc)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout n wm).width = true)
    (hwa : wa ≤ ws) (hwn : wn ≤ ws) (hwi : wi ≤ ws) (hwq : wq ≤ ws)
    (hwu : wu ≤ ws) (hwm : wm ≤ ws) (hp : Curve.p ≤ 2 ^ n)
    {ax ay x y I : Nat} (hax : ax < Curve.p) (hay : ay < Curve.p) (hx : x < Curve.p) (hy : y < Curve.p)
    (hxne : x ≠ ax) (hrec : (Curve.addPoint x y ax ay).1 ≠ ax)
    (st : St n ws I x y 0 0) :
    St n ws (act (pointAdd n ws wa wn wi wq wu wm ax ay addc negc invc sqc subc mulc) I)
      (Curve.addPoint x y ax ay).1 (Curve.addPoint x y ax ay).2 0 0 := by
  have hX : Curve.sub x ax < Curve.p := Curve.sub_lt _ _
  have hY : Curve.sub y ay < Curve.p := Curve.sub_lt _ _
  have hT : Curve.inv (Curve.sub x ax) < Curve.p := Curve.inv_lt _
  have hL : Curve.slope x y ax ay < Curve.p := Curve.slope_lt _ _ _ _
  have hS : Curve.mul (Curve.slope x y ax ay) (Curve.slope x y ax ay) < Curve.p := Curve.mul_lt _ _
  have hXS : Curve.sub (Curve.sub x ax) (Curve.mul (Curve.slope x y ax ay) (Curve.slope x y ax ay)) < Curve.p := Curve.sub_lt _ _
  have hx3 : (Curve.addPoint x y ax ay).1 < Curve.p := Curve.representable_addPoint_fst _ _ _ _
  have hy3 : (Curve.addPoint x y ax ay).2 < Curve.p := Curve.representable_addPoint_snd _ _ _ _
  have hD : Curve.sub ax (Curve.addPoint x y ax ay).1 < Curve.p := Curve.sub_lt _ _
  have hYY : Curve.add (Curve.addPoint x y ax ay).2 ay < Curve.p := Curve.add_lt _ _
  have hID : Curve.inv (Curve.sub ax (Curve.addPoint x y ax ay).1) < Curve.p := Curve.inv_lt _
  have hXA : Curve.sub (Curve.addPoint x y ax ay).1 ax < Curve.p := Curve.sub_lt _ _
  have halg := halgl ax ay x y hax hay hx hy hxne hrec
  have hcancel := Curve.slope_cancel (ax := ax) (ay := ay) (x := x) (y := y) hlaw hax hx hxne
  have hrecover := Curve.slope_recover hlaw halg hax hrec
  show St n ws (actGates _ I) _ _ _ _
  simp only [pointAdd, actGates_append]
  -- 1
  rw [step_addConst (hadd (Curve.neg ax)) (haddwf _) hwa (by omega) hp (Curve.neg_lt ax)
    (by rw [st.f0]; exact hx) st.f4, st.f0, Curve.add_neg_eq_sub hax]
  have s1 := st.write0 (fits (by omega) hp hX)
  -- 2
  rw [step_addConst (hadd (Curve.neg ay)) (haddwf _) hwa (by omega) hp (Curve.neg_lt ay)
    (by rw [s1.f1]; exact hy) s1.f4, s1.f1, Curve.add_neg_eq_sub hay]
  have s2 := s1.write1 (fits (by omega) hp hY)
  -- 3
  rw [step_invert hinv hinvwf hwi (by omega) (by omega) (by decide) hp
    (by rw [s2.f0]; exact hX) s2.f2 s2.f4, s2.f0]
  have s3 := s2.write2 (fits (by omega) hp hT)
  -- 4
  rw [step_mul hmul hmulwf hwm (by omega) (by omega) (by omega)
    (by decide) (by decide) (by decide) hp (by rw [s3.f1]; exact hY)
    (by rw [s3.f2]; exact hT) s3.f3 s3.f4, s3.f1, s3.f2,
    show Curve.sub y ay * Curve.inv (Curve.sub x ax) % Curve.p = Curve.slope x y ax ay from rfl]
  have s4 := s3.write3 (fits (by omega) hp hL)
  -- 5
  rw [step_mul_rev hmul hmulwf hwm (by omega) (by omega) (by omega)
    (by decide) (by decide) (by decide) hp (by rw [s4.f3]; exact hL)
    (by rw [s4.f0]; exact hX) s4.f4
    (by rw [s4.f3, s4.f0, s4.f1]; exact hcancel)]
  have s5 := s4.write1 (fits (by omega) hp Curve.p_pos)
  -- 6
  rw [step_invert_rev hinv hinvwf hwi (by omega) (by omega) (by decide) hp
    (by rw [s5.f0]; exact hX) s5.f4 (by rw [s5.f0, s5.f2]; try rfl)]
  have s6 := s5.write2 (fits (by omega) hp Curve.p_pos)
  -- 7
  rw [step_square hsq hsqwf hwq (by omega) (by omega) (by decide) hp
    (by rw [s6.f3]; exact hL) s6.f2 s6.f4, s6.f3,
    show Curve.slope x y ax ay * Curve.slope x y ax ay % Curve.p
      = Curve.mul (Curve.slope x y ax ay) (Curve.slope x y ax ay) from rfl]
  have s7 := s6.write2 (fits (by omega) hp hS)
  -- 8
  rw [step_sub hsub hsubwf hwu (by omega) (by omega) (by decide) hp
    (by rw [s7.f2]; exact hS) (by rw [s7.f0]; exact hX) s7.f4, s7.f0, s7.f2,
    Curve.sub_eq_mod hS]
  have s8 := s7.write0 (fits (by omega) hp hXS)
  -- 9
  rw [step_addConst (hadd (Curve.mul 3 ax)) (haddwf _) hwa (by omega) hp (Curve.mul_lt _ _)
    (by rw [s8.f0]; exact hXS) s8.f4, s8.f0]
  rw [show (Curve.sub (Curve.sub x ax) (Curve.mul (Curve.slope x y ax ay) (Curve.slope x y ax ay)) + Curve.mul 3 ax) % Curve.p
      = Curve.sub ax (Curve.addPoint x y ax ay).1 from halg.xShift]
  have s9 := s8.write0 (fits (by omega) hp hD)
  -- 10
  rw [step_square_rev hsq hsqwf hwq (by omega) (by omega) (by decide) hp
    (by rw [s9.f3]; exact hL) s9.f4 (by rw [s9.f3, s9.f2]; try rfl)]
  have s10 := s9.write2 (fits (by omega) hp Curve.p_pos)
  -- 11
  rw [step_mul hmul hmulwf hwm (by omega) (by omega) (by omega)
    (by decide) (by decide) (by decide) hp (by rw [s10.f3]; exact hL)
    (by rw [s10.f0]; exact hD) s10.f1 s10.f4, s10.f3, s10.f0]
  rw [show (Curve.slope x y ax ay * Curve.sub ax (Curve.addPoint x y ax ay).1) % Curve.p
      = Curve.add (Curve.addPoint x y ax ay).2 ay from halg.yShift]
  have s11 := s10.write1 (fits (by omega) hp hYY)
  -- 12
  rw [step_invert hinv hinvwf hwi (by omega) (by omega) (by decide) hp
    (by rw [s11.f0]; exact hD) s11.f2 s11.f4, s11.f0]
  have s12 := s11.write2 (fits (by omega) hp hID)
  -- 13
  rw [step_mul_rev hmul hmulwf hwm (by omega) (by omega) (by omega)
    (by decide) (by decide) (by decide) hp (by rw [s12.f2]; exact hID)
    (by rw [s12.f1]; exact hYY) s12.f4
    (by rw [s12.f2, s12.f1, s12.f3]; exact hrecover)]
  have s13 := s12.write3 (fits (by omega) hp Curve.p_pos)
  -- 14
  rw [step_invert_rev hinv hinvwf hwi (by omega) (by omega) (by decide) hp
    (by rw [s13.f0]; exact hD) s13.f4 (by rw [s13.f0, s13.f2]; try rfl)]
  have s14 := s13.write2 (fits (by omega) hp Curve.p_pos)
  -- 15
  rw [step_negate hneg hnegwf hwn (by omega) hp (by rw [s14.f0]; exact hD) s14.f4, s14.f0]
  rw [show (Curve.p - Curve.sub ax (Curve.addPoint x y ax ay).1) % Curve.p = Curve.sub (Curve.addPoint x y ax ay).1 ax from by
    rw [← Curve.neg_eq hD, Curve.neg_sub hax hx3]]
  have s15 := s14.write0 (fits (by omega) hp hXA)
  -- 16
  rw [step_addConst (hadd (Curve.neg ay)) (haddwf _) hwa (by omega) hp (Curve.neg_lt ay)
    (by rw [s15.f1]; exact hYY) s15.f4, s15.f1, Curve.add_neg_eq_sub hay,
    Curve.add_sub_cancel hy3 hay]
  have s16 := s15.write1 (fits (by omega) hp hy3)
  -- 17
  rw [step_addConst (hadd ax) (haddwf _) hwa (by omega) hp hax
    (by rw [s16.f0]; exact hXA) s16.f4, s16.f0]
  rw [show (Curve.sub (Curve.addPoint x y ax ay).1 ax + ax) % Curve.p = (Curve.addPoint x y ax ay).1 from
    Curve.sub_add_cancel hx3 hax]
  exact s16.write0 (fits (by omega) hp hx3)

/-! ## Well-formedness of the assembly

Seventeen placed components, each well formed at the assembly's width by
`wellFormed_placeGates`.  Reversal changes no gate. -/

theorem pointAdd_wellFormed {n ws wa wn wi wq wu wm ax ay : Nat} {addc : Nat → RCircuit}
    {negc invc sqc subc mulc : RCircuit}
    (haddwf : ∀ c, ∀ g ∈ (addc c).gates, g.wellFormed (constLayout n wa).width = true)
    (hnegwf : ∀ g ∈ negc.gates, g.wellFormed (constLayout n wn).width = true)
    (hinvwf : ∀ g ∈ invc.gates, g.wellFormed (unaryLayout n wi).width = true)
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout n wq).width = true)
    (hsubwf : ∀ g ∈ subc.gates, g.wellFormed (adderLayout n wu).width = true)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout n wm).width = true)
    (hwa : wa ≤ ws) (hwn : wn ≤ ws) (hwi : wi ≤ ws) (hwq : wq ≤ ws)
    (hwu : wu ≤ ws) (hwm : wm ≤ ws) :
    (pointAdd n ws wa wn wi wq wu wm ax ay addc negc invc sqc subc mulc).wellFormed = true := by
  have hA : ∀ c j, j < 4 →
      ((addc c).gates.map (RGate.map (place (constLayout n wa) (w1 n j)))).all
        (RGate.wellFormed (asmLayout n ws).width) = true := fun c j hj =>
    wellFormed_placeGates (disjoint2 (blk_le hj)) (by simp [w1, constLayout])
      (wW1 hj hwa) (haddwf c)
  have hN : ∀ j, j < 4 →
      (negc.gates.map (RGate.map (place (constLayout n wn) (w1 n j)))).all
        (RGate.wellFormed (asmLayout n ws).width) = true := fun j hj =>
    wellFormed_placeGates (disjoint2 (blk_le hj)) (by simp [w1, constLayout])
      (wW1 hj hwn) hnegwf
  have hV : ∀ j k, j < 4 → k < 4 → j ≠ k →
      (invc.gates.map (RGate.map (place (unaryLayout n wi) (w2 n j k)))).all
        (RGate.wellFormed (asmLayout n ws).width) = true := fun j k hj hk hjk =>
    wellFormed_placeGates (disjoint3 (blk_le hj) (blk_le hk) (blk_ne hjk))
      (by simp [w2, unaryLayout]) (wW2 hj hk hwi) hinvwf
  have hQ : ∀ j k, j < 4 → k < 4 → j ≠ k →
      (sqc.gates.map (RGate.map (place (unaryLayout n wq) (w2 n j k)))).all
        (RGate.wellFormed (asmLayout n ws).width) = true := fun j k hj hk hjk =>
    wellFormed_placeGates (disjoint3 (blk_le hj) (blk_le hk) (blk_ne hjk))
      (by simp [w2, unaryLayout]) (wW2 hj hk hwq) hsqwf
  have hS : ∀ j k, j < 4 → k < 4 → j ≠ k →
      (subc.gates.map (RGate.map (place (adderLayout n wu) (w2 n j k)))).all
        (RGate.wellFormed (asmLayout n ws).width) = true := fun j k hj hk hjk =>
    wellFormed_placeGates (disjoint3 (blk_le hj) (blk_le hk) (blk_ne hjk))
      (by simp [w2, adderLayout]) (wW2 hj hk hwu) hsubwf
  have hM : ∀ j k l, j < 4 → k < 4 → l < 4 → j ≠ k → j ≠ l → k ≠ l →
      (mulc.gates.map (RGate.map (place (mulLayout n wm) (w3 n j k l)))).all
        (RGate.wellFormed (asmLayout n ws).width) = true :=
    fun j k l hj hk hl hjk hjl hkl =>
      wellFormed_placeGates
        (disjoint4 (blk_le hj) (blk_le hk) (blk_le hl) (blk_ne hjk) (blk_ne hjl) (blk_ne hkl))
        (by simp [w3, mulLayout]) (wW3 hj hk hl hwm) hmulwf
  show (pointAdd n ws wa wn wi wq wu wm ax ay addc negc invc sqc subc mulc).gates.all
    (RGate.wellFormed (asmLayout n ws).width) = true
  simp only [pointAdd, List.all_append, List.all_reverse, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hA _ 0 (by omega), hA _ 1 (by omega)⟩,
    hV 0 2 (by omega) (by omega) (by decide)⟩,
    hM 1 2 3 (by omega) (by omega) (by omega) (by decide) (by decide) (by decide)⟩,
    hM 3 0 1 (by omega) (by omega) (by omega) (by decide) (by decide) (by decide)⟩,
    hV 0 2 (by omega) (by omega) (by decide)⟩,
    hQ 3 2 (by omega) (by omega) (by decide)⟩,
    hS 2 0 (by omega) (by omega) (by decide)⟩,
    hA _ 0 (by omega)⟩,
    hQ 3 2 (by omega) (by omega) (by decide)⟩,
    hM 3 0 1 (by omega) (by omega) (by omega) (by decide) (by decide) (by decide)⟩,
    hV 0 2 (by omega) (by omega) (by decide)⟩,
    hM 2 1 3 (by omega) (by omega) (by omega) (by decide) (by decide) (by decide)⟩,
    hV 0 2 (by omega) (by omega) (by decide)⟩,
    hN 0 (by omega)⟩,
    hA _ 1 (by omega)⟩,
    hA _ 0 (by omega)⟩

/-! ## Point-addition correctness claim

`AddsPoint` is over `curveLayout` — two coordinate fields and one workspace —
while the assembly's register has four data blocks and a shared workspace.  The
two agree on the coordinates by definition, and the claim's workspace is the
assembly's last three fields, which `readField_split` relates.

Both clauses are guarded exactly as the assembly needs: `Addable` gives the
coordinates reduced and `x ≠ ax`, and `Recoverable` is what step 13 needs to
clear the slope. -/

theorem curve_read0 (ws i : Nat) :
    (curveLayout (512 + ws)).read i 0 = (asmLayout 256 ws).read i 0 := rfl

theorem curve_read1 (ws i : Nat) :
    (curveLayout (512 + ws)).read i 1 = (asmLayout 256 ws).read i 1 := rfl

theorem curve_width (ws : Nat) :
    (curveLayout (512 + ws)).width = (asmLayout 256 ws).width := by
  simp [curveLayout, asmLayout, Layout.width]; omega

/-- The claim's workspace is clear exactly when the assembly's last three fields
are. -/
theorem curve_read2 (ws i : Nat) :
    (curveLayout (512 + ws)).read i 2 = 0 ↔
      ((asmLayout 256 ws).read i 2 = 0 ∧ (asmLayout 256 ws).read i 3 = 0
        ∧ (asmLayout 256 ws).read i 4 = 0) := by
  have e : (curveLayout (512 + ws)).read i 2 = readField i 512 (256 + (256 + ws)) := by
    show readField i 512 (512 + ws) = _
    congr 1
    omega
  rw [e, readField_split, readField_split]
  exact Iff.rfl

/-- The assembly satisfies the point-addition specification. -/
theorem pointAdd_addsPoint {ws wa wn wi wq wu wm : Nat} {addc : Nat → RCircuit}
    {negc invc sqc subc mulc : RCircuit}
    (hlaw : Curve.InverseLaw) (halgl : Curve.Alg1Law)
    (hadd : ∀ c, AddsConstMod Curve.p wa 256 c (addc c))
    (haddwf : ∀ c, ∀ g ∈ (addc c).gates, g.wellFormed (constLayout 256 wa).width = true)
    (hneg : NegatesMod Curve.p wn 256 negc)
    (hnegwf : ∀ g ∈ negc.gates, g.wellFormed (constLayout 256 wn).width = true)
    (hinv : InvertsField wi 256 invc)
    (hinvwf : ∀ g ∈ invc.gates, g.wellFormed (unaryLayout 256 wi).width = true)
    (hsq : SquaresMod Curve.p wq 256 sqc)
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout 256 wq).width = true)
    (hsub : SubsMod Curve.p wu 256 subc)
    (hsubwf : ∀ g ∈ subc.gates, g.wellFormed (adderLayout 256 wu).width = true)
    (hmul : MulsMod Curve.p wm 256 mulc)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout 256 wm).width = true)
    (hwa : wa ≤ ws) (hwn : wn ≤ ws) (hwi : wi ≤ ws) (hwq : wq ≤ ws)
    (hwu : wu ≤ ws) (hwm : wm ≤ ws)
    (ax ay : Nat) (hax : ax < Curve.p) (hay : ay < Curve.p) :
    AddsPoint ax ay (512 + ws)
      (pointAdd 256 ws wa wn wi wq wu wm ax ay addc negc invc sqc subc mulc) := by
  have hp : Curve.p ≤ 2 ^ 256 := Nat.le_of_lt p_lt_two_pow
  have hwf := pointAdd_wellFormed (n := 256) (ws := ws) (ax := ax) (ay := ay)
    haddwf hnegwf hinvwf hsqwf hsubwf hmulwf hwa hwn hwi hwq hwu hwm
  intro x y i hi h0 h1 h2
  rw [curve_read0] at h0
  rw [curve_read1] at h1
  obtain ⟨z2, z3, z4⟩ := (curve_read2 ws i).mp h2
  have hwidth : (pointAdd 256 ws wa wn wi wq wu wm ax ay addc negc invc sqc subc mulc).width
      = (asmLayout 256 ws).width := rfl
  refine ⟨?_, ?_⟩
  · intro hadd' hrecov
    have hrep : Curve.Representable x y = true := by
      simp only [Curve.Addable, Bool.and_eq_true] at hadd'
      exact hadd'.1.1.1.1
    simp only [Curve.Representable, Bool.and_eq_true, decide_eq_true_eq] at hrep
    have hxne : x ≠ ax := by
      simp only [Curve.Addable, Bool.and_eq_true, bne_iff_ne, ne_eq] at hadd'
      exact hadd'.2
    have hrec : (Curve.addPoint x y ax ay).1 ≠ ax := by
      simp only [Curve.Recoverable, bne_iff_ne, ne_eq] at hrecov
      exact hrecov
    have tr := pointAdd_trace hlaw halgl hadd haddwf hneg hnegwf hinv hinvwf hsq hsqwf
      hsub hsubwf hmul hmulwf hwa hwn hwi hwq hwu hwm hp hax hay hrep.1 hrep.2 hxne hrec
      ⟨h0, h1, z2, z3, z4⟩
    refine eq_of_read (L := curveLayout (512 + ws)) ?_ ?_ ?_
    · have hi' : i < 2 ^ (pointAdd 256 ws wa wn wi wq wu wm ax ay
          addc negc invc sqc subc mulc).width := by
        show i < 2 ^ (asmLayout 256 ws).width
        rw [← curve_width]; exact hi
      have hlt := act_lt hwf hi'
      show act _ i < 2 ^ (curveLayout (512 + ws)).width
      rw [curve_width]
      exact hlt
    · exact writeField_lt (Layout.offset_add_size_le_width _ 1)
        (writeField_lt (Layout.offset_add_size_le_width _ 0) hi)
    · intro k hk
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by simp [curveLayout] at hk; omega
      rcases hk' with rfl | rfl | rfl
      · rw [Layout.read_write_ne (by decide),
          Layout.read_write_self
            (show (Curve.addPoint x y ax ay).1 < 2 ^ (curveLayout (512 + ws)).size 0 from
              Nat.lt_trans (Curve.representable_addPoint_fst _ _ _ _) p_lt_two_pow),
          curve_read0]
        exact tr.f0
      · rw [Layout.read_write_self
            (show (Curve.addPoint x y ax ay).2 < 2 ^ (curveLayout (512 + ws)).size 1 from
              Nat.lt_trans (Curve.representable_addPoint_snd _ _ _ _) p_lt_two_pow),
          curve_read1]
        exact tr.f1
      · rw [Layout.read_write_ne (by decide), Layout.read_write_ne (by decide)]
        exact ((curve_read2 ws _).mpr ⟨tr.f2, tr.f3, tr.f4⟩).trans h2.symm
  · intro hrep hxne hrecov
    simp only [Curve.Representable, Bool.and_eq_true, decide_eq_true_eq] at hrep
    have hrec : (Curve.addPoint x y ax ay).1 ≠ ax := by
      simp only [Curve.Recoverable, bne_iff_ne, ne_eq] at hrecov
      exact hrecov
    have tr := pointAdd_trace hlaw halgl hadd haddwf hneg hnegwf hinv hinvwf hsq hsqwf
      hsub hsubwf hmul hmulwf hwa hwn hwi hwq hwu hwm hp hax hay hrep.1 hrep.2 hxne hrec
      ⟨h0, h1, z2, z3, z4⟩
    exact (curve_read2 ws _).mpr ⟨tr.f2, tr.f3, tr.f4⟩

/-! ## Assembly resources

`pointAdd_addsPoint` proves the circuit's functional action.  Resource counts
combine the components with the uncomputed ones doubled: five
constant additions, one negation, one subtraction, two squarings, four
multiplications, and four inversions, since reversal preserves every count and a
placement preserves the kind of each gate. -/

theorem pointAdd_countP (n ws wa wn wi wq wu wm ax ay : Nat) (addc : Nat → RCircuit)
    (negc invc sqc subc mulc : RCircuit) {q : RGate → Bool}
    (hq : ∀ (f : Nat → Nat) g, q (RGate.map f g) = q g) :
    (pointAdd n ws wa wn wi wq wu wm ax ay addc negc invc sqc subc mulc).gates.countP q
      = (addc (Curve.neg ax)).gates.countP q + (addc (Curve.neg ay)).gates.countP q * 2
        + (addc (Curve.mul 3 ax)).gates.countP q + (addc ax).gates.countP q
        + negc.gates.countP q + subc.gates.countP q
        + 2 * sqc.gates.countP q + 4 * mulc.gates.countP q
        + 4 * invc.gates.countP q := by
  show (_ : List RGate).countP q = _
  simp only [pointAdd, List.countP_append, List.countP_reverse,
    countP_map_gates (fun g => hq _ g)]
  omega

theorem pointAdd_length (n ws wa wn wi wq wu wm ax ay : Nat) (addc : Nat → RCircuit)
    (negc invc sqc subc mulc : RCircuit) :
    (pointAdd n ws wa wn wi wq wu wm ax ay addc negc invc sqc subc mulc).gates.length
      = (addc (Curve.neg ax)).gates.length + (addc (Curve.neg ay)).gates.length * 2
        + (addc (Curve.mul 3 ax)).gates.length + (addc ax).gates.length
        + negc.gates.length + subc.gates.length
        + 2 * sqc.gates.length + 4 * mulc.gates.length + 4 * invc.gates.length := by
  show (_ : List RGate).length = _
  simp only [pointAdd, List.length_append, List.length_reverse, List.length_map]
  omega

theorem pointAdd_toffoliCount (n ws wa wn wi wq wu wm ax ay : Nat) (addc : Nat → RCircuit)
    (negc invc sqc subc mulc : RCircuit) :
    Circuit.toffoliCount
        (compile (pointAdd n ws wa wn wi wq wu wm ax ay addc negc invc sqc subc mulc))
      = Circuit.toffoliCount (compile (addc (Curve.neg ax)))
        + Circuit.toffoliCount (compile (addc (Curve.neg ay))) * 2
        + Circuit.toffoliCount (compile (addc (Curve.mul 3 ax)))
        + Circuit.toffoliCount (compile (addc ax))
        + Circuit.toffoliCount (compile negc) + Circuit.toffoliCount (compile subc)
        + 2 * Circuit.toffoliCount (compile sqc) + 4 * Circuit.toffoliCount (compile mulc)
        + 4 * Circuit.toffoliCount (compile invc) := by
  simp only [toffoliCount_compile]
  exact pointAdd_countP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun f g => RGate.isCcx_map f g)

theorem pointAdd_cnotCount (n ws wa wn wi wq wu wm ax ay : Nat) (addc : Nat → RCircuit)
    (negc invc sqc subc mulc : RCircuit) :
    Circuit.cnotCount
        (compile (pointAdd n ws wa wn wi wq wu wm ax ay addc negc invc sqc subc mulc))
      = Circuit.cnotCount (compile (addc (Curve.neg ax)))
        + Circuit.cnotCount (compile (addc (Curve.neg ay))) * 2
        + Circuit.cnotCount (compile (addc (Curve.mul 3 ax)))
        + Circuit.cnotCount (compile (addc ax))
        + Circuit.cnotCount (compile negc) + Circuit.cnotCount (compile subc)
        + 2 * Circuit.cnotCount (compile sqc) + 4 * Circuit.cnotCount (compile mulc)
        + 4 * Circuit.cnotCount (compile invc) := by
  simp only [cnotCount_compile]
  exact pointAdd_countP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun f g => RGate.isCx_map f g)

theorem pointAdd_usedWires {n ws wa wn wi wq wu wm ax ay : Nat} {addc : Nat → RCircuit}
    {negc invc sqc subc mulc : RCircuit}
    (haddwf : ∀ c, ∀ g ∈ (addc c).gates, g.wellFormed (constLayout n wa).width = true)
    (hnegwf : ∀ g ∈ negc.gates, g.wellFormed (constLayout n wn).width = true)
    (hinvwf : ∀ g ∈ invc.gates, g.wellFormed (unaryLayout n wi).width = true)
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout n wq).width = true)
    (hsubwf : ∀ g ∈ subc.gates, g.wellFormed (adderLayout n wu).width = true)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout n wm).width = true)
    (hwa : wa ≤ ws) (hwn : wn ≤ ws) (hwi : wi ≤ ws) (hwq : wq ≤ ws)
    (hwu : wu ≤ ws) (hwm : wm ≤ ws) :
    Circuit.usedWires
        (compile (pointAdd n ws wa wn wi wq wu wm ax ay addc negc invc sqc subc mulc))
      ≤ 4 * n + ws := by
  have hwf := pointAdd_wellFormed (n := n) (ws := ws) (ax := ax) (ay := ay)
    haddwf hnegwf hinvwf hsqwf hsubwf hmulwf hwa hwn hwi hwq hwu hwm
  have h := usedWires_compile_le_width hwf
  rw [show (pointAdd n ws wa wn wi wq wu wm ax ay addc negc invc sqc subc mulc).width
      = (asmLayout n ws).width from rfl, asmLayout_width] at h
  exact h

theorem pointAdd_gateCount (n ws wa wn wi wq wu wm ax ay : Nat) (addc : Nat → RCircuit)
    (negc invc sqc subc mulc : RCircuit) :
    Circuit.gateCount
        (compile (pointAdd n ws wa wn wi wq wu wm ax ay addc negc invc sqc subc mulc))
      = Circuit.gateCount (compile (addc (Curve.neg ax)))
        + Circuit.gateCount (compile (addc (Curve.neg ay))) * 2
        + Circuit.gateCount (compile (addc (Curve.mul 3 ax)))
        + Circuit.gateCount (compile (addc ax))
        + Circuit.gateCount (compile negc) + Circuit.gateCount (compile subc)
        + 2 * Circuit.gateCount (compile sqc) + 4 * Circuit.gateCount (compile mulc)
        + 4 * Circuit.gateCount (compile invc) := by
  simp only [gateCount_compile]
  rw [pointAdd_length,
    pointAdd_countP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun f g => RGate.isCcx_map f g)]
  omega

end Reversible
end VQ
