/-
Inversion at the curve prime, by Fermat.

`a⁻¹ = a^(p-2)` in a field of prime order, and square-and-multiply computes that
in 255 squarings and 248 multiplications for this exponent.  The construction is
a single chain: each operation reads the previous chain block, and a
multiplication also reads the input, and writes the next block.  Nothing is
uncomputed until the end, when the answer is copied into the output field and the
whole chain is run backwards.

The direct construction keeps 503 blocks of `n` wires live, about 130000 at the
curve width, compared with 1200 in the published circuit.  A windowed version
that computes eight blocks, copies the endpoint, and clears those blocks uses
the same number of multiplications on about 6700 wires.  An in-place modular
multiplier would remove the accumulator chain while preserving the inversion
specification.

Squaring modulo `p` is two-to-one, so a squarer cannot clear its input without
additional information.  This construction therefore retains each intermediate
value until reversal.
-/
import VQ.Reversible.Blocks
import VQ.Reversible.Compile
import VQ.Curve.ReversibleSpec

namespace VQ
namespace Reversible

set_option maxRecDepth 20000

/-! ## Exponent recurrence

The operations for bits `k - 1` down to zero, high bit first: a squaring for each
bit, and a multiplication after it when the bit is set.  The top bit needs no
operation, because the chain starts at the input, which is `a` to the first
power. -/

/-- `false` squares, `true` multiplies by the input. -/
def ops : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, e => (if (e / 2 ^ k) % 2 == 1 then [false, true] else [false]) ++ ops k e

/-- The exponent a run of operations produces, starting from `acc`. -/
def expAfter : List Bool → Nat → Nat
  | [], acc => acc
  | b :: rest, acc => expAfter rest (if b then acc + 1 else 2 * acc)

theorem expAfter_append (X Y : List Bool) (acc : Nat) :
    expAfter (X ++ Y) acc = expAfter Y (expAfter X acc) := by
  induction X generalizing acc with
  | nil => rfl
  | cons b X ih => rw [List.cons_append]; exact ih _

/-- The operation list for `p - 2`, which is 503 long: 255 squarings and 248
multiplications. -/
def invOps : List Bool := ops 255 (Curve.p - 2)

/-- The exponent after the first `t` operations. -/
def chainExp (t : Nat) : Nat := expAfter (invOps.take t) 1

@[simp] theorem chainExp_zero : chainExp 0 = 1 := rfl

/-- One more operation doubles the exponent, or doubles and adds one. -/
theorem chainExp_succ {t : Nat} (ht : t < invOps.length) :
    chainExp (t + 1) = if invOps.getD t false then chainExp t + 1 else 2 * chainExp t := by
  have htake : invOps.take (t + 1) = invOps.take t ++ [invOps.getD t false] := by
    rw [List.take_add_one, List.getD_eq_getElem?_getD]
    congr 1
    rw [List.getElem?_eq_getElem ht]
    rfl
  rw [chainExp, htake, expAfter_append]
  cases h : invOps.getD t false with
  | false => simp [expAfter, chainExp]
  | true => simp [expAfter, chainExp]

/-- The chain's exponent is `p - 2`.  A single evaluation, since the exponent
is a constant of the curve. -/
theorem chainExp_full : chainExp invOps.length = Curve.p - 2 := by decide

/-! ## Two facts about modular powers -/

theorem powMod_double (a E : Nat) :
    Curve.powMod a (2 * E) = Curve.powMod a E * Curve.powMod a E % Curve.p := by
  rw [Nat.two_mul, Curve.powMod_eq, Curve.powMod_eq, ← Nat.mul_mod, ← Nat.pow_add]

theorem powMod_succ (a E : Nat) :
    Curve.powMod a (E + 1) = Curve.powMod a E * a % Curve.p := by
  rw [Curve.powMod_eq, Curve.powMod_eq, Nat.mod_mul_mod, Nat.pow_succ]

theorem powMod_lt (a E : Nat) : Curve.powMod a E < Curve.p := Curve.powMod_lt a E

theorem powMod_one {a : Nat} (ha : a < Curve.p) : Curve.powMod a 1 = a := by
  rw [Curve.powMod_eq, Nat.pow_one, Nat.mod_eq_of_lt ha]

/-- The head of the operation list is a squaring, whatever the exponent: each bit
contributes a squaring first. -/
theorem ops_head {k e : Nat} : (ops (k + 1) e).getD 0 false = false := by
  rw [ops]
  split <;> rfl

theorem invOps_head : invOps.getD 0 false = false := ops_head

/-! ## Inversion chain

Block 0 holds the input, block 1 the output, and blocks 2 to `invOps.length + 1`
the chain.  Operation `t` reads block `invSrc t` — the previous chain value, or the
input at the start — and writes block `t + 2`. -/

/-- The number of blocks. -/
def invB : Nat := invOps.length + 2

/-- Where operation `t` reads its operand. -/
def invSrc (t : Nat) : Nat := if t = 0 then 0 else t + 1

theorem invSrc_lt {t : Nat} (ht : t < invOps.length) : invSrc t < invB := by
  rw [invSrc, invB]; split <;> omega

theorem invSrc_ne_dst (t : Nat) : invSrc t ≠ t + 2 := by
  rw [invSrc]; split <;> omega

theorem invSrc_ne_zero {t : Nat} (ht : t ≠ 0) : invSrc t ≠ 0 := by
  rw [invSrc, if_neg ht]; omega

/-- The gate list of operation `t`. -/
def invStep (n wq wm : Nat) (sqc mulc : RCircuit) (t : Nat) : List RGate :=
  if invOps.getD t false then
    mulc.gates.map (RGate.map (place (mulLayout n wm) (bw3 n (invB * n) (invSrc t) 0 (t + 2))))
  else
    sqc.gates.map (RGate.map (place (unaryLayout n wq) (bw2 n (invB * n) (invSrc t) (t + 2))))

/-- The whole forward chain. -/
def invChain (n wq wm : Nat) (sqc mulc : RCircuit) : List RGate :=
  (List.range invOps.length).flatMap (invStep n wq wm sqc mulc)

/-! ## Inversion-chain state

Block 0 holds the input, blocks 2 to `t + 1` hold the chain values reached so
far, and every other block is clear. -/

def invState (a t : Nat) : Nat → Nat := fun j =>
  if j = 0 then a
  else if 2 ≤ j ∧ j ≤ t + 1 then Curve.powMod a (chainExp (j - 1)) else 0

theorem stateVals_src {a t : Nat} (ha : a < Curve.p) :
    invState a t (invSrc t) = Curve.powMod a (chainExp t) := by
  rw [invState, invSrc]
  by_cases ht : t = 0
  · subst ht
    simp [powMod_one ha]
  · rw [if_neg ht]
    have h1 : ¬ (t + 1 = 0) := by omega
    have h2 : 2 ≤ t + 1 ∧ t + 1 ≤ t + 1 := by omega
    simp only [h1, if_false, h2, if_true, and_self]
    congr 1

theorem stateVals_zero {a t : Nat} : invState a t 0 = a := by simp [invState]

theorem stateVals_dst {a t : Nat} : invState a t (t + 2) = 0 := by
  rw [invState]
  simp

/-- Writing the chain value at `t + 2` advances the state. -/
theorem stateVals_step (a t : Nat) :
    setBlk (invState a t) (t + 2) (Curve.powMod a (chainExp (t + 1)))
      = invState a (t + 1) := by
  funext j
  by_cases hj : j = t + 2
  · subst hj
    rw [setBlk_self, invState]
    have h1 : ¬ (t + 2 = 0) := by omega
    have h2 : 2 ≤ t + 2 ∧ t + 2 ≤ t + 1 + 1 := by omega
    simp only [h1, if_false, h2, if_true, and_self]
    congr 1
  · rw [setBlk_ne hj, invState, invState]
    by_cases h0 : j = 0
    · simp [h0]
    · have hrange : (2 ≤ j ∧ j ≤ t + 1) ↔ (2 ≤ j ∧ j ≤ t + 1 + 1) := by omega
      by_cases hin : 2 ≤ j ∧ j ≤ t + 1
      · simp [h0, hin, hrange.mp hin]
      · have : ¬ (2 ≤ j ∧ j ≤ t + 1 + 1) := by omega
        simp [h0, hin, this]

/-! ## Inversion-chain step

`invStep_advance` maps the state after `t` operations to the state after
`t + 1`.  The selected operation determines whether the proof uses the
squaring or multiplication specification.  The modular-power identities update
the exponent.
-/

theorem invStep_advance {n cw wq wm : Nat} {sqc mulc : RCircuit}
    (hsq : SquaresMod Curve.p wq n sqc)
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout n wq).width = true)
    (hmul : MulsMod Curve.p wm n mulc)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout n wm).width = true)
    (hwq : wq ≤ cw) (hwm : wm ≤ cw) (hp : Curve.p ≤ 2 ^ n)
    {a : Nat} (ha : a < Curve.p) :
    ∀ t J, t < invOps.length → BSt invB n cw J (invState a t) →
      BSt invB n cw (actGates (invStep n wq wm sqc mulc t) J) (invState a (t + 1)) := by
  intro t J ht hst
  have hsrc : invSrc t < invB := invSrc_lt ht
  have hdst : t + 2 < invB := by rw [invB]; omega
  have hzero : (0 : Nat) < invB := by rw [invB]; omega
  have hrs : (blockLayout invB n cw).read J (invSrc t) = Curve.powMod a (chainExp t) := by
    rw [hst.blk _ hsrc, stateVals_src ha]
  have hr0 : (blockLayout invB n cw).read J 0 = a := by rw [hst.blk _ hzero, stateVals_zero]
  have hrd : (blockLayout invB n cw).read J (t + 2) = 0 := by
    rw [hst.blk _ hdst, stateVals_dst]
  have hfit : Curve.powMod a (chainExp (t + 1)) < 2 ^ n :=
    Nat.lt_of_lt_of_le (powMod_lt _ _) hp
  rw [invStep]
  by_cases hop : invOps.getD t false
  · -- a multiplication by the input
    have ht0 : t ≠ 0 := by
      intro h
      subst h
      rw [invOps_head] at hop
      exact absurd hop (by simp)
    rw [if_pos hop,
      bstep_mul hmul hmulwf hwm hsrc hzero hdst (invSrc_ne_zero ht0) (invSrc_ne_dst t)
        (by omega) hp (by rw [hrs]; exact powMod_lt _ _) (by rw [hr0]; exact ha) hrd hst.ws,
      hrs, hr0]
    rw [show Curve.powMod a (chainExp t) * a % Curve.p
        = Curve.powMod a (chainExp (t + 1)) from by
      rw [chainExp_succ ht, if_pos hop, powMod_succ]]
    rw [← stateVals_step a t]
    exact hst.write hdst hfit
  · -- a squaring
    rw [if_neg hop,
      bstep_square hsq hsqwf hwq hsrc hdst (invSrc_ne_dst t) hp
        (by rw [hrs]; exact powMod_lt _ _) hrd hst.ws, hrs]
    rw [show Curve.powMod a (chainExp t) * Curve.powMod a (chainExp t) % Curve.p
        = Curve.powMod a (chainExp (t + 1)) from by
      rw [chainExp_succ ht, if_neg hop, powMod_double]]
    rw [← stateVals_step a t]
    exact hst.write hdst hfit

/-- The forward chain leaves the inverse in the last block. -/
theorem invChain_advance {n cw wq wm : Nat} {sqc mulc : RCircuit}
    (hsq : SquaresMod Curve.p wq n sqc)
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout n wq).width = true)
    (hmul : MulsMod Curve.p wm n mulc)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout n wm).width = true)
    (hwq : wq ≤ cw) (hwm : wm ≤ cw) (hp : Curve.p ≤ 2 ^ n)
    {a I : Nat} (ha : a < Curve.p) (h0 : BSt invB n cw I (invState a 0)) :
    BSt invB n cw (actGates (invChain n wq wm sqc mulc) I) (invState a invOps.length) :=
  actGates_chain_pred
    (invStep_advance hsq hsqwf hmul hmulwf hwq hwm hp ha) I h0

/-- The last block holds `Curve.inv a`. -/
theorem stateVals_last {a : Nat} :
    invState a invOps.length (invOps.length + 1) = Curve.inv a := by
  rw [invState]
  have h1 : ¬ (invOps.length + 1 = 0) := by omega
  have h2 : 2 ≤ invOps.length + 1 ∧ invOps.length + 1 ≤ invOps.length + 1 := by
    refine ⟨?_, Nat.le_refl _⟩
    show 2 ≤ invOps.length + 1
    have : 1 ≤ invOps.length := by
      rw [invOps]
      show 1 ≤ (ops 255 (Curve.p - 2)).length
      rw [ops]
      split <;> simp
    omega
  simp only [h1, if_false, h2, if_true, and_self]
  rw [show invOps.length + 1 - 1 = invOps.length from by omega, chainExp_full, Curve.inv]

/-! ## Well-formedness and non-interference of the chain

The chain has to be well formed at the register's width for its uncomputation to
undo it, and it must not touch block 1, which is where the answer is copied. -/

theorem all_flatMap_range {p : RGate → Bool} {steps : Nat → List RGate} :
    ∀ k, (∀ t, t < k → (steps t).all p = true) →
      ((List.range k).flatMap steps).all p = true := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [List.range_succ, List.flatMap_append, List.all_append, Bool.and_eq_true]
    refine ⟨ih (fun t ht => h t (Nat.lt_succ_of_lt ht)), ?_⟩
    show ((steps k) ++ []).all p = true
    rw [List.append_nil]
    exact h k (Nat.lt_succ_self k)

theorem mem_flatMap_range {steps : Nat → List RGate} {g : RGate} {k : Nat}
    (hg : g ∈ (List.range k).flatMap steps) : ∃ t, t < k ∧ g ∈ steps t := by
  obtain ⟨t, ht, hgt⟩ := List.exists_of_mem_flatMap hg
  exact ⟨t, List.mem_range.mp ht, hgt⟩

/-- Every block a step's wiring names avoids the output field. -/
theorem invStep_avoids_out {n t : Nat} :
    ∀ o ∈ [invSrc t * n, 0 * n, (t + 2) * n, invB * n], o + n ≤ n ∨ 2 * n ≤ o := by
  have hB : 2 ≤ invB := by rw [invB]; omega
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · rw [invSrc]
    by_cases h : t = 0
    · rw [if_pos h]; exact Or.inl (by omega)
    · rw [if_neg h]
      refine Or.inr ?_
      have := blk_le (b := t + 2) (n := n) (j := 2) (by omega)
      have h2 : 2 * n ≤ (t + 1) * n := Nat.mul_le_mul_right n (by omega)
      omega
  · exact Or.inl (by omega)
  · refine Or.inr (Nat.mul_le_mul_right n (by omega))
  · exact Or.inr (Nat.mul_le_mul_right n hB)

theorem invStep_wellFormed {n cw wq wm : Nat} {sqc mulc : RCircuit}
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout n wq).width = true)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout n wm).width = true)
    (hwq : wq ≤ cw) (hwm : wm ≤ cw) {t : Nat} (ht : t < invOps.length) :
    (invStep n wq wm sqc mulc t).all
      (RGate.wellFormed (blockLayout invB n cw).width) = true := by
  have hsrc : invSrc t < invB := invSrc_lt ht
  have hdst : t + 2 < invB := by rw [invB]; omega
  have hzero : (0 : Nat) < invB := by rw [invB]; omega
  rw [invStep]
  by_cases hop : invOps.getD t false
  · rw [if_pos hop]
    exact wellFormed_placeGates
      (bdisjoint4 (by have := blk_le (n := n) hsrc; omega)
        (by have := blk_le (n := n) hzero; omega)
        (by have := blk_le (n := n) hdst; omega)
        (blk_ne (invSrc_ne_zero (by intro h; subst h; rw [invOps_head] at hop; exact Bool.noConfusion hop)))
        (blk_ne (invSrc_ne_dst t)) (blk_ne (by omega)))
      (by simp [bw3, mulLayout]) (bW3 hsrc hzero hdst hwm) hmulwf
  · rw [if_neg hop]
    exact wellFormed_placeGates
      (bdisjoint3 (by have := blk_le (n := n) hsrc; omega)
        (by have := blk_le (n := n) hdst; omega) (blk_ne (invSrc_ne_dst t)))
      (by simp [bw2, unaryLayout]) (bW2 hsrc hdst hwq) hsqwf

theorem invChain_wellFormed {n cw wq wm : Nat} {sqc mulc : RCircuit}
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout n wq).width = true)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout n wm).width = true)
    (hwq : wq ≤ cw) (hwm : wm ≤ cw) :
    (invChain n wq wm sqc mulc).all
      (RGate.wellFormed (blockLayout invB n cw).width) = true :=
  all_flatMap_range _ (fun _ ht => invStep_wellFormed hsqwf hmulwf hwq hwm ht)

/-- No gate of a step touches the output field, which is block 1. -/
theorem invStep_avoids {n wq wm : Nat} {sqc mulc : RCircuit}
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout n wq).width = true)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout n wm).width = true)
    {t : Nat} (ht : t < invOps.length) :
    ∀ g ∈ invStep n wq wm sqc mulc t, ∀ q ∈ g.wires, q < n ∨ n + n ≤ q := by
  have hsrc : invSrc t < invB := invSrc_lt ht
  have hdst : t + 2 < invB := by rw [invB]; omega
  have hB : 2 ≤ invB := by rw [invB]; omega
  have hblk : ∀ j : Nat, j = 0 ∨ 2 ≤ j → j * n + n ≤ n ∨ n + n ≤ j * n := by
    intro j hj
    rcases hj with rfl | hj
    · exact Or.inl (by omega)
    · refine Or.inr ?_
      have h2 : 2 * n ≤ j * n := Nat.mul_le_mul_right n hj
      omega
  have hsrcb : invSrc t = 0 ∨ 2 ≤ invSrc t := by
    rw [invSrc]; by_cases h : t = 0
    · rw [if_pos h]; exact Or.inl rfl
    · rw [if_neg h]; exact Or.inr (by omega)
  rw [invStep]
  by_cases hop : invOps.getD t false
  · rw [if_pos hop]
    refine placeGates_avoids (by simp [bw3, mulLayout]) hmulwf ?_
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [mulLayout] at hj; omega
    rcases hj' with rfl | rfl | rfl | rfl
    · show invSrc t * n + n ≤ n ∨ n + n ≤ invSrc t * n
      exact hblk _ hsrcb
    · show 0 * n + n ≤ n ∨ n + n ≤ 0 * n
      exact hblk 0 (Or.inl rfl)
    · show (t + 2) * n + n ≤ n ∨ n + n ≤ (t + 2) * n
      exact hblk _ (Or.inr (by omega))
    · show invB * n + wm ≤ n ∨ n + n ≤ invB * n
      refine Or.inr ?_
      have h2 : 2 * n ≤ invB * n := Nat.mul_le_mul_right n hB
      omega
  · rw [if_neg hop]
    refine placeGates_avoids (by simp [bw2, unaryLayout]) hsqwf ?_
    intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by simp [unaryLayout] at hj; omega
    rcases hj' with rfl | rfl | rfl
    · show invSrc t * n + n ≤ n ∨ n + n ≤ invSrc t * n
      exact hblk _ hsrcb
    · show (t + 2) * n + n ≤ n ∨ n + n ≤ (t + 2) * n
      exact hblk _ (Or.inr (by omega))
    · show invB * n + wq ≤ n ∨ n + n ≤ invB * n
      refine Or.inr ?_
      have h2 : 2 * n ≤ invB * n := Nat.mul_le_mul_right n hB
      omega

theorem invChain_avoids {n wq wm : Nat} {sqc mulc : RCircuit}
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout n wq).width = true)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout n wm).width = true) :
    ∀ g ∈ invChain n wq wm sqc mulc, ∀ q ∈ g.wires, q < n ∨ n + n ≤ q := by
  intro g hg
  obtain ⟨t, ht, hgt⟩ := mem_flatMap_range hg
  exact invStep_avoids hsqwf hmulwf ht g hgt

/-! ## Inversion circuit

The construction runs the chain, copies the answer into the output field, and
reverses the chain.  `actGates_compute_use_uncompute` proves that the reverse
clears the chain workspace while preserving the copied answer. -/

/-- The inverter's gate list. -/
def invGates (n wq wm : Nat) (sqc mulc : RCircuit) : List RGate :=
  invChain n wq wm sqc mulc
    ++ copyField ((invOps.length + 1) * n) n n
    ++ (invChain n wq wm sqc mulc).reverse

/-- The inverter's workspace: the chain's blocks and one component workspace. -/
def IW (n cw : Nat) : Nat := invOps.length * n + cw

/-- The inverter. -/
def invCircuit (n cw wq wm : Nat) (sqc mulc : RCircuit) : RCircuit :=
  { width := (blockLayout invB n cw).width, gates := invGates n wq wm sqc mulc }

theorem invOps_pos : 1 ≤ invOps.length := by
  rw [invOps]
  show 1 ≤ (ops 255 (Curve.p - 2)).length
  rw [ops]
  split <;> simp

theorem unary_read2 (n ws i : Nat) :
    (unaryLayout n ws).read i 2 = readField i (2 * n) ws := by
  show readField i (n + (n + 0)) ws = readField i (2 * n) ws
  congr 1
  omega

theorem unary_width (n cw : Nat) :
    (unaryLayout n (IW n cw)).width = (blockLayout invB n cw).width := by
  rw [blockLayout_width, invB, IW, Nat.add_mul]
  simp [unaryLayout, Layout.width]
  omega

/-- The inverter satisfies the field-inversion specification.

Each hypothesis is a component specification, so any conforming squarer or
multiplier can replace the corresponding component. -/
theorem invCircuit_invertsField {n cw wq wm : Nat} {sqc mulc : RCircuit}
    (hsq : SquaresMod Curve.p wq n sqc)
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout n wq).width = true)
    (hmul : MulsMod Curve.p wm n mulc)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout n wm).width = true)
    (hwq : wq ≤ cw) (hwm : wm ≤ cw) :
    InvertsField (IW n cw) n (invCircuit n cw wq wm sqc mulc) := by
  intro a i _ h0 h1 h2 hp ha
  have hL := invOps_pos
  have hB : invB = invOps.length + 2 := rfl
  -- the initial state, read out of the claim's three fields
  have hst0 : BSt invB n cw i (invState a 0) := by
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [blk_read hj]
      by_cases hj0 : j = 0
      · subst hj0
        rw [invState, if_pos rfl]
        show readField i (0 * n) n = a
        rw [Nat.zero_mul, ← h0]; rfl
      · by_cases hj1 : j = 1
        · subst hj1
          rw [invState]
          simp only [show ¬ (1 = 0) from by omega, if_false,
            show ¬ (2 ≤ 1 ∧ 1 ≤ 0 + 1) from by omega, if_false]
          show readField i (1 * n) n = 0
          rw [Nat.one_mul, ← h1]; rfl
        · rw [invState]
          simp only [hj0, if_false, show ¬ (2 ≤ j ∧ j ≤ 0 + 1) from by omega, if_false]
          refine readField_sub_zero (off := 2 * n) (len := IW n cw) (o := j * n) (l := n) ?_ ?_ ?_
          · show 2 * n ≤ j * n
            exact Nat.mul_le_mul_right n (by omega)
          · rw [invB] at hj
            show j * n + n ≤ 2 * n + IW n cw
            have h1 : (j + 1) * n ≤ (invOps.length + 2) * n :=
              Nat.mul_le_mul_right n (by omega)
            have h2' : (j + 1) * n = j * n + n := Nat.succ_mul j n
            have h3 : (invOps.length + 2) * n = invOps.length * n + 2 * n := Nat.add_mul _ _ _
            rw [IW]
            omega
          · show readField i (2 * n) (IW n cw) = 0
            rw [← unary_read2]; exact h2
    · rw [blk_read_ws]
      refine readField_sub_zero (off := 2 * n) (len := IW n cw) (o := invB * n) (l := cw) ?_ ?_ ?_
      · show 2 * n ≤ invB * n
        exact Nat.mul_le_mul_right n (by rw [invB]; omega)
      · show invB * n + cw ≤ 2 * n + IW n cw
        rw [invB, IW, Nat.add_mul]
        omega
      · show readField i (2 * n) (IW n cw) = 0
        rw [← unary_read2]; exact h2
  -- the chain
  have hchain := invChain_advance hsq hsqwf hmul hmulwf hwq hwm hp ha hst0
  have hout1 : readField (actGates (invChain n wq wm sqc mulc) i) n n = 0 := by
    have := hchain.blk 1 (by rw [invB]; omega)
    rw [blk_read (b := invB) (by rw [invB]; omega), Nat.one_mul] at this
    rw [this, invState]
    simp only [show ¬ (1 = 0) from by omega, if_false,
      show ¬ (2 ≤ 1 ∧ 1 ≤ invOps.length + 1) from by omega, if_false]
  have hans : readField (actGates (invChain n wq wm sqc mulc) i)
      ((invOps.length + 1) * n) n = Curve.inv a := by
    have := hchain.blk (invOps.length + 1) (by rw [invB]; omega)
    rw [blk_read (b := invB) (by rw [invB]; omega)] at this
    rw [this, stateVals_last]
  -- copy and uncompute
  show actGates (invGates n wq wm sqc mulc) i = _
  rw [invGates,
    actGates_compute_use_uncompute (invChain_wellFormed hsqwf hmulwf hwq hwm)
      (invChain_avoids hsqwf hmulwf)
      (fun j => actGates_copyField
        (Or.inr (by
          have : 2 * n ≤ (invOps.length + 1) * n := Nat.mul_le_mul_right n (by omega)
          omega)) j) i,
    hout1, hans, Nat.zero_xor]
  rfl

/-! ## Inverter resources

Each of the 503 steps is one component, so a bound on the components bounds the
chain, and the chain runs twice.  The copy contributes its `n` CNOTs and no
Toffoli. -/

theorem invStep_countP {n wq wm : Nat} {sqc mulc : RCircuit} {q : RGate → Bool} {C : Nat}
    (hq : ∀ (f : Nat → Nat) g, q (RGate.map f g) = q g)
    (hsq : sqc.gates.countP q ≤ C) (hmul : mulc.gates.countP q ≤ C) (t : Nat) :
    (invStep n wq wm sqc mulc t).countP q ≤ C := by
  rw [invStep]
  split
  · rw [countP_map_gates (fun g => hq _ g)]; exact hmul
  · rw [countP_map_gates (fun g => hq _ g)]; exact hsq

theorem invChain_countP {n wq wm : Nat} {sqc mulc : RCircuit} {q : RGate → Bool} {C : Nat}
    (hq : ∀ (f : Nat → Nat) g, q (RGate.map f g) = q g)
    (hsq : sqc.gates.countP q ≤ C) (hmul : mulc.gates.countP q ≤ C) :
    (invChain n wq wm sqc mulc).countP q ≤ invOps.length * C :=
  countP_flatMap_range_le _ (fun t _ => invStep_countP hq hsq hmul t)

theorem invStep_length {n wq wm : Nat} {sqc mulc : RCircuit} {C : Nat}
    (hsq : sqc.gates.length ≤ C) (hmul : mulc.gates.length ≤ C) (t : Nat) :
    (invStep n wq wm sqc mulc t).length ≤ C := by
  rw [invStep]
  split
  · rw [List.length_map]; exact hmul
  · rw [List.length_map]; exact hsq

theorem invChain_length {n wq wm : Nat} {sqc mulc : RCircuit} {C : Nat}
    (hsq : sqc.gates.length ≤ C) (hmul : mulc.gates.length ≤ C) :
    (invChain n wq wm sqc mulc).length ≤ invOps.length * C :=
  length_flatMap_range_le _ (fun t _ => invStep_length hsq hmul t)

/-- The inverter's Toffoli count. -/
theorem invCircuit_toffoli_le {n cw wq wm : Nat} {sqc mulc : RCircuit} {C : Nat}
    (hsq : Circuit.toffoliCount (compile sqc) ≤ C)
    (hmul : Circuit.toffoliCount (compile mulc) ≤ C) :
    Circuit.toffoliCount (compile (invCircuit n cw wq wm sqc mulc))
      ≤ 2 * (invOps.length * C) := by
  rw [toffoliCount_compile] at hsq hmul ⊢
  show (invGates n wq wm sqc mulc).countP RGate.isCcx ≤ _
  rw [invGates, List.countP_append, List.countP_append, List.countP_reverse,
    copyField_no_ccx]
  have := invChain_countP (n := n) (wq := wq) (wm := wm)
    (fun f g => RGate.isCcx_map f g) hsq hmul
  omega

/-- The inverter's gate count, through the compilation's identity
`length + 2 * toffoli`. -/
theorem invCircuit_gates_le {n cw wq wm : Nat} {sqc mulc : RCircuit} {C : Nat}
    (hsq : Circuit.gateCount (compile sqc) ≤ C)
    (hmul : Circuit.gateCount (compile mulc) ≤ C)
    (hsqt : Circuit.toffoliCount (compile sqc) ≤ C)
    (hmult : Circuit.toffoliCount (compile mulc) ≤ C) :
    Circuit.gateCount (compile (invCircuit n cw wq wm sqc mulc))
      ≤ 2 * (invOps.length * C) + n + 2 * (2 * (invOps.length * C)) := by
  have hlsq : sqc.gates.length ≤ C := by rw [gateCount_compile] at hsq; omega
  have hlmul : mulc.gates.length ≤ C := by rw [gateCount_compile] at hmul; omega
  have htof : (invGates n wq wm sqc mulc).countP RGate.isCcx
      ≤ 2 * (invOps.length * C) := by
    have h := invCircuit_toffoli_le (n := n) (cw := cw) (wq := wq) (wm := wm) hsqt hmult
    rw [toffoliCount_compile] at h
    exact h
  have hl : (invGates n wq wm sqc mulc).length ≤ 2 * (invOps.length * C) + n := by
    rw [invGates, List.length_append, List.length_append, List.length_reverse,
      copyField_length]
    have := invChain_length (n := n) (wq := wq) (wm := wm) hlsq hlmul
    omega
  rw [gateCount_compile]
  show (invGates n wq wm sqc mulc).length
    + 2 * (invGates n wq wm sqc mulc).countP RGate.isCcx ≤ _
  omega

/-- The inverter is well formed at its declared width. -/
theorem invCircuit_wellFormed {n cw wq wm : Nat} {sqc mulc : RCircuit}
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout n wq).width = true)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout n wm).width = true)
    (hwq : wq ≤ cw) (hwm : wm ≤ cw) :
    (invCircuit n cw wq wm sqc mulc).wellFormed = true := by
  have hL := invOps_pos
  have hB2 : invB = invOps.length + 2 := rfl
  have hcopy : ∀ g ∈ copyField ((invOps.length + 1) * n) n n,
      g.wellFormed (blockLayout invB n cw).width = true := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := copyField_mem hg
    have hn : 0 < n := by omega
    have hgt : n < (invOps.length + 1) * n := by
      have h2 : 2 * n ≤ (invOps.length + 1) * n := Nat.mul_le_mul_right n (by omega)
      omega
    have hsucc : (invOps.length + 2) * n = (invOps.length + 1) * n + n := Nat.succ_mul _ _
    simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq, blockLayout_width, hB2]
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  show (invGates n wq wm sqc mulc).all
    (RGate.wellFormed (blockLayout invB n cw).width) = true
  rw [invGates, List.all_append, List.all_append, List.all_reverse, Bool.and_eq_true,
    Bool.and_eq_true]
  exact ⟨⟨invChain_wellFormed hsqwf hmulwf hwq hwm, List.all_eq_true.mpr hcopy⟩,
    invChain_wellFormed hsqwf hmulwf hwq hwm⟩

/-- The inverter's wire count. -/
theorem invCircuit_wires_le {n cw wq wm : Nat} {sqc mulc : RCircuit}
    (hsqwf : ∀ g ∈ sqc.gates, g.wellFormed (unaryLayout n wq).width = true)
    (hmulwf : ∀ g ∈ mulc.gates, g.wellFormed (mulLayout n wm).width = true)
    (hwq : wq ≤ cw) (hwm : wm ≤ cw) :
    Circuit.usedWires (compile (invCircuit n cw wq wm sqc mulc)) ≤ invB * n + cw := by
  have hL := invOps_pos
  have hB2 : invB = invOps.length + 2 := rfl
  have hsucc : (invOps.length + 2) * n = (invOps.length + 1) * n + n := Nat.succ_mul _ _
  have h2n : 2 * n ≤ invB * n := Nat.mul_le_mul_right n (by rw [invB]; omega)
  have hcopy : ∀ g ∈ copyField ((invOps.length + 1) * n) n n,
      g.wellFormed (blockLayout invB n cw).width = true := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := copyField_mem hg
    have hn : 0 < n := by omega
    have hgt : n < (invOps.length + 1) * n := by
      have h2 : 2 * n ≤ (invOps.length + 1) * n := Nat.mul_le_mul_right n (by omega)
      omega
    simp only [RGate.wellFormed, Bool.and_eq_true, decide_eq_true_eq, blockLayout_width, hB2]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · omega
  have hwf : (invGates n wq wm sqc mulc).all
      (RGate.wellFormed (blockLayout invB n cw).width) = true :=
    invCircuit_wellFormed hsqwf hmulwf hwq hwm
  have hbound : Circuit.usedWires (compile (invCircuit n cw wq wm sqc mulc))
      ≤ (blockLayout invB n cw).width := by
    refine usedWires_compile_le_of_lt (fun g hg q hq => ?_)
    have hgw : g.wellFormed (blockLayout invB n cw).width = true :=
      List.all_eq_true.mp hwf g hg
    cases g <;> simp_all [RGate.wellFormed, RGate.wires] <;> omega
  rw [blockLayout_width] at hbound
  exact hbound


end Reversible
end VQ
