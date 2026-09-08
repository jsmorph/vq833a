/-
Point addition on secp256k1 by a classical affine offset.  The construction
instantiates `VQ.Reversible.pointAdd` with a constant adder, negation,
subtraction, squaring, multiplication, and Kaliski binary-Euclidean inversion.
`VQMathlib.Curve.Laws` supplies the secp256k1 inverse and affine-addition laws.

The resulting circuit has checked upper bounds of 3,597 used wires, 32,642,112
Toffoli gates, 169,589,447 primitive gates, and 228,494,784 expanded T gates.
The generator returns the identity when either classical coordinate lies
outside the base field.
-/
import VQ
import VQMathlib.Curve.Laws
import VQ.Curve.PointAddition.Arithmetic.AddC
import VQ.Curve.PointAddition.Arithmetic.Neg
import VQ.Curve.PointAddition.Arithmetic.Subt
import VQ.Curve.PointAddition.Arithmetic.Mul
import VQ.Curve.PointAddition.Arithmetic.Sq
import VQ.Curve.PointAddition.Arithmetic.Inv

open VQ VQ.Reversible

namespace VQ.Curve.PointAddition.Arithmetic

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! ## Component circuits

Each generator's declared width equals its layout width.  Its well-formedness
theorem supplies the corresponding assembly hypothesis. -/

def cw : Nat := 1538

theorem addc_width (n : Nat) : (constLayout n VQ.Curve.PointAddition.Arithmetic.AddC.ws).width = n + VQ.Curve.PointAddition.Arithmetic.AddC.ws := by
  simp [constLayout, Layout.width]

theorem neg_width (n : Nat) : (constLayout n VQ.Curve.PointAddition.Arithmetic.Neg.ws).width = n + VQ.Curve.PointAddition.Arithmetic.Neg.ws := by
  simp [constLayout, Layout.width]

theorem sub_width (n : Nat) : (adderLayout n VQ.Curve.PointAddition.Arithmetic.Subt.ws).width = 2 * n + VQ.Curve.PointAddition.Arithmetic.Subt.ws := by
  simp [adderLayout, Layout.width]; omega

theorem sq_width (n : Nat) : (unaryLayout n VQ.Curve.PointAddition.Arithmetic.Sq.ws).width = 2 * n + VQ.Curve.PointAddition.Arithmetic.Sq.ws := by
  simp [unaryLayout, Layout.width]; omega

theorem mul_width (n : Nat) : (mulLayout n VQ.Curve.PointAddition.Arithmetic.Mul.ws).width = 3 * n + VQ.Curve.PointAddition.Arithmetic.Mul.ws := by
  simp [mulLayout, Layout.width]; omega

theorem addc_wf (n c : Nat) :
    ∀ g ∈ (VQ.Curve.PointAddition.Arithmetic.AddC.gen n c).gates, g.wellFormed (constLayout n VQ.Curve.PointAddition.Arithmetic.AddC.ws).width = true := by
  intro g hg; rw [addc_width]; exact RCircuit.wellFormed_mem (VQ.Curve.PointAddition.Arithmetic.AddC.wf n c) hg

theorem neg_wf (n : Nat) :
    ∀ g ∈ (VQ.Curve.PointAddition.Arithmetic.Neg.gen n).gates, g.wellFormed (constLayout n VQ.Curve.PointAddition.Arithmetic.Neg.ws).width = true := by
  intro g hg; rw [neg_width]; exact RCircuit.wellFormed_mem (VQ.Curve.PointAddition.Arithmetic.Neg.wf n) hg

theorem sub_wf (n : Nat) :
    ∀ g ∈ (VQ.Curve.PointAddition.Arithmetic.Subt.gen n).gates, g.wellFormed (adderLayout n VQ.Curve.PointAddition.Arithmetic.Subt.ws).width = true := by
  intro g hg; rw [sub_width]; exact RCircuit.wellFormed_mem (VQ.Curve.PointAddition.Arithmetic.Subt.wf n) hg

theorem sq_wf (n : Nat) :
    ∀ g ∈ (VQ.Curve.PointAddition.Arithmetic.Sq.gen n).gates, g.wellFormed (unaryLayout n VQ.Curve.PointAddition.Arithmetic.Sq.ws).width = true := by
  intro g hg; rw [sq_width]; exact RCircuit.wellFormed_mem (VQ.Curve.PointAddition.Arithmetic.Sq.wf n) hg

theorem mul_wf (n : Nat) :
    ∀ g ∈ (VQ.Curve.PointAddition.Arithmetic.Mul.gen n).gates, g.wellFormed (mulLayout n VQ.Curve.PointAddition.Arithmetic.Mul.ws).width = true := by
  intro g hg; rw [mul_width]; exact RCircuit.wellFormed_mem (VQ.Curve.PointAddition.Arithmetic.Mul.wf n) hg

/-! ## Inverter circuit

Kaliski's binary extended Euclidean inverter supplies `InvertsField` and
gate-level well-formedness at the layout width.  The point-addition assembly
invokes the inverter four times.  The inverter's workspace and Toffoli theorems
determine the assembly's corresponding resource bounds. -/

def invc : RCircuit := VQ.Curve.PointAddition.Arithmetic.Inv.gen 256

theorem inv_ws : (13 : Nat) + 256 * 10 = 2573 := by norm_num

theorem inv_spec : InvertsField 2573 256 invc := by
  rw [← inv_ws]
  exact VQ.Curve.PointAddition.Arithmetic.Inv.inverts 256

theorem inv_width : (unaryLayout 256 2573).width = (VQ.Curve.PointAddition.Arithmetic.Inv.gen 256).width := by
  simp [unaryLayout, Layout.width, VQ.Curve.PointAddition.Arithmetic.Inv.gen, VQ.Curve.PointAddition.Arithmetic.Inv.totalWidth]

theorem inv_wf :
    ∀ g ∈ invc.gates, g.wellFormed (unaryLayout 256 2573).width = true := by
  intro g hg
  rw [inv_width]
  exact RCircuit.wellFormed_mem (VQ.Curve.PointAddition.Arithmetic.Inv.wf 256) hg

/-! ## Point-addition assembly

The claim quantifies over every pair of offset coordinates.  `Addable` restricts
the value clause to representable offsets, while the workspace clause assumes
only a representable target.  The assembly's final constant addition requires
`ax < p`, so the generator uses the assembly for representable offsets and the
identity for all other pairs.  The identity satisfies the workspace clause by
preserving every wire. -/

/-- The inverter sets the shared workspace width to 3083 wires; the multiplier
uses 1538. -/
def ws : Nat := 2573

/-- The generator.  Its two parameters are the classical offset's coordinates. -/
def gen (ax ay : Nat) : RCircuit :=
  if ax < VQ.Curve.p ∧ ay < VQ.Curve.p then
    VQ.Reversible.pointAdd 256 ws VQ.Curve.PointAddition.Arithmetic.AddC.ws VQ.Curve.PointAddition.Arithmetic.Neg.ws 2573 VQ.Curve.PointAddition.Arithmetic.Sq.ws VQ.Curve.PointAddition.Arithmetic.Subt.ws
      VQ.Curve.PointAddition.Arithmetic.Mul.ws ax ay (fun c => VQ.Curve.PointAddition.Arithmetic.AddC.gen 256 c) (VQ.Curve.PointAddition.Arithmetic.Neg.gen 256) invc (VQ.Curve.PointAddition.Arithmetic.Sq.gen 256)
      (VQ.Curve.PointAddition.Arithmetic.Subt.gen 256) (VQ.Curve.PointAddition.Arithmetic.Mul.gen 256)
  else
    { width := (asmLayout 256 ws).width, gates := [] }

theorem wf : ∀ ax ay : Nat, RCircuit.wellFormed (VQ.Curve.PointAddition.Arithmetic.gen ax ay) = true := by
  intro ax ay
  rw [gen]
  split
  · exact VQ.Reversible.pointAdd_wellFormed (n := 256) (ws := ws) (ax := ax) (ay := ay)
      (fun c => addc_wf 256 c) (neg_wf 256) inv_wf (sq_wf 256) (sub_wf 256) (mul_wf 256)
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.AddC.ws, VQ.Curve.PointAddition.Arithmetic.AddC.k, VQ.Curve.PointAddition.Arithmetic.AddC.kp, ws])
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.Neg.ws, VQ.Curve.PointAddition.Arithmetic.Neg.k, VQ.Curve.PointAddition.Arithmetic.Neg.kp, ws])
      (Nat.le_refl _)
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.Sq.ws, VQ.Curve.PointAddition.Arithmetic.Sq.k, VQ.Curve.PointAddition.Arithmetic.Sq.kp, ws])
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.Subt.ws, VQ.Curve.PointAddition.Arithmetic.Subt.k, VQ.Curve.PointAddition.Arithmetic.Subt.kp, ws])
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.Mul.ws, VQ.Curve.PointAddition.Arithmetic.Mul.k, VQ.Curve.PointAddition.Arithmetic.Mul.kp, ws])
  · rfl

/-- The claim.  Both clauses of `AddsPoint`, on the domains it names. -/
theorem adds : ∀ ax ay : Nat, VQ.Reversible.AddsPoint ax ay 3085 (VQ.Curve.PointAddition.Arithmetic.gen ax ay) := by
  intro ax ay
  rw [gen]
  split
  · rename_i h
    exact VQ.Reversible.pointAdd_addsPoint VQBridge.Curve.inverseLaw VQBridge.Curve.alg1Law
      (fun c => VQ.Curve.PointAddition.Arithmetic.AddC.adds 256 c) (fun c => addc_wf 256 c)
      (VQ.Curve.PointAddition.Arithmetic.Neg.negs 256) (neg_wf 256) inv_spec inv_wf
      (VQ.Curve.PointAddition.Arithmetic.Sq.squares 256) (sq_wf 256) (VQ.Curve.PointAddition.Arithmetic.Subt.subs 256) (sub_wf 256)
      (VQ.Curve.PointAddition.Arithmetic.Mul.muls 256) (mul_wf 256)
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.AddC.ws, VQ.Curve.PointAddition.Arithmetic.AddC.k, VQ.Curve.PointAddition.Arithmetic.AddC.kp, ws])
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.Neg.ws, VQ.Curve.PointAddition.Arithmetic.Neg.k, VQ.Curve.PointAddition.Arithmetic.Neg.kp, ws])
      (Nat.le_refl _)
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.Sq.ws, VQ.Curve.PointAddition.Arithmetic.Sq.k, VQ.Curve.PointAddition.Arithmetic.Sq.kp, ws])
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.Subt.ws, VQ.Curve.PointAddition.Arithmetic.Subt.k, VQ.Curve.PointAddition.Arithmetic.Subt.kp, ws])
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.Mul.ws, VQ.Curve.PointAddition.Arithmetic.Mul.k, VQ.Curve.PointAddition.Arithmetic.Mul.kp, ws])
      ax ay h.1 h.2
  · rename_i h
    intro x y i _ _ _ h2
    refine ⟨fun hadd _ => ?_, fun _ _ _ => h2⟩
    exfalso
    simp only [VQ.Curve.Addable, VQ.Curve.Representable, Bool.and_eq_true,
      decide_eq_true_eq] at hadd
    exact h ⟨hadd.1.1.1.2.1, hadd.1.1.1.2.2⟩

/-! ## Resources

Each bound follows from the point-addition composition theorem and the
corresponding component bounds.  The identity branch has no gates. -/

theorem inv_toffoli : VQ.Circuit.toffoliCount (VQ.Reversible.compile invc) ≤ 5797136 := by
  have h := VQ.Curve.PointAddition.Arithmetic.Inv.toffoli_le 256
  norm_num at h
  exact h

theorem inv_gates : VQ.Circuit.gateCount (VQ.Reversible.compile invc) ≤ 29786476 := by
  have h := VQ.Curve.PointAddition.Arithmetic.Inv.gates_le 256
  norm_num at h
  exact h

theorem toffoli_le : ∀ ax ay : Nat,
    VQ.Circuit.toffoliCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.gen ax ay)) ≤ 32642112 := by
  intro ax ay
  rw [gen]
  split
  · rw [VQ.Reversible.pointAdd_toffoliCount]
    have ha := fun c => VQ.Curve.PointAddition.Arithmetic.AddC.toffoli_le 256 c
    have hn := VQ.Curve.PointAddition.Arithmetic.Neg.toffoli_le 256
    have hs := VQ.Curve.PointAddition.Arithmetic.Subt.toffoli_le 256
    have hq := VQ.Curve.PointAddition.Arithmetic.Sq.toffoli_le 256
    have hm := VQ.Curve.PointAddition.Arithmetic.Mul.toffoli_le 256
    have hi := inv_toffoli
    have h1 := ha (VQ.Curve.neg ax)
    have h2 := ha (VQ.Curve.neg ay)
    have h3 := ha (VQ.Curve.mul 3 ax)
    have h4 := ha ax
    omega
  · rw [VQ.Reversible.toffoliCount_compile]
    exact Nat.zero_le _

theorem gates_le : ∀ ax ay : Nat,
    VQ.Circuit.gateCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.gen ax ay)) ≤ 169589447 := by
  intro ax ay
  rw [gen]
  split
  · rw [VQ.Reversible.pointAdd_gateCount]
    have ha := fun c => VQ.Curve.PointAddition.Arithmetic.AddC.gates_le 256 c
    have hn := VQ.Curve.PointAddition.Arithmetic.Neg.gates_le 256
    have hs := VQ.Curve.PointAddition.Arithmetic.Subt.gates_le 256
    have hq := VQ.Curve.PointAddition.Arithmetic.Sq.gates_le 256
    have hm := VQ.Curve.PointAddition.Arithmetic.Mul.gates_le 256
    have hi := inv_gates
    have h1 := ha (VQ.Curve.neg ax)
    have h2 := ha (VQ.Curve.neg ay)
    have h3 := ha (VQ.Curve.mul 3 ax)
    have h4 := ha ax
    omega
  · rw [VQ.Reversible.gateCount_compile]
    simp

/-- The elementary-basis T count is seven per compiled Toffoli.
`VQ.Semantics.denote_expand` proves that expansion preserves denotation. -/
theorem tcount_le : ∀ ax ay : Nat,
    VQ.Circuit.expandedTCount (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.gen ax ay)) ≤ 228494784 :=
  fun ax ay => VQ.Reversible.expandedTCount_le (toffoli_le ax ay)

theorem wires_le : ∀ ax ay : Nat,
    VQ.Circuit.usedWires (VQ.Reversible.compile (VQ.Curve.PointAddition.Arithmetic.gen ax ay)) ≤ 3597 := by
  intro ax ay
  rw [gen]
  split
  · refine Nat.le_trans (VQ.Reversible.pointAdd_usedWires (n := 256) (ws := ws)
      (ax := ax) (ay := ay)
      (fun c => addc_wf 256 c) (neg_wf 256) inv_wf (sq_wf 256) (sub_wf 256) (mul_wf 256)
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.AddC.ws, VQ.Curve.PointAddition.Arithmetic.AddC.k, VQ.Curve.PointAddition.Arithmetic.AddC.kp, ws])
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.Neg.ws, VQ.Curve.PointAddition.Arithmetic.Neg.k, VQ.Curve.PointAddition.Arithmetic.Neg.kp, ws])
      (Nat.le_refl _)
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.Sq.ws, VQ.Curve.PointAddition.Arithmetic.Sq.k, VQ.Curve.PointAddition.Arithmetic.Sq.kp, ws])
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.Subt.ws, VQ.Curve.PointAddition.Arithmetic.Subt.k, VQ.Curve.PointAddition.Arithmetic.Subt.kp, ws])
      (by norm_num [VQ.Curve.PointAddition.Arithmetic.Mul.ws, VQ.Curve.PointAddition.Arithmetic.Mul.k, VQ.Curve.PointAddition.Arithmetic.Mul.kp, ws])) ?_
    show 4 * 256 + ws ≤ 3597
    norm_num [ws]
  · refine VQ.Reversible.usedWires_compile_le_of_lt (W := 3597) ?_
    intro g hg
    exact absurd hg (by simp)

end VQ.Curve.PointAddition.Arithmetic
