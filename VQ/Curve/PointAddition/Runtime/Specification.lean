/-
The offset is a 512-bit immutable classical input.  The quantum register holds
the target point in two 256-bit fields followed by the program's workspace.
Correctness requires coherent affine addition wherever `Curve.Addable` holds
and workspace cleanup for every representable target and offset.
-/
import VQ.Program.Realise

namespace VQ.Curve.PointAddition.Runtime

open Semantics Reversible

def coordBits : Nat := 256
def targetBits : Nat := 2 * coordBits
def inputBits : Nat := 2 * coordBits
def phaseLevel : Nat := 3

/-- The offset's x-coordinate occupies the low 256 input bits. -/
def offsetX (input : Nat) : Nat := readField input 0 coordBits

/-- The offset's y-coordinate occupies input bits 256 through 511. -/
def offsetY (input : Nat) : Nat := readField input coordBits coordBits

/-- The target fields and all remaining qubits as one workspace field. -/
def targetLayout (width : Nat) : Layout :=
  [coordBits, coordBits, width - targetBits]

theorem targetLayout_width {width : Nat} (hw : targetBits ≤ width) :
    (targetLayout width).width = width := by
  simp [targetBits, coordBits] at hw
  simp [targetLayout, targetBits, coordBits, Layout.width]
  omega

theorem offsetX_eq (input : Nat) : offsetX input = input % 2 ^ coordBits := rfl

theorem offsetY_eq (input : Nat) :
    offsetY input = (input / 2 ^ coordBits) % 2 ^ coordBits := by
  simp [offsetY, readField, Nat.shiftRight_eq_div_pow]

/-- The two coordinate decoders reconstruct every declared 512-bit input. -/
theorem offset_reconstruct {input : Nat} (hi : input < 2 ^ inputBits) :
    offsetX input + 2 ^ coordBits * offsetY input = input := by
  rw [offsetX_eq, offsetY_eq]
  have hbits : inputBits = coordBits + coordBits := by
    simp [inputBits, coordBits]
  have hq : input / 2 ^ coordBits < 2 ^ coordBits := by
    have hp : 2 ^ inputBits = 2 ^ coordBits * 2 ^ coordBits := by
      rw [hbits, Nat.pow_add]
    rw [hp] at hi
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos coordBits)).mpr hi
  rw [Nat.mod_eq_of_lt hq, Nat.mod_add_div]

/-- A classical input encodes two field elements. -/
def RepresentableOffset (input : Nat) : Prop :=
  input < 2 ^ inputBits ∧ Curve.Representable (offsetX input) (offsetY input) = true

/-- The target and workspace relation for one immutable offset. -/
def spec (p : Program) (input : Nat) : RegSpec where
  width := p.width
  Pre i := Curve.Representable ((targetLayout p.width).read i 0)
      ((targetLayout p.width).read i 1) = true ∧
    (targetLayout p.width).read i 2 = 0
  Post i j :=
    (targetLayout p.width).read j 2 = 0 ∧
    (Curve.Addable ((targetLayout p.width).read i 0)
        ((targetLayout p.width).read i 1) (offsetX input) (offsetY input) = true →
      (targetLayout p.width).read j 0 =
          (Curve.addPoint ((targetLayout p.width).read i 0)
            ((targetLayout p.width).read i 1) (offsetX input) (offsetY input)).1 ∧
      (targetLayout p.width).read j 1 =
          (Curve.addPoint ((targetLayout p.width).read i 0)
            ((targetLayout p.width).read i 1) (offsetX input) (offsetY input)).2)

/-- Universal correctness for immutable-input affine point addition. -/
def Correct (p : Program) : Prop :=
  p.inputBits = inputBits ∧
  targetBits ≤ p.width ∧
  p.wellFormed phaseLevel = true ∧
  ∀ input, RepresentableOffset input → RealisesAt phaseLevel input (spec p input) p

theorem correct_realisesAt {p : Program} (h : Correct p) {input : Nat}
    (hi : RepresentableOffset input) :
    RealisesAt phaseLevel input (spec p input) p :=
  h.2.2.2 input hi

theorem correct_inputBits {p : Program} (h : Correct p) : p.inputBits = inputBits := h.1

theorem correct_width {p : Program} (h : Correct p) : targetBits ≤ p.width := h.2.1

theorem correct_wellFormed {p : Program} (h : Correct p) :
    p.wellFormed phaseLevel = true := h.2.2.1

/-- The complete branch-level consequence available at one target basis input. -/
theorem correct_output {p : Program} (h : Correct p) {input i : Nat}
    (hoffset : RepresentableOffset input)
    (hi : i < 2 ^ p.width)
    (htarget : Curve.Representable ((targetLayout p.width).read i 0)
      ((targetLayout p.width).read i 1) = true)
    (hworkspace : (targetLayout p.width).read i 2 = 0) :
    ∃ (out : Nat → Nat) (amp : List Bool → Algebra.Dy (Semantics.deg phaseLevel)),
      (targetLayout p.width).read (out i) 2 = 0 ∧
      (Curve.Addable ((targetLayout p.width).read i 0)
          ((targetLayout p.width).read i 1) (offsetX input) (offsetY input) = true →
        (targetLayout p.width).read (out i) 0 =
            (Curve.addPoint ((targetLayout p.width).read i 0)
              ((targetLayout p.width).read i 1) (offsetX input) (offsetY input)).1 ∧
        (targetLayout p.width).read (out i) 1 =
            (Curve.addPoint ((targetLayout p.width).read i 0)
              ((targetLayout p.width).read i 1) (offsetX input) (offsetY input)).2) ∧
      out i < 2 ^ p.width ∧
      (∀ b ∈ runProgram phaseLevel p input (basis i),
        b.state = amp b.outcomes •
          (basis (out i) : Vec (Semantics.deg phaseLevel))) ∧
      totalProb p.width (runProgram phaseLevel p input (basis i)) =
        Algebra.Dy.one (Semantics.deg phaseLevel) := by
  rcases correct_realisesAt h hoffset with ⟨_, _, _, out, amp, hall⟩
  have hout := hall i hi ⟨htarget, hworkspace⟩
  exact ⟨out, amp, hout.1.1, hout.1.2, hout.2.1, hout.2.2.1, hout.2.2.2⟩

/-- Correct programs return the workspace to zero on every constrained input,
including equal x-coordinates, off-curve pairs, and recovery failures. -/
theorem correct_workspace {p : Program} (h : Correct p) {input i : Nat}
    (hoffset : RepresentableOffset input)
    (hi : i < 2 ^ p.width)
    (htarget : Curve.Representable ((targetLayout p.width).read i 0)
      ((targetLayout p.width).read i 1) = true)
    (hworkspace : (targetLayout p.width).read i 2 = 0) :
    ∃ out : Nat → Nat, (targetLayout p.width).read (out i) 2 = 0 := by
  rcases correct_output h hoffset hi htarget hworkspace with ⟨out, _, hws, _⟩
  exact ⟨out, hws⟩

/-- On the affine domain, the output map contains the exact secp256k1 sum. -/
theorem correct_addable {p : Program} (h : Correct p) {input i : Nat}
    (hoffset : RepresentableOffset input)
    (hi : i < 2 ^ p.width)
    (htarget : Curve.Representable ((targetLayout p.width).read i 0)
      ((targetLayout p.width).read i 1) = true)
    (hworkspace : (targetLayout p.width).read i 2 = 0)
    (ha : Curve.Addable ((targetLayout p.width).read i 0)
      ((targetLayout p.width).read i 1) (offsetX input) (offsetY input) = true) :
    ∃ out : Nat → Nat,
      (targetLayout p.width).read (out i) 0 =
          (Curve.addPoint ((targetLayout p.width).read i 0)
            ((targetLayout p.width).read i 1) (offsetX input) (offsetY input)).1 ∧
      (targetLayout p.width).read (out i) 1 =
          (Curve.addPoint ((targetLayout p.width).read i 0)
            ((targetLayout p.width).read i 1) (offsetX input) (offsetY input)).2 ∧
      (targetLayout p.width).read (out i) 2 = 0 := by
  rcases correct_output h hoffset hi htarget hworkspace with ⟨out, _, hws, hv, _⟩
  exact ⟨out, (hv ha).1, (hv ha).2, hws⟩

/-- At one fixed offset, the same record amplitude multiplies both target
components of a two-term superposition. -/
theorem correct_pair {p : Program} (h : Correct p) {input i j : Nat}
    (hoffset : RepresentableOffset input)
    (hi : i < 2 ^ p.width) (hj : j < 2 ^ p.width)
    (hitarget : Curve.Representable ((targetLayout p.width).read i 0)
      ((targetLayout p.width).read i 1) = true)
    (hjtarget : Curve.Representable ((targetLayout p.width).read j 0)
      ((targetLayout p.width).read j 1) = true)
    (hiworkspace : (targetLayout p.width).read i 2 = 0)
    (hjworkspace : (targetLayout p.width).read j 2 = 0)
    (a c : Algebra.Dy (Semantics.deg phaseLevel)) :
    ∃ (out : Nat → Nat) (amp : List Bool → Algebra.Dy (Semantics.deg phaseLevel)),
      runProgram phaseLevel p input (a • basis i + c • basis j)
        = (runProgram phaseLevel p input (basis i)).map (fun b =>
          { b with state := amp b.outcomes •
              (a • (basis (out i) : Vec (Semantics.deg phaseLevel)) +
                c • basis (out j)) }) := by
  rcases correct_realisesAt h hoffset with ⟨_, _, _, out, amp, hall⟩
  refine ⟨out, amp, realises_pair input (fun k hk hp b hb =>
    (hall k hk hp).2.2.1 b hb) hi hj ⟨hitarget, hiworkspace⟩
      ⟨hjtarget, hjworkspace⟩ a c⟩

end VQ.Curve.PointAddition.Runtime
