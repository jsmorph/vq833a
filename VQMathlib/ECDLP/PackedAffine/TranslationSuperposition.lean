import VQMathlib.Curve.FixedBaseScalarMultiplication.Math
import VQ.Program.Realise
import VQMathlib.Curve.PackedAffineTranslation

namespace VQ.Tests.PackedAffineECDLP.TranslationSuperposition

open VQ VQ.Algebra VQ.Reversible VQ.Semantics
open VQ.Curve.PointAddition.Runtime
open VQ.Tests.FixedBaseScalarMultiplication
open VQ.Tests.GroupTotalPointAddition

def superposeOn {α : Type} {d : Nat}
    (encode : α → Nat) (a : α → Dy d) : List α → Vec d
  | [] => Vec.zero d
  | i :: rest => a i • basis (encode i) + superposeOn encode a rest

theorem runOps_superposeOn_at
    {α : Type} {level w input : Nat} {ops : List Op}
    {encode out : α → Nat} {amp : List Bool → Dy (deg level)}
    {dom : α → Prop}
    (rec : List Bool) (cr : Nat)
    (hcl : ∀ i, encode i < 2 ^ w → dom i →
      ∀ b ∈ runOps level w ops (Branch.mk rec cr (basis (encode i)) input),
        b.state = amp b.outcomes • (basis (out i) : Vec (deg level))) :
    ∀ (L : List α) (a : α → Dy (deg level)),
      (∀ i ∈ L, encode i < 2 ^ w ∧ dom i) →
        ∀ b ∈ runOps level w ops
            (Branch.mk rec cr (superposeOn encode a L) input),
          b.state = amp b.outcomes • superposeOn out a L
  | [], a, _, b, hb => by
    rw [show superposeOn (d := deg level) encode a [] = Vec.zero (deg level) from rfl] at hb
    rw [runOps_zero_state level w ops rec cr input hb,
      show superposeOn (d := deg level) out a [] = Vec.zero (deg level) from rfl,
      Vec.smul_zero]
  | i :: L, a, hmem, b, hb => by
    have hi := hmem i (List.mem_cons_self ..)
    have hsplit :
        runOps level w ops
            (Branch.mk rec cr (superposeOn encode a (i :: L)) input) =
          List.zipWith addBranch
            ((runOps level w ops
                (Branch.mk rec cr (basis (encode i)) input)).map
              (smulBranch (a i)))
            (runOps level w ops
              (Branch.mk rec cr (superposeOn encode a L) input)) := by
      show runOps level w ops
        (Branch.mk rec cr
          (a i • basis (encode i) + superposeOn encode a L) input) = _
      rw [(runOps_add level w).2 ops rec cr input
        (a i • basis (encode i)) (superposeOn encode a L)]
      congr 1
      exact (runOps_smul level w).2 ops (a i)
        (Branch.mk rec cr (basis (encode i)) input)
    have hshape :
        shape ((runOps level w ops
            (Branch.mk rec cr (basis (encode i)) input)).map
          (smulBranch (a i))) =
        shape (runOps level w ops
          (Branch.mk rec cr (superposeOn encode a L) input)) := by
      rw [shape_map_smulBranch, (shape_runOps level w).2,
        (shape_runOps level w).2]
    rw [hsplit] at hb
    have hX :
        ∀ x ∈ (runOps level w ops
            (Branch.mk rec cr (basis (encode i)) input)).map
          (smulBranch (a i)),
          x.state = a i •
            (amp x.outcomes • (basis (out i) : Vec (deg level))) := by
      intro x hx
      obtain ⟨x₀, hx₀, hxe⟩ := List.mem_map.mp hx
      rw [← hxe]
      show a i • x₀.state = _
      rw [hcl i hi.1 hi.2 x₀ hx₀]
      rfl
    have hY := runOps_superposeOn_at rec cr hcl L a
      (fun j hj => hmem j (List.mem_cons_of_mem _ hj))
    have hstate := zipWith_addBranch_mem
      (g := fun s => a i •
        (amp s • (basis (out i) : Vec (deg level))))
      (h := fun s => amp s • superposeOn out a L)
      hshape hX hY b hb
    rw [hstate]
    refine Vec.ext (fun k => ?_)
    show a i * (amp b.outcomes * (basis (out i) : Vec (deg level)) k) +
        amp b.outcomes * superposeOn out a L k =
      amp b.outcomes *
        (a i * (basis (out i) : Vec (deg level)) k +
          superposeOn out a L k)
    rw [Dy.left_distrib, ← Dy.mul_assoc, ← Dy.mul_assoc,
      Dy.mul_comm (a i) (amp b.outcomes)]

def pointState (point : Nat) (enabled : Bool) : Nat :=
  VQMathlib.Curve.PackedAffineTranslation.state
    (pointX point) (pointY point) (if enabled = true then 1 else 0)

def translatedPoint (enabled : Bool) (point offset : Nat) : Nat :=
  if enabled = true then groupAddValue point offset else point

def translationAmplitude (level : Nat) : Dy (deg level) :=
  Dy.invSqrt2 (deg level) ^ 512

def OffsetValid (point : Nat) : Prop :=
  VQ.Curve.Representable (pointX point) (pointY point) = true ∧
    VQ.Curve.OnCurve (pointX point) (pointY point) = true

theorem pointState_lt (point : Nat) (enabled : Bool) :
    pointState point enabled < 2 ^ VQ.Curve.PackedAffineLayout.width := by
  simp only [pointState, VQMathlib.Curve.PackedAffineTranslation.state,
    VQMathlib.Curve.PackedAffineRawTranslation.state,
    VQMathlib.Curve.PackedAffineRetainedDivision.totalInputState,
    VQMathlib.Curve.PackedAffineRetainedDivision.inputState]
  apply writeField_lt (by decide)
  apply writeField_lt (by decide)
  have hx : pointX point < 2 ^ 256 := by
    simpa only [pointX, VQ.Curve.PointAddition.Runtime.n] using
      (readField_lt point 0 256)
  exact hx.trans_le (Nat.pow_le_pow_right (by omega) (by decide))

theorem pointCoordinates_lt {point : Nat} (h : PointValid point) :
    pointX point < VQ.Curve.p ∧ pointY point < VQ.Curve.p := by
  have hr := VQ.Curve.representable_of_groupRepresentable h.2
  simpa only [VQ.Curve.Representable, Bool.and_eq_true,
    decide_eq_true_eq] using hr

theorem offsetCoordinates_lt {point : Nat} (h : OffsetValid point) :
    pointX point < VQ.Curve.p ∧ pointY point < VQ.Curve.p := by
  simpa only [VQ.Curve.Representable, Bool.and_eq_true,
    decide_eq_true_eq] using h.1

theorem ops_correct_point
    {level point offset input : Nat} {enabled : Bool}
    (hl : 3 ≤ level) (hp : PointValid point) (ho : OffsetValid offset)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineTranslation.ops (pointX offset) (pointY offset))
      (Branch.mk rec creg (basis (pointState point enabled)) input)) :
    b.state = translationAmplitude level •
      basis (pointState (translatedPoint enabled point offset) enabled) := by
  have hpCoordinates := pointCoordinates_lt hp
  have hoCoordinates := offsetCoordinates_lt ho
  have h := VQMathlib.Curve.PackedAffineTranslation.ops_correct
    (enabled := enabled) hl hpCoordinates.1 hpCoordinates.2
    hoCoordinates.1 hoCoordinates.2 hp.2
    ho.1 ho.2
    rec creg hb
  rw [VQMathlib.Curve.PackedAffineTranslation.amplitude_eq] at h
  cases enabled with
  | false => simpa [pointState, translatedPoint, translationAmplitude] using h
  | true =>
      have hv : GroupValid point offset :=
        ⟨hp.2,
          VQBridge.Curve.PackedAffineExceptional.offset_groupRepresentable
            ho.1 ho.2⟩
      simpa [pointState, translatedPoint, translationAmplitude,
        pointX_groupAddValue hv, pointY_groupAddValue hv] using h

theorem ops_correct_superposition
    {level offset input : Nat} {enabled : Bool}
    (hl : 3 ≤ level) (ho : OffsetValid offset)
    (rec : List Bool) (creg : Nat)
    (points : List Nat) (a : Nat → Dy (deg level))
    (hpoints : ∀ point ∈ points, PointValid point)
    {b : Branch (deg level)}
    (hb : b ∈ runOps level VQ.Curve.PackedAffineLayout.width
      (VQ.Curve.PackedAffineTranslation.ops (pointX offset) (pointY offset))
      (Branch.mk rec creg
        (superposeOn (fun point => pointState point enabled) a points) input)) :
    b.state = translationAmplitude level •
      superposeOn
        (fun point => pointState (translatedPoint enabled point offset) enabled)
        a points := by
  apply runOps_superposeOn_at rec creg
    (amp := fun _ => translationAmplitude level)
    (dom := PointValid) (L := points) (a := a)
  · intro point _ hp branch hbranch
    exact ops_correct_point hl hp ho rec creg hbranch
  · intro point hpoint
    exact ⟨pointState_lt point enabled, hpoints point hpoint⟩
  · exact hb

end VQ.Tests.PackedAffineECDLP.TranslationSuperposition
