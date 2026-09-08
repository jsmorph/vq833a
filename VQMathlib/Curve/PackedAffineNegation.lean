import VQ.Curve.PackedAffineNegation

namespace VQMathlib.Curve.PackedAffineNegation

open VQ
open VQ.Reversible
open VQ.Curve.PackedAffineNegation

def gathered (I : Nat) : Nat :=
  gatherBits (place localLayout wiring) localLayout.width I

theorem gathered_target (I : Nat) :
    readField (gathered I) 0 256 = readField I targetOffset 256 := by
  simpa [gathered, localLayout, wiring, Layout.offset, Layout.size] using
    readField_gatherBits localLayout wiring 0 I (by decide)

theorem gathered_carry (I : Nat) :
    readField (gathered I) 256 1 =
      readField I (targetOffset + 256) 1 := by
  simpa [gathered, localLayout, wiring, Layout.offset, Layout.size] using
    readField_gatherBits localLayout wiring 1 I (by decide)

theorem gathered_flag (I : Nat) :
    readField (gathered I) 257 1 =
      readField I (targetOffset + 257) 1 := by
  simpa [gathered, localLayout, wiring, Layout.offset, Layout.size] using
    readField_gatherBits localLayout wiring 2 I (by decide)

theorem gathered_constant (I : Nat) :
    readField (gathered I) 258 256 =
      readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 := by
  simpa [gathered, localLayout, wiring, Layout.offset, Layout.size] using
    readField_gatherBits localLayout wiring 3 I (by decide)

theorem gathered_control (I : Nat) :
    bitValue (gathered I) 514 =
      bitValue I VQ.Curve.PackedAffineLayout.controlWire := by
  rw [← readField_one, ← readField_one]
  simpa [gathered, localLayout, wiring, Layout.offset, Layout.size] using
    readField_gatherBits localLayout wiring 4 I (by decide)

theorem gathered_scratch (I : Nat) :
    bitValue (gathered I) 515 =
      bitValue I VQ.Curve.PackedAffineLayout.equalityWire := by
  rw [← readField_one, ← readField_one]
  simpa [gathered, localLayout, wiring, Layout.offset, Layout.size] using
    readField_gatherBits localLayout wiring 5 I (by decide)

theorem gathered_workspace {I : Nat}
    (htail : readField I (targetOffset + 256) 2 = 0)
    (hinverse : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0) :
    readField (gathered I) 256 258 = 0 := by
  have hcarryPhysical : readField I (targetOffset + 256) 1 = 0 :=
    VQ.Curve.PointAddition.Arithmetic.Neg.readField_sub_zero
      (i := I) (off := targetOffset + 256) (K := 2)
      (d := 0) (e := 1) htail (by omega)
  have hflagPhysical : readField I (targetOffset + 257) 1 = 0 := by
    simpa only [Nat.add_assoc, show 256 + 1 = 257 by omega] using
      VQ.Curve.PointAddition.Arithmetic.Neg.readField_sub_zero
        (i := I) (off := targetOffset + 256) (K := 2)
        (d := 1) (e := 1) htail (by omega)
  have hcarry : readField (gathered I) 256 1 = 0 := by
    rw [gathered_carry, hcarryPhysical]
  have hflag : readField (gathered I) 257 1 = 0 := by
    rw [gathered_flag, hflagPhysical]
  have hconstant : readField (gathered I) 258 256 = 0 := by
    rw [gathered_constant, hinverse]
  have hrest : readField (gathered I) 257 257 = 0 := by
    calc
      readField (gathered I) 257 257 =
          readField (gathered I) 257 1 +
            2 ^ 1 * readField (gathered I) 258 256 := by
        simpa using VQ.Lookup.BatchedUncompute.readField_append
          (gathered I) 257 1 256
      _ = 0 := by rw [hflag, hconstant]; norm_num
  calc
    readField (gathered I) 256 258 =
        readField (gathered I) 256 1 +
          2 ^ 1 * readField (gathered I) 257 257 := by
      simpa using VQ.Lookup.BatchedUncompute.readField_append
        (gathered I) 256 1 257
    _ = 0 := by rw [hcarry, hrest]; norm_num

theorem localGates_wellFormed :
    ∀ gate ∈ (control
      (VQ.Curve.PointAddition.Arithmetic.Neg.gen 256)).gates,
      gate.wellFormed localLayout.width = true := by
  intro gate hgate
  rw [VQ.Curve.PackedAffineNegation.localLayout_width]
  exact RCircuit.wellFormed_mem
    (control_wellFormed
      (VQ.Curve.PointAddition.Arithmetic.Neg.wf 256)) hgate

theorem gates_correct {I a : Nat} {enabled : Bool}
    (htarget : readField I targetOffset 256 = a)
    (htail : readField I (targetOffset + 256) 2 = 0)
    (hinverse : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0)
    (hcontrol : bitValue I VQ.Curve.PackedAffineLayout.controlWire =
      if enabled = true then 1 else 0)
    (hscratch : bitValue I VQ.Curve.PackedAffineLayout.equalityWire = 0)
    (ha : a < VQ.Curve.p) :
    actGates gates I =
      if enabled = true then
        writeField I targetOffset 256 (VQ.Curve.neg a)
      else I := by
  have hneg : NegatesMod VQ.Curve.p 258 256
      (VQ.Curve.PointAddition.Arithmetic.Neg.gen 256) := by
    simpa [VQ.Curve.PointAddition.Arithmetic.Neg.m,
      VQ.Curve.PointAddition.Arithmetic.Neg.ws,
      VQ.Curve.PointAddition.Arithmetic.Neg.k,
      VQ.Curve.PointAddition.Arithmetic.Neg.kp] using
        VQ.Curve.PointAddition.Arithmetic.Neg.negs_general 256
  have hwidth :
      (VQ.Curve.PointAddition.Arithmetic.Neg.gen 256).width =
        (constLayout 256 258).width := by
    decide
  have hcontrolled := control_negatesMod hwidth
    (VQ.Curve.PointAddition.Arithmetic.Neg.wf 256) hneg
  have hlocal :
      actGates
          (control
            (VQ.Curve.PointAddition.Arithmetic.Neg.gen 256)).gates
          (gathered I) =
        if enabled = true then
          (controlledConstLayout 256 258).write (gathered I) 0
            ((VQ.Curve.p - a) % VQ.Curve.p)
        else gathered I := by
    apply hcontrolled enabled a
    · rw [show (controlledConstLayout 256 258).width = localLayout.width by
        decide]
      simpa only [gathered] using
        gatherBits_lt (place localLayout wiring) localLayout.width I
    · change readField (gathered I) 0 256 = a
      rw [gathered_target, htarget]
    · change readField (gathered I) 256 258 = 0
      exact gathered_workspace htail hinverse
    · change readField (gathered I) 514 1 =
        if enabled = true then 1 else 0
      rw [readField_one, gathered_control]
      exact hcontrol
    · change readField (gathered I) 515 1 = 0
      rw [readField_one, gathered_scratch, hscratch]
    · decide
    · exact ha
  cases enabled with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hlocal ⊢
      have hplaced := actGates_placed_congr (hs := [])
        VQ.Curve.PackedAffineNegation.wiring_disjoint
        VQ.Curve.PackedAffineNegation.wiring_length localGates_wellFormed
        (by intro gate hgate; simp at hgate) I hlocal
      simpa [gates, gathered, actGates_nil] using hplaced
  | true =>
      simp only [if_true] at hlocal ⊢
      have hlocal' :
          actGates
              (control
                (VQ.Curve.PointAddition.Arithmetic.Neg.gen 256)).gates
              (gathered I) =
            localLayout.write (gathered I) 0 (VQ.Curve.neg a) := by
        simpa [controlledConstLayout, localLayout, Layout.write,
          Layout.offset, Layout.size, VQ.Curve.neg_eq ha] using hlocal
      have hplaced := actGates_placed_write
        (gs := (control
          (VQ.Curve.PointAddition.Arithmetic.Neg.gen 256)).gates)
        (L := localLayout) (W := wiring) (k := 0)
        (v := VQ.Curve.neg a) (I := I)
        VQ.Curve.PackedAffineNegation.wiring_disjoint
        VQ.Curve.PackedAffineNegation.wiring_length (by decide)
        localGates_wellFormed hlocal'
      simpa [gates, localLayout, wiring, Layout.size, targetOffset] using hplaced

theorem gates_correct_set {I : Nat}
    (htarget : readField I targetOffset 256 < VQ.Curve.p)
    (htail : readField I (targetOffset + 256) 2 = 0)
    (hinverse : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0)
    (hcontrol : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 1)
    (hscratch : bitValue I VQ.Curve.PackedAffineLayout.equalityWire = 0) :
    actGates gates I =
      writeField I targetOffset 256
        (VQ.Curve.neg (readField I targetOffset 256)) := by
  exact gates_correct (enabled := true) rfl htail hinverse
    (by simp [hcontrol]) hscratch htarget

theorem gates_correct_clear {I : Nat}
    (htarget : readField I targetOffset 256 < VQ.Curve.p)
    (htail : readField I (targetOffset + 256) 2 = 0)
    (hinverse : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0)
    (hcontrol : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 0)
    (hscratch : bitValue I VQ.Curve.PackedAffineLayout.equalityWire = 0) :
    actGates gates I = I := by
  exact gates_correct (enabled := false) rfl htail hinverse
    (by simp [hcontrol]) hscratch htarget

theorem circuit_correct_set {I : Nat}
    (htarget : readField I targetOffset 256 < VQ.Curve.p)
    (htail : readField I (targetOffset + 256) 2 = 0)
    (hinverse : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0)
    (hcontrol : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 1)
    (hscratch : bitValue I VQ.Curve.PackedAffineLayout.equalityWire = 0) :
    act circuit I = writeField I targetOffset 256
      (VQ.Curve.neg (readField I targetOffset 256)) := by
  simpa only [act, circuit] using
    gates_correct_set htarget htail hinverse hcontrol hscratch

theorem circuit_correct_clear {I : Nat}
    (htarget : readField I targetOffset 256 < VQ.Curve.p)
    (htail : readField I (targetOffset + 256) 2 = 0)
    (hinverse : readField I VQ.Curve.PackedAffineLayout.inverseOffset 256 = 0)
    (hcontrol : bitValue I VQ.Curve.PackedAffineLayout.controlWire = 0)
    (hscratch : bitValue I VQ.Curve.PackedAffineLayout.equalityWire = 0) :
    act circuit I = I := by
  simpa only [act, circuit] using
    gates_correct_clear htarget htail hinverse hcontrol hscratch

end VQMathlib.Curve.PackedAffineNegation
