import VQMathlib.ECDLP.PackedAffine.ShapeCount
import VQ.Program.ResourceReport

namespace VQ.Tests.PackedAffineECDLP.ProgramResources

open VQ
open VQ.Tests.PackedAffineECDLP

def classicalWidth : Nat := 768

def program (pointQ : Nat) : Program :=
  { width := VQ.Curve.PackedAffineLayout.width
    cbits := classicalWidth
    ops := TwoScalarLoop.ops pointQ }

private theorem finalizeOps_wellFormed
    {level resultBit cbits : Nat} (hl : 3 ≤ level)
    (hresult : resultBit < cbits) :
    Program.opsWellFormed level VQ.Curve.PackedAffineLayout.width 0 cbits
      (ScalarProgram.finalizeOps resultBit) = true := by
  have hcontrol : ScalarProgram.controlWire <
      VQ.Curve.PackedAffineLayout.width := by decide
  have hhadamard :
      Program.opsWellFormed level VQ.Curve.PackedAffineLayout.width 0 cbits
        [.gate (.h ScalarProgram.controlWire)] = true := by
    simp [Program.opsWellFormed, Program.opWellFormed, Gate.wellFormedAt,
      hcontrol, hl]
  have hmeasure := ScalarStep.measureAndClearOps_wellFormed
    (level := level) (width := VQ.Curve.PackedAffineLayout.width)
    (control := ScalarProgram.controlWire) (resultBit := resultBit)
    (cbits := cbits) hcontrol hresult
  simpa only [ScalarProgram.finalizeOps, Program.opsWellFormed_append,
    Bool.and_eq_true] using And.intro hhadamard hmeasure

private theorem stepOps_wellFormed
    {level resultOffset count offset cbits : Nat}
    (hl : 3 ≤ level) (hresultOffset : 256 ≤ resultOffset)
    (hcount : count + 1 ≤ level)
    (hresult : resultOffset + count < cbits) :
    Program.opsWellFormed level VQ.Curve.PackedAffineLayout.width 0 cbits
      (ScalarProgram.stepOps resultOffset count offset) = true := by
  have htranslation256 :=
    VQ.Curve.PackedAffineTranslation.program_wellFormed
      (level := level) (ax := VQ.Curve.PointAddition.Runtime.pointX offset)
        (ay := VQ.Curve.PointAddition.Runtime.pointY offset) hl
  simp only [VQ.Curve.PackedAffineTranslation.program,
    Program.wellFormed] at htranslation256
  have htranslation :=
    VQ.Lookup.MeasuredUncompute.opsWellFormed_cbits_mono
      (show 256 ≤ cbits by omega)
      (VQ.Curve.PackedAffineTranslation.ops
        (VQ.Curve.PointAddition.Runtime.pointX offset)
        (VQ.Curve.PointAddition.Runtime.pointY offset))
      htranslation256
  have hcorrection := ScalarStep.correctionOps_wellFormed
    (level := level) (width := VQ.Curve.PackedAffineLayout.width)
    (resultOffset := resultOffset) (control := ScalarProgram.controlWire)
    (count := count) (cbits := cbits) (by decide) hcount (by omega)
  have hfinal := finalizeOps_wellFormed
    (level := level) (resultBit := resultOffset + count)
      (cbits := cbits) hl hresult
  have hcontrol : ScalarProgram.controlWire <
      VQ.Curve.PackedAffineLayout.width := by decide
  have hhadamard :
      Program.opsWellFormed level VQ.Curve.PackedAffineLayout.width 0 cbits
        [.gate (.h ScalarProgram.controlWire)] = true := by
    simp [Program.opsWellFormed, Program.opWellFormed, Gate.wellFormedAt,
      hcontrol, hl]
  simpa only [ScalarProgram.stepOps, Program.opsWellFormed_append,
    Bool.and_eq_true] using
      And.intro hhadamard
        (And.intro htranslation (And.intro hcorrection hfinal))

private theorem scalarOps_wellFormed
    {level resultOffset count cbits : Nat} {offsets : List Nat}
    (hl : 3 ≤ level) (hresultOffset : 256 ≤ resultOffset)
    (hlevel : count + offsets.length ≤ level)
    (hresult : resultOffset + count + offsets.length ≤ cbits) :
    Program.opsWellFormed level VQ.Curve.PackedAffineLayout.width 0 cbits
      (ScalarLoop.scalarOps resultOffset count offsets) = true := by
  induction offsets generalizing count with
  | nil => rfl
  | cons offset offsets ih =>
      simp only [List.length_cons] at hlevel hresult
      rw [ScalarLoop.scalarOps, Program.opsWellFormed_append]
      simp only [Bool.and_eq_true]
      constructor
      · exact stepOps_wellFormed hl hresultOffset (by omega) (by omega)
      · exact ih (count := count + 1) (by omega) (by omega)

private theorem fullScalarOps_wellFormed
    {level resultOffset m point cbits : Nat}
    (hl : 3 ≤ level) (hresultOffset : 256 ≤ resultOffset)
    (hlevel : m ≤ level) (hresult : resultOffset + m ≤ cbits) :
    Program.opsWellFormed level VQ.Curve.PackedAffineLayout.width 0 cbits
      (ScalarLoop.fullScalarOps resultOffset m point) = true := by
  apply scalarOps_wellFormed hl hresultOffset
  · simpa [ScalarLoop.scalarOffsets_length] using hlevel
  · simpa [ScalarLoop.scalarOffsets_length] using hresult

theorem program_wellFormed {level pointQ : Nat} (hlevel : 257 ≤ level) :
    (program pointQ).wellFormed level = true := by
  rw [program, Program.wellFormed, TwoScalarLoop.ops,
    Program.opsWellFormed_append]
  simp only [Bool.and_eq_true]
  constructor
  · exact fullScalarOps_wellFormed (by omega) (by decide)
      (by simpa [TwoScalarLoop.scalarWidth] using
        (show 256 ≤ level by omega)) (by decide)
  · exact fullScalarOps_wellFormed (by omega) (by decide)
      (by simpa [TwoScalarLoop.scalarWidth] using
        (show 256 ≤ level by omega)) (by decide)

theorem program_peakLogicalQubits (pointQ : Nat) :
    (Program.resourceReport (program pointQ)).qubits = 833 := by
  rw [Program.resourceReport, program,
    VQ.Curve.PackedAffineLayout.layout_width]

end VQ.Tests.PackedAffineECDLP.ProgramResources
