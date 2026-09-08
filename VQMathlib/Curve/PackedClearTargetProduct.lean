import VQ.Curve.PackedClearTargetProduct
import VQMathlib.Curve.PackedModularDoubling

namespace VQMathlib.Curve.PackedClearTargetProduct

open VQ
open VQ.Algebra
open VQ.Reversible
open VQ.Semantics
open VQ.Curve.PackedClearTargetProduct
open VQ.Curve.PackedModularAddition

theorem blockMap_target {wordWidth controlBit q : Nat}
    (hq : q < wordWidth) :
    blockMap wordWidth controlBit q =
      VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth + q := by
  simpa [blockMap, blockLayout, blockWiring, Layout.offset, Layout.size]
    using place_field (blockLayout wordWidth)
      (blockWiring wordWidth controlBit) 0 q
        (by norm_num [blockWiring]) hq

theorem blockMap_targetExtension (wordWidth controlBit : Nat) :
    blockMap wordWidth controlBit
        (VQ.Curve.PackedModularAddition.targetExtensionWire wordWidth) =
      auxiliaryOffset wordWidth := by
  simpa [blockMap, blockLayout, blockWiring, Layout.offset, Layout.size,
    VQ.Curve.PackedModularAddition.targetExtensionWire]
    using place_field (blockLayout wordWidth)
      (blockWiring wordWidth controlBit) 1 0
        (by norm_num [blockWiring])
        (by norm_num [blockLayout, Layout.size])

theorem blockMap_source {wordWidth controlBit q : Nat}
    (hq : q < wordWidth) :
    blockMap wordWidth controlBit
        (VQ.Curve.PackedModularAddition.sourceOffset wordWidth + q) =
      multiplicandOffset wordWidth + q := by
  simpa [blockMap, blockLayout, blockWiring, Layout.offset, Layout.size,
    VQ.Curve.PackedModularAddition.sourceOffset]
    using place_field (blockLayout wordWidth)
      (blockWiring wordWidth controlBit) 2 q
        (by norm_num [blockWiring]) hq

theorem blockMap_sourceExtension (wordWidth controlBit : Nat) :
    blockMap wordWidth controlBit
        (VQ.Curve.PackedModularAddition.sourceExtensionWire wordWidth) =
      auxiliaryOffset wordWidth + 1 := by
  unfold blockMap
  rw [show VQ.Curve.PackedModularAddition.sourceExtensionWire wordWidth =
      Layout.offset (blockLayout wordWidth) 3 + 0 by
        simp [VQ.Curve.PackedModularAddition.sourceExtensionWire,
          blockLayout, Layout.offset]
        omega,
    place_field (blockLayout wordWidth) (blockWiring wordWidth controlBit)
      3 0 (by norm_num [blockWiring])
        (by norm_num [blockLayout, Layout.size])]
  simp [blockWiring]

theorem blockMap_carryIn (wordWidth controlBit : Nat) :
    blockMap wordWidth controlBit
        (VQ.Curve.PackedModularAddition.carryInWire wordWidth) =
      auxiliaryOffset wordWidth + 2 := by
  unfold blockMap
  rw [show VQ.Curve.PackedModularAddition.carryInWire wordWidth =
      Layout.offset (blockLayout wordWidth) 4 + 0 by
        simp [VQ.Curve.PackedModularAddition.carryInWire,
          blockLayout, Layout.offset]
        omega,
    place_field (blockLayout wordWidth) (blockWiring wordWidth controlBit)
      4 0 (by norm_num [blockWiring])
        (by norm_num [blockLayout, Layout.size])]
  simp [blockWiring]

theorem blockMap_carryOut (wordWidth controlBit : Nat) :
    blockMap wordWidth controlBit
        (VQ.Curve.PackedModularAddition.carryOutWire wordWidth) =
      auxiliaryOffset wordWidth + 3 := by
  unfold blockMap
  rw [show VQ.Curve.PackedModularAddition.carryOutWire wordWidth =
      Layout.offset (blockLayout wordWidth) 5 + 0 by
        simp [VQ.Curve.PackedModularAddition.carryOutWire,
          blockLayout, Layout.offset]
        omega,
    place_field (blockLayout wordWidth) (blockWiring wordWidth controlBit)
      5 0 (by norm_num [blockWiring])
        (by norm_num [blockLayout, Layout.size])]
  simp [blockWiring]

theorem blockMap_scratch (wordWidth controlBit : Nat) :
    blockMap wordWidth controlBit
        (VQ.Curve.PackedModularAddition.scratchWire wordWidth) =
      auxiliaryOffset wordWidth + 4 := by
  unfold blockMap
  rw [show VQ.Curve.PackedModularAddition.scratchWire wordWidth =
      Layout.offset (blockLayout wordWidth) 6 + 0 by
        simp [VQ.Curve.PackedModularAddition.scratchWire,
          blockLayout, Layout.offset]
        omega,
    place_field (blockLayout wordWidth) (blockWiring wordWidth controlBit)
      6 0 (by norm_num [blockWiring])
        (by norm_num [blockLayout, Layout.size])]
  simp [blockWiring]

theorem blockMap_reduction (wordWidth controlBit : Nat) :
    blockMap wordWidth controlBit
        (VQ.Curve.PackedModularAddition.reductionWire wordWidth) =
      auxiliaryOffset wordWidth + 5 := by
  unfold blockMap
  rw [show VQ.Curve.PackedModularAddition.reductionWire wordWidth =
      Layout.offset (blockLayout wordWidth) 7 + 0 by
        simp [VQ.Curve.PackedModularAddition.reductionWire,
          blockLayout, Layout.offset]
        omega,
    place_field (blockLayout wordWidth) (blockWiring wordWidth controlBit)
      7 0 (by norm_num [blockWiring])
        (by norm_num [blockLayout, Layout.size])]
  simp [blockWiring]

theorem blockMap_control (wordWidth controlBit : Nat) :
    blockMap wordWidth controlBit
        (VQ.Curve.PackedModularAddition.controlWire wordWidth) = controlBit := by
  unfold blockMap
  rw [show VQ.Curve.PackedModularAddition.controlWire wordWidth =
      Layout.offset (blockLayout wordWidth) 8 + 0 by
        simp [VQ.Curve.PackedModularAddition.controlWire,
          blockLayout, Layout.offset]
        omega,
    place_field (blockLayout wordWidth) (blockWiring wordWidth controlBit)
      8 0 (by norm_num [blockWiring])
        (by norm_num [blockLayout, Layout.size])]
  simp [blockWiring, multiplierOffset]

def AuxiliaryClear (wordWidth index : Nat) : Prop :=
  ∀ q, q < 6 → bitValue index (auxiliaryOffset wordWidth + q) = 0

theorem AuxiliaryClear.writeTarget
    {wordWidth index value : Nat}
    (hclear : AuxiliaryClear wordWidth index) :
    AuxiliaryClear wordWidth
      (writeField index
        (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
        wordWidth value) := by
  intro q hq
  rw [bitValue_write_out]
  · exact hclear q hq
  · simp [VQ.Curve.PackedClearTargetProduct.targetOffset, auxiliaryOffset]
    omega

theorem replaceBits_targetWrite
    {wordWidth controlBit original value : Nat}
    (hwidth : 0 < wordWidth) (hcontrol : controlBit < wordWidth) :
    replaceBits (blockMap wordWidth controlBit)
        (VQ.Curve.PackedModularAddition.width wordWidth)
        (writeField
          (sourceIndex (blockMap wordWidth controlBit)
            (VQ.Curve.PackedModularAddition.width wordWidth) original)
          0 wordWidth value)
        original =
      writeField original
        (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
        wordWidth value := by
  let f := blockMap wordWidth controlBit
  let localWidth := VQ.Curve.PackedModularAddition.width wordWidth
  have hinj : ∀ x y, x < localWidth → y < localWidth →
      f x = f y → x = y :=
    fun x y hx hy hxy => blockMap_injective hwidth hcontrol hx hy hxy
  have hmap : ∀ q, q < wordWidth → f q =
      VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth + q :=
    fun q hq => blockMap_target hq
  apply Nat.eq_of_testBit_eq
  intro q
  by_cases himage : ∃ r, r < localWidth ∧ f r = q
  · obtain ⟨r, hr, rfl⟩ := himage
    rw [testBit_replaceBits hr hinj]
    by_cases htarget : r < wordWidth
    · rw [testBit_writeField_inside (Nat.zero_le r) (by omega),
        hmap r htarget,
        testBit_writeField_inside (by
          simp [VQ.Curve.PackedClearTargetProduct.targetOffset]) (by
          simp [VQ.Curve.PackedClearTargetProduct.targetOffset]
          omega)]
      simp [VQ.Curve.PackedClearTargetProduct.targetOffset]
    · have houtside : f r <
          VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth ∨
          VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth +
            wordWidth ≤ f r := by
        by_contra h
        have hrange :
            VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth ≤ f r ∧
            f r < VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth +
              wordWidth := by omega
        let s := f r -
          VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth
        have hs : s < wordWidth := by simp [s]; omega
        have hfs : f s = f r := by simp [hmap s hs, s]; omega
        have hrs : r = s := hinj r s hr (by
          simp [localWidth, VQ.Curve.PackedModularAddition.width]
          omega) hfs.symm
        exact htarget (hrs ▸ hs)
      rw [testBit_writeField_outside (Or.inr (by omega)),
        testBit_sourceIndex hr,
        testBit_writeField_outside houtside]
  · rw [testBit_replaceBits_outside (by
        intro r hr heq
        exact himage ⟨r, hr, heq.symm⟩)]
    by_cases hq :
        VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth ≤ q ∧
        q < VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth +
          wordWidth
    · let r := q -
        VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth
      have hr : r < wordWidth := by simp [r]; omega
      exact (himage ⟨r, by
        simp [localWidth, VQ.Curve.PackedModularAddition.width]
        omega, by simp [hmap r hr, r]; omega⟩).elim
    · rw [testBit_writeField_outside (by omega)]

def localIndex (wordWidth controlBit index : Nat) : Nat :=
  sourceIndex (blockMap wordWidth controlBit)
    (VQ.Curve.PackedModularAddition.width wordWidth) index

theorem localIndex_target
    {wordWidth controlBit index : Nat} :
    readField (localIndex wordWidth controlBit index) 0 wordWidth =
      readField index
        (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
        wordWidth := by
  apply readField_sourceIndex
  · simp [VQ.Curve.PackedModularAddition.width]
    omega
  · intro q hq
    simpa using blockMap_target (controlBit := controlBit) hq

theorem localIndex_source
    {wordWidth controlBit index : Nat} :
    readField (localIndex wordWidth controlBit index)
        (VQ.Curve.PackedModularAddition.sourceOffset wordWidth) wordWidth =
      readField index (multiplicandOffset wordWidth) wordWidth := by
  apply readField_sourceIndex
  · simp [VQ.Curve.PackedModularAddition.sourceOffset,
      VQ.Curve.PackedModularAddition.width]
    omega
  · intro q hq
    exact blockMap_source hq

theorem localIndex_testBit
    {wordWidth controlBit index q : Nat}
    (hq : q < VQ.Curve.PackedModularAddition.width wordWidth) :
    (localIndex wordWidth controlBit index).testBit q =
      index.testBit (blockMap wordWidth controlBit q) := by
  exact testBit_sourceIndex hq

theorem localIndex_bitValue
    {wordWidth controlBit index q : Nat}
    (hq : q < VQ.Curve.PackedModularAddition.width wordWidth) :
    bitValue (localIndex wordWidth controlBit index) q =
      bitValue index (blockMap wordWidth controlBit q) := by
  unfold bitValue
  rw [localIndex_testBit hq]

theorem localIndex_control
    {wordWidth controlBit index : Nat}
    (_hwidth : 0 < wordWidth) :
    (localIndex wordWidth controlBit index).testBit
        (VQ.Curve.PackedModularAddition.controlWire wordWidth) =
      index.testBit controlBit := by
  rw [localIndex_testBit (by
    simp [VQ.Curve.PackedModularAddition.controlWire,
      VQ.Curve.PackedModularAddition.width]), blockMap_control]

theorem localIndex_rawSum
    {wordWidth controlBit index : Nat}
    (hwidth : 0 < wordWidth) :
    VQMathlib.Curve.PackedModularAddition.rawSum wordWidth
        (localIndex wordWidth controlBit index) =
      bitValue index controlBit *
          readField index (multiplicandOffset wordWidth) wordWidth +
        readField index
          (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
          wordWidth := by
  cases hcontrol : index.testBit controlBit <;>
    simp [VQMathlib.Curve.PackedModularAddition.rawSum,
      VQ.Curve.PackedModularAddition.selectedSource,
      VQ.Curve.PackedModularAddition.targetOffset,
      localIndex_control hwidth, localIndex_source, localIndex_target,
      bitValue, hcontrol]

theorem localIndex_rawDouble
    {wordWidth controlBit index : Nat} :
    VQMathlib.Curve.PackedModularDoubling.rawDouble wordWidth
        (localIndex wordWidth controlBit index) =
      2 * readField index
        (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
        wordWidth := by
  simp [VQMathlib.Curve.PackedModularDoubling.rawDouble,
    VQMathlib.Curve.PackedModularDoubling.targetValue,
    VQ.Curve.PackedModularAddition.targetOffset,
    localIndex_target]

theorem localIndex_workspace
    {wordWidth controlBit index : Nat}
    (hclear : AuxiliaryClear wordWidth index) :
    VQ.Curve.PackedModularAddition.WorkspaceClear wordWidth
      (localIndex wordWidth controlBit index) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [localIndex_bitValue (by
      simp [VQ.Curve.PackedModularAddition.carryInWire,
        VQ.Curve.PackedModularAddition.width]), blockMap_carryIn]
    exact hclear 2 (by omega)
  · rw [localIndex_bitValue (by
      simp [VQ.Curve.PackedModularAddition.carryOutWire,
        VQ.Curve.PackedModularAddition.width]), blockMap_carryOut]
    exact hclear 3 (by omega)
  · rw [localIndex_bitValue (by
      simp [VQ.Curve.PackedModularAddition.scratchWire,
        VQ.Curve.PackedModularAddition.width]), blockMap_scratch]
    exact hclear 4 (by omega)

theorem localIndex_targetExtension
    {wordWidth controlBit index : Nat}
    (hclear : AuxiliaryClear wordWidth index) :
    bitValue (localIndex wordWidth controlBit index)
        (VQ.Curve.PackedModularAddition.targetExtensionWire wordWidth) = 0 := by
  rw [localIndex_bitValue (by
    simp [VQ.Curve.PackedModularAddition.targetExtensionWire,
      VQ.Curve.PackedModularAddition.width]
    omega), blockMap_targetExtension]
  exact hclear 0 (by omega)

theorem localIndex_reduction
    {wordWidth controlBit index : Nat}
    (hclear : AuxiliaryClear wordWidth index) :
    bitValue (localIndex wordWidth controlBit index)
        (VQ.Curve.PackedModularAddition.reductionWire wordWidth) = 0 := by
  rw [localIndex_bitValue (by
    simp [VQ.Curve.PackedModularAddition.reductionWire,
      VQ.Curve.PackedModularAddition.width]), blockMap_reduction]
  exact hclear 5 (by omega)

theorem addOps_correct
    {level modulus wordWidth controlBit original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus) (hmodulus : modulus < 2 ^ wordWidth)
    (hcontrol : controlBit < wordWidth)
    (hsource : readField original (multiplicandOffset wordWidth) wordWidth ≤
      modulus)
    (htarget : readField original
        (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
        wordWidth < modulus)
    (hclear : AuxiliaryClear wordWidth original)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level
      (VQ.Curve.PackedClearTargetProduct.width wordWidth)
      (addOps modulus wordWidth controlBit)
      (Branch.mk rec creg (basis original) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
      basis (writeField original
        (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
        wordWidth
        ((bitValue original controlBit *
              readField original (multiplicandOffset wordWidth) wordWidth +
            readField original
              (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
              wordWidth) % modulus)) := by
  let f := blockMap wordWidth controlBit
  let localWidth := VQ.Curve.PackedModularAddition.width wordWidth
  let localOriginal := localIndex wordWidth controlBit original
  have hinj : ∀ x y, x < localWidth → y < localWidth →
      f x = f y → x = y :=
    fun x y hx hy hxy => blockMap_injective (by omega) hcontrol hx hy hxy
  have hrun := runOps_relabel
    (level := level) (width := localWidth)
    (totalWidth := VQ.Curve.PackedClearTargetProduct.width wordWidth)
    (inputBits := 0) (cbits := wordWidth) (f := f) (ambient := original)
    (ops := VQ.Curve.PackedModularAddition.modularAddOps modulus wordWidth)
    (b := Branch.mk rec creg (basis localOriginal) input)
    (fun q hq => blockMap_lt (by omega) hcontrol hq) hinj
    (VQ.Curve.PackedModularAddition.modularAddOps_wellFormed hl hwidth)
    (wfVec_basis (sourceIndex_lt f localWidth original))
  have hstart : placeBranch f localWidth original
      (Branch.mk rec creg (basis localOriginal : Vec (deg level)) input) =
      Branch.mk rec creg (basis original) input := by
    exact placeBranch_sourceIndex_basis hinj rec creg input
  rw [hstart] at hrun
  rw [addOps, hrun, List.mem_map] at hb
  obtain ⟨localBranch, hlocalBranch, rfl⟩ := hb
  have hsourceValue :
      VQMathlib.Curve.PackedModularAddition.sourceValue wordWidth
          localOriginal =
        readField original (multiplicandOffset wordWidth) wordWidth := by
    exact localIndex_source
  have htargetValue :
      VQMathlib.Curve.PackedModularAddition.targetValue wordWidth
          localOriginal =
        readField original
          (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
          wordWidth := by
    exact localIndex_target
  have hlocalState :=
    VQMathlib.Curve.PackedModularAddition.modularAddOps_correct
      hl hwidth hmodulusPos hmodulus
      (by rw [hsourceValue]; exact hsource)
      (by rw [htargetValue]; exact htarget)
      (by simpa [localOriginal] using localIndex_workspace hclear)
      (by simpa [localOriginal] using localIndex_reduction hclear)
      (by simpa [localOriginal] using localIndex_targetExtension hclear)
      rec creg hlocalBranch
  let value :=
    (bitValue original controlBit *
          readField original (multiplicandOffset wordWidth) wordWidth +
        readField original
          (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
          wordWidth) % modulus
  have hlocalValue :
      VQMathlib.Curve.PackedModularAddition.rawSum wordWidth localOriginal %
          modulus =
        value := by
    rw [localIndex_rawSum (by omega)]
  have hresultFit : writeField localOriginal 0 wordWidth value <
      2 ^ localWidth := by
    apply writeField_lt
    · simp [localWidth, VQ.Curve.PackedModularAddition.width]
      omega
    · exact sourceIndex_lt f localWidth original
  have hlocalStateZero : localBranch.state =
      Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
        basis (writeField localOriginal 0 wordWidth value) := by
    simpa [VQ.Curve.PackedModularAddition.targetOffset, hlocalValue] using
      hlocalState
  change placeVec f localWidth original localBranch.state = _
  rw [hlocalStateZero, placeVec_smul, placeVec_basis hresultFit]
  have hreplace :
      replaceBits f localWidth
          (writeField localOriginal 0 wordWidth value) original =
        writeField original
          (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
          wordWidth value := by
    simpa [f, localWidth, localOriginal, localIndex] using
      replaceBits_targetWrite (wordWidth := wordWidth)
        (controlBit := controlBit) (original := original) (value := value)
        (by omega) hcontrol
  simpa [value] using congrArg
    (fun index => Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
      (basis index : Vec (deg level))) hreplace

theorem doubleOps_correct
    {level modulus wordWidth controlBit original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus) (hmodulus : modulus < 2 ^ wordWidth)
    (hmodulusOdd : modulus % 2 = 1)
    (hcontrol : controlBit < wordWidth)
    (htarget : readField original
        (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
        wordWidth < modulus)
    (hclear : AuxiliaryClear wordWidth original)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level
      (VQ.Curve.PackedClearTargetProduct.width wordWidth)
      (doubleOps modulus wordWidth controlBit)
      (Branch.mk rec creg (basis original) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
      basis (writeField original
        (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
        wordWidth
        ((2 * readField original
          (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
          wordWidth) % modulus)) := by
  let f := blockMap wordWidth controlBit
  let localWidth := VQ.Curve.PackedModularAddition.width wordWidth
  let localOriginal := localIndex wordWidth controlBit original
  have hinj : ∀ x y, x < localWidth → y < localWidth →
      f x = f y → x = y :=
    fun x y hx hy hxy => blockMap_injective (by omega) hcontrol hx hy hxy
  have hrun := runOps_relabel
    (level := level) (width := localWidth)
    (totalWidth := VQ.Curve.PackedClearTargetProduct.width wordWidth)
    (inputBits := 0) (cbits := wordWidth) (f := f) (ambient := original)
    (ops := VQ.Curve.PackedModularDoubling.modularDoubleOps modulus wordWidth)
    (b := Branch.mk rec creg (basis localOriginal) input)
    (fun q hq => blockMap_lt (by omega) hcontrol hq) hinj
    (VQ.Curve.PackedModularDoubling.modularDoubleOps_wellFormed hl hwidth)
    (wfVec_basis (sourceIndex_lt f localWidth original))
  have hstart : placeBranch f localWidth original
      (Branch.mk rec creg (basis localOriginal : Vec (deg level)) input) =
      Branch.mk rec creg (basis original) input := by
    exact placeBranch_sourceIndex_basis hinj rec creg input
  rw [hstart] at hrun
  rw [doubleOps, hrun, List.mem_map] at hb
  obtain ⟨localBranch, hlocalBranch, rfl⟩ := hb
  have htargetValue :
      VQMathlib.Curve.PackedModularDoubling.targetValue wordWidth
          localOriginal =
        readField original
          (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
          wordWidth := by
    exact localIndex_target
  have hlocalState :=
    VQMathlib.Curve.PackedModularDoubling.modularDoubleOps_correct
      hl hwidth hmodulusPos hmodulus hmodulusOdd
      (by rw [htargetValue]; exact htarget)
      (by simpa [localOriginal] using localIndex_workspace hclear)
      (by simpa [localOriginal] using localIndex_reduction hclear)
      (by simpa [localOriginal] using localIndex_targetExtension hclear)
      rec creg hlocalBranch
  let value := (2 * readField original
    (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
    wordWidth) % modulus
  have hlocalValue :
      VQMathlib.Curve.PackedModularDoubling.rawDouble wordWidth localOriginal %
        modulus = value := by
    rw [localIndex_rawDouble]
  have hresultFit : writeField localOriginal 0 wordWidth value <
      2 ^ localWidth := by
    apply writeField_lt
    · simp [localWidth, VQ.Curve.PackedModularAddition.width]
      omega
    · exact sourceIndex_lt f localWidth original
  have hlocalStateZero : localBranch.state =
      Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
        basis (writeField localOriginal 0 wordWidth value) := by
    simpa [VQ.Curve.PackedModularAddition.targetOffset, hlocalValue] using
      hlocalState
  change placeVec f localWidth original localBranch.state = _
  rw [hlocalStateZero, placeVec_smul, placeVec_basis hresultFit]
  have hreplace :
      replaceBits f localWidth
          (writeField localOriginal 0 wordWidth value) original =
        writeField original
          (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
          wordWidth value := by
    simpa [f, localWidth, localOriginal, localIndex] using
      replaceBits_targetWrite (wordWidth := wordWidth)
        (controlBit := controlBit) (original := original) (value := value)
        (by omega) hcontrol
  simpa [value] using congrArg
    (fun index => Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
      (basis index : Vec (deg level))) hreplace

def productValue (modulus wordWidth index : Nat)
    (controls : List Nat) : Nat :=
  VQBridge.Curve.LuoMultiplication.horner modulus
    (readField index (multiplicandOffset wordWidth) wordWidth)
    (controls.map fun q => index.testBit q)

def amplitudeExponent (wordWidth : Nat) : List Nat → Nat
  | [] => 0
  | [_] => 3 * wordWidth - 1
  | _ :: nextBit :: rest =>
      amplitudeExponent wordWidth (nextBit :: rest) +
        (3 * wordWidth - 1) + (3 * wordWidth - 1)

theorem decode_append (xs ys : List Bool) :
    VQBridge.Curve.LuoMultiplication.decode (xs ++ ys) =
      VQBridge.Curve.LuoMultiplication.decode xs +
        2 ^ xs.length * VQBridge.Curve.LuoMultiplication.decode ys := by
  induction xs with
  | nil => simp [VQBridge.Curve.LuoMultiplication.decode]
  | cons bit xs ih =>
      simp [VQBridge.Curve.LuoMultiplication.decode, ih, Nat.pow_succ]
      ring

theorem decode_range_testBits (index wordWidth : Nat) :
    VQBridge.Curve.LuoMultiplication.decode
        ((List.range wordWidth).map fun q => index.testBit q) =
      readField index 0 wordWidth := by
  induction wordWidth with
  | zero =>
      simp [VQBridge.Curve.LuoMultiplication.decode, readField_size_zero]
  | succ wordWidth ih =>
      rw [List.range_succ, List.map_append, decode_append, ih,
        readField_high]
      simp [VQBridge.Curve.LuoMultiplication.decode,
        VQBridge.Curve.LuoMultiplication.bitValue, bitValue]

theorem amplitudeExponent_eq
    {wordWidth : Nat} : ∀ {controls : List Nat}, controls ≠ [] →
      amplitudeExponent wordWidth controls =
        (2 * controls.length - 1) * (3 * wordWidth - 1)
  | [], hcontrols => (hcontrols rfl).elim
  | [_], _ => by simp [amplitudeExponent]
  | controlBit :: nextBit :: rest, _ => by
      rw [amplitudeExponent,
        amplitudeExponent_eq (controls := nextBit :: rest) (by simp)]
      simp only [List.length_cons]
      have htailLength : 2 * (rest.length + 1) - 1 =
          2 * rest.length + 1 := by omega
      have hallLength : 2 * (rest.length + 1 + 1) - 1 =
          2 * rest.length + 3 := by omega
      rw [htailLength, hallLength]
      ring

theorem productValue_range (modulus wordWidth index : Nat) :
    productValue modulus wordWidth index (List.range wordWidth) =
      readField index multiplierOffset wordWidth *
        readField index (multiplicandOffset wordWidth) wordWidth % modulus := by
  rw [productValue, VQBridge.Curve.LuoMultiplication.horner_correct,
    decode_range_testBits]
  rfl

theorem productValue_lt
    {modulus wordWidth index : Nat} (hmodulusPos : 0 < modulus) :
    ∀ {controls : List Nat}, controls ≠ [] →
      productValue modulus wordWidth index controls < modulus
  | [], hcontrols => (hcontrols rfl).elim
  | _ :: _, _ => by
      simp [productValue, VQBridge.Curve.LuoMultiplication.horner]
      exact Nat.mod_lt _ hmodulusPos

theorem productOpsAux_correct
    {level modulus wordWidth original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus) (hmodulus : modulus < 2 ^ wordWidth)
    (hmodulusOdd : modulus % 2 = 1)
    (hsource : readField original (multiplicandOffset wordWidth) wordWidth ≤
      modulus)
    (htarget : readField original
      (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
      wordWidth = 0)
    (hclear : AuxiliaryClear wordWidth original) :
    ∀ controls,
      (∀ controlBit ∈ controls, controlBit < wordWidth) →
      ∀ (rec : List Bool) (creg : Nat) {b : Branch (deg level)},
        b ∈ runOps level
          (VQ.Curve.PackedClearTargetProduct.width wordWidth)
          (productOpsAux modulus wordWidth controls)
          (Branch.mk rec creg (basis original) input) →
        b.state = Algebra.Dy.invSqrt2 (deg level) ^
            amplitudeExponent wordWidth controls •
          basis (writeField original
            (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
            wordWidth (productValue modulus wordWidth original controls))
  | [], _, rec, creg, b, hb => by
      simp only [productOpsAux, runOps_nil, List.mem_singleton] at hb
      subst b
      have hwrite : writeField original
          (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
          wordWidth 0 = original := by
        rw [← htarget, writeField_read]
      rw [show productValue modulus wordWidth original [] = 0 by rfl, hwrite]
      change (basis original : Vec (deg level)) =
        Algebra.Dy.invSqrt2 (deg level) ^ 0 • basis original
      rw [Algebra.Dy.pow_zero_eq, Vec.one_smul]
  | [controlBit], hcontrols, rec, creg, b, hb => by
      have hcontrol : controlBit < wordWidth :=
        hcontrols controlBit (by simp)
      have hstate := addOps_correct hl hwidth hmodulusPos hmodulus
        hcontrol hsource (by rw [htarget]; exact hmodulusPos) hclear
        rec creg hb
      simpa [amplitudeExponent, productValue,
        VQBridge.Curve.LuoMultiplication.horner,
        VQBridge.Curve.LuoMultiplication.bitValue, bitValue, htarget,
        Nat.add_comm] using hstate
  | controlBit :: nextBit :: rest, hcontrols, rec, creg, b, hb => by
      let tailControls := nextBit :: rest
      let tailValue := productValue modulus wordWidth original tailControls
      let tailIndex := writeField original
        (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
        wordWidth tailValue
      let doubleValue := 2 * tailValue % modulus
      let doubleIndex := writeField original
        (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
        wordWidth doubleValue
      let finalValue :=
        (bitValue original controlBit *
            readField original (multiplicandOffset wordWidth) wordWidth +
          doubleValue) % modulus
      have hcontrol : controlBit < wordWidth :=
        hcontrols controlBit (by simp)
      have htailControls : ∀ q ∈ tailControls, q < wordWidth := by
        intro q hq
        exact hcontrols q (List.mem_cons_of_mem controlBit hq)
      simp only [productOpsAux] at hb
      rw [runOps_append, List.mem_flatMap] at hb
      obtain ⟨beforeAdd, hbeforeAdd, haddBranch⟩ := hb
      rw [runOps_append, List.mem_flatMap] at hbeforeAdd
      obtain ⟨tailBranch, htailBranch, hdoubleBranch⟩ := hbeforeAdd
      have htailState := productOpsAux_correct hl hwidth hmodulusPos
        hmodulus hmodulusOdd hsource htarget hclear tailControls
        htailControls rec creg htailBranch
      change tailBranch.state =
        Algebra.Dy.invSqrt2 (deg level) ^
            amplitudeExponent wordWidth tailControls • basis tailIndex at htailState
      have htailValueLt : tailValue < modulus := by
        exact productValue_lt hmodulusPos (by simp [tailControls])
      have htailValueFit : tailValue < 2 ^ wordWidth :=
        htailValueLt.trans hmodulus
      have htargetTail : readField tailIndex
          (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
          wordWidth < modulus := by
        rw [readField_writeField_self htailValueFit]
        exact htailValueLt
      have hclearTail : AuxiliaryClear wordWidth tailIndex :=
        hclear.writeTarget
      obtain ⟨normalizedDouble, hnormalizedDouble, hdoubleEq⟩ :=
        VQ.Curve.PackedModularAddition.mem_runOps_smul_basis
          htailState hdoubleBranch
      cases normalizedDouble with
      | mk recDouble cregDouble stateDouble inputDouble =>
          have hnormalizedDoubleState := doubleOps_correct hl hwidth
            hmodulusPos hmodulus hmodulusOdd hcontrol htargetTail hclearTail
            tailBranch.outcomes tailBranch.creg hnormalizedDouble
          have hdoubleTarget :
              2 * readField tailIndex
                  (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
                  wordWidth % modulus = doubleValue := by
            rw [readField_writeField_self htailValueFit]
          have hdoubleIndex : writeField tailIndex
                (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
                wordWidth doubleValue = doubleIndex := by
            simp [tailIndex, doubleIndex, writeField_writeField]
          have hnormalizedDoubleState' : stateDouble =
              Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
                basis doubleIndex := by
            simpa [hdoubleTarget, hdoubleIndex] using hnormalizedDoubleState
          have hdoubleState : beforeAdd.state =
              (Algebra.Dy.invSqrt2 (deg level) ^
                    amplitudeExponent wordWidth tailControls *
                  Algebra.Dy.invSqrt2 (deg level) ^
                    (3 * wordWidth - 1)) • basis doubleIndex := by
            rw [hdoubleEq]
            simp only [smulBranch]
            rw [hnormalizedDoubleState', Vec.smul_smul]
          have hdoubleValueLt : doubleValue < modulus := by
            exact Nat.mod_lt _ hmodulusPos
          have hdoubleValueFit : doubleValue < 2 ^ wordWidth :=
            hdoubleValueLt.trans hmodulus
          have htargetDouble : readField doubleIndex
              (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
              wordWidth < modulus := by
            rw [readField_writeField_self hdoubleValueFit]
            exact hdoubleValueLt
          have hsourceDouble : readField doubleIndex
              (multiplicandOffset wordWidth) wordWidth ≤ modulus := by
            simp only [doubleIndex]
            rw [readField_writeField_of_disjoint (Or.inr (by
              simp [multiplicandOffset,
                VQ.Curve.PackedClearTargetProduct.targetOffset]
              omega))]
            exact hsource
          have hclearDouble : AuxiliaryClear wordWidth doubleIndex :=
            hclear.writeTarget
          obtain ⟨normalizedAdd, hnormalizedAdd, haddEq⟩ :=
            VQ.Curve.PackedModularAddition.mem_runOps_smul_basis
              hdoubleState haddBranch
          cases normalizedAdd with
          | mk recAdd cregAdd stateAdd inputAdd =>
              have hnormalizedAddState := addOps_correct hl hwidth
                hmodulusPos hmodulus hcontrol hsourceDouble htargetDouble
                hclearDouble beforeAdd.outcomes beforeAdd.creg
                hnormalizedAdd
              have hcontrolDouble : bitValue doubleIndex controlBit =
                  bitValue original controlBit := by
                simp only [doubleIndex]
                rw [bitValue_write_out (Or.inl (by
                  simp [VQ.Curve.PackedClearTargetProduct.targetOffset]
                  omega))]
              have hsourceDoubleValue : readField doubleIndex
                  (multiplicandOffset wordWidth) wordWidth =
                readField original (multiplicandOffset wordWidth) wordWidth := by
                simp only [doubleIndex]
                rw [readField_writeField_of_disjoint (Or.inr (by
                  simp [multiplicandOffset,
                    VQ.Curve.PackedClearTargetProduct.targetOffset]
                  omega))]
              have htargetDoubleValue : readField doubleIndex
                  (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
                  wordWidth = doubleValue :=
                readField_writeField_self hdoubleValueFit
              have hfinalIndex : writeField doubleIndex
                    (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
                    wordWidth finalValue =
                  writeField original
                    (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
                    wordWidth finalValue := by
                simp [doubleIndex, writeField_writeField]
              have hnormalizedAddState' : stateAdd =
                  Algebra.Dy.invSqrt2 (deg level) ^ (3 * wordWidth - 1) •
                    basis (writeField original
                      (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
                      wordWidth finalValue) := by
                simpa [hcontrolDouble, hsourceDoubleValue,
                  htargetDoubleValue, hfinalIndex, finalValue] using
                  hnormalizedAddState
              have hbState : b.state =
                  ((Algebra.Dy.invSqrt2 (deg level) ^
                        amplitudeExponent wordWidth tailControls *
                      Algebra.Dy.invSqrt2 (deg level) ^
                        (3 * wordWidth - 1)) *
                    Algebra.Dy.invSqrt2 (deg level) ^
                      (3 * wordWidth - 1)) •
                    basis (writeField original
                      (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
                      wordWidth finalValue) := by
                rw [haddEq]
                simp only [smulBranch]
                rw [hnormalizedAddState', Vec.smul_smul]
              have hvalue : finalValue = productValue modulus wordWidth
                  original (controlBit :: nextBit :: rest) := by
                calc
                  finalValue =
                      (doubleValue + bitValue original controlBit *
                        readField original (multiplicandOffset wordWidth)
                          wordWidth) % modulus := by
                    simp [finalValue, Nat.add_comm]
                  _ = (2 * tailValue + bitValue original controlBit *
                        readField original (multiplicandOffset wordWidth)
                          wordWidth) % modulus := by
                    simp only [doubleValue]
                    rw [Nat.mod_add_mod]
                  _ = productValue modulus wordWidth original
                      (controlBit :: nextBit :: rest) := by
                    simp [productValue,
                      VQBridge.Curve.LuoMultiplication.horner, tailValue,
                      tailControls, VQBridge.Curve.LuoMultiplication.bitValue,
                      bitValue]
              rw [hbState, hvalue]
              congr 1
              rw [← Algebra.Dy.pow_add, ← Algebra.Dy.pow_add]
              rfl

theorem productOps_correct
    {level modulus wordWidth original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus) (hmodulus : modulus < 2 ^ wordWidth)
    (hmodulusOdd : modulus % 2 = 1)
    (hsource : readField original (multiplicandOffset wordWidth) wordWidth ≤
      modulus)
    (htarget : readField original
      (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
      wordWidth = 0)
    (hclear : AuxiliaryClear wordWidth original)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level
      (VQ.Curve.PackedClearTargetProduct.width wordWidth)
      (productOps modulus wordWidth)
      (Branch.mk rec creg (basis original) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^
        amplitudeExponent wordWidth (List.range wordWidth) •
      basis (writeField original
        (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
        wordWidth
        (productValue modulus wordWidth original (List.range wordWidth))) := by
  apply productOpsAux_correct hl hwidth hmodulusPos hmodulus hmodulusOdd
    hsource htarget hclear
  · intro controlBit hcontrol
    exact List.mem_range.mp hcontrol
  · exact hb

theorem productOps_modularProduct_correct
    {level modulus wordWidth original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hmodulusPos : 0 < modulus) (hmodulus : modulus < 2 ^ wordWidth)
    (hmodulusOdd : modulus % 2 = 1)
    (hsource : readField original (multiplicandOffset wordWidth) wordWidth ≤
      modulus)
    (htarget : readField original
      (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
      wordWidth = 0)
    (hclear : AuxiliaryClear wordWidth original)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level
      (VQ.Curve.PackedClearTargetProduct.width wordWidth)
      (productOps modulus wordWidth)
      (Branch.mk rec creg (basis original) input)) :
    b.state = Algebra.Dy.invSqrt2 (deg level) ^
        ((2 * wordWidth - 1) * (3 * wordWidth - 1)) •
      basis (writeField original
        (VQ.Curve.PackedClearTargetProduct.targetOffset wordWidth)
        wordWidth
        (readField original multiplierOffset wordWidth *
          readField original (multiplicandOffset wordWidth) wordWidth %
            modulus)) := by
  have hstate := productOps_correct hl hwidth hmodulusPos hmodulus
    hmodulusOdd hsource htarget hclear rec creg hb
  rw [amplitudeExponent_eq (controls := List.range wordWidth) (by
      intro hempty
      have hlength := congrArg List.length hempty
      simp at hlength
      omega), productValue_range] at hstate
  simpa using hstate

end VQMathlib.Curve.PackedClearTargetProduct
