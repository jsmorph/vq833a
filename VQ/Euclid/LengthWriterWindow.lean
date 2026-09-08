import VQ.Euclid.SwapLength

namespace VQ
namespace Euclid
namespace LengthWriterWindow

open Reversible

theorem upperResult_prefix
    {I source boundary fullWidth endpointWidth result count : Nat}
    (hprefix : count + 1 ≤ fullWidth)
    (hboundaryUpper : boundary ≤ count)
    (hresult : SwapLength.UpperResult I source boundary fullWidth
      endpointWidth result) :
    SwapLength.UpperResult I source boundary (count + 1)
      endpointWidth result := by
  rcases hresult with
      ⟨index, _hindex, hboundary, hbit, hhigher, hvalue⟩ |
      ⟨hzero, hvalue⟩
  · left
    refine ⟨index, by omega, hboundary, hbit, ?_, hvalue⟩
    intro j hj hjindex hjboundary
    exact hhigher j (by omega) hjindex hjboundary
  · right
    refine ⟨?_, hvalue⟩
    intro j hj hjboundary
    exact hzero j (by omega) hjboundary

def LowerResult
    (n I source start boundary workWidth endpointWidth result : Nat) : Prop :=
  (∃ index, index < workWidth ∧ boundary ≤ start + index ∧
    bitValue I (source + index) = 1 ∧
    (∀ j, j < workWidth → j < index → boundary ≤ start + j →
      bitValue I (source + j) = 0) ∧
    result = LengthWriter.lowerValue n endpointWidth (start + index)) ∨
  ((∀ j, j < workWidth → boundary ≤ start + j →
      bitValue I (source + j) = 0) ∧
    result = encodedZero endpointWidth)

theorem lowerResult_suffix
    {n I source boundary fullWidth endpointWidth result skip count : Nat}
    (hspan : skip + (count + 1) = fullWidth)
    (hstart : skip + 1 ≤ boundary)
    (hresult : SwapLength.LowerResult n I source boundary fullWidth
      endpointWidth result) :
    LowerResult n I (source + skip) (skip + 1) boundary (count + 1)
      endpointWidth result := by
  rcases hresult with
      ⟨index, hindex, hboundary, hbit, hlowest, hvalue⟩ |
      ⟨hzero, hvalue⟩
  · have hskip : skip ≤ index := by omega
    have hindexEq : skip + (index - skip) = index :=
      Nat.add_sub_of_le hskip
    left
    refine ⟨index - skip, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · simpa [Nat.add_assoc, hindexEq] using hbit
    · intro j hj hjindex hjboundary
      have hglobal := hlowest (skip + j) (by omega) (by omega) (by omega)
      simpa [Nat.add_assoc] using hglobal
    · rw [show skip + 1 + (index - skip) = index + 1 by omega]
      exact hvalue
  · right
    refine ⟨?_, hvalue⟩
    intro j hj hjboundary
    have hglobal := hzero (skip + j) (by omega) (by omega)
    simpa [Nat.add_assoc] using hglobal

theorem gathered_sourceBit
    {source dirty boundary target workWidth fullWidth endpointWidth I j : Nat}
    (hj : j < workWidth) :
    bitValue
        (gatherBits
          (place (LengthWriter.layout workWidth endpointWidth)
            (SwapLength.writerWiring source dirty boundary target
              fullWidth endpointWidth))
          (LengthWriter.layout workWidth endpointWidth).width I) j =
      bitValue I (source + j) := by
  unfold bitValue
  rw [testBit_gatherBits]
  have hjlocal : j < (LengthWriter.layout workWidth endpointWidth).width := by
    simp [LengthWriter.layout, Interval.layout, Layout.width]
    omega
  simp only [hjlocal, decide_true, Bool.true_and]
  rw [show place (LengthWriter.layout workWidth endpointWidth)
      (SwapLength.writerWiring source dirty boundary target
        fullWidth endpointWidth) j = source + j by
    have hplace := place_field
      (LengthWriter.layout workWidth endpointWidth)
      (SwapLength.writerWiring source dirty boundary target
        fullWidth endpointWidth)
      0 j (by simp [SwapLength.writerWiring]) (by
        simpa [LengthWriter.layout, Interval.layout, Layout.size] using hj)
    simpa [LengthWriter.layout, Interval.layout, Layout.offset,
      SwapLength.writerWiring] using hplace]

theorem gathered_stable
    {source dirty boundaryOffset target workWidth fullWidth endpointWidth I
      boundary : Nat}
    (hboundary : readField I boundaryOffset endpointWidth = boundary)
    (h : SwapLength.Enabled fullWidth endpointWidth I) :
    Interval.Stable boundary (readField I target endpointWidth)
      workWidth endpointWidth
      (gatherBits
        (place (LengthWriter.layout workWidth endpointWidth)
          (SwapLength.writerWiring source dirty boundaryOffset target
            fullWidth endpointWidth))
        (LengthWriter.layout workWidth endpointWidth).width I) := by
  let L := LengthWriter.layout workWidth endpointWidth
  let W := SwapLength.writerWiring source dirty boundaryOffset target
    fullWidth endpointWidth
  let gathered := gatherBits (place L W) L.width I
  have hread (j : Nat) (hj : j < 12) :
      readField gathered (L.offset j) (L.size j) =
        readField I (W.getD j 0) (L.size j) :=
    readField_gatherBits L W j I (by simp [W, SwapLength.writerWiring]; omega)
  constructor
  · rw [show Interval.leftOffset workWidth = L.offset 2 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.leftOffset, Layout.offset]
      omega]
    change readField gathered (L.offset 2) (L.size 2) = boundary
    have hp : readField I (W.getD 2 0) (L.size 2) = boundary := by
      change readField I boundaryOffset endpointWidth = boundary
      exact hboundary
    exact (hread 2 (by omega)).trans hp
  · rw [show Interval.rightOffset workWidth endpointWidth = L.offset 3 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.rightOffset, Layout.offset]
      omega]
    change readField gathered (L.offset 3) (L.size 3) =
      readField I target endpointWidth
    exact hread 3 (by omega)
  · have hc : bitValue gathered
        (Interval.outerWire workWidth endpointWidth) = 1 := by
      rw [← readField_one]
      rw [show Interval.outerWire workWidth endpointWidth = L.offset 4 by
        simp [L, LengthWriter.layout, Interval.layout,
          Interval.outerWire, Layout.offset]
        omega]
      change readField gathered (L.offset 4) (L.size 4) = 1
      have hp : readField I (W.getD 4 0) (L.size 4) = 1 := by
        change readField I (SwapLength.controlWire fullWidth endpointWidth) 1 = 1
        simpa [readField_one] using h.controlSet
      exact (hread 4 (by omega)).trans hp
    cases hcbit : gathered.testBit
      (Interval.outerWire workWidth endpointWidth) <;>
      simp_all [bitValue]
  · rw [← readField_one]
    rw [show Interval.leftFlagWire workWidth endpointWidth = L.offset 8 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.leftFlagWire, Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 8) (L.size 8) = 0
    have hp : readField I (W.getD 8 0) (L.size 8) = 0 := by
      change readField I
        (SwapLength.leftFlagWire fullWidth endpointWidth) 1 = 0
      simpa [readField_one] using h.leftFlagClear
    exact (hread 8 (by omega)).trans hp
  · rw [← readField_one]
    rw [show Interval.rightFlagWire workWidth endpointWidth = L.offset 9 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.rightFlagWire, Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 9) (L.size 9) = 0
    have hp : readField I (W.getD 9 0) (L.size 9) = 0 := by
      change readField I
        (SwapLength.rightFlagWire fullWidth endpointWidth) 1 = 0
      simpa [readField_one] using h.rightFlagClear
    exact (hread 9 (by omega)).trans hp
  · rw [show Interval.selectorScratchOffset workWidth endpointWidth =
        L.offset 10 by
      simp [L, LengthWriter.layout, Interval.layout,
        Interval.selectorScratchOffset, Interval.outerWire, Layout.offset]
      omega]
    change readField gathered (L.offset 10) (L.size 10) = 0
    have hp : readField I (W.getD 10 0) (L.size 10) = 0 := by
      change readField I
        (SwapLength.selectorScratchOffset fullWidth endpointWidth)
          endpointWidth = 0
      exact h.selectorScratchClear
    exact (hread 10 (by omega)).trans hp
  · have hc : bitValue gathered
        (Interval.cellScratchWire workWidth endpointWidth) = 0 := by
      rw [← readField_one]
      rw [show Interval.cellScratchWire workWidth endpointWidth =
          L.offset 11 by
        simp [L, LengthWriter.layout, Interval.layout,
          Interval.cellScratchWire, Interval.selectorScratchOffset,
          Interval.outerWire, Layout.offset]
        omega]
      change readField gathered (L.offset 11) (L.size 11) = 0
      have hp : readField I (W.getD 11 0) (L.size 11) = 0 := by
        change readField I
          (SwapLength.cellScratchWire fullWidth endpointWidth) 1 = 0
        simpa [readField_one] using h.cellScratchClear
      exact (hread 11 (by omega)).trans hp
    cases hcbit : gathered.testBit
      (Interval.cellScratchWire workWidth endpointWidth) <;>
      simp_all [bitValue]

theorem gathered_accumulator
    {source dirty boundary target workWidth fullWidth endpointWidth I : Nat}
    (h : SwapLength.Enabled fullWidth endpointWidth I) :
    bitValue
        (gatherBits
          (place (LengthWriter.layout workWidth endpointWidth)
            (SwapLength.writerWiring source dirty boundary target
              fullWidth endpointWidth))
          (LengthWriter.layout workWidth endpointWidth).width I)
        (RangeZero.accumulatorWire workWidth endpointWidth) = 0 := by
  let L := LengthWriter.layout workWidth endpointWidth
  let W := SwapLength.writerWiring source dirty boundary target
    fullWidth endpointWidth
  let gathered := gatherBits (place L W) L.width I
  rw [← readField_one]
  rw [show RangeZero.accumulatorWire workWidth endpointWidth = L.offset 7 by
    simp [L, LengthWriter.layout, Interval.layout,
      RangeZero.accumulatorWire, Interval.accumulatorWire,
      Interval.outerWire, Layout.offset]
    omega]
  change readField gathered (L.offset 7) (L.size 7) = 0
  have hp : readField I (W.getD 7 0) (L.size 7) = 0 := by
    change readField I
      (SwapLength.accumulatorWire fullWidth endpointWidth) 1 = 0
    simpa [readField_one] using h.accumulatorClear
  exact (readField_gatherBits L W 7 I
    (by simp [W, SwapLength.writerWiring])).trans hp

theorem upperWriter_act
    {source dirty boundaryOffset target count fullWidth endpointWidth I
      boundary result : Nat}
    (hd : Wiring.Disjoint (LengthWriter.layout (count + 1) endpointWidth)
      (SwapLength.writerWiring source dirty boundaryOffset target
        fullWidth endpointWidth))
    (hwidth : count + 1 < 2 ^ endpointWidth)
    (hboundaryLower : 1 ≤ boundary)
    (hboundaryUpper : boundary ≤ count)
    (hboundaryRead : readField I boundaryOffset endpointWidth = boundary)
    (henabled : SwapLength.Enabled fullWidth endpointWidth I)
    (hresult : SwapLength.UpperResult I source boundary (count + 1)
      endpointWidth result) :
    actGates
        (LengthWriterPlaced.gates
          (LengthWriter.upperGates 1 (count + 1) endpointWidth)
          (count + 1) endpointWidth
          (SwapLength.writerWiring source dirty boundaryOffset target
            fullWidth endpointWidth)) I =
      writeField I target endpointWidth
        (readField I target endpointWidth ^^^ result) := by
  have hstable := gathered_stable
    (source := source) (dirty := dirty) (boundaryOffset := boundaryOffset)
    (target := target) (workWidth := count + 1)
    hboundaryRead henabled
  have hacc := gathered_accumulator
    (source := source) (dirty := dirty) (boundary := boundaryOffset)
    (target := target) (workWidth := count + 1) henabled
  rcases hresult with
      ⟨index, hindex, hindexBoundary, hbit, hhigher, rfl⟩ |
      ⟨hzero, rfl⟩
  · have hbitLocal := (gathered_sourceBit
      (source := source) (dirty := dirty) (boundary := boundaryOffset)
      (target := target) (fullWidth := fullWidth)
      (endpointWidth := endpointWidth) (I := I) hindex).trans hbit
    have hhigherLocal : ∀ j, j < count + 1 → index < j →
        1 + j ≤ boundary →
        bitValue
          (gatherBits
            (place (LengthWriter.layout (count + 1) endpointWidth)
              (SwapLength.writerWiring source dirty boundaryOffset target
                fullWidth endpointWidth))
            (LengthWriter.layout (count + 1) endpointWidth).width I) j = 0 := by
      intro j hj hindexj hjboundary
      rw [gathered_sourceBit
        (source := source) (dirty := dirty) (boundary := boundaryOffset)
        (target := target) (fullWidth := fullWidth) hj]
      exact hhigher j hj hindexj (by omega)
    have hact := LengthWriterPlaced.upper_highest
      (W := SwapLength.writerWiring source dirty boundaryOffset target
        fullWidth endpointWidth)
      (boundary := boundary) (right := readField I target endpointWidth)
      (start := 1) (count := count) (index := index)
      hd (by simp [LengthWriter.layout, Interval.layout,
        SwapLength.writerWiring])
      (by omega) hboundaryLower (by omega) hstable hacc hindex
      (by omega) hbitLocal hhigherLocal
    simpa [SwapLength.writerWiring, Nat.add_comm] using hact
  · have hzeroLocal : ∀ j, j < count + 1 → 1 + j ≤ boundary →
        bitValue
          (gatherBits
            (place (LengthWriter.layout (count + 1) endpointWidth)
              (SwapLength.writerWiring source dirty boundaryOffset target
                fullWidth endpointWidth))
            (LengthWriter.layout (count + 1) endpointWidth).width I) j = 0 := by
      intro j hj hjboundary
      rw [gathered_sourceBit
        (source := source) (dirty := dirty) (boundary := boundaryOffset)
        (target := target) (fullWidth := fullWidth) hj]
      exact hzero j hj (by omega)
    have hact := LengthWriterPlaced.upper_none
      (W := SwapLength.writerWiring source dirty boundaryOffset target
        fullWidth endpointWidth)
      (boundary := boundary) (right := readField I target endpointWidth)
      (start := 1) (count := count)
      hd (by simp [LengthWriter.layout, Interval.layout,
        SwapLength.writerWiring])
      (by omega) hboundaryLower (by omega) hstable hacc hzeroLocal
    simpa [SwapLength.writerWiring] using hact

theorem upperWriter_act_prefix
    {source dirty boundaryOffset target count fullWidth endpointWidth I
      boundary result : Nat}
    (hd : Wiring.Disjoint (LengthWriter.layout (count + 1) endpointWidth)
      (SwapLength.writerWiring source dirty boundaryOffset target
        fullWidth endpointWidth))
    (hprefix : count + 1 ≤ fullWidth)
    (hwidth : count + 1 < 2 ^ endpointWidth)
    (hboundaryLower : 1 ≤ boundary)
    (hboundaryUpper : boundary ≤ count)
    (hboundaryRead : readField I boundaryOffset endpointWidth = boundary)
    (henabled : SwapLength.Enabled fullWidth endpointWidth I)
    (hresult : SwapLength.UpperResult I source boundary fullWidth
      endpointWidth result) :
    actGates
        (LengthWriterPlaced.gates
          (LengthWriter.upperGates 1 (count + 1) endpointWidth)
          (count + 1) endpointWidth
          (SwapLength.writerWiring source dirty boundaryOffset target
            fullWidth endpointWidth)) I =
      writeField I target endpointWidth
        (readField I target endpointWidth ^^^ result) := by
  apply upperWriter_act hd hwidth hboundaryLower hboundaryUpper
    hboundaryRead henabled
  exact upperResult_prefix hprefix hboundaryUpper hresult

theorem lowerWriter_act
    {n source dirty boundaryOffset target start count fullWidth endpointWidth I
      boundary result : Nat}
    (hd : Wiring.Disjoint (LengthWriter.layout (count + 1) endpointWidth)
      (SwapLength.writerWiring source dirty boundaryOffset target
        fullWidth endpointWidth))
    (hwidth : start + count < 2 ^ endpointWidth)
    (hboundaryLower : start ≤ boundary)
    (hboundaryUpper : boundary ≤ start + count)
    (hboundaryRead : readField I boundaryOffset endpointWidth = boundary)
    (henabled : SwapLength.Enabled fullWidth endpointWidth I)
    (hresult : LowerResult n I source start boundary (count + 1)
      endpointWidth result) :
    actGates
        (LengthWriterPlaced.gates
          (LengthWriter.lowerGates n start (count + 1) endpointWidth)
          (count + 1) endpointWidth
          (SwapLength.writerWiring source dirty boundaryOffset target
            fullWidth endpointWidth)) I =
      writeField I target endpointWidth
        (readField I target endpointWidth ^^^ result) := by
  have hstable := gathered_stable
    (source := source) (dirty := dirty) (boundaryOffset := boundaryOffset)
    (target := target) (workWidth := count + 1)
    hboundaryRead henabled
  have hacc := gathered_accumulator
    (source := source) (dirty := dirty) (boundary := boundaryOffset)
    (target := target) (workWidth := count + 1) henabled
  rcases hresult with
      ⟨index, hindex, hindexBoundary, hbit, hlowest, rfl⟩ |
      ⟨hzero, rfl⟩
  · have hbitLocal := (gathered_sourceBit
      (source := source) (dirty := dirty) (boundary := boundaryOffset)
      (target := target) (fullWidth := fullWidth)
      (endpointWidth := endpointWidth) (I := I) hindex).trans hbit
    have hlowestLocal : ∀ j, j < count + 1 → j < index →
        boundary ≤ start + j →
        bitValue
          (gatherBits
            (place (LengthWriter.layout (count + 1) endpointWidth)
              (SwapLength.writerWiring source dirty boundaryOffset target
                fullWidth endpointWidth))
            (LengthWriter.layout (count + 1) endpointWidth).width I) j = 0 := by
      intro j hj hindexj hjboundary
      rw [gathered_sourceBit
        (source := source) (dirty := dirty) (boundary := boundaryOffset)
        (target := target) (fullWidth := fullWidth) hj]
      exact hlowest j hj hindexj hjboundary
    have hact := LengthWriterPlaced.lower_lowest
      (n := n)
      (W := SwapLength.writerWiring source dirty boundaryOffset target
        fullWidth endpointWidth)
      (boundary := boundary) (right := readField I target endpointWidth)
      (start := start) (count := count) (index := index)
      hd (by simp [LengthWriter.layout, Interval.layout,
        SwapLength.writerWiring])
      hwidth hboundaryLower hboundaryUpper hstable hacc hindex
      hindexBoundary hbitLocal hlowestLocal
    simpa [SwapLength.writerWiring] using hact
  · have hzeroLocal : ∀ j, j < count + 1 → boundary ≤ start + j →
        bitValue
          (gatherBits
            (place (LengthWriter.layout (count + 1) endpointWidth)
              (SwapLength.writerWiring source dirty boundaryOffset target
                fullWidth endpointWidth))
            (LengthWriter.layout (count + 1) endpointWidth).width I) j = 0 := by
      intro j hj hjboundary
      rw [gathered_sourceBit
        (source := source) (dirty := dirty) (boundary := boundaryOffset)
        (target := target) (fullWidth := fullWidth) hj]
      exact hzero j hj hjboundary
    have hact := LengthWriterPlaced.lower_none
      (n := n)
      (W := SwapLength.writerWiring source dirty boundaryOffset target
        fullWidth endpointWidth)
      (boundary := boundary) (right := readField I target endpointWidth)
      (start := start) (count := count)
      hd (by simp [LengthWriter.layout, Interval.layout,
        SwapLength.writerWiring])
      hwidth hboundaryLower hboundaryUpper hstable hacc hzeroLocal
    simpa [SwapLength.writerWiring] using hact

theorem lowerWriter_act_suffix
    {n source dirty boundaryOffset target fullWidth endpointWidth I boundary
      result skip count : Nat}
    (hd : Wiring.Disjoint (LengthWriter.layout (count + 1) endpointWidth)
      (SwapLength.writerWiring (source + skip) (dirty + skip)
        boundaryOffset target fullWidth endpointWidth))
    (hspan : skip + (count + 1) = fullWidth)
    (hwidth : fullWidth < 2 ^ endpointWidth)
    (hstart : skip + 1 ≤ boundary)
    (hboundaryUpper : boundary ≤ fullWidth)
    (hboundaryRead : readField I boundaryOffset endpointWidth = boundary)
    (henabled : SwapLength.Enabled fullWidth endpointWidth I)
    (hresult : SwapLength.LowerResult n I source boundary fullWidth
      endpointWidth result) :
    actGates
        (LengthWriterPlaced.gates
          (LengthWriter.lowerGates n (skip + 1) (count + 1) endpointWidth)
          (count + 1) endpointWidth
          (SwapLength.writerWiring (source + skip) (dirty + skip)
            boundaryOffset target fullWidth endpointWidth)) I =
      writeField I target endpointWidth
        (readField I target endpointWidth ^^^ result) := by
  apply lowerWriter_act hd
  · omega
  · exact hstart
  · omega
  · exact hboundaryRead
  · exact henabled
  · exact lowerResult_suffix hspan hstart hresult

end LengthWriterWindow
end Euclid
end VQ
