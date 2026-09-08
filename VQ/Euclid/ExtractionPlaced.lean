/-
Placement of coherent terminal extraction on the Euclidean step layout.
-/
import VQ.Euclid.Extraction
import VQ.Euclid.StepState.Common
import Mathlib.Tactic.IntervalCases

namespace VQ.Euclid.ExtractionPlaced

open Reversible

def baseWidth (n lengthWidth shiftWidth : Nat) : Nat :=
  (StepLayout.layout n lengthWidth shiftWidth).width

def layout (n lengthWidth shiftWidth : Nat) : Layout :=
  StepLayout.layout n lengthWidth shiftWidth ++ [n]

def outputOffset (n lengthWidth shiftWidth : Nat) : Nat :=
  baseWidth n lengthWidth shiftWidth

def wiring (n lengthWidth shiftWidth : Nat) : Wiring :=
  [StepLayout.work2Offset n,
    StepLayout.shiftOffset n lengthWidth,
    StepLayout.controlWire n lengthWidth shiftWidth,
    StepLayout.poolOffset n lengthWidth shiftWidth,
    outputOffset n lengthWidth shiftWidth]

def gates (n lengthWidth shiftWidth : Nat) : List RGate :=
  StepLayout.placed
    (Extraction.layout (workWidth n) shiftWidth n)
    (wiring n lengthWidth shiftWidth)
    (Extraction.gates (workWidth n) shiftWidth n)

def circuit (n lengthWidth shiftWidth : Nat) : RCircuit :=
  { width := (layout n lengthWidth shiftWidth).width,
    gates := gates n lengthWidth shiftWidth }

theorem layout_width (n lengthWidth shiftWidth : Nat) :
    (layout n lengthWidth shiftWidth).width =
      baseWidth n lengthWidth shiftWidth + n := by
  have append_width : ∀ L : Layout, (L ++ [n]).width = L.width + n := by
    intro L
    induction L with
    | nil => simp [Layout.width]
    | cons width rest ih =>
        simp only [List.cons_append, Layout.width, ih]
        omega
  exact append_width (StepLayout.layout n lengthWidth shiftWidth)

theorem wiring_disjoint (n lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (Extraction.layout (workWidth n) shiftWidth n)
      (wiring n lengthWidth shiftWidth) := by
  have hshift : shiftWidth ≤ StepLayout.selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_right _ _
  intro j k hj hk hne
  simp [wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [Extraction.layout, Layout.size, wiring, workWidth,
      StepLayout.work2Offset, StepLayout.shiftOffset,
      StepLayout.controlWire, StepLayout.phase1Wire,
      StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
      StepLayout.selectorWidth, outputOffset,
      baseWidth, StepLayout.layout_width, StepLayout.auxWidth] <;>
    omega

theorem wiring_bound (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (Extraction.layout (workWidth n) shiftWidth n).length →
      (wiring n lengthWidth shiftWidth).getD j 0 +
          (Extraction.layout (workWidth n) shiftWidth n).size j ≤
        (layout n lengthWidth shiftWidth).width := by
  have hshift : shiftWidth ≤ StepLayout.selectorWidth lengthWidth shiftWidth :=
    Nat.le_max_right _ _
  intro j hj
  simp [Extraction.layout] at hj
  interval_cases j <;>
    simp_all [Extraction.layout, Layout.size, wiring, layout_width,
      workWidth, StepLayout.work2Offset, StepLayout.shiftOffset,
      StepLayout.controlWire, StepLayout.phase1Wire,
      StepLayout.poolOffset, StepLayout.carryWire, StepLayout.auxOffset,
      StepLayout.selectorWidth, outputOffset,
      baseWidth, StepLayout.layout_width, StepLayout.auxWidth] <;>
    omega

theorem encodeWork2Raw_lt_of_packed
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hpacked : Packed n lengthWidth shiftWidth s) :
    encodeWork2Raw n s < 2 ^ workWidth n := by
  rcases hpacked with
    ⟨_hlenT, _hlenRPrime, _hlenTFit, _hlenQFit, _hlenRPrimeFit,
      _hshiftFit, _hwork1Allocation, hwork2Allocation, _htFit,
      _hqAligned, _hlenQ, _hrFit, htPrimeFit, _hrPrimeFit⟩
  rw [encodeWork2Raw_eq_split n s hwork2Allocation]
  exact encodeSplit_lt (Nat.sub_le _ _) htPrimeFit

theorem read_output_encoded
    (n lengthWidth shiftWidth : Nat) (s : State) :
    readField (StepState.encoded n lengthWidth shiftWidth s)
        (outputOffset n lengthWidth shiftWidth) n = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_readField]
  by_cases hb : b < n
  · simp only [hb, decide_true, Bool.true_and, Nat.zero_testBit]
    have hbase := StepState.encoded_lt n lengthWidth shiftWidth s
    have hpower :
        2 ^ baseWidth n lengthWidth shiftWidth ≤
          2 ^ (baseWidth n lengthWidth shiftWidth + b) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hbit := Nat.testBit_lt_two_pow (hbase.trans_le hpower)
    simpa [outputOffset] using hbit
  · simp [hb]

theorem gates_act_encoded
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hpacked : Packed n lengthWidth shiftWidth s) :
    actGates (gates n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      writeField (StepState.encoded n lengthWidth shiftWidth s)
        (outputOffset n lengthWidth shiftWidth) n
        (readField (encodeWork2Raw n s) 0 n) := by
  let L := Extraction.layout (workWidth n) shiftWidth n
  let W := wiring n lengthWidth shiftWidth
  let input := StepState.encoded n lengthWidth shiftWidth s
  let gathered := gatherBits (place L W) L.width input
  have hcontrol :
      bitValue gathered (Extraction.controlWire (workWidth n) shiftWidth) = 0 := by
    rw [← readField_one]
    change L.read gathered 2 = 0
    rw [read_gatherBits L W 2 input (by simp [W, wiring])]
    simpa [input, L, W, Extraction.layout, Layout.size, wiring,
      readField_one] using StepState.read_control n lengthWidth shiftWidth s
  have hscratch :
      readField gathered (Extraction.scratchOffset (workWidth n) shiftWidth)
          shiftWidth = 0 := by
    change L.read gathered 3 = 0
    rw [read_gatherBits L W 3 input (by simp [W, wiring])]
    have hclean : readField input
        (StepLayout.poolOffset n lengthWidth shiftWidth) shiftWidth = 0 := by
      apply StepState.read_aux_subfield
      · simp [StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxOffset]
        omega
      · have hshift :
            shiftWidth ≤ StepLayout.selectorWidth lengthWidth shiftWidth :=
          Nat.le_max_right _ _
        simp [StepLayout.poolOffset, StepLayout.carryWire,
          StepLayout.auxOffset, StepLayout.auxWidth]
        omega
    simpa [input, L, W, Extraction.layout, Layout.size, wiring] using hclean
  have hout :
      readField gathered (Extraction.outputOffset (workWidth n) shiftWidth)
          n = 0 := by
    have hread := readField_gatherBits L W 4 input (by simp [W, wiring])
    have hclean := read_output_encoded n lengthWidth shiftWidth s
    simpa [gathered, input, L, W, Extraction.layout,
      Extraction.outputOffset, Extraction.scratchOffset,
      Extraction.controlWire, Layout.offset, Layout.size, wiring,
      Nat.add_assoc] using hread.trans hclean
  have hshift :
      readField gathered (Extraction.shiftOffset (workWidth n)) shiftWidth =
        encodeLength shiftWidth s.shift := by
    change L.read gathered 1 = encodeLength shiftWidth s.shift
    rw [read_gatherBits L W 1 input (by simp [W, wiring])]
    simpa [input, L, W, Extraction.layout, Layout.size, wiring] using
      StepState.read_shift n lengthWidth shiftWidth s
  have hwork :
      readField gathered Extraction.workOffset (workWidth n) =
        rotatePositionsLeft (workWidth n) s.shift (encodeWork2Raw n s) := by
    change L.read gathered 0 =
      rotatePositionsLeft (workWidth n) s.shift (encodeWork2Raw n s)
    rw [read_gatherBits L W 0 input (by simp [W, wiring])]
    simpa [input, L, W, Extraction.layout, Layout.size, wiring,
      encodeWork2] using StepState.read_work2 n lengthWidth shiftWidth s
  have hshiftFit : s.shift < 2 ^ shiftWidth :=
    hpacked.2.2.2.2.2.1
  have hraw := encodeWork2Raw_lt_of_packed hpacked
  have hlocal := Extraction.gates_act_of_clear
    (workWidth := workWidth n) (shiftWidth := shiftWidth) (outputWidth := n)
    (by simp [workWidth]) (by simp [workWidth]) hcontrol hscratch hout
    hshift hshiftFit hwork hraw
  have hlocalWrite :
      actGates (Extraction.gates (workWidth n) shiftWidth n) gathered =
        L.write gathered 4 (readField (encodeWork2Raw n s) 0 n) := by
    simpa [L, Extraction.layout, Layout.write, Layout.offset, Layout.size,
      Extraction.outputOffset, Extraction.scratchOffset,
      Extraction.controlWire, Nat.add_assoc] using hlocal
  have hplaced := actGates_placed_write
    (L := L) (W := W) (k := 4)
    (wiring_disjoint n lengthWidth shiftWidth)
    (by simp [L, W, Extraction.layout, wiring])
    (by simp [L, Extraction.layout])
    (fun g hg => RCircuit.wellFormed_mem
      (Extraction.circuit_wellFormed
        (workWidth := workWidth n) (shiftWidth := shiftWidth)
        (outputWidth := n)
        (by simp [workWidth]) (by simp [workWidth])) hg)
    hlocalWrite
  simpa [gates, StepLayout.placed, L, W, input, wiring,
    Extraction.layout, Extraction.circuit, Layout.size, outputOffset] using
    hplaced

theorem encodeWork2Raw_terminal
    {n : Nat} {s : State} (hterminal : Terminal s) :
    encodeWork2Raw n s = s.tPrime := by
  simp [encodeWork2Raw, hterminal.2.1, reverseBits]

theorem gates_act_encoded_terminal
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hterminal : Terminal s) :
    actGates (gates n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      writeField (StepState.encoded n lengthWidth shiftWidth s)
        (outputOffset n lengthWidth shiftWidth) n
        (readField s.tPrime 0 n) := by
  rw [gates_act_encoded hpacked, encodeWork2Raw_terminal hterminal]

theorem gates_act_encoded_terminal_of_fit
    {n lengthWidth shiftWidth : Nat} {s : State}
    (hpacked : Packed n lengthWidth shiftWidth s)
    (hterminal : Terminal s) (htPrime : s.tPrime < 2 ^ n) :
    actGates (gates n lengthWidth shiftWidth)
        (StepState.encoded n lengthWidth shiftWidth s) =
      writeField (StepState.encoded n lengthWidth shiftWidth s)
        (outputOffset n lengthWidth shiftWidth) n s.tPrime := by
  rw [gates_act_encoded_terminal hpacked hterminal, readField_zero,
    Nat.mod_eq_of_lt htPrime]

theorem gates_wellFormed
    (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply wellFormed_placeGates
    (wiring_disjoint n lengthWidth shiftWidth)
    (by simp [Extraction.layout, wiring])
    (wiring_bound n lengthWidth shiftWidth)
  intro g hg
  exact RCircuit.wellFormed_mem
    (Extraction.circuit_wellFormed
      (workWidth := workWidth n) (shiftWidth := shiftWidth)
      (outputWidth := n)
      (by simp [workWidth]) (by simp [workWidth])) hg

theorem circuit_wellFormed (n lengthWidth shiftWidth : Nat) :
    (circuit n lengthWidth shiftWidth).wellFormed = true :=
  gates_wellFormed n lengthWidth shiftWidth

theorem gates_length (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).length =
      (Extraction.gates (workWidth n) shiftWidth n).length := by
  exact StepLayout.placed_length _ _ _

theorem gates_ccx (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).countP RGate.isCcx =
      (Extraction.gates (workWidth n) shiftWidth n).countP RGate.isCcx := by
  exact StepLayout.placed_ccx _ _ _

theorem gates_cx (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).countP RGate.isCx =
      (Extraction.gates (workWidth n) shiftWidth n).countP RGate.isCx := by
  exact StepLayout.placed_cx _ _ _

theorem gates_length_le (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).length ≤
      2 * (Increment.lengthCost shiftWidth + 2 +
        3 * workWidth n * shiftWidth) + n := by
  rw [gates_length]
  exact Extraction.gates_length_le _ _ _ (by simp [workWidth])

theorem gates_ccx_le (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).countP RGate.isCcx ≤
      2 * (Increment.ccxCost shiftWidth + workWidth n * shiftWidth) := by
  rw [gates_ccx]
  exact Extraction.gates_ccx_le _ _ _ (by simp [workWidth])

theorem gates_cx_le (n lengthWidth shiftWidth : Nat) :
    (gates n lengthWidth shiftWidth).countP RGate.isCx ≤
      2 * (Increment.cxCost shiftWidth + 2 * workWidth n * shiftWidth) + n := by
  rw [gates_cx]
  exact Extraction.gates_cx_le _ _ _ (by simp [workWidth])

end VQ.Euclid.ExtractionPlaced
