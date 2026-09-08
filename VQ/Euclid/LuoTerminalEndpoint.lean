/-
Terminal endpoint composition from the Luo version 2 companion circuit.
-/
import VQ.Euclid.LuoTerminalExtraction
import VQ.Euclid.Placed
import VQ.Euclid.TerminalCompression

namespace VQ.Euclid.LuoTerminalEndpoint

open Reversible

def outputOffset (workWidth shiftWidth : Nat) : Nat :=
  LuoTerminalExtraction.outputOffset workWidth shiftWidth

def terminalLengthOffset
    (workWidth shiftWidth outputWidth : Nat) : Nat :=
  LuoTerminalExtraction.width workWidth shiftWidth outputWidth

def width
    (workWidth shiftWidth outputWidth lengthWidth : Nat) : Nat :=
  terminalLengthOffset workWidth shiftWidth outputWidth + lengthWidth

def flagGates
    (workWidth shiftWidth outputWidth lengthWidth : Nat) : List RGate :=
  Placed.selectorGates (2 ^ lengthWidth - 1) lengthWidth
    (terminalLengthOffset workWidth shiftWidth outputWidth)
    (LuoTerminalCanonicalization.outerWire workWidth shiftWidth)
    (TerminalCanonicalization.scratchOffset workWidth shiftWidth)

def compressionLayout : Layout := [1, 1, 1, 1, 1]

def compressionWiring (workWidth shiftWidth : Nat) : Wiring :=
  [TerminalCanonicalization.counterOffset workWidth,
    TerminalCanonicalization.counterOffset workWidth + 1,
    TerminalCanonicalization.epochWire workWidth shiftWidth,
    LuoTerminalCanonicalization.outerWire workWidth shiftWidth,
    TerminalCanonicalization.scratchOffset workWidth shiftWidth]

def compressionGates (workWidth shiftWidth : Nat) : List RGate :=
  TerminalCompression.gates.map
    (RGate.map (place compressionLayout
      (compressionWiring workWidth shiftWidth)))

def preparationGates
    (workWidth shiftWidth outputWidth lengthWidth : Nat) : List RGate :=
  flagGates workWidth shiftWidth outputWidth lengthWidth ++
    LuoTerminalCanonicalization.gates workWidth shiftWidth ++
    compressionGates workWidth shiftWidth ++
    flagGates workWidth shiftWidth outputWidth lengthWidth

def copyGates (workWidth shiftWidth outputWidth : Nat) : List RGate :=
  copyField TerminalCanonicalization.workOffset
    (outputOffset workWidth shiftWidth) outputWidth

def gates
    (workWidth shiftWidth outputWidth lengthWidth : Nat) : List RGate :=
  preparationGates workWidth shiftWidth outputWidth lengthWidth ++
    copyGates workWidth shiftWidth outputWidth ++
    (preparationGates workWidth shiftWidth outputWidth lengthWidth).reverse

def circuit
    (workWidth shiftWidth outputWidth lengthWidth : Nat) : RCircuit :=
  { width := width workWidth shiftWidth outputWidth lengthWidth,
    gates := gates workWidth shiftWidth outputWidth lengthWidth }

theorem flagWiring_disjoint
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth) :
    Wiring.Disjoint (Selector.layout lengthWidth)
      (Placed.selectorWiring
        (terminalLengthOffset workWidth shiftWidth outputWidth)
        (LuoTerminalCanonicalization.outerWire workWidth shiftWidth)
        (TerminalCanonicalization.scratchOffset workWidth shiftWidth)) := by
  simp [TerminalCanonicalization.counterWidth] at hlength
  intro j k hj hk hne
  simp [Placed.selectorWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp [Placed.selectorWiring, Selector.layout, Layout.size,
      terminalLengthOffset, LuoTerminalExtraction.width,
      LuoTerminalExtraction.outputOffset,
      LuoTerminalCanonicalization.width,
      LuoTerminalCanonicalization.outerWire,
      LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.scratchOffset,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth] <;> omega

theorem flagGates_wellFormed
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth) :
    (flagGates workWidth shiftWidth outputWidth lengthWidth).all
      (RGate.wellFormed
        (width workWidth shiftWidth outputWidth lengthWidth)) = true := by
  apply Placed.selector_wellFormed (flagWiring_disjoint hlength)
  intro j hj
  simp [Selector.layout] at hj
  interval_cases j <;>
    simp [Placed.selectorWiring, Selector.layout, Layout.size, width,
      terminalLengthOffset, LuoTerminalExtraction.width,
      LuoTerminalExtraction.outputOffset,
      LuoTerminalCanonicalization.width,
      LuoTerminalCanonicalization.outerWire,
      LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.scratchOffset,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth] <;> omega

theorem compressionWiring_disjoint
    {workWidth shiftWidth : Nat} (hshift : 2 ≤ shiftWidth) :
    Wiring.Disjoint compressionLayout
      (compressionWiring workWidth shiftWidth) := by
  intro j k hj hk hne
  simp [compressionWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp [compressionLayout, compressionWiring, Layout.size,
      LuoTerminalCanonicalization.outerWire,
      LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.counterOffset,
      TerminalCanonicalization.epochWire,
      TerminalCanonicalization.scratchOffset,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth] <;> omega

theorem compressionGates_wellFormed
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (hshift : 2 ≤ shiftWidth) :
    (compressionGates workWidth shiftWidth).all
      (RGate.wellFormed
        (width workWidth shiftWidth outputWidth lengthWidth)) = true := by
  apply wellFormed_placeGates (compressionWiring_disjoint hshift)
  · simp [compressionLayout, compressionWiring]
  · intro j hj
    simp [compressionLayout] at hj
    interval_cases j <;>
      simp [compressionLayout, compressionWiring, Layout.size, width,
        terminalLengthOffset, LuoTerminalExtraction.width,
        LuoTerminalExtraction.outputOffset,
        LuoTerminalCanonicalization.width,
        LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.counterOffset,
        TerminalCanonicalization.epochWire,
        TerminalCanonicalization.scratchOffset,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth] <;> omega
  · intro g hg
    exact List.all_eq_true.mp
      (show TerminalCompression.gates.all
          (RGate.wellFormed compressionLayout.width) = true by
        simpa [compressionLayout, TerminalCompression.layout, Layout.width] using
          TerminalCompression.gates_wellFormed) g hg

theorem canonicalization_wellFormed
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (hworkWidth : 0 < workWidth) :
    (LuoTerminalCanonicalization.gates workWidth shiftWidth).all
      (RGate.wellFormed
        (width workWidth shiftWidth outputWidth lengthWidth)) = true := by
  apply List.all_eq_true.mpr
  intro g hg
  apply RGate.wellFormed_mono
    (w := LuoTerminalCanonicalization.width workWidth shiftWidth)
  · simp [width, terminalLengthOffset, LuoTerminalExtraction.width,
      LuoTerminalExtraction.outputOffset]
    omega
  · exact List.all_eq_true.mp
      (LuoTerminalCanonicalization.gates_wellFormed hworkWidth) g hg

theorem preparationGates_wellFormed
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (hworkWidth : 0 < workWidth) (hshift : 2 ≤ shiftWidth)
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth) :
    (preparationGates workWidth shiftWidth outputWidth lengthWidth).all
      (RGate.wellFormed
        (width workWidth shiftWidth outputWidth lengthWidth)) = true := by
  simp [preparationGates, flagGates_wellFormed hlength,
    canonicalization_wellFormed hworkWidth,
    compressionGates_wellFormed
      (outputWidth := outputWidth) (lengthWidth := lengthWidth) hshift]

theorem copyGates_wellFormed
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (houtput : outputWidth ≤ workWidth) :
    (copyGates workWidth shiftWidth outputWidth).all
      (RGate.wellFormed
        (width workWidth shiftWidth outputWidth lengthWidth)) = true := by
  apply copyFieldBlock_wf
  · left
    simp [TerminalCanonicalization.workOffset, outputOffset,
      LuoTerminalExtraction.outputOffset,
      LuoTerminalCanonicalization.width,
      LuoTerminalCanonicalization.outerWire,
      LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.carryWire]
    omega
  · simp [width, terminalLengthOffset, LuoTerminalExtraction.width,
      LuoTerminalExtraction.outputOffset,
      TerminalCanonicalization.workOffset]
    omega
  · simp [width, terminalLengthOffset, LuoTerminalExtraction.width,
      outputOffset, LuoTerminalExtraction.outputOffset]

theorem gates_wellFormed
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (hworkWidth : 0 < workWidth) (hshift : 2 ≤ shiftWidth)
    (houtput : outputWidth ≤ workWidth)
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth) :
    (gates workWidth shiftWidth outputWidth lengthWidth).all
      (RGate.wellFormed
        (width workWidth shiftWidth outputWidth lengthWidth)) = true := by
  simp [gates, preparationGates_wellFormed hworkWidth hshift hlength,
    copyGates_wellFormed (lengthWidth := lengthWidth) houtput,
    List.all_reverse]

theorem circuit_wellFormed
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (hworkWidth : 0 < workWidth) (hshift : 2 ≤ shiftWidth)
    (houtput : outputWidth ≤ workWidth)
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth) :
    (circuit workWidth shiftWidth outputWidth lengthWidth).wellFormed = true :=
  gates_wellFormed hworkWidth hshift houtput hlength

theorem flagGates_avoids_work
    {workWidth shiftWidth outputWidth lengthWidth : Nat} :
    ∀ g ∈ flagGates workWidth shiftWidth outputWidth lengthWidth,
      ∀ q ∈ g.wires,
        q < TerminalCanonicalization.workOffset ∨
          TerminalCanonicalization.workOffset + workWidth ≤ q := by
  apply placeGates_avoids
    (L := Selector.layout lengthWidth)
    (W := Placed.selectorWiring
      (terminalLengthOffset workWidth shiftWidth outputWidth)
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth)
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth))
  · simp [Selector.layout, Placed.selectorWiring]
  · intro g hg
    exact RCircuit.wellFormed_mem
      (Selector.circuit_wellFormed (2 ^ lengthWidth - 1) lengthWidth) hg
  · intro j hj
    simp [Selector.layout] at hj
    interval_cases j <;>
      simp [Placed.selectorWiring, Selector.layout, Layout.size,
        TerminalCanonicalization.workOffset,
        terminalLengthOffset, LuoTerminalExtraction.width,
        LuoTerminalExtraction.outputOffset,
        LuoTerminalCanonicalization.width,
        LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.scratchOffset,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth] <;> omega

theorem flagGates_avoids_output
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth) :
    ∀ g ∈ flagGates workWidth shiftWidth outputWidth lengthWidth,
      ∀ q ∈ g.wires,
        q < outputOffset workWidth shiftWidth ∨
          outputOffset workWidth shiftWidth + outputWidth ≤ q := by
  apply placeGates_avoids
    (L := Selector.layout lengthWidth)
    (W := Placed.selectorWiring
      (terminalLengthOffset workWidth shiftWidth outputWidth)
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth)
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth))
  · simp [Selector.layout, Placed.selectorWiring]
  · intro g hg
    exact RCircuit.wellFormed_mem
      (Selector.circuit_wellFormed (2 ^ lengthWidth - 1) lengthWidth) hg
  · intro j hj
    simp [TerminalCanonicalization.counterWidth] at hlength
    simp [Selector.layout] at hj
    interval_cases j <;>
      simp [Placed.selectorWiring, Selector.layout, Layout.size,
        outputOffset, terminalLengthOffset,
        LuoTerminalExtraction.width,
        LuoTerminalExtraction.outputOffset,
        LuoTerminalCanonicalization.width,
        LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.scratchOffset,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth] <;> omega

theorem compressionGates_avoids_work
    {workWidth shiftWidth : Nat} :
    ∀ g ∈ compressionGates workWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < TerminalCanonicalization.workOffset ∨
          TerminalCanonicalization.workOffset + workWidth ≤ q := by
  apply placeGates_avoids
    (L := compressionLayout) (W := compressionWiring workWidth shiftWidth)
  · simp [compressionLayout, compressionWiring]
  · intro g hg
    exact List.all_eq_true.mp
      (show TerminalCompression.gates.all
          (RGate.wellFormed compressionLayout.width) = true by
        simpa [compressionLayout, TerminalCompression.layout, Layout.width] using
          TerminalCompression.gates_wellFormed) g hg
  · intro j hj
    simp [compressionLayout] at hj
    interval_cases j <;>
      simp [compressionLayout, compressionWiring, Layout.size,
        TerminalCanonicalization.workOffset,
        LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.counterOffset,
        TerminalCanonicalization.epochWire,
        TerminalCanonicalization.scratchOffset,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth] <;> omega

theorem compressionGates_avoids_output
    {workWidth shiftWidth outputWidth : Nat} :
    ∀ g ∈ compressionGates workWidth shiftWidth,
      ∀ q ∈ g.wires,
        q < outputOffset workWidth shiftWidth ∨
          outputOffset workWidth shiftWidth + outputWidth ≤ q := by
  apply placeGates_avoids
    (L := compressionLayout) (W := compressionWiring workWidth shiftWidth)
  · simp [compressionLayout, compressionWiring]
  · intro g hg
    exact List.all_eq_true.mp
      (show TerminalCompression.gates.all
          (RGate.wellFormed compressionLayout.width) = true by
        simpa [compressionLayout, TerminalCompression.layout, Layout.width] using
          TerminalCompression.gates_wellFormed) g hg
  · intro j hj
    simp [compressionLayout] at hj
    interval_cases j <;>
      simp [compressionLayout, compressionWiring, Layout.size,
        outputOffset, LuoTerminalExtraction.outputOffset,
        LuoTerminalCanonicalization.width,
        LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.counterOffset,
        TerminalCanonicalization.epochWire,
        TerminalCanonicalization.scratchOffset,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth] <;> omega

private theorem compressionGates_preserves_controlField
    {workWidth shiftWidth i k : Nat}
    (hshift : 2 ≤ shiftWidth) (hk : k = 3 ∨ k = 4)
    (hscratch : bitValue i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth) = 0) :
    readField (actGates (compressionGates workWidth shiftWidth) i)
        ((compressionWiring workWidth shiftWidth).getD k 0) 1 =
      readField i ((compressionWiring workWidth shiftWidth).getD k 0) 1 := by
  let gathered := gatherBits
    (place compressionLayout (compressionWiring workWidth shiftWidth))
    compressionLayout.width i
  have hlocalScratch : bitValue gathered TerminalCompression.scratchWire = 0 := by
    rw [← readField_one]
    change readField gathered (compressionLayout.offset 4) 1 = 0
    have hgather := readField_gatherBits compressionLayout
      (compressionWiring workWidth shiftWidth) 4 i
      (by simp [compressionWiring])
    rw [show gathered = gatherBits
      (place compressionLayout (compressionWiring workWidth shiftWidth))
      compressionLayout.width i by rfl]
    rw [show readField
        (gatherBits
          (place compressionLayout (compressionWiring workWidth shiftWidth))
          compressionLayout.width i)
        (compressionLayout.offset 4) 1 =
          readField i
            ((compressionWiring workWidth shiftWidth).getD 4 0) 1 by
      simpa [compressionLayout, Layout.size] using hgather]
    simpa [compressionWiring, TerminalCompression.scratchWire,
      readField_one] using hscratch
  have hlocal := TerminalCompression.gates_act
    (gatherBits_lt
      (place compressionLayout (compressionWiring workWidth shiftWidth))
      compressionLayout.width i) hlocalScratch
  have hlocalPreserved :
      readField (actGates TerminalCompression.gates gathered)
          (compressionLayout.offset k) 1 =
        readField gathered (compressionLayout.offset k) 1 := by
    rw [hlocal]
    simp only [TerminalCompression.out]
    split
    · apply readField_writeField_of_disjoint
      rcases hk with rfl | rfl <;>
        simp [compressionLayout, TerminalCompression.codeOffset, Layout.offset]
    · rfl
  have hplaced := readField_actGates_placed
    (gs := TerminalCompression.gates) (L := compressionLayout)
    (W := compressionWiring workWidth shiftWidth) (k := k) (q := 0)
    (len := 1) (I := i) (compressionWiring_disjoint hshift)
    (by simp [compressionLayout, compressionWiring])
    (by rcases hk with rfl | rfl <;> simp [compressionLayout])
    (fun g hg => List.all_eq_true.mp
      (show TerminalCompression.gates.all
          (RGate.wellFormed compressionLayout.width) = true by
        simpa [compressionLayout, TerminalCompression.layout, Layout.width]
          using TerminalCompression.gates_wellFormed) g hg)
    (by rcases hk with rfl | rfl <;> simp [compressionLayout, Layout.size])
  have hgatherInput : readField gathered (compressionLayout.offset k) 1 =
      readField i ((compressionWiring workWidth shiftWidth).getD k 0) 1 := by
    rcases hk with rfl | rfl
    · simpa [gathered, compressionLayout, Layout.size] using
        (readField_gatherBits compressionLayout
          (compressionWiring workWidth shiftWidth) 3 i
          (by simp [compressionWiring]))
    · simpa [gathered, compressionLayout, Layout.size] using
        (readField_gatherBits compressionLayout
          (compressionWiring workWidth shiftWidth) 4 i
          (by simp [compressionWiring]))
  simpa [compressionGates, Nat.add_zero] using
    hplaced.trans (hlocalPreserved.trans hgatherInput)

theorem compressionGates_preserves_outer
    {workWidth shiftWidth i : Nat}
    (hshift : 2 ≤ shiftWidth)
    (hscratch : bitValue i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth) = 0) :
    bitValue (actGates (compressionGates workWidth shiftWidth) i)
        (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) =
      bitValue i
        (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) := by
  simpa [readField_one, compressionWiring] using
    (compressionGates_preserves_controlField
      (workWidth := workWidth) (shiftWidth := shiftWidth) (i := i) (k := 3)
      hshift (Or.inl rfl) hscratch)

theorem compressionGates_preserves_scratchHead
    {workWidth shiftWidth i : Nat}
    (hshift : 2 ≤ shiftWidth)
    (hscratch : bitValue i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth) = 0) :
    bitValue (actGates (compressionGates workWidth shiftWidth) i)
        (TerminalCanonicalization.scratchOffset workWidth shiftWidth) = 0 := by
  rw [← hscratch]
  simpa [readField_one, compressionWiring] using
    (compressionGates_preserves_controlField
      (workWidth := workWidth) (shiftWidth := shiftWidth) (i := i) (k := 4)
      hshift (Or.inr rfl) hscratch)

theorem compressionGates_readField_of_outside
    {workWidth shiftWidth off len i : Nat}
    (houtside : ∀ j, j < compressionLayout.length →
      (compressionWiring workWidth shiftWidth).getD j 0 +
          compressionLayout.size j ≤ off ∨
        off + len ≤
          (compressionWiring workWidth shiftWidth).getD j 0) :
    readField (actGates (compressionGates workWidth shiftWidth) i) off len =
      readField i off len := by
  apply readField_actGates_map_of_outside
    (w := compressionLayout.width)
  · intro g hg
    exact List.all_eq_true.mp
      (show TerminalCompression.gates.all
          (RGate.wellFormed compressionLayout.width) = true by
        simpa [compressionLayout, TerminalCompression.layout, Layout.width]
          using TerminalCompression.gates_wellFormed) g hg
  · exact place_avoids
      (by simp [compressionLayout, compressionWiring]) houtside

theorem preparationGates_avoids_output
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (hworkWidth : 0 < workWidth)
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth) :
    ∀ g ∈ preparationGates workWidth shiftWidth outputWidth lengthWidth,
      ∀ q ∈ g.wires,
        q < outputOffset workWidth shiftWidth ∨
          outputOffset workWidth shiftWidth + outputWidth ≤ q := by
  intro g hg q hq
  simp only [preparationGates, List.mem_append] at hg
  rcases hg with hrest | hflag
  · rcases hrest with hrest | hcompression
    · rcases hrest with hflag | hcanonical
      · exact flagGates_avoids_output hlength g hflag q hq
      · exact LuoTerminalExtraction.canonicalization_avoids_output
          (outputWidth := outputWidth) hworkWidth g hcanonical q hq
    · exact compressionGates_avoids_output g hcompression q hq
  · exact flagGates_avoids_output hlength g hflag q hq

theorem flagGates_act_terminal
    {workWidth shiftWidth outputWidth lengthWidth i : Nat}
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth)
    (hscratch : readField i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0)
    (hterminalLength : readField i
      (terminalLengthOffset workWidth shiftWidth outputWidth) lengthWidth =
        2 ^ lengthWidth - 1)
    (houter : bitValue i
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 0) :
    actGates (flagGates workWidth shiftWidth outputWidth lengthWidth) i =
      writeField i
        (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) 1 1 := by
  have hflagScratch : readField i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      lengthWidth = 0 :=
    readField_narrow hlength hscratch
  have hmask : (2 ^ lengthWidth - 1) % 2 ^ lengthWidth =
      2 ^ lengthWidth - 1 := by
    apply Nat.mod_eq_of_lt
    have hpow := Nat.two_pow_pos lengthWidth
    omega
  have hact := Placed.selector_act
    (value := 2 ^ lengthWidth - 1) (width := lengthWidth)
    (source := terminalLengthOffset workWidth shiftWidth outputWidth)
    (flag := LuoTerminalCanonicalization.outerWire workWidth shiftWidth)
    (scratch := TerminalCanonicalization.scratchOffset workWidth shiftWidth)
    (i := i) (flagWiring_disjoint hlength) hflagScratch
  simpa [flagGates, hterminalLength, houter, hmask] using hact

theorem preparationGates_read_work
    {workWidth shiftWidth outputWidth lengthWidth shift raw i : Nat}
    (hworkWidth : 0 < workWidth)
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth)
    (hscratch : readField i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0)
    (hcarry : bitValue i
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0)
    (hjoint : bitValue i
      (LuoTerminalCanonicalization.jointWire workWidth shiftWidth) = 0)
    (houter : bitValue i
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 0)
    (hterminalLength : readField i
      (terminalLengthOffset workWidth shiftWidth outputWidth) lengthWidth =
        2 ^ lengthWidth - 1)
    (hdecoded : TerminalCanonicalization.decodedCounter
      workWidth shiftWidth i = shift)
    (hwork : readField i TerminalCanonicalization.workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth) :
    readField
        (actGates
          (preparationGates workWidth shiftWidth outputWidth lengthWidth) i)
        TerminalCanonicalization.workOffset workWidth = raw := by
  let flag := flagGates workWidth shiftWidth outputWidth lengthWidth
  let canonicalize := LuoTerminalCanonicalization.gates workWidth shiftWidth
  let compression := compressionGates workWidth shiftWidth
  let flagged := actGates flag i
  have hflagged : flagged =
      writeField i
        (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) 1 1 := by
    simpa [flagged, flag] using
      flagGates_act_terminal hlength hscratch hterminalLength houter
  have hscratchFlagged : readField flagged
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0 := by
    rw [hflagged, readField_writeField_of_disjoint]
    · exact hscratch
    · right
      simp [LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.scratchOffset,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth]
      omega
  have hcarryFlagged : bitValue flagged
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0 := by
    rw [hflagged, bitValue_write_ne]
    · exact hcarry
    · simp [LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire]
      omega
  have hjointFlagged : bitValue flagged
      (LuoTerminalCanonicalization.jointWire workWidth shiftWidth) = 0 := by
    rw [hflagged, bitValue_write_ne]
    · exact hjoint
    · simp [LuoTerminalCanonicalization.outerWire]
  have houterFlagged : bitValue flagged
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 1 := by
    rw [hflagged, bitValue_write_self]
  have hcounterFlagged : readField flagged
      (TerminalCanonicalization.counterOffset workWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) =
        readField i (TerminalCanonicalization.counterOffset workWidth)
          (TerminalCanonicalization.counterWidth shiftWidth) := by
    rw [hflagged, readField_writeField_of_disjoint]
    right
    simp [LuoTerminalCanonicalization.outerWire,
      LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.counterOffset,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth]
    omega
  have hepochFlagged : bitValue flagged
      (TerminalCanonicalization.epochWire workWidth shiftWidth) =
        bitValue i (TerminalCanonicalization.epochWire workWidth shiftWidth) := by
    rw [hflagged, bitValue_write_ne]
    simp [LuoTerminalCanonicalization.outerWire,
      LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.epochWire,
      TerminalCanonicalization.counterOffset,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth]
    omega
  have hdecodedFlagged : TerminalCanonicalization.decodedCounter
      workWidth shiftWidth flagged = shift := by
    simp only [TerminalCanonicalization.decodedCounter,
      TerminalCanonicalization.counterAfterFlip]
    rw [hcounterFlagged, hepochFlagged]
    exact hdecoded
  have hworkFlagged : readField flagged
      TerminalCanonicalization.workOffset workWidth =
        rotatePositionsLeft workWidth shift raw := by
    rw [hflagged, readField_writeField_of_disjoint]
    · exact hwork
    · right
      simp [TerminalCanonicalization.workOffset,
        LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth]
      omega
  have hcanonical : actGates canonicalize flagged =
      writeField flagged TerminalCanonicalization.workOffset workWidth raw := by
    simpa [canonicalize] using
      LuoTerminalCanonicalization.gates_act_on hworkWidth
        hscratchFlagged hcarryFlagged hjointFlagged houterFlagged
        hdecodedFlagged hworkFlagged hraw
  simp only [preparationGates, actGates_append]
  change readField
      (actGates flag
        (actGates compression (actGates canonicalize flagged)))
      TerminalCanonicalization.workOffset workWidth = raw
  rw [readField_actGates_of_outside
      (flagGates_avoids_work
        (workWidth := workWidth) (shiftWidth := shiftWidth)
        (outputWidth := outputWidth) (lengthWidth := lengthWidth)),
    readField_actGates_of_outside
      (compressionGates_avoids_work
        (workWidth := workWidth) (shiftWidth := shiftWidth)),
    hcanonical, readField_writeField_self hraw]

theorem preparationGates_workspace_clear
    {workWidth shiftWidth outputWidth lengthWidth shift raw i : Nat}
    (hworkWidth : 0 < workWidth) (hshift : 2 ≤ shiftWidth)
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth)
    (hscratch : readField i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0)
    (hcarry : bitValue i
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0)
    (hjoint : bitValue i
      (LuoTerminalCanonicalization.jointWire workWidth shiftWidth) = 0)
    (houter : bitValue i
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 0)
    (hterminalLength : readField i
      (terminalLengthOffset workWidth shiftWidth outputWidth) lengthWidth =
        2 ^ lengthWidth - 1)
    (hdecoded : TerminalCanonicalization.decodedCounter
      workWidth shiftWidth i = shift)
    (hwork : readField i TerminalCanonicalization.workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth) :
    let result := actGates
      (preparationGates workWidth shiftWidth outputWidth lengthWidth) i
    readField result
        (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
        (TerminalCanonicalization.counterWidth shiftWidth) = 0 ∧
      bitValue result
          (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0 ∧
      bitValue result
          (LuoTerminalCanonicalization.jointWire workWidth shiftWidth) = 0 ∧
      bitValue result
          (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 0 ∧
      readField result
          (terminalLengthOffset workWidth shiftWidth outputWidth) lengthWidth =
        2 ^ lengthWidth - 1 := by
  dsimp only
  let flag := flagGates workWidth shiftWidth outputWidth lengthWidth
  let canonicalize := LuoTerminalCanonicalization.gates workWidth shiftWidth
  let compression := compressionGates workWidth shiftWidth
  let flagged := actGates flag i
  let canonical := actGates canonicalize flagged
  let compressed := actGates compression canonical
  have hflagged : flagged = writeField i
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) 1 1 := by
    simpa [flagged, flag] using
      flagGates_act_terminal hlength hscratch hterminalLength houter
  have hscratchFlagged : readField flagged
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0 := by
    rw [hflagged, readField_writeField_of_disjoint]
    · exact hscratch
    · right
      simp [LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.scratchOffset,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth]
      omega
  have hcarryFlagged : bitValue flagged
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0 := by
    rw [hflagged, bitValue_write_ne]
    · exact hcarry
    · simp [LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire]
      omega
  have hjointFlagged : bitValue flagged
      (LuoTerminalCanonicalization.jointWire workWidth shiftWidth) = 0 := by
    rw [hflagged, bitValue_write_ne]
    · exact hjoint
    · simp [LuoTerminalCanonicalization.outerWire]
  have houterFlagged : bitValue flagged
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 1 := by
    rw [hflagged, bitValue_write_self]
  have hcounterFlagged : readField flagged
      (TerminalCanonicalization.counterOffset workWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) =
        readField i (TerminalCanonicalization.counterOffset workWidth)
          (TerminalCanonicalization.counterWidth shiftWidth) := by
    rw [hflagged, readField_writeField_of_disjoint]
    right
    simp [LuoTerminalCanonicalization.outerWire,
      LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.counterOffset,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth]
    omega
  have hepochFlagged : bitValue flagged
      (TerminalCanonicalization.epochWire workWidth shiftWidth) =
        bitValue i (TerminalCanonicalization.epochWire workWidth shiftWidth) := by
    rw [hflagged, bitValue_write_ne]
    simp [LuoTerminalCanonicalization.outerWire,
      LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.epochWire,
      TerminalCanonicalization.counterOffset,
      TerminalCanonicalization.carryWire,
      TerminalCanonicalization.counterWidth]
    omega
  have hdecodedFlagged : TerminalCanonicalization.decodedCounter
      workWidth shiftWidth flagged = shift := by
    simp only [TerminalCanonicalization.decodedCounter,
      TerminalCanonicalization.counterAfterFlip]
    rw [hcounterFlagged, hepochFlagged]
    exact hdecoded
  have hworkFlagged : readField flagged
      TerminalCanonicalization.workOffset workWidth =
        rotatePositionsLeft workWidth shift raw := by
    rw [hflagged, readField_writeField_of_disjoint]
    · exact hwork
    · right
      simp [TerminalCanonicalization.workOffset,
        LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth]
      omega
  have hcanonical : canonical =
      writeField flagged TerminalCanonicalization.workOffset workWidth raw := by
    simpa [canonical, canonicalize] using
      LuoTerminalCanonicalization.gates_act_on hworkWidth hscratchFlagged
        hcarryFlagged hjointFlagged houterFlagged hdecodedFlagged hworkFlagged
        hraw
  have hscratchCanonical : readField canonical
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0 := by
    rw [hcanonical, readField_writeField_of_disjoint (Or.inl (by
      simp [TerminalCanonicalization.workOffset,
        TerminalCanonicalization.scratchOffset,
        TerminalCanonicalization.counterWidth]))]
    exact hscratchFlagged
  have hcarryCanonical : bitValue canonical
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0 := by
    rw [hcanonical, bitValue_write_out (Or.inr (by
      simp [TerminalCanonicalization.workOffset,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth]))]
    exact hcarryFlagged
  have hjointCanonical : bitValue canonical
      (LuoTerminalCanonicalization.jointWire workWidth shiftWidth) = 0 := by
    rw [hcanonical, bitValue_write_out (Or.inr (by
      simp [TerminalCanonicalization.workOffset,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth]
      omega))]
    exact hjointFlagged
  have houterCanonical : bitValue canonical
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 1 := by
    rw [hcanonical, bitValue_write_out (Or.inr (by
      simp [TerminalCanonicalization.workOffset,
        LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth]
      omega))]
    exact houterFlagged
  have hscratchHeadCanonical : bitValue canonical
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth) = 0 := by
    rw [← readField_one]
    exact readField_sub_zero (by omega) (by
      simp [TerminalCanonicalization.counterWidth]) hscratchCanonical
  have houterCompressed : bitValue compressed
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 1 := by
    rw [show compressed = actGates
      (compressionGates workWidth shiftWidth) canonical by rfl,
      compressionGates_preserves_outer hshift hscratchHeadCanonical]
    exact houterCanonical
  have hscratchHeadCompressed : bitValue compressed
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth) = 0 := by
    exact compressionGates_preserves_scratchHead hshift hscratchHeadCanonical
  have hcompressionOutside : ∀ {off len : Nat},
      (∀ j, j < compressionLayout.length →
        (compressionWiring workWidth shiftWidth).getD j 0 +
            compressionLayout.size j ≤ off ∨
          off + len ≤
            (compressionWiring workWidth shiftWidth).getD j 0) →
      readField compressed off len = readField canonical off len := by
    intro off len houtside
    exact compressionGates_readField_of_outside houtside
  have hscratchTailCompressed : readField compressed
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth + 1)
      shiftWidth = 0 := by
    rw [hcompressionOutside (by
      intro j hj
      simp [compressionLayout] at hj
      interval_cases j <;>
        simp [compressionLayout, compressionWiring, Layout.size,
          LuoTerminalCanonicalization.outerWire,
          LuoTerminalCanonicalization.jointWire,
          TerminalCanonicalization.counterOffset,
          TerminalCanonicalization.epochWire,
          TerminalCanonicalization.scratchOffset,
          TerminalCanonicalization.carryWire,
          TerminalCanonicalization.counterWidth] <;> omega)]
    exact readField_sub_zero (by omega) (by
      simp [TerminalCanonicalization.counterWidth]
      omega) hscratchCanonical
  have hscratchCompressed : readField compressed
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0 := by
    rw [TerminalCanonicalization.counterWidth, readField_succ,
      hscratchHeadCompressed, hscratchTailCompressed]
  have hcarryCompressed : bitValue compressed
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0 := by
    rw [← readField_one, hcompressionOutside (by
      intro j hj
      simp [compressionLayout] at hj
      interval_cases j <;>
        simp [compressionLayout, compressionWiring, Layout.size,
          LuoTerminalCanonicalization.outerWire,
          LuoTerminalCanonicalization.jointWire,
          TerminalCanonicalization.counterOffset,
          TerminalCanonicalization.epochWire,
          TerminalCanonicalization.scratchOffset,
          TerminalCanonicalization.carryWire,
          TerminalCanonicalization.counterWidth] <;> omega),
      readField_one]
    exact hcarryCanonical
  have hjointCompressed : bitValue compressed
      (LuoTerminalCanonicalization.jointWire workWidth shiftWidth) = 0 := by
    rw [← readField_one, hcompressionOutside (by
      intro j hj
      simp [compressionLayout] at hj
      interval_cases j <;>
        simp [compressionLayout, compressionWiring, Layout.size,
          LuoTerminalCanonicalization.outerWire,
          LuoTerminalCanonicalization.jointWire,
          TerminalCanonicalization.counterOffset,
          TerminalCanonicalization.epochWire,
          TerminalCanonicalization.scratchOffset,
          TerminalCanonicalization.carryWire,
          TerminalCanonicalization.counterWidth] <;> omega),
      readField_one]
    exact hjointCanonical
  have hterminalLengthFlagged : readField flagged
      (terminalLengthOffset workWidth shiftWidth outputWidth) lengthWidth =
        2 ^ lengthWidth - 1 := by
    rw [hflagged, readField_writeField_of_disjoint]
    · exact hterminalLength
    · left
      simp [terminalLengthOffset, LuoTerminalExtraction.width,
        LuoTerminalExtraction.outputOffset,
        LuoTerminalCanonicalization.width,
        LuoTerminalCanonicalization.outerWire]
  have hterminalLengthCanonical : readField canonical
      (terminalLengthOffset workWidth shiftWidth outputWidth) lengthWidth =
        2 ^ lengthWidth - 1 := by
    rw [hcanonical, readField_writeField_of_disjoint]
    · exact hterminalLengthFlagged
    · left
      simp [TerminalCanonicalization.workOffset, terminalLengthOffset,
        LuoTerminalExtraction.width, LuoTerminalExtraction.outputOffset,
        LuoTerminalCanonicalization.width,
        LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth]
      omega
  have hterminalLengthCompressed : readField compressed
      (terminalLengthOffset workWidth shiftWidth outputWidth) lengthWidth =
        2 ^ lengthWidth - 1 := by
    rw [hcompressionOutside (by
      intro j hj
      simp [compressionLayout] at hj
      interval_cases j <;>
        simp [compressionLayout, compressionWiring, Layout.size,
          terminalLengthOffset, LuoTerminalExtraction.width,
          LuoTerminalExtraction.outputOffset,
          LuoTerminalCanonicalization.width,
          LuoTerminalCanonicalization.outerWire,
          LuoTerminalCanonicalization.jointWire,
          TerminalCanonicalization.counterOffset,
          TerminalCanonicalization.epochWire,
          TerminalCanonicalization.scratchOffset,
          TerminalCanonicalization.carryWire,
          TerminalCanonicalization.counterWidth] <;> omega)]
    exact hterminalLengthCanonical
  have hfinal : actGates flag compressed = writeField compressed
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) 1 0 := by
    have hflagScratch : readField compressed
        (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
        lengthWidth = 0 := readField_narrow hlength hscratchCompressed
    have hact := Placed.selector_act
      (value := 2 ^ lengthWidth - 1) (width := lengthWidth)
      (source := terminalLengthOffset workWidth shiftWidth outputWidth)
      (flag := LuoTerminalCanonicalization.outerWire workWidth shiftWidth)
      (scratch := TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (i := compressed) (flagWiring_disjoint hlength) hflagScratch
    have hmask : (2 ^ lengthWidth - 1) % 2 ^ lengthWidth =
        2 ^ lengthWidth - 1 := by
      apply Nat.mod_eq_of_lt
      have hpow := Nat.two_pow_pos lengthWidth
      omega
    simpa [flag, flagGates, hterminalLengthCompressed, houterCompressed,
      hmask] using hact
  simp only [preparationGates, actGates_append]
  change readField (actGates flag compressed)
          (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
          (TerminalCanonicalization.counterWidth shiftWidth) = 0 ∧
    bitValue (actGates flag compressed)
          (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0 ∧
    bitValue (actGates flag compressed)
          (LuoTerminalCanonicalization.jointWire workWidth shiftWidth) = 0 ∧
    bitValue (actGates flag compressed)
          (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 0 ∧
    readField (actGates flag compressed)
          (terminalLengthOffset workWidth shiftWidth outputWidth) lengthWidth =
        2 ^ lengthWidth - 1
  rw [hfinal]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [readField_writeField_of_disjoint]
    · exact hscratchCompressed
    · right
      simp [LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire,
        TerminalCanonicalization.scratchOffset,
        TerminalCanonicalization.carryWire,
        TerminalCanonicalization.counterWidth]
      omega
  · rw [bitValue_write_ne]
    · exact hcarryCompressed
    · simp [LuoTerminalCanonicalization.outerWire,
        LuoTerminalCanonicalization.jointWire]
      omega
  · rw [bitValue_write_ne]
    · exact hjointCompressed
    · simp [LuoTerminalCanonicalization.outerWire]
  · rw [bitValue_write_self]
  · rw [readField_writeField_of_disjoint]
    · exact hterminalLengthCompressed
    · left
      simp [terminalLengthOffset, LuoTerminalExtraction.width,
        LuoTerminalExtraction.outputOffset,
        LuoTerminalCanonicalization.width]

theorem gates_act_on
    {workWidth shiftWidth outputWidth lengthWidth shift raw i : Nat}
    (hworkWidth : 0 < workWidth) (hshift : 2 ≤ shiftWidth)
    (houtput : outputWidth ≤ workWidth)
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth)
    (hscratch : readField i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0)
    (hcarry : bitValue i
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0)
    (hjoint : bitValue i
      (LuoTerminalCanonicalization.jointWire workWidth shiftWidth) = 0)
    (houter : bitValue i
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 0)
    (hterminalLength : readField i
      (terminalLengthOffset workWidth shiftWidth outputWidth) lengthWidth =
        2 ^ lengthWidth - 1)
    (hdecoded : TerminalCanonicalization.decodedCounter
      workWidth shiftWidth i = shift)
    (hwork : readField i TerminalCanonicalization.workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth) :
    actGates (gates workWidth shiftWidth outputWidth lengthWidth) i =
      writeField i (outputOffset workWidth shiftWidth) outputWidth
        (readField i (outputOffset workWidth shiftWidth) outputWidth ^^^
          readField raw 0 outputWidth) := by
  let prep := preparationGates workWidth shiftWidth outputWidth lengthWidth
  let copy := copyGates workWidth shiftWidth outputWidth
  have hprepWork : readField (actGates prep i)
      TerminalCanonicalization.workOffset workWidth = raw := by
    simpa [prep] using
      preparationGates_read_work hworkWidth hlength hscratch hcarry hjoint
        houter hterminalLength hdecoded hwork hraw
  have hprepPrefix : readField (actGates prep i)
      TerminalCanonicalization.workOffset outputWidth =
        readField raw 0 outputWidth := by
    have h := congrArg (fun v => readField v 0 outputWidth) hprepWork
    rw [readField_readField
      (D := TerminalCanonicalization.workOffset) (W := workWidth)
      (by simpa [TerminalCanonicalization.workOffset] using houtput)] at h
    simpa [TerminalCanonicalization.workOffset] using h
  have hprepOutput : readField (actGates prep i)
      (outputOffset workWidth shiftWidth) outputWidth =
        readField i (outputOffset workWidth shiftWidth) outputWidth := by
    simpa [prep] using
      readField_actGates_of_outside
        (preparationGates_avoids_output hworkWidth hlength) i
  have hcopy : ∀ j, actGates copy j =
      writeField j (outputOffset workWidth shiftWidth) outputWidth
        (readField j (outputOffset workWidth shiftWidth) outputWidth ^^^
          readField j TerminalCanonicalization.workOffset outputWidth) := by
    intro j
    apply actGates_copyField
    left
    simp [TerminalCanonicalization.workOffset, outputOffset,
      LuoTerminalExtraction.outputOffset,
      LuoTerminalCanonicalization.width,
      LuoTerminalCanonicalization.outerWire,
      LuoTerminalCanonicalization.jointWire,
      TerminalCanonicalization.carryWire]
    omega
  have hcompute := actGates_compute_use_uncompute
    (gs := prep) (cp := copy)
    (w := width workWidth shiftWidth outputWidth lengthWidth)
    (off := outputOffset workWidth shiftWidth) (len := outputWidth)
    (f := fun j =>
      readField j (outputOffset workWidth shiftWidth) outputWidth ^^^
        readField j TerminalCanonicalization.workOffset outputWidth)
    (by
      simpa [prep] using
        preparationGates_wellFormed hworkWidth hshift hlength)
    (by
      simpa [prep] using
        preparationGates_avoids_output hworkWidth hlength)
    hcopy i
  rw [hprepOutput, hprepPrefix] at hcompute
  simpa [gates, prep, copy] using hcompute

theorem gates_act_on_of_clear
    {workWidth shiftWidth outputWidth lengthWidth shift raw i : Nat}
    (hworkWidth : 0 < workWidth) (hshift : 2 ≤ shiftWidth)
    (houtput : outputWidth ≤ workWidth)
    (hlength : lengthWidth ≤
      TerminalCanonicalization.counterWidth shiftWidth)
    (hscratch : readField i
      (TerminalCanonicalization.scratchOffset workWidth shiftWidth)
      (TerminalCanonicalization.counterWidth shiftWidth) = 0)
    (hcarry : bitValue i
      (TerminalCanonicalization.carryWire workWidth shiftWidth) = 0)
    (hjoint : bitValue i
      (LuoTerminalCanonicalization.jointWire workWidth shiftWidth) = 0)
    (houter : bitValue i
      (LuoTerminalCanonicalization.outerWire workWidth shiftWidth) = 0)
    (hterminalLength : readField i
      (terminalLengthOffset workWidth shiftWidth outputWidth) lengthWidth =
        2 ^ lengthWidth - 1)
    (hdecoded : TerminalCanonicalization.decodedCounter
      workWidth shiftWidth i = shift)
    (hwork : readField i TerminalCanonicalization.workOffset workWidth =
      rotatePositionsLeft workWidth shift raw)
    (hraw : raw < 2 ^ workWidth)
    (houtputClear : readField i
      (outputOffset workWidth shiftWidth) outputWidth = 0) :
    actGates (gates workWidth shiftWidth outputWidth lengthWidth) i =
      writeField i (outputOffset workWidth shiftWidth) outputWidth
        (readField raw 0 outputWidth) := by
  rw [gates_act_on hworkWidth hshift houtput hlength hscratch hcarry
    hjoint houter hterminalLength hdecoded hwork hraw,
    houtputClear, Nat.zero_xor]

theorem circuit_width
    (workWidth shiftWidth outputWidth lengthWidth : Nat) :
    (circuit workWidth shiftWidth outputWidth lengthWidth).width =
      workWidth +
        2 * TerminalCanonicalization.counterWidth shiftWidth +
        3 + outputWidth + lengthWidth := by
  simp [circuit, width, terminalLengthOffset,
    LuoTerminalExtraction.width,
    LuoTerminalExtraction.outputOffset,
    LuoTerminalCanonicalization.width,
    LuoTerminalCanonicalization.outerWire,
    LuoTerminalCanonicalization.jointWire,
    TerminalCanonicalization.carryWire]

theorem flagGates_length
    (workWidth shiftWidth outputWidth lengthWidth : Nat) :
    (flagGates workWidth shiftWidth outputWidth lengthWidth).length =
      2 * (lengthWidth - 2) + 1 := by
  rw [flagGates, Placed.selector_length]
  exact Selector.gates_allOnes_length lengthWidth

theorem flagGates_ccx
    (workWidth shiftWidth outputWidth lengthWidth : Nat) :
    (flagGates workWidth shiftWidth outputWidth lengthWidth).countP
        RGate.isCcx =
      2 * (lengthWidth - 1) - 1 := by
  rw [flagGates, Placed.selector_ccx]
  exact Selector.gates_allOnes_ccx lengthWidth

theorem flagGates_cx
    (workWidth shiftWidth outputWidth lengthWidth : Nat) :
    (flagGates workWidth shiftWidth outputWidth lengthWidth).countP
        RGate.isCx =
      if lengthWidth = 1 then 1 else 0 := by
  rw [flagGates, Placed.selector_cx]
  exact Selector.gates_allOnes_cx lengthWidth

theorem compressionGates_length (workWidth shiftWidth : Nat) :
    (compressionGates workWidth shiftWidth).length = 23 := by
  simp [compressionGates, TerminalCompression.gates_length]

theorem compressionGates_ccx (workWidth shiftWidth : Nat) :
    (compressionGates workWidth shiftWidth).countP RGate.isCcx = 15 := by
  rw [compressionGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact TerminalCompression.gates_ccx

theorem compressionGates_cx (workWidth shiftWidth : Nat) :
    (compressionGates workWidth shiftWidth).countP RGate.isCx = 0 := by
  rw [compressionGates,
    countP_map_gates (fun g => RGate.isCx_map _ g)]
  exact TerminalCompression.gates_cx

theorem gates_length_le
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth outputWidth lengthWidth).length ≤
      2 *
        (18 * TerminalCanonicalization.counterWidth shiftWidth + 2 +
          3 * (workWidth - 1) *
            TerminalCanonicalization.counterWidth shiftWidth +
          2 * (2 * (lengthWidth - 2) + 1) + 23) +
        outputWidth := by
  have hcanonical := LuoTerminalCanonicalization.gates_length_le
    (shiftWidth := shiftWidth) hworkWidth
  have hflag := flagGates_length
    workWidth shiftWidth outputWidth lengthWidth
  simp only [gates, preparationGates, List.length_append,
    List.length_reverse, copyGates, copyField_length]
  rw [compressionGates_length]
  omega

theorem gates_ccx_le
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth outputWidth lengthWidth).countP RGate.isCcx ≤
      2 *
        (6 * TerminalCanonicalization.counterWidth shiftWidth +
          (workWidth - 1) *
            TerminalCanonicalization.counterWidth shiftWidth +
          2 * (2 * (lengthWidth - 1) - 1) + 15) := by
  have hcanonical := LuoTerminalCanonicalization.gates_ccx_le
    (shiftWidth := shiftWidth) hworkWidth
  have hflag := flagGates_ccx
    workWidth shiftWidth outputWidth lengthWidth
  simp only [gates, preparationGates, List.countP_append,
    List.countP_reverse, copyGates, copyField_no_ccx]
  rw [compressionGates_ccx]
  omega

theorem gates_cx_le
    {workWidth shiftWidth outputWidth lengthWidth : Nat}
    (hworkWidth : 0 < workWidth) :
    (gates workWidth shiftWidth outputWidth lengthWidth).countP RGate.isCx ≤
      2 *
        (8 * TerminalCanonicalization.counterWidth shiftWidth +
          2 * (workWidth - 1) *
            TerminalCanonicalization.counterWidth shiftWidth +
          2 * (if lengthWidth = 1 then 1 else 0)) +
        outputWidth := by
  have hcanonical := LuoTerminalCanonicalization.gates_cx_le
    (shiftWidth := shiftWidth) hworkWidth
  have hflag := flagGates_cx
    workWidth shiftWidth outputWidth lengthWidth
  simp only [gates, preparationGates, List.countP_append,
    List.countP_reverse, copyGates, copyField_cx]
  rw [compressionGates_cx]
  omega

end VQ.Euclid.LuoTerminalEndpoint
