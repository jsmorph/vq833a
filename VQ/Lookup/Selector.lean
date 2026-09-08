import VQ.Lookup.Spec
import VQ.Euclid.Selector
import VQ.Reversible.ControlledConstant
import VQ.Reversible.Wiring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace VQ.Lookup.Selector

open Reversible

def workspaceWidth (addressWidth : Nat) : Nat := addressWidth + 1

def circuitLayout (addressWidth outputWidth : Nat) : Layout :=
  Lookup.layout addressWidth outputWidth (workspaceWidth addressWidth)

def outputOffset (addressWidth : Nat) : Nat := addressWidth

def flagWire (addressWidth outputWidth : Nat) : Nat :=
  addressWidth + outputWidth

def scratchOffset (addressWidth outputWidth : Nat) : Nat :=
  flagWire addressWidth outputWidth + 1

def width (addressWidth outputWidth : Nat) : Nat :=
  (circuitLayout addressWidth outputWidth).width

def selectorWiring (addressWidth outputWidth : Nat) : Wiring :=
  [0, flagWire addressWidth outputWidth,
    scratchOffset addressWidth outputWidth]

def selectorGates (row addressWidth outputWidth : Nat) : List RGate :=
  (Euclid.Selector.gates row addressWidth).map
    (RGate.map (place (Euclid.Selector.layout addressWidth)
      (selectorWiring addressWidth outputWidth)))

def rowGates (row word addressWidth outputWidth : Nat) : List RGate :=
  selectorGates row addressWidth outputWidth ++
    controlledXorGates (flagWire addressWidth outputWidth)
      (outputOffset addressWidth) outputWidth word ++
    (selectorGates row addressWidth outputWidth).reverse

def rows (table : List Nat) (addressWidth outputWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | row, count + 1 =>
      rowGates row (Lookup.value table outputWidth row)
        addressWidth outputWidth ++
      rows table addressWidth outputWidth (row + 1) count

def gates (table : List Nat) (addressWidth outputWidth : Nat) : List RGate :=
  rows table addressWidth outputWidth 0 (2 ^ addressWidth)

def circuit (table : List Nat) (addressWidth outputWidth : Nat) : RCircuit :=
  { width := width addressWidth outputWidth
    gates := gates table addressWidth outputWidth }

theorem circuitLayout_width (addressWidth outputWidth : Nat) :
    width addressWidth outputWidth =
      2 * addressWidth + outputWidth + 1 := by
  simp [width, circuitLayout, Lookup.layout, workspaceWidth, Layout.width]
  omega

theorem selectorWiring_disjoint (addressWidth outputWidth : Nat) :
    Wiring.Disjoint (Euclid.Selector.layout addressWidth)
      (selectorWiring addressWidth outputWidth) := by
  intro j k hj hk hne
  simp only [selectorWiring, List.length_cons, List.length_nil,
    Nat.zero_add] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp [selectorWiring, Euclid.Selector.layout, Layout.size,
      flagWire, scratchOffset] at * <;> omega

theorem selectorWiring_bound (addressWidth outputWidth : Nat) :
    ∀ j, j < (Euclid.Selector.layout addressWidth).length →
      (selectorWiring addressWidth outputWidth).getD j 0 +
          (Euclid.Selector.layout addressWidth).size j ≤
      width addressWidth outputWidth := by
  intro j hj
  simp [Euclid.Selector.layout] at hj
  interval_cases j <;>
    simp [selectorWiring, Euclid.Selector.layout, Layout.size,
      flagWire, scratchOffset, circuitLayout_width] at * <;> omega

theorem selectorGates_wellFormed (row addressWidth outputWidth : Nat) :
    (selectorGates row addressWidth outputWidth).all
      (RGate.wellFormed (width addressWidth outputWidth)) = true := by
  apply wellFormed_placeGates
  · exact selectorWiring_disjoint addressWidth outputWidth
  · simp [selectorWiring, Euclid.Selector.layout]
  · exact selectorWiring_bound addressWidth outputWidth
  · exact List.all_eq_true.mp
      (Euclid.Selector.gates_wellFormed row addressWidth)

theorem selectorGates_outside_output (row addressWidth outputWidth : Nat) :
    ∀ g ∈ selectorGates row addressWidth outputWidth, ∀ q ∈ g.wires,
      q < outputOffset addressWidth ∨
        outputOffset addressWidth + outputWidth ≤ q := by
  apply placeGates_avoids
  · simp [selectorWiring, Euclid.Selector.layout]
  · exact List.all_eq_true.mp
      (Euclid.Selector.gates_wellFormed row addressWidth)
  · intro j hj
    simp [Euclid.Selector.layout] at hj
    interval_cases j <;>
      simp [selectorWiring, Euclid.Selector.layout, Layout.size,
        outputOffset, flagWire, scratchOffset] at *

theorem selectorGates_act {row addressWidth outputWidth i : Nat}
    (hworkspace :
      Lookup.workspace addressWidth outputWidth (workspaceWidth addressWidth) i = 0) :
    actGates (selectorGates row addressWidth outputWidth) i =
      writeField i (flagWire addressWidth outputWidth) 1
        (if Lookup.address addressWidth outputWidth
            (workspaceWidth addressWidth) i = row % 2 ^ addressWidth
          then 1 else 0) := by
  let selectorLayout := Euclid.Selector.layout addressWidth
  let wiring := selectorWiring addressWidth outputWidth
  let localState := gatherBits (place selectorLayout wiring) selectorLayout.width i
  have hworkspace' :
      readField i (flagWire addressWidth outputWidth)
          (workspaceWidth addressWidth) = 0 := by
    simpa [Lookup.workspace, Lookup.layout, workspaceWidth, flagWire,
      Layout.read, Layout.offset, Layout.size] using hworkspace
  have hlocalScratch : Euclid.Selector.scratch addressWidth localState = 0 := by
    change selectorLayout.read localState 2 = 0
    rw [read_gatherBits selectorLayout wiring 2 i (by simp [wiring, selectorWiring])]
    apply readField_sub_zero
      (off := flagWire addressWidth outputWidth)
      (len := workspaceWidth addressWidth)
      (o := scratchOffset addressWidth outputWidth)
      (l := addressWidth)
    · simp [scratchOffset]
    · simp [scratchOffset, workspaceWidth]
      omega
    · exact hworkspace'
  have hlocalFlag : Euclid.Selector.flag addressWidth localState = 0 := by
    change selectorLayout.read localState 1 = 0
    rw [read_gatherBits selectorLayout wiring 1 i (by simp [wiring, selectorWiring])]
    have hflagClear := readField_narrow
      (i := i) (off := flagWire addressWidth outputWidth)
      (w := workspaceWidth addressWidth) (w' := 1)
      (by simp [workspaceWidth]) hworkspace'
    simpa [selectorLayout, wiring, selectorWiring, Euclid.Selector.layout,
      Layout.size] using hflagClear
  have hlocalSource : Euclid.Selector.source addressWidth localState =
      Lookup.address addressWidth outputWidth (workspaceWidth addressWidth) i := by
    change selectorLayout.read localState 0 = _
    rw [read_gatherBits selectorLayout wiring 0 i (by simp [wiring, selectorWiring])]
    rfl
  have hlocal := Euclid.Selector.act_gates
    (value := row) (width := addressWidth) (i := localState) hlocalScratch
  have hlocalWrite :
      actGates (Euclid.Selector.gates row addressWidth) localState =
        selectorLayout.write localState 1
          (if Lookup.address addressWidth outputWidth
              (workspaceWidth addressWidth) i = row % 2 ^ addressWidth
            then 1 else 0) := by
    rw [hlocal]
    simp only [Euclid.Selector.out, hlocalFlag, hlocalSource, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by split <;> omega)]
  have hplaced := actGates_placed_write
    (L := selectorLayout) (W := wiring) (gs := Euclid.Selector.gates row addressWidth)
    (k := 1) (I := i)
    (selectorWiring_disjoint addressWidth outputWidth)
    (by simp [selectorLayout, wiring, Euclid.Selector.layout, selectorWiring])
    (by simp [selectorLayout, Euclid.Selector.layout])
    (List.all_eq_true.mp (Euclid.Selector.gates_wellFormed row addressWidth))
    hlocalWrite
  simpa [selectorGates, selectorLayout, wiring, selectorWiring,
    Euclid.Selector.layout, Layout.size, flagWire] using hplaced

theorem rowGates_act {row word addressWidth outputWidth i : Nat}
    (hworkspace :
      Lookup.workspace addressWidth outputWidth (workspaceWidth addressWidth) i = 0) :
    actGates (rowGates row word addressWidth outputWidth) i =
      if Lookup.address addressWidth outputWidth
          (workspaceWidth addressWidth) i = row % 2 ^ addressWidth then
        writeField i (outputOffset addressWidth) outputWidth
          (Lookup.output addressWidth outputWidth
              (workspaceWidth addressWidth) i ^^^
            word)
      else i := by
  have hcompute := selectorGates_wellFormed row addressWidth outputWidth
  have houtside := selectorGates_outside_output row addressWidth outputWidth
  have hcopy : ∀ j,
      actGates
          (controlledXorGates (flagWire addressWidth outputWidth)
            (outputOffset addressWidth) outputWidth word) j =
        writeField j (outputOffset addressWidth) outputWidth
          (readField j (outputOffset addressWidth) outputWidth ^^^
            bitValue j (flagWire addressWidth outputWidth) * word) := by
    intro j
    exact controlledXorGates_act outputWidth (outputOffset addressWidth) word j
      (Or.inr (by simp [flagWire, outputOffset]))
  have hcu := actGates_compute_use_uncompute hcompute houtside hcopy i
  rw [rowGates, hcu, selectorGates_act hworkspace]
  by_cases haddress :
      Lookup.address addressWidth outputWidth (workspaceWidth addressWidth) i =
        row % 2 ^ addressWidth
  · simp only [haddress, if_true, bitValue_write_self, Nat.one_mod,
      Nat.one_mul]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [outputOffset, flagWire]))]
    rfl
  · simp only [haddress, if_false, bitValue_write_self, Nat.zero_mod,
      Nat.zero_mul, Nat.xor_zero]
    rw [readField_writeField_of_disjoint (Or.inr (by
      simp [outputOffset, flagWire])), writeField_read]

theorem rowGates_wellFormed (row word addressWidth outputWidth : Nat) :
    (rowGates row word addressWidth outputWidth).all
      (RGate.wellFormed (width addressWidth outputWidth)) = true := by
  simp only [rowGates, List.all_append, List.all_reverse,
    selectorGates_wellFormed, Bool.true_and]
  rw [Bool.and_true]
  exact controlledXorGates_wellFormed
    (Or.inr (by simp [flagWire, outputOffset]))
    (by rw [circuitLayout_width]; simp [flagWire]; omega)
    (by rw [circuitLayout_width]; simp [outputOffset]; omega)

theorem rowGates_value_act {table : List Nat}
    {row addressWidth outputWidth i : Nat}
    (hrow : row < 2 ^ addressWidth)
    (hworkspace :
      Lookup.workspace addressWidth outputWidth (workspaceWidth addressWidth) i = 0) :
    actGates
        (rowGates row (Lookup.value table outputWidth row)
          addressWidth outputWidth) i =
      if Lookup.address addressWidth outputWidth
          (workspaceWidth addressWidth) i = row then
        Lookup.xorOutput table addressWidth outputWidth
          (workspaceWidth addressWidth) i
      else i := by
  rw [rowGates_act hworkspace, Nat.mod_eq_of_lt hrow]
  by_cases haddress : Lookup.address addressWidth outputWidth
      (workspaceWidth addressWidth) i = row
  · simp [haddress, Lookup.xorOutput, Lookup.layout, outputOffset,
      Layout.write, Layout.offset, Layout.size]
  · simp [haddress]

theorem rows_wellFormed (table : List Nat)
    (addressWidth outputWidth start count : Nat) :
    (rows table addressWidth outputWidth start count).all
      (RGate.wellFormed (width addressWidth outputWidth)) = true := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [rows, List.all_append,
        rowGates_wellFormed, ih, Bool.and_self]

theorem rows_act {table : List Nat}
    {addressWidth outputWidth start count i : Nat}
    (hbound : start + count ≤ 2 ^ addressWidth)
    (hworkspace :
      Lookup.workspace addressWidth outputWidth (workspaceWidth addressWidth) i = 0) :
    actGates (rows table addressWidth outputWidth start count) i =
      if start ≤ Lookup.address addressWidth outputWidth
          (workspaceWidth addressWidth) i ∧
          Lookup.address addressWidth outputWidth
            (workspaceWidth addressWidth) i < start + count then
        Lookup.xorOutput table addressWidth outputWidth
          (workspaceWidth addressWidth) i
      else i := by
  induction count generalizing start i with
  | zero =>
      rw [rows, actGates_nil, if_neg]
      omega
  | succ count ih =>
      rw [rows, actGates_append,
        rowGates_value_act (show start < 2 ^ addressWidth by omega) hworkspace]
      by_cases heq : Lookup.address addressWidth outputWidth
          (workspaceWidth addressWidth) i = start
      · rw [if_pos heq]
        have haddress := Lookup.address_xorOutput table addressWidth outputWidth
          (workspaceWidth addressWidth) i
        have hworkspace' : Lookup.workspace addressWidth outputWidth
            (workspaceWidth addressWidth)
            (Lookup.xorOutput table addressWidth outputWidth
              (workspaceWidth addressWidth) i) = 0 := by
          rw [Lookup.workspace_xorOutput, hworkspace]
        rw [ih (start := start + 1)
          (i := Lookup.xorOutput table addressWidth outputWidth
            (workspaceWidth addressWidth) i) (by omega) hworkspace']
        rw [if_neg (by rw [haddress, heq]; omega), if_pos (by omega)]
      · rw [if_neg heq, ih (start := start + 1) (i := i)
          (by omega) hworkspace]
        by_cases hrange : start + 1 ≤
            Lookup.address addressWidth outputWidth
              (workspaceWidth addressWidth) i ∧
            Lookup.address addressWidth outputWidth
              (workspaceWidth addressWidth) i < start + 1 + count
        · rw [if_pos hrange, if_pos (by omega)]
        · rw [if_neg hrange, if_neg (by
            intro h
            apply hrange
            constructor <;> omega)]

theorem circuit_wellFormed (table : List Nat)
    (addressWidth outputWidth : Nat) :
    (circuit table addressWidth outputWidth).wellFormed = true := by
  exact rows_wellFormed table addressWidth outputWidth 0 (2 ^ addressWidth)

theorem circuit_act {table : List Nat}
    {addressWidth outputWidth i : Nat}
    (hworkspace :
      Lookup.workspace addressWidth outputWidth (workspaceWidth addressWidth) i = 0) :
    act (circuit table addressWidth outputWidth) i =
      Lookup.xorOutput table addressWidth outputWidth
        (workspaceWidth addressWidth) i := by
  rw [circuit, gates]
  change actGates (rows table addressWidth outputWidth 0 (2 ^ addressWidth)) i = _
  rw [rows_act (by omega) hworkspace, if_pos]
  exact ⟨Nat.zero_le _, by
    simpa [Lookup.address, Lookup.layout, Layout.read, Layout.offset,
      Layout.size] using readField_lt i 0 addressWidth⟩

theorem circuit_correct (table : List Nat)
    (addressWidth outputWidth : Nat) :
    Lookup.CoherentXorLookup table addressWidth outputWidth
      (workspaceWidth addressWidth)
      (circuit table addressWidth outputWidth) := by
  exact ⟨rfl, circuit_wellFormed table addressWidth outputWidth,
    fun _ => circuit_act⟩

theorem selectorGates_length_le (row addressWidth outputWidth : Nat) :
    (selectorGates row addressWidth outputWidth).length ≤
      4 * addressWidth + 1 := by
  rw [selectorGates, List.length_map]
  exact Euclid.Selector.gates_length_le row addressWidth

theorem selectorGates_ccx_le (row addressWidth outputWidth : Nat) :
    (selectorGates row addressWidth outputWidth).countP RGate.isCcx ≤
      2 * addressWidth := by
  rw [selectorGates,
    countP_map_gates (fun gate => RGate.isCcx_map _ gate)]
  exact Euclid.Selector.gates_ccx_le row addressWidth

theorem rowGates_length_le (row word addressWidth outputWidth : Nat) :
    (rowGates row word addressWidth outputWidth).length ≤
      8 * addressWidth + outputWidth + 2 := by
  rw [rowGates, List.length_append, List.length_append, List.length_reverse]
  have hselector := selectorGates_length_le row addressWidth outputWidth
  have hcopy := controlledXorGates_length_le
    (flagWire addressWidth outputWidth) (outputOffset addressWidth) word outputWidth
  omega

theorem rowGates_ccx_le (row word addressWidth outputWidth : Nat) :
    (rowGates row word addressWidth outputWidth).countP RGate.isCcx ≤
      4 * addressWidth := by
  rw [rowGates, List.countP_append, List.countP_append, List.countP_reverse,
    controlledXorGates_ccx]
  have hselector := selectorGates_ccx_le row addressWidth outputWidth
  omega

theorem rows_length_le (table : List Nat) (addressWidth outputWidth start : Nat) :
    ∀ count, (rows table addressWidth outputWidth start count).length ≤
      count * (8 * addressWidth + outputWidth + 2) := by
  intro count
  induction count generalizing start with
  | zero => simp [rows]
  | succ count ih =>
      rw [rows, List.length_append, Nat.succ_mul]
      have hrow := rowGates_length_le start
        (Lookup.value table outputWidth start) addressWidth outputWidth
      have htail := ih (start + 1)
      omega

theorem rows_ccx_le (table : List Nat) (addressWidth outputWidth start : Nat) :
    ∀ count, (rows table addressWidth outputWidth start count).countP RGate.isCcx ≤
      count * (4 * addressWidth) := by
  intro count
  induction count generalizing start with
  | zero => simp [rows]
  | succ count ih =>
      rw [rows, List.countP_append, Nat.succ_mul]
      have hrow := rowGates_ccx_le start
        (Lookup.value table outputWidth start) addressWidth outputWidth
      have htail := ih (start + 1)
      omega

theorem gates_length_le (table : List Nat) (addressWidth outputWidth : Nat) :
    (gates table addressWidth outputWidth).length ≤
      2 ^ addressWidth * (8 * addressWidth + outputWidth + 2) := by
  exact rows_length_le table addressWidth outputWidth 0 (2 ^ addressWidth)

theorem gates_ccx_le (table : List Nat) (addressWidth outputWidth : Nat) :
    (gates table addressWidth outputWidth).countP RGate.isCcx ≤
      2 ^ addressWidth * (4 * addressWidth) := by
  exact rows_ccx_le table addressWidth outputWidth 0 (2 ^ addressWidth)

theorem compiled_toffoli_le (table : List Nat)
    (addressWidth outputWidth : Nat) :
    VQ.Circuit.toffoliCount (compile (circuit table addressWidth outputWidth)) ≤
      2 ^ addressWidth * (4 * addressWidth) := by
  rw [toffoliCount_compile]
  exact gates_ccx_le table addressWidth outputWidth

theorem width_16_512 : width 16 512 = 545 := by
  exact circuitLayout_width 16 512

theorem gates_16_512_length_le (table : List Nat) :
    (gates table 16 512).length ≤ 42074112 := by
  have h := gates_length_le table 16 512
  norm_num at h
  exact h

theorem compiled_16_512_toffoli_le (table : List Nat) :
    VQ.Circuit.toffoliCount (compile (circuit table 16 512)) ≤ 4194304 := by
  have h := compiled_toffoli_le table 16 512
  norm_num at h
  exact h

end VQ.Lookup.Selector
