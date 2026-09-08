import VQ.Euclid.Inverter
import Mathlib.Tactic.IntervalCases

namespace VQ.Euclid.InverterCaller

open Reversible

def baseWidth (n lengthWidth shiftWidth : Nat) : Nat :=
  ExtractionPlaced.baseWidth n lengthWidth shiftWidth

def workspaceWidth (n lengthWidth shiftWidth : Nat) : Nat :=
  baseWidth n lengthWidth shiftWidth - n

def localLayout (n lengthWidth shiftWidth : Nat) : Layout :=
  [n, workspaceWidth n lengthWidth shiftWidth, n]

def layout (n lengthWidth shiftWidth : Nat) : Layout :=
  [n, n, workspaceWidth n lengthWidth shiftWidth]

def wiring (n _lengthWidth _shiftWidth : Nat) : Wiring :=
  [0, 2 * n, n]

def rawInput (n lengthWidth shiftWidth a : Nat) : Nat :=
  (layout n lengthWidth shiftWidth).pack [a, 0, 0]

def placedState (n lengthWidth shiftWidth i : Nat) : Nat :=
  (layout n lengthWidth shiftWidth).pack
    [(localLayout n lengthWidth shiftWidth).read i 0,
      (localLayout n lengthWidth shiftWidth).read i 2,
      (localLayout n lengthWidth shiftWidth).read i 1]

def placedInverterGates
    (rounds n lengthWidth shiftWidth : Nat) : List RGate :=
  (Inverter.gates rounds n lengthWidth shiftWidth).map
    (RGate.map (place (localLayout n lengthWidth shiftWidth)
      (wiring n lengthWidth shiftWidth)))

def gates (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) : List RGate :=
  prep ++ placedInverterGates rounds n lengthWidth shiftWidth ++ prep.reverse

def circuit (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) : RCircuit :=
  { width := (layout n lengthWidth shiftWidth).width,
    gates := gates prep rounds n lengthWidth shiftWidth }

structure PreprocessorSpec (prep : List RGate)
    (p n lengthWidth shiftWidth : Nat) : Prop where
  wellFormed : prep.all
    (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true
  avoidsOutput : ∀ g ∈ prep, ∀ q ∈ g.wires, q < n ∨ 2 * n ≤ q
  prepares : ∀ {a : Nat}, 0 < a → a < p →
    actGates prep (rawInput n lengthWidth shiftWidth a) =
      placedState n lengthWidth shiftWidth
        (StepState.encoded n lengthWidth shiftWidth
          (preprocessedState p a))

theorem source_le_base (n lengthWidth shiftWidth : Nat) :
    n ≤ baseWidth n lengthWidth shiftWidth := by
  simp [baseWidth, ExtractionPlaced.baseWidth, StepLayout.layout,
    VQ.Euclid.layout, Layout.width, workWidth]
  omega

theorem localLayout_width (n lengthWidth shiftWidth : Nat) :
    (localLayout n lengthWidth shiftWidth).width =
      (Inverter.layout n lengthWidth shiftWidth).width := by
  have hbase := source_le_base n lengthWidth shiftWidth
  rw [Inverter.layout, TerminalCircuit.layout,
    ExtractionPlaced.layout_width]
  simp [localLayout, workspaceWidth, baseWidth, Layout.width]
  change n ≤ ExtractionPlaced.baseWidth n lengthWidth shiftWidth at hbase
  omega

theorem layout_width (n lengthWidth shiftWidth : Nat) :
    (layout n lengthWidth shiftWidth).width =
      (Inverter.layout n lengthWidth shiftWidth).width := by
  have hbase := source_le_base n lengthWidth shiftWidth
  rw [Inverter.layout, TerminalCircuit.layout,
    ExtractionPlaced.layout_width]
  simp [layout, workspaceWidth, baseWidth, Layout.width]
  change n ≤ ExtractionPlaced.baseWidth n lengthWidth shiftWidth at hbase
  omega

theorem wiring_disjoint (n lengthWidth shiftWidth : Nat) :
    Wiring.Disjoint (localLayout n lengthWidth shiftWidth)
      (wiring n lengthWidth shiftWidth) := by
  have hbase := source_le_base n lengthWidth shiftWidth
  intro j k hj hk hne
  simp [wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [localLayout, wiring, workspaceWidth, Layout.size] <;>
    omega

theorem wiring_bound (n lengthWidth shiftWidth : Nat) :
    ∀ j, j < (localLayout n lengthWidth shiftWidth).length →
      (wiring n lengthWidth shiftWidth).getD j 0 +
          (localLayout n lengthWidth shiftWidth).size j ≤
        (layout n lengthWidth shiftWidth).width := by
  have hbase := source_le_base n lengthWidth shiftWidth
  intro j hj
  simp [localLayout] at hj
  interval_cases j <;>
    simp_all [localLayout, layout, wiring, workspaceWidth, Layout.size,
      Layout.width]
  all_goals omega

theorem gather_placedState
    {n lengthWidth shiftWidth i : Nat}
    (hi : i < 2 ^ (localLayout n lengthWidth shiftWidth).width) :
    gatherBits
        (place (localLayout n lengthWidth shiftWidth)
          (wiring n lengthWidth shiftWidth))
        (localLayout n lengthWidth shiftWidth).width
        (placedState n lengthWidth shiftWidth i) = i := by
  let L := localLayout n lengthWidth shiftWidth
  let W := wiring n lengthWidth shiftWidth
  let E := layout n lengthWidth shiftWidth
  apply Layout.ext (gatherBits_lt _ _ _) hi
  intro k hk
  have hkW : k < W.length := by
    simpa [L, W, localLayout, wiring] using hk
  rw [read_gatherBits L W k _ hkW]
  have hk3 : k < 3 := by
    simpa [L, localLayout] using hk
  interval_cases k
  · change readField (placedState n lengthWidth shiftWidth i) 0 n = L.read i 0
    change E.read (placedState n lengthWidth shiftWidth i) 0 = L.read i 0
    rw [show placedState n lengthWidth shiftWidth i =
      E.pack [L.read i 0, L.read i 2, L.read i 1] by rfl,
      Layout.read_pack]
    change L.read i 0 % 2 ^ n = L.read i 0
    exact Nat.mod_eq_of_lt (by
      simpa [L, localLayout, Layout.size] using Layout.read_lt L i 0)
  · change readField (placedState n lengthWidth shiftWidth i)
      (2 * n) (workspaceWidth n lengthWidth shiftWidth) = L.read i 1
    rw [show 2 * n = n + n by omega]
    change E.read (placedState n lengthWidth shiftWidth i) 2 = L.read i 1
    rw [show placedState n lengthWidth shiftWidth i =
      E.pack [L.read i 0, L.read i 2, L.read i 1] by rfl,
      Layout.read_pack]
    change L.read i 1 % 2 ^ workspaceWidth n lengthWidth shiftWidth =
      L.read i 1
    exact Nat.mod_eq_of_lt (by
      simpa [L, localLayout, Layout.size] using Layout.read_lt L i 1)
  · change readField (placedState n lengthWidth shiftWidth i) n n = L.read i 2
    change E.read (placedState n lengthWidth shiftWidth i) 1 = L.read i 2
    rw [show placedState n lengthWidth shiftWidth i =
      E.pack [L.read i 0, L.read i 2, L.read i 1] by rfl,
      Layout.read_pack]
    change L.read i 2 % 2 ^ n = L.read i 2
    exact Nat.mod_eq_of_lt (by
      simpa [L, localLayout, Layout.size] using Layout.read_lt L i 2)

theorem placedInverterGates_wellFormed
    {rounds n lengthWidth shiftWidth : Nat}
    (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    (placedInverterGates rounds n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  apply wellFormed_placeGates
    (wiring_disjoint n lengthWidth shiftWidth)
    (by simp [localLayout, wiring])
    (wiring_bound n lengthWidth shiftWidth)
  intro g hg
  have h := List.all_eq_true.mp
    (Inverter.gates_wellFormed
      (rounds := rounds) (n := n) hlength hwidths) g hg
  simpa only [localLayout_width] using h

set_option maxHeartbeats 3000000 in
theorem placedInverterGates_act_preprocessed_linear_schedule
    {p a n lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n < 2 ^ shiftWidth)
    (ha0 : 0 < a)
    (ha : a < p) :
    let final := run lengthWidth shiftWidth (12 * n)
      (preprocessedState p a)
    actGates (placedInverterGates (12 * n) n lengthWidth shiftWidth)
        (placedState n lengthWidth shiftWidth
          (StepState.encoded n lengthWidth shiftWidth
            (preprocessedState p a))) =
      (layout n lengthWidth shiftWidth).write
        (placedState n lengthWidth shiftWidth
          (StepState.encoded n lengthWidth shiftWidth
            (preprocessedState p a))) 1
        (decodedInverse p final) := by
  dsimp only
  let L := localLayout n lengthWidth shiftWidth
  let W := wiring n lengthWidth shiftWidth
  let I := placedState n lengthWidth shiftWidth
    (StepState.encoded n lengthWidth shiftWidth (preprocessedState p a))
  have hlength : 0 < lengthWidth := by
    by_contra hnot
    have hzero : lengthWidth = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hwork
    simp [workWidth] at hwork
  have hlocalWidth := localLayout_width n lengthWidth shiftWidth
  have hencoded :
      StepState.encoded n lengthWidth shiftWidth (preprocessedState p a) <
        2 ^ L.width := by
    have h := StepState.encoded_lt n lengthWidth shiftWidth
      (preprocessedState p a)
    have hw :
        (StepLayout.layout n lengthWidth shiftWidth).width ≤ L.width := by
      rw [hlocalWidth, Inverter.layout, TerminalCircuit.layout,
        ExtractionPlaced.layout_width]
      simp [ExtractionPlaced.baseWidth]
    exact h.trans_le (Nat.pow_le_pow_right (by omega) hw)
  have hgather :
      gatherBits (place L W) L.width I =
        StepState.encoded n lengthWidth shiftWidth
          (preprocessedState p a) := by
    exact gather_placedState hencoded
  have hlocal := Inverter.gates_act_preprocessed_linear_schedule
    hpPrime hpFit hwork hwidths hscheduleFit ha0 ha
  have hoff :
      L.offset 2 =
        ExtractionPlaced.outputOffset n lengthWidth shiftWidth := by
    simpa [L, localLayout, workspaceWidth, baseWidth,
      ExtractionPlaced.outputOffset, Layout.offset] using
      Nat.add_sub_of_le (source_le_base n lengthWidth shiftWidth)
  have hsize : L.size 2 = n := by
    rfl
  have hlocalAction :
      actGates (Inverter.gates (12 * n) n lengthWidth shiftWidth)
          (gatherBits (place L W) L.width I) =
        L.write (gatherBits (place L W) L.width I) 2
          (decodedInverse p
            (run lengthWidth shiftWidth (12 * n)
              (preprocessedState p a))) := by
    rw [hgather]
    simpa only [Layout.write, hoff, hsize] using hlocal
  have hplaced := actGates_placed_write
    (L := L) (W := W) (k := 2)
    (wiring_disjoint n lengthWidth shiftWidth)
    (by simp [L, W, localLayout, wiring])
    (by simp [L, localLayout])
    (fun g hg => by
      rw [hlocalWidth]
      exact List.all_eq_true.mp
        (Inverter.gates_wellFormed
          (rounds := 12 * n) (n := n) hlength hwidths) g hg)
    hlocalAction
  change actGates
      ((Inverter.gates (12 * n) n lengthWidth shiftWidth).map
        (RGate.map (place L W))) I =
    writeField I n n
      (decodedInverse p
        (run lengthWidth shiftWidth (12 * n) (preprocessedState p a)))
  exact hplaced

theorem gates_act_preprocessed_linear_schedule
    {prep : List RGate} {p a n lengthWidth shiftWidth : Nat}
    (hprep : PreprocessorSpec prep p n lengthWidth shiftWidth)
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n < 2 ^ shiftWidth)
    (ha0 : 0 < a)
    (ha : a < p) :
    let final := run lengthWidth shiftWidth (12 * n)
      (preprocessedState p a)
    actGates (gates prep (12 * n) n lengthWidth shiftWidth)
        (rawInput n lengthWidth shiftWidth a) =
      (layout n lengthWidth shiftWidth).write
        (rawInput n lengthWidth shiftWidth a) 1
        (decodedInverse p final) := by
  dsimp only
  have hplaced := placedInverterGates_act_preprocessed_linear_schedule
    hpPrime hpFit hwork hwidths hscheduleFit ha0 ha
  have hreverseOutside :
      ∀ g ∈ prep.reverse, ∀ q ∈ g.wires, q < n ∨ 2 * n ≤ q := by
    intro g hg
    exact hprep.avoidsOutput g (List.mem_reverse.mp hg)
  rw [gates, actGates_append, actGates_append,
    hprep.prepares ha0 ha, hplaced]
  change actGates prep.reverse
      (writeField
        (placedState n lengthWidth shiftWidth
          (StepState.encoded n lengthWidth shiftWidth
            (preprocessedState p a))) n n
        (decodedInverse p
          (run lengthWidth shiftWidth (12 * n) (preprocessedState p a)))) =
    writeField (rawInput n lengthWidth shiftWidth a) n n
      (decodedInverse p
        (run lengthWidth shiftWidth (12 * n) (preprocessedState p a)))
  have hreverseOutside' :
      ∀ g ∈ prep.reverse, ∀ q ∈ g.wires, q < n ∨ n + n ≤ q := by
    simpa [two_mul] using hreverseOutside
  rw [actGates_write_of_outside hreverseOutside']
  rw [← hprep.prepares ha0 ha, actGates_reverse hprep.wellFormed]

theorem circuit_spec_preprocessed_linear_schedule
    {prep : List RGate} {p a n lengthWidth shiftWidth : Nat}
    (hprep : PreprocessorSpec prep p n lengthWidth shiftWidth)
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n < 2 ^ shiftWidth)
    (ha0 : 0 < a)
    (ha : a < p) :
    let final := run lengthWidth shiftWidth (12 * n)
      (preprocessedState p a)
    act (circuit prep (12 * n) n lengthWidth shiftWidth)
        (rawInput n lengthWidth shiftWidth a) =
          (layout n lengthWidth shiftWidth).write
            (rawInput n lengthWidth shiftWidth a) 1
            (decodedInverse p final) ∧
      decodedInverse p final < p ∧
      a * decodedInverse p final ≡ 1 [MOD p] := by
  dsimp only
  have haction := gates_act_preprocessed_linear_schedule
    hprep hpPrime hpFit hwork hwidths hscheduleFit ha0 ha
  have hresult := Inverter.circuit_spec_preprocessed_linear_schedule
    hpPrime hpFit hwork hwidths hscheduleFit ha0 ha
  exact ⟨by simpa [circuit, Reversible.act] using haction,
    hresult.2.1, hresult.2.2⟩

theorem gates_wellFormed
    {prep : List RGate} {p rounds n lengthWidth shiftWidth : Nat}
    (hprep : PreprocessorSpec prep p n lengthWidth shiftWidth)
    (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    (gates prep rounds n lengthWidth shiftWidth).all
      (RGate.wellFormed (layout n lengthWidth shiftWidth).width) = true := by
  have hplaced := placedInverterGates_wellFormed
    (rounds := rounds) (n := n) hlength hwidths
  simp [gates, hprep.wellFormed, hplaced, List.all_reverse]

theorem circuit_wellFormed
    {prep : List RGate} {p rounds n lengthWidth shiftWidth : Nat}
    (hprep : PreprocessorSpec prep p n lengthWidth shiftWidth)
    (hlength : 0 < lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth) :
    (circuit prep rounds n lengthWidth shiftWidth).wellFormed = true :=
  gates_wellFormed hprep hlength hwidths

theorem gates_length (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (gates prep rounds n lengthWidth shiftWidth).length =
      2 * prep.length +
        (Inverter.gates rounds n lengthWidth shiftWidth).length := by
  simp [gates, placedInverterGates]
  omega

theorem gates_ccx (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (gates prep rounds n lengthWidth shiftWidth).countP RGate.isCcx =
      2 * prep.countP RGate.isCcx +
        (Inverter.gates rounds n lengthWidth shiftWidth).countP RGate.isCcx := by
  simp [gates, placedInverterGates,
    countP_map_gates (fun g => RGate.isCcx_map _ g)]
  omega

theorem gates_cx (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (gates prep rounds n lengthWidth shiftWidth).countP RGate.isCx =
      2 * prep.countP RGate.isCx +
        (Inverter.gates rounds n lengthWidth shiftWidth).countP RGate.isCx := by
  simp [gates, placedInverterGates,
    countP_map_gates (fun g => RGate.isCx_map _ g)]
  omega

theorem gates_length_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (gates prep rounds n lengthWidth shiftWidth).length ≤
      2 * prep.length +
        (2 * (rounds * StepResources.gateBound n lengthWidth shiftWidth) +
          (2 * (Increment.lengthCost shiftWidth + 2 +
            3 * workWidth n * shiftWidth) + n + (11 * n + 4))) := by
  rw [gates_length]
  exact Nat.add_le_add_left
    (Inverter.gates_length_le rounds n lengthWidth shiftWidth) _

theorem gates_ccx_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (gates prep rounds n lengthWidth shiftWidth).countP RGate.isCcx ≤
      2 * prep.countP RGate.isCcx +
        (2 * (rounds * StepResources.ccxBound n lengthWidth shiftWidth) +
          (2 * (Increment.ccxCost shiftWidth + workWidth n * shiftWidth) +
            10 * n)) := by
  rw [gates_ccx]
  exact Nat.add_le_add_left
    (Inverter.gates_ccx_le rounds n lengthWidth shiftWidth) _

theorem gates_cx_le (prep : List RGate)
    (rounds n lengthWidth shiftWidth : Nat) :
    (gates prep rounds n lengthWidth shiftWidth).countP RGate.isCx ≤
      2 * prep.countP RGate.isCx +
        (2 * (rounds * StepResources.cxBound n lengthWidth shiftWidth) +
          (2 * (Increment.cxCost shiftWidth +
            2 * workWidth n * shiftWidth) + n + (7 * n + 2))) := by
  rw [gates_cx]
  exact Nat.add_le_add_left
    (Inverter.gates_cx_le rounds n lengthWidth shiftWidth) _

end VQ.Euclid.InverterCaller
