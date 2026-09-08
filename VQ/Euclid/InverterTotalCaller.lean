import VQ.Euclid.InverterCaller
import VQ.Curve.ReversibleSpec

namespace VQ.Euclid.InverterTotalCaller

open Reversible

structure PreprocessorSpec (prep : List RGate)
    (p n lengthWidth shiftWidth : Nat) : Prop where
  positive : InverterCaller.PreprocessorSpec
    prep p n lengthWidth shiftWidth
  preparesZero :
    actGates prep (InverterCaller.rawInput n lengthWidth shiftWidth 0) =
      InverterCaller.placedState n lengthWidth shiftWidth
        (StepState.encoded n lengthWidth shiftWidth
          (zeroPreparedState p))

def result (p n lengthWidth shiftWidth a : Nat) : Nat :=
  if a = 0 then 0
  else decodedInverse p
    (run lengthWidth shiftWidth (12 * n) (preprocessedState p a))

theorem placedInverterGates_act_zero
    {p n lengthWidth shiftWidth : Nat}
    (hn : 0 < n)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n + 1 < 2 ^ shiftWidth) :
    actGates
        (InverterCaller.placedInverterGates
          (12 * n) n lengthWidth shiftWidth)
        (InverterCaller.placedState n lengthWidth shiftWidth
          (StepState.encoded n lengthWidth shiftWidth
            (zeroPreparedState p))) =
      (InverterCaller.layout n lengthWidth shiftWidth).write
        (InverterCaller.placedState n lengthWidth shiftWidth
          (StepState.encoded n lengthWidth shiftWidth
            (zeroPreparedState p))) 1 0 := by
  let L := InverterCaller.localLayout n lengthWidth shiftWidth
  let W := InverterCaller.wiring n lengthWidth shiftWidth
  let I := InverterCaller.placedState n lengthWidth shiftWidth
    (StepState.encoded n lengthWidth shiftWidth (zeroPreparedState p))
  have hlength : 0 < lengthWidth := by
    by_contra hnot
    have hzero : lengthWidth = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hwork
    simp [workWidth] at hwork
  have hlocalWidth :=
    InverterCaller.localLayout_width n lengthWidth shiftWidth
  have hencoded :
      StepState.encoded n lengthWidth shiftWidth (zeroPreparedState p) <
        2 ^ L.width := by
    have h := StepState.encoded_lt n lengthWidth shiftWidth
      (zeroPreparedState p)
    have hw :
        (StepLayout.layout n lengthWidth shiftWidth).width ≤ L.width := by
      rw [hlocalWidth, Inverter.layout, TerminalCircuit.layout,
        ExtractionPlaced.layout_width]
      simp [ExtractionPlaced.baseWidth]
    exact h.trans_le (Nat.pow_le_pow_right (by omega) hw)
  have hgather :
      gatherBits (place L W) L.width I =
        StepState.encoded n lengthWidth shiftWidth
          (zeroPreparedState p) := by
    exact InverterCaller.gather_placedState hencoded
  have hlocal := Inverter.gates_act_zeroPrepared_linear_schedule
    hn hpFit hwork hwidths hscheduleFit
  have hoff :
      L.offset 2 =
        ExtractionPlaced.outputOffset n lengthWidth shiftWidth := by
    simpa [L, InverterCaller.localLayout,
      InverterCaller.workspaceWidth, InverterCaller.baseWidth,
      ExtractionPlaced.outputOffset, Layout.offset] using
      Nat.add_sub_of_le
        (InverterCaller.source_le_base n lengthWidth shiftWidth)
  have hsize : L.size 2 = n := by
    rfl
  have hlocalAction :
      actGates (Inverter.gates (12 * n) n lengthWidth shiftWidth)
          (gatherBits (place L W) L.width I) =
        L.write (gatherBits (place L W) L.width I) 2 0 := by
    rw [hgather]
    simpa only [Layout.write, hoff, hsize] using hlocal
  have hplaced := actGates_placed_write
    (L := L) (W := W) (k := 2)
    (InverterCaller.wiring_disjoint n lengthWidth shiftWidth)
    (by simp [L, W, InverterCaller.localLayout, InverterCaller.wiring])
    (by simp [L, InverterCaller.localLayout])
    (fun g hg => by
      rw [hlocalWidth]
      exact List.all_eq_true.mp
        (Inverter.gates_wellFormed
          (rounds := 12 * n) (n := n) hlength hwidths) g hg)
    hlocalAction
  change actGates
      ((Inverter.gates (12 * n) n lengthWidth shiftWidth).map
        (RGate.map (place L W))) I =
    writeField I n n 0
  exact hplaced

theorem gates_act_zero
    {prep : List RGate} {p n lengthWidth shiftWidth : Nat}
    (hprep : PreprocessorSpec prep p n lengthWidth shiftWidth)
    (hn : 0 < n)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n + 1 < 2 ^ shiftWidth) :
    actGates
        (InverterCaller.gates prep (12 * n) n lengthWidth shiftWidth)
        (InverterCaller.rawInput n lengthWidth shiftWidth 0) =
      (InverterCaller.layout n lengthWidth shiftWidth).write
        (InverterCaller.rawInput n lengthWidth shiftWidth 0) 1 0 := by
  have hplaced := placedInverterGates_act_zero
    hn hpFit hwork hwidths hscheduleFit
  have hreverseOutside :
      ∀ g ∈ prep.reverse, ∀ q ∈ g.wires, q < n ∨ 2 * n ≤ q := by
    intro g hg
    exact hprep.positive.avoidsOutput g (List.mem_reverse.mp hg)
  rw [InverterCaller.gates, actGates_append, actGates_append,
    hprep.preparesZero, hplaced]
  change actGates prep.reverse
      (writeField
        (InverterCaller.placedState n lengthWidth shiftWidth
          (StepState.encoded n lengthWidth shiftWidth
            (zeroPreparedState p))) n n 0) =
    writeField (InverterCaller.rawInput n lengthWidth shiftWidth 0) n n 0
  have hreverseOutside' :
      ∀ g ∈ prep.reverse, ∀ q ∈ g.wires, q < n ∨ n + n ≤ q := by
    simpa [two_mul] using hreverseOutside
  rw [actGates_write_of_outside hreverseOutside']
  rw [← hprep.preparesZero,
    actGates_reverse hprep.positive.wellFormed]

theorem gates_act_positive
    {prep : List RGate} {p a n lengthWidth shiftWidth : Nat}
    (hprep : PreprocessorSpec prep p n lengthWidth shiftWidth)
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n + 1 < 2 ^ shiftWidth)
    (ha0 : 0 < a)
    (ha : a < p) :
    actGates
        (InverterCaller.gates prep (12 * n) n lengthWidth shiftWidth)
        (InverterCaller.rawInput n lengthWidth shiftWidth a) =
      (InverterCaller.layout n lengthWidth shiftWidth).write
        (InverterCaller.rawInput n lengthWidth shiftWidth a) 1
        (result p n lengthWidth shiftWidth a) := by
  have hfit : 12 * n < 2 ^ shiftWidth := by omega
  have h := InverterCaller.gates_act_preprocessed_linear_schedule
    hprep.positive hpPrime hpFit hwork hwidths hfit ha0 ha
  simpa [result, Nat.ne_of_gt ha0] using h

theorem gates_act
    {prep : List RGate} {p a n lengthWidth shiftWidth : Nat}
    (hprep : PreprocessorSpec prep p n lengthWidth shiftWidth)
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n + 1 < 2 ^ shiftWidth)
    (ha : a < p) :
    actGates
        (InverterCaller.gates prep (12 * n) n lengthWidth shiftWidth)
        (InverterCaller.rawInput n lengthWidth shiftWidth a) =
      (InverterCaller.layout n lengthWidth shiftWidth).write
        (InverterCaller.rawInput n lengthWidth shiftWidth a) 1
        (result p n lengthWidth shiftWidth a) := by
  have hn : 0 < n := by
    by_contra hnot
    have hnZero : n = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hnZero] at hpFit
    simp only [pow_zero] at hpFit
    omega
  by_cases ha0 : a = 0
  · subst a
    simpa [result] using gates_act_zero
      hprep hn hpFit hwork hwidths hscheduleFit
  · exact gates_act_positive hprep hpPrime hpFit hwork hwidths
      hscheduleFit (Nat.pos_of_ne_zero ha0) ha

theorem result_lt
    {p a n lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n + 1 < 2 ^ shiftWidth)
    (ha : a < p) :
    result p n lengthWidth shiftWidth a < p := by
  by_cases ha0 : a = 0
  · simp [result, ha0, hpPrime.pos]
  · have hfit : 12 * n < 2 ^ shiftWidth := by omega
    have hspec := Inverter.circuit_spec_preprocessed_linear_schedule
      hpPrime hpFit hwork hwidths hfit (Nat.pos_of_ne_zero ha0) ha
    simpa [result, ha0] using hspec.2.1

theorem result_modEq
    {p a n lengthWidth shiftWidth : Nat}
    (hpPrime : p.Prime)
    (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n + 1 < 2 ^ shiftWidth)
    (ha0 : 0 < a)
    (ha : a < p) :
    a * result p n lengthWidth shiftWidth a ≡ 1 [MOD p] := by
  have hfit : 12 * n < 2 ^ shiftWidth := by omega
  have hspec := Inverter.circuit_spec_preprocessed_linear_schedule
    hpPrime hpFit hwork hwidths hfit ha0 ha
  simpa [result, Nat.ne_of_gt ha0] using hspec.2.2

theorem eq_rawInput_of_reads
    {i a n lengthWidth shiftWidth : Nat}
    (hi : i < 2 ^ (InverterCaller.layout n lengthWidth shiftWidth).width)
    (ha : a < 2 ^ n)
    (hsource :
      (InverterCaller.layout n lengthWidth shiftWidth).read i 0 = a)
    (houtput :
      (InverterCaller.layout n lengthWidth shiftWidth).read i 1 = 0)
    (hworkspace :
      (InverterCaller.layout n lengthWidth shiftWidth).read i 2 = 0) :
    i = InverterCaller.rawInput n lengthWidth shiftWidth a := by
  let L := InverterCaller.layout n lengthWidth shiftWidth
  apply Layout.ext hi (Layout.pack_lt L [a, 0, 0])
  intro k hk
  have hk3 : k < 3 := by
    simpa [L, InverterCaller.layout] using hk
  interval_cases k
  · rw [hsource]
    change a = L.read (L.pack [a, 0, 0]) 0
    rw [Layout.read_pack]
    change a = a % 2 ^ n
    exact (Nat.mod_eq_of_lt ha).symm
  · rw [houtput]
    change 0 = L.read (L.pack [a, 0, 0]) 1
    rw [Layout.read_pack]
    simp
  · rw [hworkspace]
    change 0 = L.read (L.pack [a, 0, 0]) 2
    rw [Layout.read_pack]
    simp

theorem result_eq_curveInv
    {a n lengthWidth shiftWidth : Nat}
    (hinverse : Curve.InverseLaw)
    (hpPrime : Curve.p.Prime)
    (hpFit : Curve.p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n + 1 < 2 ^ shiftWidth)
    (ha : a < Curve.p) :
    result Curve.p n lengthWidth shiftWidth a = Curve.inv a := by
  by_cases ha0 : a = 0
  · subst a
    rw [result, if_pos rfl, Curve.inv, Curve.powMod_eq]
    rw [Nat.zero_pow (show 0 < Curve.p - 2 by decide), Nat.zero_mod]
  · have hresultLt := result_lt hpPrime hpFit hwork hwidths
      hscheduleFit ha
    have hmodEq := result_modEq hpPrime hpFit hwork hwidths
      hscheduleFit (Nat.pos_of_ne_zero ha0) ha
    have hresultMul :
        Curve.mul a (result Curve.p n lengthWidth shiftWidth a) = 1 := by
      simpa [Curve.mul, Nat.ModEq, Nat.mod_eq_of_lt
        (show 1 < Curve.p by decide)] using hmodEq
    have hinvMul := hinverse a ha ha0
    calc
      result Curve.p n lengthWidth shiftWidth a =
          Curve.mul (result Curve.p n lengthWidth shiftWidth a) 1 :=
        (Curve.mul_one hresultLt).symm
      _ = Curve.mul (result Curve.p n lengthWidth shiftWidth a)
          (Curve.mul (Curve.inv a) a) := by rw [hinvMul]
      _ = Curve.mul
          (Curve.mul (result Curve.p n lengthWidth shiftWidth a)
            (Curve.inv a)) a := (Curve.mul_assoc _ _ _).symm
      _ = Curve.mul
          (Curve.mul (Curve.inv a)
            (result Curve.p n lengthWidth shiftWidth a)) a := by
        rw [Curve.mul_comm
          (result Curve.p n lengthWidth shiftWidth a) (Curve.inv a)]
      _ = Curve.mul (Curve.inv a)
          (Curve.mul (result Curve.p n lengthWidth shiftWidth a) a) :=
        Curve.mul_assoc _ _ _
      _ = Curve.mul (Curve.inv a)
          (Curve.mul a (result Curve.p n lengthWidth shiftWidth a)) := by
        rw [Curve.mul_comm
          (result Curve.p n lengthWidth shiftWidth a) a]
      _ = Curve.mul (Curve.inv a) 1 := by rw [hresultMul]
      _ = Curve.inv a := Curve.mul_one (Curve.inv_lt a)

theorem invertsField
    {prep : List RGate} {n lengthWidth shiftWidth : Nat}
    (hprep : PreprocessorSpec
      prep Curve.p n lengthWidth shiftWidth)
    (hinverse : Curve.InverseLaw)
    (hpPrime : Curve.p.Prime)
    (hpFit : Curve.p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth)
    (hwidths : lengthWidth ≤ shiftWidth)
    (hscheduleFit : 12 * n + 1 < 2 ^ shiftWidth) :
    InvertsField (InverterCaller.workspaceWidth n lengthWidth shiftWidth) n
      (InverterCaller.circuit prep (12 * n) n lengthWidth shiftWidth) := by
  intro a i hi hsource houtput hworkspace _hp ha
  have hi' :
      i < 2 ^ (InverterCaller.layout n lengthWidth shiftWidth).width := by
    simpa [InverterCaller.layout, unaryLayout] using hi
  have hsource' :
      (InverterCaller.layout n lengthWidth shiftWidth).read i 0 = a := by
    simpa [InverterCaller.layout, unaryLayout] using hsource
  have houtput' :
      (InverterCaller.layout n lengthWidth shiftWidth).read i 1 = 0 := by
    simpa [InverterCaller.layout, unaryLayout] using houtput
  have hworkspace' :
      (InverterCaller.layout n lengthWidth shiftWidth).read i 2 = 0 := by
    simpa [InverterCaller.layout, unaryLayout] using hworkspace
  have haFit : a < 2 ^ n := ha.trans hpFit
  have hiRaw := eq_rawInput_of_reads
    hi' haFit hsource' houtput' hworkspace'
  have haction := gates_act hprep hpPrime hpFit hwork hwidths
    hscheduleFit ha
  have hvalue := result_eq_curveInv hinverse hpPrime hpFit hwork hwidths
    hscheduleFit ha
  subst i
  simpa [InverterCaller.circuit, Reversible.act, hvalue,
    InverterCaller.layout, unaryLayout] using haction

end VQ.Euclid.InverterTotalCaller
