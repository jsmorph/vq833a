import VQMathlib.ECDLP.FourierPlacement.Basic

namespace VQ.Tests.ECDLPQFTPlacement

open Algebra Semantics

theorem testBit_div_prefix (offset q i : Nat) :
    (i / 2 ^ offset).testBit q = i.testBit (offset + q) := by
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

theorem xor_mod_prefix (offset q i : Nat) :
    (i ^^^ (1 <<< (offset + q))) % 2 ^ offset = i % 2 ^ offset := by
  rw [Nat.xor_mod_two_pow]
  simp [Nat.one_shiftLeft, Nat.pow_add]

theorem xor_div_prefix (offset q i : Nat) :
    (i ^^^ (1 <<< (offset + q))) / 2 ^ offset =
      i / 2 ^ offset ^^^ (1 <<< q) := by
  rw [Nat.xor_div_two_pow]
  simp [Nat.one_shiftLeft, Nat.pow_add]

theorem cxIndex_mod_prefix (offset ctrl target i : Nat) :
    cxIndex (offset + ctrl) (offset + target) i % 2 ^ offset =
      i % 2 ^ offset := by
  simp only [cxIndex]
  split
  · exact xor_mod_prefix offset target i
  · rfl

theorem cxIndex_div_prefix (offset ctrl target i : Nat) :
    cxIndex (offset + ctrl) (offset + target) i / 2 ^ offset =
      cxIndex ctrl target (i / 2 ^ offset) := by
  simp only [cxIndex]
  rw [testBit_div_prefix offset ctrl i]
  split
  · exact xor_div_prefix offset target i
  · rfl

theorem gate_map_shift_comp (outer inner : Nat) (g : Gate) :
    (g.map (shiftWire inner)).map (shiftWire outer) =
      g.map (shiftWire (outer + inner)) := by
  cases g <;> simp [Gate.map, shiftWire, Nat.add_assoc]

theorem gates_map_shift_comp (outer inner : Nat) (gates : List Gate) :
    (gates.map (Gate.map (shiftWire inner))).map
        (Gate.map (shiftWire outer)) =
      gates.map (Gate.map (shiftWire (outer + inner))) := by
  induction gates with
  | nil => rfl
  | cons g gates ih =>
      simp only [List.map_cons, gate_map_shift_comp, ih]

theorem mul_mul_swap (a b c : Dy d) :
    a * (b * c) = b * (a * c) := by
  rw [← Dy.mul_assoc, Dy.mul_comm a b, Dy.mul_assoc]

theorem mul_factor_add (a b c d : Dy e) :
    a * (b * c + b * d) = b * (a * (c + d)) := by
  calc
    a * (b * c + b * d) = a * (b * c) + a * (b * d) :=
      Dy.left_distrib _ _ _
    _ = b * (a * c) + b * (a * d) := by
      congr 1
      · exact mul_mul_swap _ _ _
      · exact mul_mul_swap _ _ _
    _ = b * (a * c + a * d) := (Dy.left_distrib _ _ _).symm
    _ = b * (a * (c + d)) :=
      congrArg (fun x => b * x) (Dy.left_distrib a c d).symm

theorem mul_factor_sub (a b c d : Dy e) :
    a * (b * c - b * d) = b * (a * (c - d)) := by
  calc
    a * (b * c - b * d) = a * (b * c) - a * (b * d) :=
      Semantics.mul_sub _ _ _
    _ = b * (a * c) - b * (a * d) := by
      congr 1
      · exact mul_mul_swap _ _ _
      · exact mul_mul_swap _ _ _
    _ = b * (a * c - a * d) := (Semantics.mul_sub _ _ _).symm
    _ = b * (a * (c - d)) :=
      congrArg (fun x => b * x) (Semantics.mul_sub a c d).symm

theorem gateVec_join_right {level offset activeWidth scratch : Nat} {g : Gate}
    (hg : g.wellFormedAt level activeWidth = true)
    (prefixState active : Vec (deg level)) :
    gateVec level (offset + activeWidth + scratch)
        (g.map (shiftWire offset))
        (RegisterState.join offset activeWidth scratch prefixState active) =
      RegisterState.join offset activeWidth scratch prefixState
        (gateVec level activeWidth g active) := by
  have hgShiftActive :
      (g.map (shiftWire offset)).wellFormedAt
        level (offset + activeWidth) = true := by
    apply gate_map_wellFormedAt
      (sourceWidth := activeWidth)
      (targetWidth := offset + activeWidth)
      (f := shiftWire offset)
    · intro q hq
      simp [shiftWire]
      omega
    · intro a b ha hb hab
      simp [shiftWire] at hab
      omega
    · exact hg
  have hgShiftTotal :
      (g.map (shiftWire offset)).wellFormedAt
        level (offset + activeWidth + scratch) = true := by
    apply gate_map_wellFormedAt
      (sourceWidth := activeWidth)
      (targetWidth := offset + activeWidth + scratch)
      (f := shiftWire offset)
    · intro q hq
      simp [shiftWire]
      omega
    · intro a b ha hb hab
      simp [shiftWire] at hab
      omega
    · exact hg
  apply Vec.ext
  intro i
  by_cases hi : i < 2 ^ (offset + activeWidth)
  · rw [RegisterState.join_apply_of_lt hi,
      gateVec_of_wf hgShiftTotal, gateVec_of_wf hg]
    cases g with
    | h q =>
        have hq : q < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        have hxor : i ^^^ (1 <<< (offset + q)) <
            2 ^ (offset + activeWidth) := by
          apply Nat.xor_lt_two_pow hi
          rw [Nat.one_shiftLeft]
          exact Nat.pow_lt_pow_of_lt (by omega) (by omega)
        simp only [Gate.map, shiftWire, gateAction, hVec]
        rw [← testBit_div_prefix offset q i]
        split
        · rw [RegisterState.join_apply_of_lt hxor,
            RegisterState.join_apply_of_lt hi,
            xor_mod_prefix, xor_div_prefix]
          exact mul_factor_sub _ _ _ _
        · rw [RegisterState.join_apply_of_lt hi,
            RegisterState.join_apply_of_lt hxor,
            xor_mod_prefix, xor_div_prefix]
          exact mul_factor_add _ _ _ _
    | x q =>
        have hq : q < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        have hxor : i ^^^ (1 <<< (offset + q)) <
            2 ^ (offset + activeWidth) := by
          apply Nat.xor_lt_two_pow hi
          rw [Nat.one_shiftLeft]
          exact Nat.pow_lt_pow_of_lt (by omega) (by omega)
        simp only [Gate.map, shiftWire, gateAction, flipVec]
        rw [RegisterState.join_apply_of_lt hxor,
          xor_mod_prefix, xor_div_prefix]
    | y q =>
        have hq : q < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        have hxor : i ^^^ (1 <<< (offset + q)) <
            2 ^ (offset + activeWidth) := by
          apply Nat.xor_lt_two_pow hi
          rw [Nat.one_shiftLeft]
          exact Nat.pow_lt_pow_of_lt (by omega) (by omega)
        simp only [Gate.map, shiftWire, gateAction, yVec]
        rw [← testBit_div_prefix offset q i,
          RegisterState.join_apply_of_lt hxor,
          xor_mod_prefix, xor_div_prefix]
        exact mul_mul_swap _ _ _
    | z q =>
        have hq : q < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        simp only [Gate.map, shiftWire, gateAction, diagVec]
        rw [← testBit_div_prefix offset q i]
        split
        · rw [RegisterState.join_apply_of_lt hi]
          exact mul_mul_swap _ _ _
        · rw [RegisterState.join_apply_of_lt hi]
    | s q =>
        have hq : q < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        simp only [Gate.map, shiftWire, gateAction, diagVec]
        rw [← testBit_div_prefix offset q i]
        split
        · rw [RegisterState.join_apply_of_lt hi]
          exact mul_mul_swap _ _ _
        · rw [RegisterState.join_apply_of_lt hi]
    | sdg q =>
        have hq : q < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        simp only [Gate.map, shiftWire, gateAction, diagVec]
        rw [← testBit_div_prefix offset q i]
        split
        · rw [RegisterState.join_apply_of_lt hi]
          exact mul_mul_swap _ _ _
        · rw [RegisterState.join_apply_of_lt hi]
    | t q =>
        have hq : q < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        simp only [Gate.map, shiftWire, gateAction, diagVec]
        rw [← testBit_div_prefix offset q i]
        split
        · rw [RegisterState.join_apply_of_lt hi]
          exact mul_mul_swap _ _ _
        · rw [RegisterState.join_apply_of_lt hi]
    | tdg q =>
        have hq : q < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        simp only [Gate.map, shiftWire, gateAction, diagVec]
        rw [← testBit_div_prefix offset q i]
        split
        · rw [RegisterState.join_apply_of_lt hi]
          exact mul_mul_swap _ _ _
        · rw [RegisterState.join_apply_of_lt hi]
    | p phaseLevel q =>
        have hq : q < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        simp only [Gate.map, shiftWire, gateAction, diagVec]
        rw [← testBit_div_prefix offset q i]
        split
        · rw [RegisterState.join_apply_of_lt hi]
          exact mul_mul_swap _ _ _
        · rw [RegisterState.join_apply_of_lt hi]
    | pdg phaseLevel q =>
        have hq : q < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        simp only [Gate.map, shiftWire, gateAction, diagVec]
        rw [← testBit_div_prefix offset q i]
        split
        · rw [RegisterState.join_apply_of_lt hi]
          exact mul_mul_swap _ _ _
        · rw [RegisterState.join_apply_of_lt hi]
    | cx ctrl target =>
        have hctrl : ctrl < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        have htarget : target < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        have hcx : cxIndex (offset + ctrl) (offset + target) i <
            2 ^ (offset + activeWidth) := by
          rw [cxIndex]
          split
          · apply Nat.xor_lt_two_pow hi
            rw [Nat.one_shiftLeft]
            exact Nat.pow_lt_pow_of_lt (by omega) (by omega)
          · exact hi
        simp only [Gate.map, shiftWire, gateAction, cxVec]
        rw [RegisterState.join_apply_of_lt hcx,
          cxIndex_mod_prefix, cxIndex_div_prefix]
    | ccz a b c =>
        have ha : a < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        have hb : b < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        have hc : c < activeWidth := by
          simp [Gate.wellFormedAt] at hg
          omega
        simp only [Gate.map, shiftWire, gateAction, cczVec]
        rw [← testBit_div_prefix offset a i,
          ← testBit_div_prefix offset b i,
          ← testBit_div_prefix offset c i]
        split
        · rw [RegisterState.join_apply_of_lt hi]
          exact (Dy.mul_neg _ _).symm
        · rw [RegisterState.join_apply_of_lt hi]
  · rw [RegisterState.join_apply_of_not_lt hi,
      gateVec_of_wf hgShiftTotal, ← gateVec_of_wf hgShiftActive]
    exact wfVec_gateVec level (offset + activeWidth)
      (g.map (shiftWire offset))
      (RegisterState.join_support offset activeWidth scratch prefixState active)
      i (by omega)

theorem runGates_join_right {level offset activeWidth scratch : Nat}
    {gates : List Gate}
    (hgates : ∀ g ∈ gates, g.wellFormedAt level activeWidth = true)
    (prefixState active : Vec (deg level)) :
    runGates level (offset + activeWidth + scratch)
        (gates.map (Gate.map (shiftWire offset)))
        (RegisterState.join offset activeWidth scratch prefixState active) =
      RegisterState.join offset activeWidth scratch prefixState
        (runGates level activeWidth gates active) := by
  induction gates generalizing active with
  | nil => rfl
  | cons g gates ih =>
      have hg : g.wellFormedAt level activeWidth = true :=
        hgates g List.mem_cons_self
      have hrest : ∀ h ∈ gates,
          h.wellFormedAt level activeWidth = true := by
        intro h hh
        exact hgates h (List.mem_cons_of_mem g hh)
      rw [List.map_cons, runGates_cons, runGates_cons,
        gateVec_join_right hg]
      exact ih hrest (gateVec level activeWidth g active)

theorem run_placedCircuit_product {level offset width : Nat}
    {c : Circuit} (hfit : offset + c.width ≤ width)
    (hc : c.wellFormedAt level = true)
    (prefixState active suffixState : Vec (deg level)) :
    run level (placedCircuit offset width c)
        (factorizedProduct offset c.width width
          prefixState active suffixState) =
      factorizedProduct offset c.width width
        prefixState (run level c active) suffixState := by
  let suffix := suffixWidth offset c.width width
  have hwidth : offset + (c.width + suffix) = width :=
    suffixWidth_eq hfit
  have hcWide :
      (Circuit.ofGates (c.width + suffix) c.gates).wellFormedAt level = true :=
    Circuit.wellFormedAt_widen (by omega) hc
  have hgates : ∀ g ∈ c.gates,
      g.wellFormedAt level (c.width + suffix) = true := by
    simpa only [Circuit.wellFormedAt, Circuit.ofGates,
      List.all_eq_true] using hcWide
  have houter := runGates_join_right
    (level := level) (offset := offset)
    (activeWidth := c.width + suffix) (scratch := 0)
    hgates
    prefixState
    (RegisterState.join c.width suffix 0 active suffixState)
  have hinner := RegisterState.run_embedded_join
    (level := level) (m := c.width) (s := suffix) (k := 0)
    (c := c) rfl hc active suffixState
  have houter' :
      runGates level width
          (c.gates.map (Gate.map (shiftWire offset)))
          (RegisterState.join offset (c.width + suffix) 0
            prefixState
            (RegisterState.join c.width suffix 0 active suffixState)) =
        RegisterState.join offset (c.width + suffix) 0
          prefixState
          (runGates level (c.width + suffix) c.gates
            (RegisterState.join c.width suffix 0 active suffixState)) := by
    simpa only [Nat.add_zero, hwidth] using houter
  change runGates level width
      (c.gates.map (Gate.map (shiftWire offset)))
      (RegisterState.join offset (c.width + suffix) 0
        prefixState
        (RegisterState.join c.width suffix 0 active suffixState)) = _
  rw [houter']
  rw [show runGates level (c.width + suffix) c.gates
      (RegisterState.join c.width suffix 0 active suffixState) =
      RegisterState.join c.width suffix 0 (run level c active) suffixState by
      change runGates level (c.width + suffix + 0) c.gates
        (RegisterState.join c.width suffix 0 active suffixState) = _ at hinner
      simpa only [Nat.add_zero] using hinner]
  rfl

theorem run_placedCircuit_factorized {level offset width context : Nat}
    {c : Circuit} (hfit : offset + c.width ≤ width)
    (hc : c.wellFormedAt level = true) (u : Vec (deg level)) :
    run level (placedCircuit offset width c)
        (factorizedState offset c.width width context u) =
      factorizedState offset c.width width context (run level c u) := by
  simpa [factorizedState] using run_placedCircuit_product hfit hc
    (basis (prefixContext context offset) : Vec (deg level)) u
    (basis (suffixContext context offset c.width width))

theorem run_placedQFT_product {level offset n width : Nat}
    (hfit : offset + n ≤ width) (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level)
    (prefixState active suffixState : Vec (deg level)) :
    run level (placedQFT offset n width)
        (factorizedProduct offset n width
          prefixState active suffixState) =
      factorizedProduct offset n width prefixState
        (run level (QFT.qftCircuit n) active) suffixState := by
  exact run_placedCircuit_product hfit
    (QFTFamily.qftCircuit_wellFormedAt_uniform hl3 hlevel)
    prefixState active suffixState

theorem run_placedIQFT_product {level offset n width : Nat}
    (hfit : offset + n ≤ width) (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level)
    (prefixState active suffixState : Vec (deg level)) :
    run level (placedIQFT offset n width)
        (factorizedProduct offset n width
          prefixState active suffixState) =
      factorizedProduct offset n width prefixState
        (run level (QFTFamily.iqftCircuit n) active) suffixState := by
  apply run_placedCircuit_product hfit
  · rw [QFTFamily.iqftCircuit,
      Adjoint.circuit_adjoint_wellFormedAt]
    exact QFTFamily.qftCircuit_wellFormedAt_uniform hl3 hlevel

theorem run_leftQFT_adjacent
    {level offset leftWidth rightWidth width : Nat}
    (hfit : offset + leftWidth + rightWidth ≤ width)
    (hl3 : 3 ≤ level) (hleftLevel : leftWidth + 1 ≤ level)
    (prefixState leftState rightState suffixState : Vec (deg level)) :
    run level (placedQFT offset leftWidth width)
        (adjacentProduct offset leftWidth rightWidth width
          prefixState leftState rightState suffixState) =
      adjacentProduct offset leftWidth rightWidth width prefixState
        (run level (QFT.qftCircuit leftWidth) leftState)
        rightState suffixState := by
  have h := run_placedQFT_product
    (level := level) (offset := offset) (n := leftWidth) (width := width)
    (by omega) hl3 hleftLevel prefixState leftState
    (RegisterState.join rightWidth
      (adjacentSuffixWidth offset leftWidth rightWidth width) 0
      rightState suffixState)
  simpa [adjacentProduct, factorizedProduct,
    suffixWidth_left_eq hfit] using h

theorem run_rightQFT_adjacent
    {level offset leftWidth rightWidth width : Nat}
    (hfit : offset + leftWidth + rightWidth ≤ width)
    (hl3 : 3 ≤ level) (hrightLevel : rightWidth + 1 ≤ level)
    (prefixState leftState rightState suffixState : Vec (deg level)) :
    run level (placedQFT (offset + leftWidth) rightWidth width)
        (adjacentProduct offset leftWidth rightWidth width
          prefixState leftState rightState suffixState) =
      adjacentProduct offset leftWidth rightWidth width prefixState
        leftState (run level (QFT.qftCircuit rightWidth) rightState)
        suffixState := by
  let tail := adjacentSuffixWidth offset leftWidth rightWidth width
  let rightBlockWidth := rightWidth + tail
  let innerWidth := leftWidth + rightBlockWidth
  have hwidth : offset + innerWidth = width := by
    dsimp [innerWidth, rightBlockWidth, tail]
    exact adjacentSuffixWidth_eq hfit
  have hrightFit : rightWidth ≤ rightBlockWidth := by
    simp [rightBlockWidth]
  have hinnerFit : leftWidth + rightWidth ≤ innerWidth := by
    simp [innerWidth, rightBlockWidth]
  have hc : (QFT.qftCircuit rightWidth).wellFormedAt level = true :=
    QFTFamily.qftCircuit_wellFormedAt_uniform hl3 hrightLevel
  have hcRightWide :
      (Circuit.ofGates rightBlockWidth
        (QFT.qftCircuit rightWidth).gates).wellFormedAt level = true :=
    Circuit.wellFormedAt_widen hrightFit hc
  have hgatesRight : ∀ g ∈ (QFT.qftCircuit rightWidth).gates,
      g.wellFormedAt level rightBlockWidth = true := by
    simpa only [Circuit.wellFormedAt, Circuit.ofGates,
      List.all_eq_true] using hcRightWide
  have hcShifted :
      (placedCircuit leftWidth innerWidth
        (QFT.qftCircuit rightWidth)).wellFormedAt level = true :=
    placedCircuit_wellFormedAt hinnerFit hc
  have hgatesShifted : ∀ g ∈
      (QFT.qftCircuit rightWidth).gates.map
        (Gate.map (shiftWire leftWidth)),
      g.wellFormedAt level innerWidth = true := by
    simpa only [Circuit.wellFormedAt, placedCircuit_gates,
      placedCircuit_width,
      List.all_eq_true] using hcShifted
  have houter := runGates_join_right
    (level := level) (offset := offset)
    (activeWidth := innerWidth) (scratch := 0)
    hgatesShifted prefixState
    (RegisterState.join leftWidth rightBlockWidth 0 leftState
      (RegisterState.join rightWidth tail 0 rightState suffixState))
  have hmiddle := runGates_join_right
    (level := level) (offset := leftWidth)
    (activeWidth := rightBlockWidth) (scratch := 0)
    hgatesRight leftState
    (RegisterState.join rightWidth tail 0 rightState suffixState)
  have hright := RegisterState.run_embedded_join
    (level := level) (m := rightWidth) (s := tail) (k := 0)
    (c := QFT.qftCircuit rightWidth) rfl hc rightState suffixState
  have houter' :
      runGates level width
          ((QFT.qftCircuit rightWidth).gates.map
            (Gate.map (shiftWire (offset + leftWidth))))
          (RegisterState.join offset innerWidth 0 prefixState
            (RegisterState.join leftWidth rightBlockWidth 0 leftState
              (RegisterState.join rightWidth tail 0
                rightState suffixState))) =
        RegisterState.join offset innerWidth 0 prefixState
          (runGates level innerWidth
            ((QFT.qftCircuit rightWidth).gates.map
              (Gate.map (shiftWire leftWidth)))
            (RegisterState.join leftWidth rightBlockWidth 0 leftState
              (RegisterState.join rightWidth tail 0
                rightState suffixState))) := by
    rw [← gates_map_shift_comp offset leftWidth]
    simpa only [Nat.add_zero, hwidth] using houter
  have hmiddle' :
      runGates level innerWidth
          ((QFT.qftCircuit rightWidth).gates.map
            (Gate.map (shiftWire leftWidth)))
          (RegisterState.join leftWidth rightBlockWidth 0 leftState
            (RegisterState.join rightWidth tail 0 rightState suffixState)) =
        RegisterState.join leftWidth rightBlockWidth 0 leftState
          (runGates level rightBlockWidth
            (QFT.qftCircuit rightWidth).gates
            (RegisterState.join rightWidth tail 0
              rightState suffixState)) := by
    simpa only [Nat.add_zero, innerWidth] using hmiddle
  have hright' :
      runGates level rightBlockWidth
          (QFT.qftCircuit rightWidth).gates
          (RegisterState.join rightWidth tail 0 rightState suffixState) =
        RegisterState.join rightWidth tail 0
          (run level (QFT.qftCircuit rightWidth) rightState)
          suffixState := by
    change runGates level (rightWidth + tail + 0)
      (QFT.qftCircuit rightWidth).gates
      (RegisterState.join rightWidth tail 0 rightState suffixState) = _ at hright
    simpa only [Nat.add_zero, rightBlockWidth] using hright
  change runGates level width
      ((QFT.qftCircuit rightWidth).gates.map
        (Gate.map (shiftWire (offset + leftWidth))))
      (RegisterState.join offset innerWidth 0 prefixState
        (RegisterState.join leftWidth rightBlockWidth 0 leftState
          (RegisterState.join rightWidth tail 0 rightState suffixState))) = _
  rw [houter', hmiddle', hright']
  rfl

theorem run_rightQFT_run_leftQFT_adjacent
    {level offset leftWidth rightWidth width : Nat}
    (hfit : offset + leftWidth + rightWidth ≤ width)
    (hl3 : 3 ≤ level) (hleftLevel : leftWidth + 1 ≤ level)
    (hrightLevel : rightWidth + 1 ≤ level)
    (prefixState leftState rightState suffixState : Vec (deg level)) :
    run level (placedQFT (offset + leftWidth) rightWidth width)
        (run level (placedQFT offset leftWidth width)
          (adjacentProduct offset leftWidth rightWidth width
            prefixState leftState rightState suffixState)) =
      adjacentProduct offset leftWidth rightWidth width prefixState
        (run level (QFT.qftCircuit leftWidth) leftState)
        (run level (QFT.qftCircuit rightWidth) rightState)
        suffixState := by
  rw [run_leftQFT_adjacent hfit hl3 hleftLevel,
    run_rightQFT_adjacent hfit hl3 hrightLevel]

theorem run_leftQFT_run_rightQFT_adjacent
    {level offset leftWidth rightWidth width : Nat}
    (hfit : offset + leftWidth + rightWidth ≤ width)
    (hl3 : 3 ≤ level) (hleftLevel : leftWidth + 1 ≤ level)
    (hrightLevel : rightWidth + 1 ≤ level)
    (prefixState leftState rightState suffixState : Vec (deg level)) :
    run level (placedQFT offset leftWidth width)
        (run level (placedQFT (offset + leftWidth) rightWidth width)
          (adjacentProduct offset leftWidth rightWidth width
            prefixState leftState rightState suffixState)) =
      adjacentProduct offset leftWidth rightWidth width prefixState
        (run level (QFT.qftCircuit leftWidth) leftState)
        (run level (QFT.qftCircuit rightWidth) rightState)
        suffixState := by
  rw [run_rightQFT_adjacent hfit hl3 hrightLevel,
    run_leftQFT_adjacent hfit hl3 hleftLevel]

theorem placedQFTs_commute_on_adjacent_product
    {level offset leftWidth rightWidth width : Nat}
    (hfit : offset + leftWidth + rightWidth ≤ width)
    (hl3 : 3 ≤ level) (hleftLevel : leftWidth + 1 ≤ level)
    (hrightLevel : rightWidth + 1 ≤ level)
    (prefixState leftState rightState suffixState : Vec (deg level)) :
    run level (placedQFT (offset + leftWidth) rightWidth width)
        (run level (placedQFT offset leftWidth width)
          (adjacentProduct offset leftWidth rightWidth width
            prefixState leftState rightState suffixState)) =
      run level (placedQFT offset leftWidth width)
        (run level (placedQFT (offset + leftWidth) rightWidth width)
          (adjacentProduct offset leftWidth rightWidth width
            prefixState leftState rightState suffixState)) := by
  rw [run_rightQFT_run_leftQFT_adjacent hfit hl3 hleftLevel hrightLevel,
    run_leftQFT_run_rightQFT_adjacent hfit hl3 hleftLevel hrightLevel]

theorem run_placedQFT_factorized {level offset n width context : Nat}
    (hfit : offset + n ≤ width) (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level) (u : Vec (deg level)) :
    run level (placedQFT offset n width)
        (factorizedState offset n width context u) =
      factorizedState offset n width context
        (run level (QFT.qftCircuit n) u) := by
  exact run_placedCircuit_factorized hfit
    (QFTFamily.qftCircuit_wellFormedAt_uniform hl3 hlevel) u

theorem run_placedIQFT_factorized {level offset n width context : Nat}
    (hfit : offset + n ≤ width) (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level) (u : Vec (deg level)) :
    run level (placedIQFT offset n width)
        (factorizedState offset n width context u) =
      factorizedState offset n width context
        (run level (QFTFamily.iqftCircuit n) u) := by
  apply run_placedCircuit_factorized hfit
  rw [QFTFamily.iqftCircuit,
    Adjoint.circuit_adjoint_wellFormedAt]
  exact QFTFamily.qftCircuit_wellFormedAt_uniform hl3 hlevel

theorem run_placedQFT_basis {level offset n width context x : Nat}
    (hfit : offset + n ≤ width) (hx : x < 2 ^ n)
    (hl3 : 3 ≤ level) (hlevel : n + 1 ≤ level) :
    run level (placedQFT offset n width)
        (factorizedState offset n width context (basis x)) =
      factorizedState offset n width context
        (QFT.FourierColumn level n x) := by
  rw [run_placedQFT_factorized hfit hl3 hlevel,
    QFTFamily.run_qft_basis hx hl3 hlevel]

theorem run_placedIQFT_fourierColumn
    {level offset n width context x : Nat}
    (hfit : offset + n ≤ width) (hx : x < 2 ^ n)
    (hl3 : 3 ≤ level) (hlevel : n + 1 ≤ level) :
    run level (placedIQFT offset n width)
        (factorizedState offset n width context
          (QFT.FourierColumn level n x)) =
      factorizedState offset n width context (basis x) := by
  rw [run_placedIQFT_factorized hfit hl3 hlevel,
    QFTFamily.run_iqft_fourierColumn hx hl3 hlevel]

theorem run_placedIQFT_run_placedQFT
    {level offset n width context : Nat}
    (hfit : offset + n ≤ width) (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level) (u : Vec (deg level)) :
    run level (placedIQFT offset n width)
        (run level (placedQFT offset n width)
          (factorizedState offset n width context u)) =
      factorizedState offset n width context u := by
  rw [run_placedQFT_factorized hfit hl3 hlevel,
    run_placedIQFT_factorized hfit hl3 hlevel,
    QFTFamily.run_iqft_run_qft _ hl3 hlevel]

theorem run_placedQFT_run_placedIQFT
    {level offset n width context : Nat}
    (hfit : offset + n ≤ width) (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level) (u : Vec (deg level)) :
    run level (placedQFT offset n width)
        (run level (placedIQFT offset n width)
          (factorizedState offset n width context u)) =
      factorizedState offset n width context u := by
  rw [run_placedIQFT_factorized hfit hl3 hlevel,
    run_placedQFT_factorized hfit hl3 hlevel,
    QFTFamily.run_qft_run_iqft _ hl3 hlevel]

/-- info: 'VQ.Tests.ECDLPQFTPlacement.gateVec_join_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gateVec_join_right

/-- info: 'VQ.Tests.ECDLPQFTPlacement.run_placedCircuit_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_placedCircuit_product

/-- info: 'VQ.Tests.ECDLPQFTPlacement.run_placedQFT_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_placedQFT_product

/-- info: 'VQ.Tests.ECDLPQFTPlacement.run_rightQFT_run_leftQFT_adjacent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_rightQFT_run_leftQFT_adjacent

/-- info: 'VQ.Tests.ECDLPQFTPlacement.placedQFTs_commute_on_adjacent_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms placedQFTs_commute_on_adjacent_product

/-- info: 'VQ.Tests.ECDLPQFTPlacement.run_placedIQFT_fourierColumn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_placedIQFT_fourierColumn

end VQ.Tests.ECDLPQFTPlacement
