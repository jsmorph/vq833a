import VQMathlib.Algorithms.QFT.ApproximateError
import VQMathlib.ECDLP.FourierPlacement.Basic

open scoped Matrix.Norms.L2Operator

namespace VQ.Tests.ECDLPQFTPlacement

open VQ VQ.Circuit

def shiftedQFTWires (offset n : Nat) : List Nat :=
  (List.range n).reverse.map (shiftWire offset)

def placedApproximateQFT (offset n width cutoff : Nat) : Circuit :=
  Circuit.ofGates width
    (ApproximateQFT.gates cutoff (shiftedQFTWires offset n))

@[simp] theorem placedApproximateQFT_width (offset n width cutoff : Nat) :
    (placedApproximateQFT offset n width cutoff).width = width := rfl

@[simp] theorem placedApproximateQFT_gates (offset n width cutoff : Nat) :
    (placedApproximateQFT offset n width cutoff).gates =
      ApproximateQFT.gates cutoff (shiftedQFTWires offset n) := rfl

theorem phase_map (f : Nat → Nat) (k q : Nat) :
    (Circuit.phase k q).map (Gate.map f) = Circuit.phase k (f q) := by
  rcases k with (_ | _ | _ | _ | k) <;> rfl

theorem phaseInv_map (f : Nat → Nat) (k q : Nat) :
    (Circuit.phaseInv k q).map (Gate.map f) = Circuit.phaseInv k (f q) := by
  rcases k with (_ | _ | _ | _ | k) <;> rfl

theorem cphase_map (f : Nat → Nat) (k a b : Nat) :
    (Circuit.cphase k a b).map (Gate.map f) =
      Circuit.cphase k (f a) (f b) := by
  simp only [Circuit.cphase, List.map_append, phase_map, phaseInv_map,
    List.map_cons, List.map_nil, Gate.map]

theorem fullPhaseRows_map (f : Nat → Nat) (rest : List Nat)
    (start q : Nat) :
    (ApproximateQFT.fullPhaseRows rest start q).map (Gate.map f) =
      ApproximateQFT.fullPhaseRows (rest.map f) start (f q) := by
  induction rest generalizing start with
  | nil => rfl
  | cons r rest ih =>
      simp only [ApproximateQFT.fullPhaseRows, List.map_append,
        List.map_cons, cphase_map]
      rw [ih]

theorem fullNoSwap_map (f : Nat → Nat) (wires : List Nat) :
    (ApproximateQFT.fullNoSwap wires).map (Gate.map f) =
      ApproximateQFT.fullNoSwap (wires.map f) := by
  induction wires with
  | nil => rfl
  | cons q rest ih =>
      simp only [ApproximateQFT.fullNoSwap, List.map_append,
        List.map_cons, Gate.map, fullPhaseRows_map]
      rw [ih]

theorem qftNoSwap_map (f : Nat → Nat) (wires : List Nat) :
    (Circuit.qftNoSwap wires).map (Gate.map f) =
      Circuit.qftNoSwap (wires.map f) := by
  rw [← ApproximateQFT.fullNoSwap_eq_qftNoSwap,
    ← ApproximateQFT.fullNoSwap_eq_qftNoSwap, fullNoSwap_map]

theorem qftSwaps_map (f : Nat → Nat) (wires : List Nat) :
    (QFT.qftSwaps wires).map (Gate.map f) =
      QFT.qftSwaps (wires.map f) := by
  simp only [QFT.qftSwaps, List.length_map, List.map_flatMap,
    List.getElem?_map]
  apply List.flatMap_congr
  intro i _
  generalize ha : wires[i]? = a
  generalize hb : wires[wires.length - 1 - i]? = b
  cases a <;> cases b <;> rfl

theorem qft_map (f : Nat → Nat) (wires : List Nat) :
    (Circuit.qft wires).map (Gate.map f) =
      Circuit.qft (wires.map f) := by
  change
    (Circuit.qftNoSwap wires ++ QFT.qftSwaps wires).map (Gate.map f) =
      Circuit.qftNoSwap (wires.map f) ++ QFT.qftSwaps (wires.map f)
  rw [List.map_append, qftNoSwap_map, qftSwaps_map]

theorem placedQFT_gates_eq_qft_shifted (offset n width : Nat) :
    (placedQFT offset n width).gates =
      Circuit.qft (shiftedQFTWires offset n) := by
  change
    (Circuit.qft (List.range n).reverse).map (Gate.map (shiftWire offset)) =
      Circuit.qft ((List.range n).reverse.map (shiftWire offset))
  exact qft_map (shiftWire offset) (List.range n).reverse

theorem shiftedQFTWires_mem_lt {offset n width : Nat}
    (hfit : offset + n ≤ width) :
    ∀ q ∈ shiftedQFTWires offset n, q < width := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  have hrn : r < n :=
    List.mem_range.mp (List.mem_reverse.mp hr)
  simp only [shiftWire]
  omega

theorem shiftedQFTWires_nodup (offset n : Nat) :
    (shiftedQFTWires offset n).Nodup := by
  apply (List.nodup_reverse.mpr List.nodup_range).map
  · intro a b hab
    simpa only [shiftWire, Nat.add_left_cancel_iff] using hab

theorem placedApproximateQFT_wellFormedAt
    {level offset n width cutoff : Nat}
    (hfit : offset + n ≤ width) (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level) :
    (placedApproximateQFT offset n width cutoff).wellFormedAt level = true := by
  let wires := shiftedQFTWires offset n
  have hw : ∀ q ∈ wires, q < width := shiftedQFTWires_mem_lt hfit
  have hn : wires.Nodup := shiftedQFTWires_nodup offset n
  have hlen : wires.length + 1 ≤ level := by
    simpa [wires, shiftedQFTWires] using hlevel
  change (ApproximateQFT.gates cutoff wires).all
    (Gate.wellFormedAt level width) = true
  rw [ApproximateQFT.gates, List.all_append,
    ApproximateQFT.noSwap_wellFormedAt_of_fullLevel wires hw hn hl3 hlen,
    QFT.qftSwaps_wellFormedAt wires hw hn]
  rfl

theorem placedApproximateQFT_error
    {level offset n width cutoff : Nat}
    (hfit : offset + n ≤ width) (hl3 : 3 ≤ level)
    (hlevel : n + 1 ≤ level) :
    ‖VQBridge.cmat level width
        (placedApproximateQFT offset n width cutoff).gates -
      VQBridge.cmat level width (placedQFT offset n width).gates‖ ≤
        ApproximateQFT.noSwapError cutoff n := by
  rw [placedApproximateQFT_gates, placedQFT_gates_eq_qft_shifted]
  have h := ApproximateQFT.gates_error
    (level := level) (width := width) (cutoff := cutoff)
    (shiftedQFTWires offset n)
    (shiftedQFTWires_mem_lt hfit)
    (shiftedQFTWires_nodup offset n) hl3 (by
      simpa [shiftedQFTWires] using hlevel)
  simpa [shiftedQFTWires] using h

end VQ.Tests.ECDLPQFTPlacement

/-- info: 'VQ.Tests.ECDLPQFTPlacement.placedApproximateQFT_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms VQ.Tests.ECDLPQFTPlacement.placedApproximateQFT_error
