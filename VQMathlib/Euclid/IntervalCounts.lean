import VQ.Euclid.IntervalBigEndianNoSign
import VQMathlib.Euclid.LengthWriterCounts

namespace VQMathlib.Euclid.IntervalCounts

open VQ VQ.Euclid VQ.Reversible

theorem endpointGates_ccx (value workWidth endpoint flag : Nat) :
    (Interval.endpointGates value workWidth 9 endpoint flag).countP
      RGate.isCcx = 31 := by
  have h := LengthWriterCounts.endpointToggle_ccx value workWidth
  unfold RangeZero.endpointToggle Interval.leftToggle Interval.endpointGates at h
  rw [countP_map_gates (fun g => RGate.isCcx_map _ g)] at h
  unfold Interval.endpointGates
  rw [countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact h

theorem firstScan_ccx (workWidth top count : Nat) :
    (IntervalBigEndian.firstScan workWidth 9 top count).countP RGate.isCcx =
      65 * count := by
  induction count generalizing top with
  | zero => rfl
  | succ count ih =>
    simp only [IntervalBigEndian.firstScan, List.countP_append,
      Interval.rightToggle, Interval.leftToggle, endpointGates_ccx,
      Interval.majAt, CellPlaced.gates,
      countP_map_gates (fun g => RGate.isCcx_map _ g), Cell.maj_ccx, ih]
    omega

theorem secondScan_ccx (workWidth start count : Nat) :
    (IntervalBigEndian.secondScan workWidth 9 start count).countP RGate.isCcx =
      66 * count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [IntervalBigEndian.secondScan, List.countP_append,
      Interval.rightToggle, Interval.leftToggle, endpointGates_ccx,
      Interval.umaAt, CellPlaced.gates,
      countP_map_gates (fun g => RGate.isCcx_map _ g), Cell.uma_ccx, ih]
    omega

theorem gates_ccx (workWidth : Nat) :
    (IntervalBigEndian.gates workWidth 9).countP RGate.isCcx =
      131 * workWidth := by
  simp only [IntervalBigEndian.gates, List.countP_append, firstScan_ccx,
    secondScan_ccx, List.countP_cons, List.countP_nil, RGate.isCcx,
    Bool.false_eq_true, if_false]
  omega

theorem noSignGates_ccx (workWidth : Nat) :
    (IntervalBigEndian.noSignGates workWidth 9).countP RGate.isCcx =
      131 * workWidth := by
  simp only [IntervalBigEndian.noSignGates, List.countP_append, firstScan_ccx,
    secondScan_ccx]
  omega

end VQMathlib.Euclid.IntervalCounts
