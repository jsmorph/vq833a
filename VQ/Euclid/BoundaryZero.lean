/-
Fixed-boundary zero maps specify coherent length scans.
-/
import VQ.Euclid.DirtyZero

namespace VQ
namespace Euclid
namespace BoundaryZero

open Reversible

def zeroAndGates (next target : Nat) : List RGate := [.cx next target]

def zeroBitGates (target : Nat) : List RGate := [.x target]

def selectedBit (enabled : Bool) (i source : Nat) : Nat :=
  if enabled then bitValue i source else 0

def selectedNotAndGates (enabled : Bool)
    (source next target : Nat) : List RGate :=
  if enabled then DirtyZero.notAndGates source next target
  else zeroAndGates next target

def selectedNotBitGates (enabled : Bool)
    (source target : Nat) : List RGate :=
  if enabled then DirtyZero.notBitGates source target
  else zeroBitGates target

def selectedNotAndValue (enabled : Bool)
    (i source next target : Nat) : Nat :=
  (bitValue i target +
    (1 - selectedBit enabled i source) * bitValue i next) % 2

def selectedNotBitValue (enabled : Bool)
    (i source target : Nat) : Nat :=
  (bitValue i target + 1 - selectedBit enabled i source) % 2

theorem selectedNotAndGates_act {enabled : Bool}
    {i source next target : Nat}
    (hst : source ≠ target) (hnt : next ≠ target) :
    actGates (selectedNotAndGates enabled source next target) i =
      writeField i target 1
        (selectedNotAndValue enabled i source next target) := by
  cases enabled with
  | false =>
      simp only [selectedNotAndGates, Bool.false_eq_true, if_false,
        zeroAndGates, actGates_cons, actGates_nil, act_cx_write]
      apply write_congr
      simp [selectedNotAndValue, selectedBit]
  | true =>
      simp only [selectedNotAndGates, if_true]
      rw [DirtyZero.notAndGates_act hst hnt]
      apply write_congr
      simp [selectedNotAndValue, selectedBit, DirtyZero.notAndValue]

theorem selectedNotBitGates_act {enabled : Bool}
    {i source target : Nat} (hst : source ≠ target) :
    actGates (selectedNotBitGates enabled source target) i =
      writeField i target 1
        (selectedNotBitValue enabled i source target) := by
  cases enabled with
  | false =>
      simp only [selectedNotBitGates, Bool.false_eq_true, if_false,
        zeroBitGates, actGates_cons, actGates_nil, act_x_write]
      apply write_congr
      simp [selectedNotBitValue, selectedBit]
  | true =>
      simp only [selectedNotBitGates, if_true]
      rw [DirtyZero.notBitGates_act hst]
      apply write_congr
      simp [selectedNotBitValue, selectedBit, DirtyZero.notBitValue]

theorem selectedNotAndGates_wellFormed {enabled : Bool}
    {source next target width : Nat}
    (hs : source < width) (hn : next < width) (ht : target < width)
    (hsn : source ≠ next) (hst : source ≠ target) (hnt : next ≠ target) :
    (selectedNotAndGates enabled source next target).all
      (RGate.wellFormed width) = true := by
  cases enabled <;>
    simp [selectedNotAndGates, zeroAndGates,
      DirtyZero.notAndGates, RGate.wellFormed, hs, hn, ht, hsn, hst, hnt]

theorem selectedNotBitGates_wellFormed {enabled : Bool}
    {source target width : Nat}
    (hs : source < width) (ht : target < width) (hst : source ≠ target) :
    (selectedNotBitGates enabled source target).all
      (RGate.wellFormed width) = true := by
  cases enabled <;>
    simp [selectedNotBitGates, zeroBitGates,
      DirtyZero.notBitGates, RGate.wellFormed, hs, ht, hst]

def upperForward (enabled : Nat → Bool) :
    Nat → Nat → Nat → Nat → List RGate
  | _, _, _, 0 => []
  | label, source, dirty, 1 =>
      selectedNotBitGates (enabled label) source dirty
  | label, source, dirty, count + 2 =>
      selectedNotAndGates (enabled label) source (dirty + 1) dirty ++
        upperForward enabled (label + 1) (source + 1) (dirty + 1) (count + 1)

def upperReverse (enabled : Nat → Bool) :
    Nat → Nat → Nat → Nat → List RGate
  | _, _, _, 0 => []
  | _, _, _, 1 => []
  | label, source, dirty, count + 2 =>
      upperReverse enabled (label + 1) (source + 1) (dirty + 1) (count + 1) ++
        selectedNotAndGates (enabled label) source (dirty + 1) dirty

def upperGates (enabled : Nat → Bool)
    (label source dirty count : Nat) : List RGate :=
  upperForward enabled label source dirty count ++
    upperReverse enabled label source dirty count

def upperZero (enabled : Nat → Bool) (i : Nat) :
    Nat → Nat → Nat → Nat
  | _, _, 0 => 1
  | label, source, count + 1 =>
      (1 - selectedBit (enabled label) i source) *
        upperZero enabled i (label + 1) (source + 1) count

theorem selectedBit_lt (enabled : Bool) (i source : Nat) :
    selectedBit enabled i source < 2 := by
  cases enabled <;> simp [selectedBit, bitValue_lt]

theorem selectedBit_write_ne {enabled : Bool} {i target value source : Nat}
    (h : source ≠ target) :
    selectedBit enabled (writeField i target 1 value) source =
      selectedBit enabled i source := by
  cases enabled <;> simp [selectedBit, bitValue_write_ne h]

theorem selectedBit_congr {enabled : Bool} {i j source : Nat}
    (h : bitValue i source = bitValue j source) :
    selectedBit enabled i source = selectedBit enabled j source := by
  cases enabled <;> simp [selectedBit, h]

theorem upperForward_wellFormed {enabled : Nat → Bool}
    {label source dirty count width : Nat}
    (hsource : source + count ≤ dirty) (hdirty : dirty + count ≤ width) :
    (upperForward enabled label source dirty count).all
      (RGate.wellFormed width) = true := by
  induction count generalizing label source dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          exact selectedNotBitGates_wellFormed
            (by omega) (by omega) (by omega)
      | succ count =>
          simp only [upperForward, List.all_append, Bool.and_eq_true]
          exact ⟨selectedNotAndGates_wellFormed
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            ih (label := label + 1) (source := source + 1)
              (dirty := dirty + 1) (by omega) (by omega)⟩

theorem upperReverse_wellFormed {enabled : Nat → Bool}
    {label source dirty count width : Nat}
    (hsource : source + count ≤ dirty) (hdirty : dirty + count ≤ width) :
    (upperReverse enabled label source dirty count).all
      (RGate.wellFormed width) = true := by
  induction count generalizing label source dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          simp only [upperReverse, List.all_append, Bool.and_eq_true]
          exact ⟨ih (label := label + 1) (source := source + 1)
              (dirty := dirty + 1) (by omega) (by omega),
            selectedNotAndGates_wellFormed
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem upperGates_wellFormed {enabled : Nat → Bool}
    {label source dirty count width : Nat}
    (hsource : source + count ≤ dirty) (hdirty : dirty + count ≤ width) :
    (upperGates enabled label source dirty count).all
      (RGate.wellFormed width) = true := by
  simp only [upperGates, List.all_append, Bool.and_eq_true]
  exact ⟨upperForward_wellFormed hsource hdirty,
    upperReverse_wellFormed hsource hdirty⟩

theorem upperZero_lt (enabled : Nat → Bool)
    (i label source count : Nat) :
    upperZero enabled i label source count < 2 := by
  induction count generalizing label source with
  | zero => simp [upperZero]
  | succ count ih =>
      rw [upperZero]
      have hb := selectedBit_lt (enabled label) i source
      have hb' : selectedBit (enabled label) i source = 0 ∨
          selectedBit (enabled label) i source = 1 := by omega
      rcases hb' with hb' | hb' <;> simp [hb', ih]

theorem upperZero_write_out {enabled : Nat → Bool}
    {i target value label source count : Nat}
    (h : target < source ∨ source + count ≤ target) :
    upperZero enabled (writeField i target 1 value) label source count =
      upperZero enabled i label source count := by
  induction count generalizing label source with
  | zero => rfl
  | succ count ih =>
      rw [upperZero, upperZero, selectedBit_write_ne (by omega),
        ih (label := label + 1) (source := source + 1) (by omega)]

theorem upperGates_succ_succ (enabled : Nat → Bool)
    (label source dirty count : Nat) :
    upperGates enabled label source dirty (count + 2) =
      selectedNotAndGates (enabled label) source (dirty + 1) dirty ++
        upperGates enabled (label + 1) (source + 1) (dirty + 1) (count + 1) ++
        selectedNotAndGates (enabled label) source (dirty + 1) dirty := by
  simp [upperGates, upperForward, upperReverse, List.append_assoc]

theorem upperReverse_top (enabled : Nat → Bool)
    (label source dirty count : Nat) :
    upperReverse enabled label source dirty (count + 2) =
      selectedNotAndGates (enabled (label + count)) (source + count)
        (dirty + count + 1) (dirty + count) ++
      upperReverse enabled label source dirty (count + 1) := by
  induction count generalizing label source dirty with
  | zero => simp [upperReverse]
  | succ count ih =>
      calc
        upperReverse enabled label source dirty (count + 1 + 2) =
            upperReverse enabled (label + 1) (source + 1) (dirty + 1)
                (count + 2) ++
              selectedNotAndGates (enabled label) source (dirty + 1) dirty := rfl
        _ = (selectedNotAndGates (enabled (label + 1 + count))
                (source + 1 + count) (dirty + 1 + count + 1)
                (dirty + 1 + count) ++
              upperReverse enabled (label + 1) (source + 1) (dirty + 1)
                (count + 1)) ++
              selectedNotAndGates (enabled label) source (dirty + 1) dirty := by
            rw [ih]
        _ = selectedNotAndGates (enabled (label + (count + 1)))
                (source + (count + 1)) (dirty + (count + 1) + 1)
                (dirty + (count + 1)) ++
              upperReverse enabled label source dirty (count + 1 + 1) := by
            simp only [upperReverse]
            simp [Nat.add_comm, Nat.add_left_comm,
              List.append_assoc]

theorem upperGates_bitValue_out {enabled : Nat → Bool}
    {label source dirty count i q : Nat}
    (hsource : source + count ≤ dirty)
    (hq : q < dirty ∨ dirty + count ≤ q) :
    bitValue (actGates (upperGates enabled label source dirty count) i) q =
      bitValue i q := by
  induction count generalizing label source dirty i with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          rw [upperGates, upperForward, upperReverse, List.append_nil,
            selectedNotBitGates_act (by omega),
            bitValue_write_ne (by omega)]
      | succ count =>
          let g := selectedNotAndGates (enabled label) source (dirty + 1) dirty
          let i₁ := actGates g i
          let i₂ := actGates
            (upperGates enabled (label + 1) (source + 1)
              (dirty + 1) (count + 1)) i₁
          have hfirst : i₁ = writeField i dirty 1
              (selectedNotAndValue (enabled label) i source
                (dirty + 1) dirty) := by
            exact selectedNotAndGates_act (by omega) (by omega)
          have hrec : bitValue i₂ q = bitValue i₁ q := by
            exact ih (label := label + 1) (source := source + 1)
              (dirty := dirty + 1) (i := i₁) (by omega) (by omega)
          have hlast : bitValue (actGates g i₂) q = bitValue i₂ q := by
            rw [selectedNotAndGates_act (by omega) (by omega),
              bitValue_write_ne (by omega)]
          rw [upperGates_succ_succ, actGates_append, actGates_append]
          change bitValue (actGates g i₂) q = bitValue i q
          rw [hlast, hrec, hfirst, bitValue_write_ne (by omega)]

theorem upperGates_bitValue {enabled : Nat → Bool}
    {label source dirty count i j : Nat}
    (hsource : source + count ≤ dirty) (hj : j < count) :
    bitValue
        (actGates (upperGates enabled label source dirty count) i)
        (dirty + j) =
      (bitValue i (dirty + j) +
        upperZero enabled i (label + j) (source + j) (count - j)) % 2 := by
  induction count generalizing label source dirty i j with
  | zero => omega
  | succ count ih =>
      cases count with
      | zero =>
          have hj0 : j = 0 := by omega
          subst j
          simp only [Nat.add_zero, Nat.sub_zero]
          rw [upperGates, upperForward, upperReverse, List.append_nil,
            selectedNotBitGates_act (by omega), bitValue_write_self]
          simp only [selectedNotBitValue, upperZero, Nat.mul_one, Nat.mod_mod]
          apply congrArg (fun x => x % 2)
          have hb := selectedBit_lt (enabled label) i source
          omega
      | succ count =>
          let g := selectedNotAndGates (enabled label) source (dirty + 1) dirty
          let i₁ := actGates g i
          let i₂ := actGates
            (upperGates enabled (label + 1) (source + 1)
              (dirty + 1) (count + 1)) i₁
          have hfirst : i₁ = writeField i dirty 1
              (selectedNotAndValue (enabled label) i source
                (dirty + 1) dirty) := by
            exact selectedNotAndGates_act (by omega) (by omega)
          have hlast : actGates g i₂ = writeField i₂ dirty 1
              (selectedNotAndValue (enabled label) i₂ source
                (dirty + 1) dirty) := by
            exact selectedNotAndGates_act (by omega) (by omega)
          rw [upperGates_succ_succ, actGates_append, actGates_append]
          change bitValue (actGates g i₂) (dirty + j) = _
          cases j with
          | zero =>
              simp only [Nat.add_zero, Nat.sub_zero]
              have hsource₁ : selectedBit (enabled label) i₁ source =
                  selectedBit (enabled label) i source := by
                rw [hfirst, selectedBit_write_ne (by omega)]
              have hnext₁ : bitValue i₁ (dirty + 1) =
                  bitValue i (dirty + 1) := by
                rw [hfirst, bitValue_write_ne (by omega)]
              have htarget₁ : bitValue i₁ dirty =
                  selectedNotAndValue (enabled label) i source
                    (dirty + 1) dirty % 2 := by
                rw [hfirst, bitValue_write_self]
              have hsource₂ : selectedBit (enabled label) i₂ source =
                  selectedBit (enabled label) i₁ source := by
                apply selectedBit_congr
                exact upperGates_bitValue_out (i := i₁) (by omega) (by omega)
              have htarget₂ : bitValue i₂ dirty = bitValue i₁ dirty := by
                exact upperGates_bitValue_out (i := i₁) (by omega) (by omega)
              have hnext₂ : bitValue i₂ (dirty + 1) =
                  (bitValue i₁ (dirty + 1) +
                    upperZero enabled i₁ (label + 1) (source + 1)
                      (count + 1)) % 2 := by
                exact ih (label := label + 1) (source := source + 1)
                  (dirty := dirty + 1) (i := i₁) (j := 0)
                  (by omega) (by omega)
              have hzero :
                  upperZero enabled i₁ (label + 1) (source + 1) (count + 1) =
                    upperZero enabled i (label + 1) (source + 1)
                      (count + 1) := by
                rw [hfirst]
                exact upperZero_write_out (by omega)
              rw [hlast, bitValue_write_self]
              unfold selectedNotAndValue
              rw [hsource₂, htarget₂, hnext₂, hzero, hsource₁, htarget₁,
                hnext₁]
              change _ = (bitValue i dirty +
                (1 - selectedBit (enabled label) i source) *
                  upperZero enabled i (label + 1) (source + 1)
                    (count + 1)) % 2
              have ha := selectedBit_lt (enabled label) i source
              have hn := bitValue_lt i (dirty + 1)
              have hd := bitValue_lt i dirty
              have hz := upperZero_lt enabled i (label + 1)
                (source + 1) (count + 1)
              have ha' : selectedBit (enabled label) i source = 0 ∨
                  selectedBit (enabled label) i source = 1 := by omega
              have hn' : bitValue i (dirty + 1) = 0 ∨
                  bitValue i (dirty + 1) = 1 := by omega
              have hd' : bitValue i dirty = 0 ∨ bitValue i dirty = 1 := by omega
              have hz' : upperZero enabled i (label + 1) (source + 1)
                    (count + 1) = 0 ∨
                  upperZero enabled i (label + 1) (source + 1)
                    (count + 1) = 1 := by omega
              rcases ha' with ha' | ha' <;>
                rcases hn' with hn' | hn' <;>
                rcases hd' with hd' | hd' <;>
                rcases hz' with hz' | hz' <;>
                simp [selectedNotAndValue, ha', hn', hd', hz']
          | succ j =>
              have hj' : j < count + 1 := by omega
              have hq : dirty + (j + 1) = (dirty + 1) + j := by omega
              have hinner : bitValue i₂ ((dirty + 1) + j) =
                  (bitValue i₁ ((dirty + 1) + j) +
                    upperZero enabled i₁ ((label + 1) + j)
                      ((source + 1) + j) ((count + 1) - j)) % 2 := by
                exact ih (label := label + 1) (source := source + 1)
                  (dirty := dirty + 1) (i := i₁) (j := j) (by omega) hj'
              have hzero :
                  upperZero enabled i₁ ((label + 1) + j)
                      ((source + 1) + j) ((count + 1) - j) =
                    upperZero enabled i ((label + 1) + j)
                      ((source + 1) + j) ((count + 1) - j) := by
                rw [hfirst]
                exact upperZero_write_out (by omega)
              rw [hlast, bitValue_write_ne (by omega), hq, hinner,
                hzero, hfirst, bitValue_write_ne (by omega)]
              have hlidx : (label + 1) + j = label + (j + 1) := by omega
              have hsidx : (source + 1) + j = source + (j + 1) := by omega
              have hcidx : (count + 1) - j =
                  count + 1 + 1 - (j + 1) := by omega
              rw [hlidx, hsidx, hcidx]

theorem upperZero_upperGates {enabled : Nat → Bool}
    {zeroLabel zeroSource zeroCount label source dirty count i : Nat}
    (hsource : source + count ≤ dirty)
    (hzeroSource : zeroSource + zeroCount ≤ dirty) :
    upperZero enabled
        (actGates (upperGates enabled label source dirty count) i)
        zeroLabel zeroSource zeroCount =
      upperZero enabled i zeroLabel zeroSource zeroCount := by
  induction zeroCount generalizing zeroLabel zeroSource with
  | zero => rfl
  | succ zeroCount ih =>
      rw [upperZero, upperZero]
      have hb := upperGates_bitValue_out (enabled := enabled)
        (label := label) (i := i) hsource (q := zeroSource)
        (Or.inl (by omega))
      rw [selectedBit_congr hb,
        ih (zeroLabel := zeroLabel + 1) (zeroSource := zeroSource + 1)
          (by omega)]

theorem upperGates_involutive {enabled : Nat → Bool}
    {label source dirty count i : Nat}
    (hsource : source + count ≤ dirty) :
    actGates (upperGates enabled label source dirty count)
        (actGates (upperGates enabled label source dirty count) i) = i := by
  apply Nat.eq_of_testBit_eq
  intro q
  apply DirtyZero.testBit_eq_of_bitValue_eq
  by_cases hq : q < dirty ∨ dirty + count ≤ q
  · rw [upperGates_bitValue_out hsource hq,
      upperGates_bitValue_out hsource hq]
  · have hq' : dirty ≤ q ∧ q < dirty + count := by omega
    let j := q - dirty
    have hj : j < count := by omega
    have hqj : dirty + j = q := by omega
    rw [← hqj, upperGates_bitValue hsource hj,
      upperGates_bitValue hsource hj,
      upperZero_upperGates hsource (by omega)]
    have hd := bitValue_lt i (dirty + j)
    have hz := upperZero_lt enabled i (label + j) (source + j) (count - j)
    omega

def lowerForward (enabled : Nat → Bool) :
    Nat → Nat → Nat → Nat → List RGate
  | _, _, _, 0 => []
  | label, source, dirty, 1 =>
      selectedNotBitGates (enabled label) source dirty
  | label, source, dirty, count + 2 =>
      selectedNotAndGates (enabled (label + count + 1))
          (source + count + 1) (dirty + count) (dirty + count + 1) ++
        lowerForward enabled label source dirty (count + 1)

def lowerReverse (enabled : Nat → Bool) :
    Nat → Nat → Nat → Nat → List RGate
  | _, _, _, 0 => []
  | _, _, _, 1 => []
  | label, source, dirty, count + 2 =>
      lowerReverse enabled label source dirty (count + 1) ++
        selectedNotAndGates (enabled (label + count + 1))
          (source + count + 1) (dirty + count) (dirty + count + 1)

def lowerGates (enabled : Nat → Bool)
    (label source dirty count : Nat) : List RGate :=
  lowerForward enabled label source dirty count ++
    lowerReverse enabled label source dirty count

def lowerZero (enabled : Nat → Bool) (i label source : Nat) : Nat → Nat
  | 0 => 1
  | count + 1 =>
      lowerZero enabled i label source count *
        (1 - selectedBit (enabled (label + count)) i (source + count))

theorem lowerForward_wellFormed {enabled : Nat → Bool}
    {label source dirty count width : Nat}
    (hsource : source + count ≤ dirty) (hdirty : dirty + count ≤ width) :
    (lowerForward enabled label source dirty count).all
      (RGate.wellFormed width) = true := by
  induction count generalizing label source dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          exact selectedNotBitGates_wellFormed
            (by omega) (by omega) (by omega)
      | succ count =>
          simp only [lowerForward, List.all_append, Bool.and_eq_true]
          exact ⟨selectedNotAndGates_wellFormed
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            ih (label := label) (source := source) (dirty := dirty)
              (by omega) (by omega)⟩

theorem lowerReverse_wellFormed {enabled : Nat → Bool}
    {label source dirty count width : Nat}
    (hsource : source + count ≤ dirty) (hdirty : dirty + count ≤ width) :
    (lowerReverse enabled label source dirty count).all
      (RGate.wellFormed width) = true := by
  induction count generalizing label source dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          simp only [lowerReverse, List.all_append, Bool.and_eq_true]
          exact ⟨ih (label := label) (source := source) (dirty := dirty)
              (by omega) (by omega),
            selectedNotAndGates_wellFormed
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem lowerGates_wellFormed {enabled : Nat → Bool}
    {label source dirty count width : Nat}
    (hsource : source + count ≤ dirty) (hdirty : dirty + count ≤ width) :
    (lowerGates enabled label source dirty count).all
      (RGate.wellFormed width) = true := by
  simp only [lowerGates, List.all_append, Bool.and_eq_true]
  exact ⟨lowerForward_wellFormed hsource hdirty,
    lowerReverse_wellFormed hsource hdirty⟩

theorem lowerZero_lt (enabled : Nat → Bool) (i label source count : Nat) :
    lowerZero enabled i label source count < 2 := by
  induction count with
  | zero => simp [lowerZero]
  | succ count ih =>
      rw [lowerZero]
      have hb := selectedBit_lt (enabled (label + count)) i (source + count)
      have hb' : selectedBit (enabled (label + count)) i (source + count) = 0 ∨
          selectedBit (enabled (label + count)) i (source + count) = 1 := by
        omega
      rcases hb' with hb' | hb' <;> simp [hb', ih]

theorem lowerZero_write_out {enabled : Nat → Bool}
    {i target value label source count : Nat}
    (h : target < source ∨ source + count ≤ target) :
    lowerZero enabled (writeField i target 1 value) label source count =
      lowerZero enabled i label source count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hprev : target < source ∨ source + count ≤ target := by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      rw [lowerZero, lowerZero, ih hprev,
        selectedBit_write_ne (by omega)]

theorem lowerGates_succ_succ (enabled : Nat → Bool)
    (label source dirty count : Nat) :
    lowerGates enabled label source dirty (count + 2) =
      selectedNotAndGates (enabled (label + count + 1))
          (source + count + 1) (dirty + count) (dirty + count + 1) ++
        lowerGates enabled label source dirty (count + 1) ++
        selectedNotAndGates (enabled (label + count + 1))
          (source + count + 1) (dirty + count) (dirty + count + 1) := by
  simp [lowerGates, lowerForward, lowerReverse, List.append_assoc]

theorem lowerGates_bitValue_out {enabled : Nat → Bool}
    {label source dirty count i q : Nat}
    (hsource : source + count ≤ dirty)
    (hq : q < dirty ∨ dirty + count ≤ q) :
    bitValue (actGates (lowerGates enabled label source dirty count) i) q =
      bitValue i q := by
  induction count generalizing label source dirty i with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          rw [lowerGates, lowerForward, lowerReverse, List.append_nil,
            selectedNotBitGates_act (by omega),
            bitValue_write_ne (by omega)]
      | succ count =>
          let g := selectedNotAndGates (enabled (label + count + 1))
            (source + count + 1) (dirty + count) (dirty + count + 1)
          let i₁ := actGates g i
          let i₂ := actGates
            (lowerGates enabled label source dirty (count + 1)) i₁
          have hfirst : i₁ = writeField i (dirty + count + 1) 1
              (selectedNotAndValue (enabled (label + count + 1)) i
                (source + count + 1) (dirty + count)
                (dirty + count + 1)) := by
            exact selectedNotAndGates_act (by omega) (by omega)
          have hrec : bitValue i₂ q = bitValue i₁ q := by
            exact ih (label := label) (source := source) (dirty := dirty)
              (i := i₁) (by omega) (by omega)
          have hlast : bitValue (actGates g i₂) q = bitValue i₂ q := by
            rw [selectedNotAndGates_act (by omega) (by omega),
              bitValue_write_ne (by omega)]
          rw [lowerGates_succ_succ, actGates_append, actGates_append]
          change bitValue (actGates g i₂) q = bitValue i q
          rw [hlast, hrec, hfirst, bitValue_write_ne (by omega)]

theorem lowerGates_bitValue {enabled : Nat → Bool}
    {label source dirty count i j : Nat}
    (hsource : source + count ≤ dirty) (hj : j < count) :
    bitValue (actGates (lowerGates enabled label source dirty count) i)
        (dirty + j) =
      (bitValue i (dirty + j) +
        lowerZero enabled i label source (j + 1)) % 2 := by
  induction count generalizing label source dirty i j with
  | zero => omega
  | succ count ih =>
      cases count with
      | zero =>
          have hj0 : j = 0 := by omega
          subst j
          simp only [Nat.add_zero]
          rw [lowerGates, lowerForward, lowerReverse, List.append_nil,
            selectedNotBitGates_act (by omega), bitValue_write_self]
          simp only [selectedNotBitValue, lowerZero, Nat.add_zero,
            Nat.one_mul, Nat.mod_mod]
          apply congrArg (fun x => x % 2)
          have hb := selectedBit_lt (enabled label) i source
          omega
      | succ count =>
          let g := selectedNotAndGates (enabled (label + count + 1))
            (source + count + 1) (dirty + count) (dirty + count + 1)
          let i₁ := actGates g i
          let i₂ := actGates
            (lowerGates enabled label source dirty (count + 1)) i₁
          have hfirst : i₁ = writeField i (dirty + count + 1) 1
              (selectedNotAndValue (enabled (label + count + 1)) i
                (source + count + 1) (dirty + count)
                (dirty + count + 1)) := by
            exact selectedNotAndGates_act (by omega) (by omega)
          have hlast : actGates g i₂ =
              writeField i₂ (dirty + count + 1) 1
                (selectedNotAndValue (enabled (label + count + 1)) i₂
                  (source + count + 1) (dirty + count)
                  (dirty + count + 1)) := by
            exact selectedNotAndGates_act (by omega) (by omega)
          rw [lowerGates_succ_succ, actGates_append, actGates_append]
          change bitValue (actGates g i₂) (dirty + j) = _
          by_cases hjlow : j < count + 1
          · have hinner : bitValue i₂ (dirty + j) =
                (bitValue i₁ (dirty + j) +
                  lowerZero enabled i₁ label source (j + 1)) % 2 := by
              exact ih (label := label) (source := source) (dirty := dirty)
                (i := i₁) (j := j) (by omega) hjlow
            have hzero : lowerZero enabled i₁ label source (j + 1) =
                lowerZero enabled i label source (j + 1) := by
              rw [hfirst]
              exact lowerZero_write_out (by omega)
            rw [hlast, bitValue_write_ne (by omega), hinner, hzero,
              hfirst, bitValue_write_ne (by omega)]
          · have hjhigh : j = count + 1 := by omega
            subst j
            have htargetIndex : dirty + (count + 1) =
                dirty + count + 1 := by omega
            rw [htargetIndex]
            have hsource₁ :
                selectedBit (enabled (label + count + 1)) i₁
                    (source + count + 1) =
                  selectedBit (enabled (label + count + 1)) i
                    (source + count + 1) := by
              rw [hfirst, selectedBit_write_ne (by omega)]
            have hprev₁ : bitValue i₁ (dirty + count) =
                bitValue i (dirty + count) := by
              rw [hfirst, bitValue_write_ne (by omega)]
            have htarget₁ : bitValue i₁ (dirty + count + 1) =
                selectedNotAndValue (enabled (label + count + 1)) i
                  (source + count + 1) (dirty + count)
                  (dirty + count + 1) % 2 := by
              rw [hfirst, bitValue_write_self]
            have hsource₂ :
                selectedBit (enabled (label + count + 1)) i₂
                    (source + count + 1) =
                  selectedBit (enabled (label + count + 1)) i₁
                    (source + count + 1) := by
              apply selectedBit_congr
              exact lowerGates_bitValue_out (i := i₁) (by omega) (by omega)
            have htarget₂ : bitValue i₂ (dirty + count + 1) =
                bitValue i₁ (dirty + count + 1) := by
              exact lowerGates_bitValue_out (i := i₁) (by omega) (by omega)
            have hprev₂ : bitValue i₂ (dirty + count) =
                (bitValue i₁ (dirty + count) +
                  lowerZero enabled i₁ label source (count + 1)) % 2 := by
              exact ih (label := label) (source := source) (dirty := dirty)
                (i := i₁) (j := count) (by omega) (by omega)
            have hzero : lowerZero enabled i₁ label source (count + 1) =
                lowerZero enabled i label source (count + 1) := by
              rw [hfirst]
              exact lowerZero_write_out (by omega)
            rw [hlast, bitValue_write_self]
            unfold selectedNotAndValue
            rw [hsource₂, htarget₂, hprev₂, hzero, hsource₁,
              htarget₁, hprev₁]
            change _ = (bitValue i (dirty + count + 1) +
              lowerZero enabled i label source (count + 1) *
                (1 - selectedBit (enabled (label + count + 1)) i
                  (source + count + 1))) % 2
            have ha := selectedBit_lt (enabled (label + count + 1)) i
              (source + count + 1)
            have hp := bitValue_lt i (dirty + count)
            have hd := bitValue_lt i (dirty + count + 1)
            have hz := lowerZero_lt enabled i label source (count + 1)
            have ha' : selectedBit (enabled (label + count + 1)) i
                  (source + count + 1) = 0 ∨
                selectedBit (enabled (label + count + 1)) i
                  (source + count + 1) = 1 := by
              omega
            have hp' : bitValue i (dirty + count) = 0 ∨
                bitValue i (dirty + count) = 1 := by omega
            have hd' : bitValue i (dirty + count + 1) = 0 ∨
                bitValue i (dirty + count + 1) = 1 := by omega
            have hz' : lowerZero enabled i label source (count + 1) = 0 ∨
                lowerZero enabled i label source (count + 1) = 1 := by omega
            rcases ha' with ha' | ha' <;>
              rcases hp' with hp' | hp' <;>
              rcases hd' with hd' | hd' <;>
              rcases hz' with hz' | hz' <;>
              simp [selectedNotAndValue, ha', hp', hd', hz', Nat.mul_comm]

theorem lowerZero_lowerGates {enabled : Nat → Bool}
    {zeroLabel zeroSource zeroCount label source dirty count i : Nat}
    (hsource : source + count ≤ dirty)
    (hzeroSource : zeroSource + zeroCount ≤ dirty) :
    lowerZero enabled
        (actGates (lowerGates enabled label source dirty count) i)
        zeroLabel zeroSource zeroCount =
      lowerZero enabled i zeroLabel zeroSource zeroCount := by
  induction zeroCount with
  | zero => rfl
  | succ zeroCount ih =>
      rw [lowerZero, lowerZero, ih (by omega)]
      have hb := lowerGates_bitValue_out (enabled := enabled)
        (label := label) (i := i) hsource (q := zeroSource + zeroCount)
        (Or.inl (by omega))
      rw [selectedBit_congr hb]

theorem lowerGates_involutive {enabled : Nat → Bool}
    {label source dirty count i : Nat}
    (hsource : source + count ≤ dirty) :
    actGates (lowerGates enabled label source dirty count)
        (actGates (lowerGates enabled label source dirty count) i) = i := by
  apply Nat.eq_of_testBit_eq
  intro q
  apply DirtyZero.testBit_eq_of_bitValue_eq
  by_cases hq : q < dirty ∨ dirty + count ≤ q
  · rw [lowerGates_bitValue_out hsource hq,
      lowerGates_bitValue_out hsource hq]
  · have hq' : dirty ≤ q ∧ q < dirty + count := by omega
    let j := q - dirty
    have hj : j < count := by omega
    have hqj : dirty + j = q := by omega
    rw [← hqj, lowerGates_bitValue hsource hj,
      lowerGates_bitValue hsource hj,
      lowerZero_lowerGates hsource (by omega)]
    have hd := bitValue_lt i (dirty + j)
    have hz := lowerZero_lt enabled i label source (j + 1)
    omega

end BoundaryZero
end Euclid
end VQ
