/-
Dirty-target prefix and suffix zero maps for reversible length updates.
-/
import VQ.Reversible.Permutation

namespace VQ
namespace Euclid
namespace DirtyZero

open Reversible

def notAndGates (bit next target : Nat) : List RGate :=
  [.cx next target, .ccx bit next target]

def notBitGates (bit target : Nat) : List RGate :=
  [.x target, .cx bit target]

def notAndValue (i bit next target : Nat) : Nat :=
  (bitValue i target +
    (1 - bitValue i bit) * bitValue i next) % 2

def notBitValue (i bit target : Nat) : Nat :=
  (bitValue i target + 1 - bitValue i bit) % 2

theorem notAndGates_act {i bit next target : Nat}
    (hbt : bit ≠ target) (hnt : next ≠ target) :
    actGates (notAndGates bit next target) i =
      writeField i target 1 (notAndValue i bit next target) := by
  rw [notAndGates, actGates_cons, actGates_cons, actGates_nil,
    act_cx_write, act_ccx_write]
  rw [bitValue_write_self,
    bitValue_write_ne hbt, bitValue_write_ne hnt,
    writeField_writeField]
  apply write_congr
  have hb := bitValue_lt i bit
  have hn := bitValue_lt i next
  have ht := bitValue_lt i target
  have hb' : bitValue i bit = 0 ∨ bitValue i bit = 1 := by omega
  have hn' : bitValue i next = 0 ∨ bitValue i next = 1 := by omega
  have ht' : bitValue i target = 0 ∨ bitValue i target = 1 := by omega
  rcases hb' with hb' | hb' <;>
    rcases hn' with hn' | hn' <;>
    rcases ht' with ht' | ht' <;>
    simp [notAndValue, hb', hn', ht']

theorem notBitGates_act {i bit target : Nat} (hbt : bit ≠ target) :
    actGates (notBitGates bit target) i =
      writeField i target 1 (notBitValue i bit target) := by
  rw [notBitGates, actGates_cons, actGates_cons, actGates_nil,
    act_x_write, act_cx_write]
  rw [bitValue_write_self, bitValue_write_ne hbt,
    writeField_writeField]
  apply write_congr
  have hb := bitValue_lt i bit
  have ht := bitValue_lt i target
  unfold notBitValue
  omega

def upperForward : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | bit, dirty, 1 => notBitGates bit dirty
  | bit, dirty, count + 2 =>
      notAndGates bit (dirty + 1) dirty ++
        upperForward (bit + 1) (dirty + 1) (count + 1)

def upperReverse : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | _, _, 1 => []
  | bit, dirty, count + 2 =>
      upperReverse (bit + 1) (dirty + 1) (count + 1) ++
        notAndGates bit (dirty + 1) dirty

def upperGates (bit dirty count : Nat) : List RGate :=
  upperForward bit dirty count ++ upperReverse bit dirty count

def lowerForward : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | bit, dirty, 1 => notBitGates bit dirty
  | bit, dirty, count + 2 =>
      notAndGates (bit + count + 1) (dirty + count) (dirty + count + 1) ++
        lowerForward bit dirty (count + 1)

def lowerReverse : Nat → Nat → Nat → List RGate
  | _, _, 0 => []
  | _, _, 1 => []
  | bit, dirty, count + 2 =>
      lowerReverse bit dirty (count + 1) ++
        notAndGates (bit + count + 1) (dirty + count) (dirty + count + 1)

def lowerGates (bit dirty count : Nat) : List RGate :=
  lowerForward bit dirty count ++ lowerReverse bit dirty count

theorem notAndGates_wellFormed {bit next target width : Nat}
    (hb : bit < width) (hn : next < width) (ht : target < width)
    (hbn : bit ≠ next) (hbt : bit ≠ target) (hnt : next ≠ target) :
    (notAndGates bit next target).all (RGate.wellFormed width) = true := by
  simp [notAndGates, RGate.wellFormed, hb, hn, ht, hbn, hbt, hnt]

theorem notBitGates_wellFormed {bit target width : Nat}
    (hb : bit < width) (ht : target < width) (hbt : bit ≠ target) :
    (notBitGates bit target).all (RGate.wellFormed width) = true := by
  simp [notBitGates, RGate.wellFormed, hb, ht, hbt]

theorem upperForward_wellFormed {bit dirty count width : Nat}
    (hbit : bit + count ≤ dirty) (hdirty : dirty + count ≤ width) :
    (upperForward bit dirty count).all (RGate.wellFormed width) = true := by
  induction count generalizing bit dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          exact notBitGates_wellFormed (by omega) (by omega) (by omega)
      | succ count =>
          simp only [upperForward, List.all_append, Bool.and_eq_true]
          exact ⟨notAndGates_wellFormed
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            ih (bit := bit + 1) (dirty := dirty + 1) (by omega) (by omega)⟩

theorem upperReverse_wellFormed {bit dirty count width : Nat}
    (hbit : bit + count ≤ dirty) (hdirty : dirty + count ≤ width) :
    (upperReverse bit dirty count).all (RGate.wellFormed width) = true := by
  induction count generalizing bit dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          simp only [upperReverse, List.all_append, Bool.and_eq_true]
          exact ⟨ih (bit := bit + 1) (dirty := dirty + 1)
              (by omega) (by omega),
            notAndGates_wellFormed
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem upperGates_wellFormed {bit dirty count width : Nat}
    (hbit : bit + count ≤ dirty) (hdirty : dirty + count ≤ width) :
    (upperGates bit dirty count).all (RGate.wellFormed width) = true := by
  simp only [upperGates, List.all_append, Bool.and_eq_true]
  exact ⟨upperForward_wellFormed hbit hdirty,
    upperReverse_wellFormed hbit hdirty⟩

theorem upperGates_length (bit dirty count : Nat) :
    (upperGates bit dirty count).length = 4 * count - 2 := by
  unfold upperGates
  induction count generalizing bit dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => simp [upperForward, upperReverse, notBitGates]
      | succ count =>
          simp only [upperForward, upperReverse, List.length_append,
            notAndGates, List.length_cons, List.length_nil]
          have h := ih (bit + 1) (dirty + 1)
          simp only [List.length_append] at h
          omega

theorem lowerForward_wellFormed {bit dirty count width : Nat}
    (hbit : bit + count ≤ dirty) (hdirty : dirty + count ≤ width) :
    (lowerForward bit dirty count).all (RGate.wellFormed width) = true := by
  induction count generalizing bit dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          exact notBitGates_wellFormed (by omega) (by omega) (by omega)
      | succ count =>
          simp only [lowerForward, List.all_append, Bool.and_eq_true]
          exact ⟨notAndGates_wellFormed
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            ih (bit := bit) (dirty := dirty) (by omega) (by omega)⟩

theorem lowerReverse_wellFormed {bit dirty count width : Nat}
    (hbit : bit + count ≤ dirty) (hdirty : dirty + count ≤ width) :
    (lowerReverse bit dirty count).all (RGate.wellFormed width) = true := by
  induction count generalizing bit dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          simp only [lowerReverse, List.all_append, Bool.and_eq_true]
          exact ⟨ih (bit := bit) (dirty := dirty) (by omega) (by omega),
            notAndGates_wellFormed
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem lowerGates_wellFormed {bit dirty count width : Nat}
    (hbit : bit + count ≤ dirty) (hdirty : dirty + count ≤ width) :
    (lowerGates bit dirty count).all (RGate.wellFormed width) = true := by
  simp only [lowerGates, List.all_append, Bool.and_eq_true]
  exact ⟨lowerForward_wellFormed hbit hdirty,
    lowerReverse_wellFormed hbit hdirty⟩

theorem lowerGates_length (bit dirty count : Nat) :
    (lowerGates bit dirty count).length = 4 * count - 2 := by
  unfold lowerGates
  induction count generalizing bit dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => simp [lowerForward, lowerReverse, notBitGates]
      | succ count =>
          simp only [lowerForward, lowerReverse, List.length_append,
            notAndGates, List.length_cons, List.length_nil]
          have h := ih bit dirty
          simp only [List.length_append] at h
          omega

def upperZero (i bit : Nat) : Nat → Nat
  | 0 => 1
  | count + 1 =>
      (1 - bitValue i bit) * upperZero i (bit + 1) count

theorem upperZero_lt (i bit count : Nat) : upperZero i bit count < 2 := by
  induction count generalizing bit with
  | zero => simp [upperZero]
  | succ count ih =>
      rw [upperZero]
      have hb := bitValue_lt i bit
      have hb' : bitValue i bit = 0 ∨ bitValue i bit = 1 := by omega
      rcases hb' with hb' | hb' <;> simp [hb', ih]

theorem upperZero_write_out {i target value bit count : Nat}
    (h : target < bit ∨ bit + count ≤ target) :
    upperZero (writeField i target 1 value) bit count =
      upperZero i bit count := by
  induction count generalizing bit with
  | zero => rfl
  | succ count ih =>
      rw [upperZero, upperZero, bitValue_write_ne (by omega),
        ih (bit := bit + 1) (by omega)]

theorem upperGates_succ_succ (bit dirty count : Nat) :
    upperGates bit dirty (count + 2) =
      notAndGates bit (dirty + 1) dirty ++
        upperGates (bit + 1) (dirty + 1) (count + 1) ++
        notAndGates bit (dirty + 1) dirty := by
  simp [upperGates, upperForward, upperReverse, List.append_assoc]

theorem upperGates_bitValue_out {bit dirty count i q : Nat}
    (hbit : bit + count ≤ dirty)
    (hq : q < dirty ∨ dirty + count ≤ q) :
    bitValue (actGates (upperGates bit dirty count) i) q = bitValue i q := by
  induction count generalizing bit dirty i with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          rw [upperGates, upperForward, upperReverse, List.append_nil,
            notBitGates_act (by omega), bitValue_write_ne (by omega)]
      | succ count =>
          let g := notAndGates bit (dirty + 1) dirty
          let i₁ := actGates g i
          let i₂ := actGates
            (upperGates (bit + 1) (dirty + 1) (count + 1)) i₁
          have hfirst : i₁ =
              writeField i dirty 1
                (notAndValue i bit (dirty + 1) dirty) := by
            exact notAndGates_act (by omega) (by omega)
          have hrec : bitValue i₂ q = bitValue i₁ q := by
            exact ih (bit := bit + 1) (dirty := dirty + 1) (i := i₁)
              (by omega) (by omega)
          have hlast : bitValue (actGates g i₂) q = bitValue i₂ q := by
            rw [notAndGates_act (by omega) (by omega),
              bitValue_write_ne (by omega)]
          rw [upperGates_succ_succ, actGates_append, actGates_append]
          change bitValue (actGates g i₂) q = bitValue i q
          rw [hlast, hrec, hfirst, bitValue_write_ne (by omega)]

theorem upperGates_bitValue {bit dirty count i j : Nat}
    (hbit : bit + count ≤ dirty) (hj : j < count) :
    bitValue (actGates (upperGates bit dirty count) i) (dirty + j) =
      (bitValue i (dirty + j) +
        upperZero i (bit + j) (count - j)) % 2 := by
  induction count generalizing bit dirty i j with
  | zero => omega
  | succ count ih =>
      cases count with
      | zero =>
          have hj0 : j = 0 := by omega
          subst j
          simp only [Nat.add_zero, Nat.sub_zero]
          rw [upperGates, upperForward, upperReverse, List.append_nil,
            notBitGates_act (by omega), bitValue_write_self]
          simp only [notBitValue, upperZero, Nat.mul_one, Nat.mod_mod]
          apply congrArg (fun x => x % 2)
          have hb := bitValue_lt i bit
          omega
      | succ count =>
          let g := notAndGates bit (dirty + 1) dirty
          let i₁ := actGates g i
          let i₂ := actGates
            (upperGates (bit + 1) (dirty + 1) (count + 1)) i₁
          have hfirst : i₁ =
              writeField i dirty 1
                (notAndValue i bit (dirty + 1) dirty) := by
            exact notAndGates_act (by omega) (by omega)
          have hlast : actGates g i₂ =
              writeField i₂ dirty 1
                (notAndValue i₂ bit (dirty + 1) dirty) := by
            exact notAndGates_act (by omega) (by omega)
          rw [upperGates_succ_succ, actGates_append, actGates_append]
          change bitValue (actGates g i₂) (dirty + j) = _
          cases j with
          | zero =>
              simp only [Nat.add_zero, Nat.sub_zero]
              have hsource₁ : bitValue i₁ bit = bitValue i bit := by
                rw [hfirst, bitValue_write_ne (by omega)]
              have hnext₁ : bitValue i₁ (dirty + 1) =
                  bitValue i (dirty + 1) := by
                rw [hfirst, bitValue_write_ne (by omega)]
              have htarget₁ : bitValue i₁ dirty =
                  notAndValue i bit (dirty + 1) dirty % 2 := by
                rw [hfirst, bitValue_write_self]
              have hsource₂ : bitValue i₂ bit = bitValue i₁ bit := by
                exact upperGates_bitValue_out (i := i₁) (by omega) (by omega)
              have htarget₂ : bitValue i₂ dirty = bitValue i₁ dirty := by
                exact upperGates_bitValue_out (i := i₁) (by omega) (by omega)
              have hnext₂ : bitValue i₂ (dirty + 1) =
                  (bitValue i₁ (dirty + 1) +
                    upperZero i₁ (bit + 1) (count + 1)) % 2 := by
                exact ih (bit := bit + 1) (dirty := dirty + 1)
                  (i := i₁) (j := 0) (by omega) (by omega)
              have hzero : upperZero i₁ (bit + 1) (count + 1) =
                  upperZero i (bit + 1) (count + 1) := by
                rw [hfirst]
                exact upperZero_write_out (by omega)
              rw [hlast, bitValue_write_self]
              unfold notAndValue
              rw [hsource₂, htarget₂, hnext₂, hzero, hsource₁, htarget₁,
                hnext₁]
              change _ = (bitValue i dirty + (1 - bitValue i bit) *
                upperZero i (bit + 1) (count + 1)) % 2
              have ha := bitValue_lt i bit
              have hn := bitValue_lt i (dirty + 1)
              have hd := bitValue_lt i dirty
              have hz := upperZero_lt i (bit + 1) (count + 1)
              have ha' : bitValue i bit = 0 ∨ bitValue i bit = 1 := by omega
              have hn' : bitValue i (dirty + 1) = 0 ∨
                  bitValue i (dirty + 1) = 1 := by omega
              have hd' : bitValue i dirty = 0 ∨ bitValue i dirty = 1 := by omega
              have hz' : upperZero i (bit + 1) (count + 1) = 0 ∨
                  upperZero i (bit + 1) (count + 1) = 1 := by omega
              rcases ha' with ha' | ha' <;>
                rcases hn' with hn' | hn' <;>
                rcases hd' with hd' | hd' <;>
                rcases hz' with hz' | hz' <;>
                simp [notAndValue, ha', hn', hd', hz']
          | succ j =>
              have hj' : j < count + 1 := by omega
              have hq : dirty + (j + 1) = (dirty + 1) + j := by omega
              have hinner : bitValue i₂ ((dirty + 1) + j) =
                  (bitValue i₁ ((dirty + 1) + j) +
                    upperZero i₁ ((bit + 1) + j) ((count + 1) - j)) % 2 := by
                exact ih (bit := bit + 1) (dirty := dirty + 1)
                  (i := i₁) (j := j) (by omega) hj'
              have hzero : upperZero i₁ ((bit + 1) + j) ((count + 1) - j) =
                  upperZero i ((bit + 1) + j) ((count + 1) - j) := by
                rw [hfirst]
                exact upperZero_write_out (by omega)
              rw [hlast, bitValue_write_ne (by omega), hq, hinner,
                hzero, hfirst, bitValue_write_ne (by omega)]
              have hbidx : (bit + 1) + j = bit + (j + 1) := by omega
              have hcidx : (count + 1) - j =
                  count + 1 + 1 - (j + 1) := by omega
              rw [hbidx, hcidx]

theorem upperZero_upperGates {source sourceCount bit dirty count i : Nat}
    (hbit : bit + count ≤ dirty)
    (hsource : source + sourceCount ≤ dirty) :
    upperZero (actGates (upperGates bit dirty count) i) source sourceCount =
      upperZero i source sourceCount := by
  induction sourceCount generalizing source with
  | zero => rfl
  | succ sourceCount ih =>
      rw [upperZero, upperZero,
        upperGates_bitValue_out hbit (Or.inl (by omega)),
        ih (source := source + 1) (by omega)]

theorem testBit_eq_of_bitValue_eq {i j q : Nat}
    (h : bitValue i q = bitValue j q) : i.testBit q = j.testBit q := by
  unfold bitValue at h
  cases hi : i.testBit q <;> cases hj : j.testBit q <;> simp_all

theorem upperGates_involutive {bit dirty count i : Nat}
    (hbit : bit + count ≤ dirty) :
    actGates (upperGates bit dirty count)
        (actGates (upperGates bit dirty count) i) = i := by
  apply Nat.eq_of_testBit_eq
  intro q
  apply testBit_eq_of_bitValue_eq
  by_cases hq : q < dirty ∨ dirty + count ≤ q
  · rw [upperGates_bitValue_out hbit hq,
      upperGates_bitValue_out hbit hq]
  · have hq' : dirty ≤ q ∧ q < dirty + count := by omega
    let j := q - dirty
    have hj : j < count := by omega
    have hqj : dirty + j = q := by omega
    rw [← hqj, upperGates_bitValue hbit hj,
      upperGates_bitValue hbit hj,
      upperZero_upperGates hbit (by omega)]
    have hd := bitValue_lt i (dirty + j)
    have hz := upperZero_lt i (bit + j) (count - j)
    omega

def lowerZero (i bit : Nat) : Nat → Nat
  | 0 => 1
  | count + 1 =>
      lowerZero i bit count * (1 - bitValue i (bit + count))

theorem lowerZero_lt (i bit count : Nat) : lowerZero i bit count < 2 := by
  induction count with
  | zero => simp [lowerZero]
  | succ count ih =>
      rw [lowerZero]
      have hb := bitValue_lt i (bit + count)
      have hb' : bitValue i (bit + count) = 0 ∨
          bitValue i (bit + count) = 1 := by omega
      rcases hb' with hb' | hb' <;> simp [hb', ih]

theorem lowerZero_write_out {i target value bit count : Nat}
    (h : target < bit ∨ bit + count ≤ target) :
    lowerZero (writeField i target 1 value) bit count =
      lowerZero i bit count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hprev : target < bit ∨ bit + count ≤ target := by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      rw [lowerZero, lowerZero, ih hprev,
        bitValue_write_ne (by omega)]

theorem lowerGates_succ_succ (bit dirty count : Nat) :
    lowerGates bit dirty (count + 2) =
      notAndGates (bit + count + 1) (dirty + count) (dirty + count + 1) ++
        lowerGates bit dirty (count + 1) ++
        notAndGates (bit + count + 1) (dirty + count) (dirty + count + 1) := by
  simp [lowerGates, lowerForward, lowerReverse, List.append_assoc]

theorem lowerGates_bitValue_out {bit dirty count i q : Nat}
    (hbit : bit + count ≤ dirty)
    (hq : q < dirty ∨ dirty + count ≤ q) :
    bitValue (actGates (lowerGates bit dirty count) i) q = bitValue i q := by
  induction count generalizing bit dirty i with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero =>
          rw [lowerGates, lowerForward, lowerReverse, List.append_nil,
            notBitGates_act (by omega), bitValue_write_ne (by omega)]
      | succ count =>
          let g := notAndGates (bit + count + 1) (dirty + count)
            (dirty + count + 1)
          let i₁ := actGates g i
          let i₂ := actGates (lowerGates bit dirty (count + 1)) i₁
          have hfirst : i₁ = writeField i (dirty + count + 1) 1
              (notAndValue i (bit + count + 1) (dirty + count)
                (dirty + count + 1)) := by
            exact notAndGates_act (by omega) (by omega)
          have hrec : bitValue i₂ q = bitValue i₁ q := by
            exact ih (bit := bit) (dirty := dirty) (i := i₁)
              (by omega) (by omega)
          have hlast : bitValue (actGates g i₂) q = bitValue i₂ q := by
            rw [notAndGates_act (by omega) (by omega),
              bitValue_write_ne (by omega)]
          rw [lowerGates_succ_succ, actGates_append, actGates_append]
          change bitValue (actGates g i₂) q = bitValue i q
          rw [hlast, hrec, hfirst, bitValue_write_ne (by omega)]

theorem lowerGates_bitValue {bit dirty count i j : Nat}
    (hbit : bit + count ≤ dirty) (hj : j < count) :
    bitValue (actGates (lowerGates bit dirty count) i) (dirty + j) =
      (bitValue i (dirty + j) + lowerZero i bit (j + 1)) % 2 := by
  induction count generalizing bit dirty i j with
  | zero => omega
  | succ count ih =>
      cases count with
      | zero =>
          have hj0 : j = 0 := by omega
          subst j
          simp only [Nat.add_zero]
          rw [lowerGates, lowerForward, lowerReverse, List.append_nil,
            notBitGates_act (by omega), bitValue_write_self]
          simp only [notBitValue, lowerZero, Nat.add_zero, Nat.one_mul,
            Nat.mod_mod]
          apply congrArg (fun x => x % 2)
          have hb := bitValue_lt i bit
          omega
      | succ count =>
          let g := notAndGates (bit + count + 1) (dirty + count)
            (dirty + count + 1)
          let i₁ := actGates g i
          let i₂ := actGates (lowerGates bit dirty (count + 1)) i₁
          have hfirst : i₁ = writeField i (dirty + count + 1) 1
              (notAndValue i (bit + count + 1) (dirty + count)
                (dirty + count + 1)) := by
            exact notAndGates_act (by omega) (by omega)
          have hlast : actGates g i₂ = writeField i₂ (dirty + count + 1) 1
              (notAndValue i₂ (bit + count + 1) (dirty + count)
                (dirty + count + 1)) := by
            exact notAndGates_act (by omega) (by omega)
          rw [lowerGates_succ_succ, actGates_append, actGates_append]
          change bitValue (actGates g i₂) (dirty + j) = _
          by_cases hjlow : j < count + 1
          · have hinner : bitValue i₂ (dirty + j) =
                (bitValue i₁ (dirty + j) + lowerZero i₁ bit (j + 1)) % 2 := by
              exact ih (bit := bit) (dirty := dirty) (i := i₁) (j := j)
                (by omega) hjlow
            have hzero : lowerZero i₁ bit (j + 1) =
                lowerZero i bit (j + 1) := by
              rw [hfirst]
              exact lowerZero_write_out (by omega)
            rw [hlast, bitValue_write_ne (by omega), hinner, hzero,
              hfirst, bitValue_write_ne (by omega)]
          · have hjhigh : j = count + 1 := by omega
            subst j
            have htargetIndex : dirty + (count + 1) =
                dirty + count + 1 := by omega
            rw [htargetIndex]
            have hsource₁ : bitValue i₁ (bit + count + 1) =
                bitValue i (bit + count + 1) := by
              rw [hfirst, bitValue_write_ne (by omega)]
            have hprev₁ : bitValue i₁ (dirty + count) =
                bitValue i (dirty + count) := by
              rw [hfirst, bitValue_write_ne (by omega)]
            have htarget₁ : bitValue i₁ (dirty + count + 1) =
                notAndValue i (bit + count + 1) (dirty + count)
                  (dirty + count + 1) % 2 := by
              rw [hfirst, bitValue_write_self]
            have hsource₂ : bitValue i₂ (bit + count + 1) =
                bitValue i₁ (bit + count + 1) := by
              exact lowerGates_bitValue_out (i := i₁) (by omega) (by omega)
            have htarget₂ : bitValue i₂ (dirty + count + 1) =
                bitValue i₁ (dirty + count + 1) := by
              exact lowerGates_bitValue_out (i := i₁) (by omega) (by omega)
            have hprev₂ : bitValue i₂ (dirty + count) =
                (bitValue i₁ (dirty + count) +
                  lowerZero i₁ bit (count + 1)) % 2 := by
              exact ih (bit := bit) (dirty := dirty) (i := i₁)
                (j := count) (by omega) (by omega)
            have hzero : lowerZero i₁ bit (count + 1) =
                lowerZero i bit (count + 1) := by
              rw [hfirst]
              exact lowerZero_write_out (by omega)
            rw [hlast, bitValue_write_self]
            unfold notAndValue
            rw [hsource₂, htarget₂, hprev₂, hzero, hsource₁, htarget₁,
              hprev₁]
            change _ = (bitValue i (dirty + count + 1) +
              lowerZero i bit (count + 1) *
                (1 - bitValue i (bit + count + 1))) % 2
            have ha := bitValue_lt i (bit + count + 1)
            have hp := bitValue_lt i (dirty + count)
            have hd := bitValue_lt i (dirty + count + 1)
            have hz := lowerZero_lt i bit (count + 1)
            have ha' : bitValue i (bit + count + 1) = 0 ∨
                bitValue i (bit + count + 1) = 1 := by omega
            have hp' : bitValue i (dirty + count) = 0 ∨
                bitValue i (dirty + count) = 1 := by omega
            have hd' : bitValue i (dirty + count + 1) = 0 ∨
                bitValue i (dirty + count + 1) = 1 := by omega
            have hz' : lowerZero i bit (count + 1) = 0 ∨
                lowerZero i bit (count + 1) = 1 := by omega
            rcases ha' with ha' | ha' <;>
              rcases hp' with hp' | hp' <;>
              rcases hd' with hd' | hd' <;>
              rcases hz' with hz' | hz' <;>
              simp [notAndValue, ha', hp', hd', hz', Nat.mul_comm]

theorem lowerZero_lowerGates {source sourceCount bit dirty count i : Nat}
    (hbit : bit + count ≤ dirty)
    (hsource : source + sourceCount ≤ dirty) :
    lowerZero (actGates (lowerGates bit dirty count) i) source sourceCount =
      lowerZero i source sourceCount := by
  induction sourceCount with
  | zero => rfl
  | succ sourceCount ih =>
      rw [lowerZero, lowerZero, ih (by omega),
        lowerGates_bitValue_out hbit (Or.inl (by omega))]

theorem lowerGates_involutive {bit dirty count i : Nat}
    (hbit : bit + count ≤ dirty) :
    actGates (lowerGates bit dirty count)
        (actGates (lowerGates bit dirty count) i) = i := by
  apply Nat.eq_of_testBit_eq
  intro q
  apply testBit_eq_of_bitValue_eq
  by_cases hq : q < dirty ∨ dirty + count ≤ q
  · rw [lowerGates_bitValue_out hbit hq,
      lowerGates_bitValue_out hbit hq]
  · have hq' : dirty ≤ q ∧ q < dirty + count := by omega
    let j := q - dirty
    have hj : j < count := by omega
    have hqj : dirty + j = q := by omega
    rw [← hqj, lowerGates_bitValue hbit hj,
      lowerGates_bitValue hbit hj,
      lowerZero_lowerGates hbit (by omega)]
    have hd := bitValue_lt i (dirty + j)
    have hz := lowerZero_lt i bit (j + 1)
    omega

theorem upperGates_ccx (bit dirty count : Nat) :
    (upperGates bit dirty count).countP RGate.isCcx = 2 * count - 2 := by
  induction count generalizing bit dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          rw [upperGates_succ_succ, List.countP_append,
            List.countP_append, ih]
          simp [notAndGates, RGate.isCcx]
          omega

theorem upperGates_cx (bit dirty count : Nat) :
    (upperGates bit dirty count).countP RGate.isCx = 2 * count - 1 := by
  induction count generalizing bit dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          rw [upperGates_succ_succ, List.countP_append,
            List.countP_append, ih]
          simp [notAndGates, List.countP_cons, RGate.isCx]
          omega

theorem lowerGates_ccx (bit dirty count : Nat) :
    (lowerGates bit dirty count).countP RGate.isCcx = 2 * count - 2 := by
  induction count generalizing bit dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          rw [lowerGates_succ_succ, List.countP_append,
            List.countP_append, ih]
          simp [notAndGates, RGate.isCcx]
          omega

theorem lowerGates_cx (bit dirty count : Nat) :
    (lowerGates bit dirty count).countP RGate.isCx = 2 * count - 1 := by
  induction count generalizing bit dirty with
  | zero => rfl
  | succ count ih =>
      cases count with
      | zero => rfl
      | succ count =>
          rw [lowerGates_succ_succ, List.countP_append,
            List.countP_append, ih]
          simp [notAndGates, List.countP_cons, RGate.isCx]
          omega

end DirtyZero
end Euclid
end VQ
