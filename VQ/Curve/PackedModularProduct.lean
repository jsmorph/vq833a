import VQ.Lookup.BatchedUncompute
import VQ.Reversible.Adder
import VQ.Reversible.Control
import VQ.Reversible.ControlledConstant

namespace VQ.Curve.PackedModularProduct

open Algebra Reversible Semantics

def copiedIndex (value dirty i : Nat) : Nat :=
  if i.testBit value then i ^^^ (1 <<< dirty) else i

def outputIndex (value dirty i : Nat) : Nat :=
  writeBit (copiedIndex value dirty i) value false

def correctionOps (value dirty : Nat) : List Op :=
  [.gate (.x value), .gate (.z dirty)]

def measureCopiedOps (value dirty cbit : Nat) : List Op :=
  [.gate (.cx value dirty), .gate (.h value), .measure value cbit,
    .branch (.localBit cbit) (correctionOps value dirty) []]

def recordParity (dirtyOffset : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | count + 1, creg, i =>
      Bool.xor (recordParity dirtyOffset count creg i)
        (i.testBit (dirtyOffset + count) && creg.testBit count)

theorem recordParity_writeBit_after {dirtyOffset count creg i cbit : Nat}
    {value : Bool} (hcount : count ≤ cbit) :
    recordParity dirtyOffset count (writeBit creg cbit value) i =
      recordParity dirtyOffset count creg i := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [recordParity, recordParity, ih (by omega),
        testBit_writeBit_of_ne (by omega)]

def phaseCorrectionOps (dirtyOffset : Nat) : Nat → List Op
  | 0 => []
  | count + 1 =>
      phaseCorrectionOps dirtyOffset count ++
        [.branch (.localBit count) [.gate (.z (dirtyOffset + count))] []]

def boolBit (b : Bool) : Nat := if b then 1 else 0

def xorProductGates (x y target : Nat)
    (invertX invertY : Bool) : List RGate :=
  match invertX, invertY with
  | false, false => [.ccx x y target]
  | false, true => [.x y, .ccx x y target, .x y]
  | true, false => [.x x, .ccx x y target, .x x]
  | true, true => [.x x, .x y, .ccx x y target, .x y, .x x]

def targetWire (bit : Nat) : Nat := bit

def dirtyWire (width bit : Nat) : Nat := width + bit

def carryWire (width bit : Nat) : Nat := 2 * width + bit % 2

def spareWire (width bit : Nat) : Nat := carryWire width (bit + 1)

def ancillaWire (width : Nat) : Nat := 2 * width + 2

def adderWidth (width : Nat) : Nat := 2 * width + 3

def gateOps (gates : List RGate) : List Op :=
  Lookup3.gateOps gates

def carryCoreGates (width bit : Nat) : List RGate :=
  [.cx (carryWire width bit) (ancillaWire width),
    .cx (carryWire width bit) (targetWire bit),
    .ccx (targetWire bit) (ancillaWire width) (spareWire width bit),
    .cx (carryWire width bit) (spareWire width bit),
    .cx (carryWire width bit) (ancillaWire width)]

def carryStepGates (constant width bit : Nat) : List RGate :=
  (if constant.testBit bit then [.x (ancillaWire width)] else []) ++
    carryCoreGates width bit ++
    if constant.testBit bit then
      [.x (ancillaWire width), .x (targetWire bit)]
    else []

def carryStepOps (constant width bit : Nat) : List Op :=
  gateOps (carryStepGates constant width bit) ++
    if bit = 0 then []
    else measureCopiedOps (carryWire width bit) (dirtyWire width (bit - 1))
      (bit - 1)

def carryPrefixOps (constant width : Nat) : Nat → List Op
  | 0 => []
  | count + 1 =>
      carryPrefixOps constant width count ++
        carryStepOps constant width count

def carryTopGates (constant width : Nat) : List RGate :=
  (if constant.testBit (width - 1) then
      [.x (targetWire (width - 1))]
    else []) ++
    [.cx (carryWire width (width - 1)) (targetWire (width - 1))]

def carryTopOps (constant width : Nat) : List Op :=
  gateOps (carryTopGates constant width) ++
    measureCopiedOps (carryWire width (width - 1))
      (dirtyWire width (width - 2)) (width - 2)

def carryChainOps (constant width : Nat) : List Op :=
  carryPrefixOps constant width (width - 1) ++ carryTopOps constant width

def carryReverseStepGates (constant width bit : Nat) : List RGate :=
  xorProductGates (targetWire bit) (dirtyWire width (bit - 1))
    (dirtyWire width bit) (constant.testBit bit) false

def carryForwardStepGates (constant width bit : Nat) : List RGate :=
  xorProductGates (targetWire bit) (dirtyWire width (bit - 1))
    (dirtyWire width bit) (constant.testBit bit) (constant.testBit bit)

def carryReverseGates (constant width : Nat) : Nat → List RGate
  | 0 => []
  | count + 1 =>
      carryReverseStepGates constant width (count + 1) ++
        carryReverseGates constant width count

def carryForwardGates (constant width : Nat) : Nat → List RGate
  | 0 => []
  | count + 1 =>
      carryForwardGates constant width count ++
        carryForwardStepGates constant width (count + 1)

def carryBaseGates (constant width : Nat) : List RGate :=
  xorProductGates (carryWire width 0) (targetWire 0) (dirtyWire width 0)
    (constant.testBit 0) (constant.testBit 0)

def carryReconstructionGates (constant width : Nat) : List RGate :=
  constantXorGates (2 ^ width - 1) 0 width ++
    carryReverseGates constant width (width - 2) ++
    constantXorGates constant width (width - 1) ++
    carryBaseGates constant width ++
    carryForwardGates constant width (width - 2) ++
    constantXorGates (2 ^ width - 1) 0 width

def constantAddOps (constant width : Nat) : List Op :=
  carryChainOps constant width ++
    (gateOps (carryReconstructionGates constant width) ++
      phaseCorrectionOps width (width - 1))

def carryStepOut (constant width bit i : Nat) : Nat :=
  let j := actGates (carryStepGates constant width bit) i
  if bit = 0 then j
  else outputIndex (carryWire width bit) (dirtyWire width (bit - 1)) j

def carryPrefixOut (constant width : Nat) : Nat → Nat → Nat
  | 0, i => i
  | count + 1, i =>
      carryStepOut constant width count
        (carryPrefixOut constant width count i)

def carryTopOut (constant width i : Nat) : Nat :=
  outputIndex (carryWire width (width - 1))
    (dirtyWire width (width - 2))
    (actGates (carryTopGates constant width) i)

def carryChainOut (constant width i : Nat) : Nat :=
  carryTopOut constant width
    (carryPrefixOut constant width (width - 1) i)

def addCarry (constant input : Nat) : Nat → Nat
  | 0 => 0
  | bit + 1 =>
      (bitValue input bit + bitValue constant bit +
        addCarry constant input bit) / 2

def CarryPrefixState (original constant width count state : Nat) : Prop :=
  count ≤ width ∧
  (∀ bit, bit < count →
    bitValue state (targetWire bit) =
      (bitValue original (targetWire bit) + bitValue constant bit +
        addCarry constant original bit) % 2) ∧
  (∀ bit, count ≤ bit → bit < width →
    bitValue state (targetWire bit) = bitValue original (targetWire bit)) ∧
  (∀ bit, bit + 1 < count →
    bitValue state (dirtyWire width bit) =
      (bitValue original (dirtyWire width bit) +
        addCarry constant original (bit + 1)) % 2) ∧
  (∀ bit, count ≤ bit + 1 → bit < width →
    bitValue state (dirtyWire width bit) =
      bitValue original (dirtyWire width bit)) ∧
  bitValue state (carryWire width count) = addCarry constant original count ∧
  bitValue state (spareWire width count) = 0 ∧
  bitValue state (ancillaWire width) = 0

def CarryChainState (original constant width state : Nat) : Prop :=
  (2 ≤ width) ∧
  (∀ bit, bit < width →
    bitValue state (targetWire bit) =
      (bitValue original (targetWire bit) + bitValue constant bit +
        addCarry constant original bit) % 2) ∧
  (∀ bit, bit + 1 < width →
    bitValue state (dirtyWire width bit) =
      (bitValue original (dirtyWire width bit) +
        addCarry constant original (bit + 1)) % 2) ∧
  bitValue state (dirtyWire width (width - 1)) =
    bitValue original (dirtyWire width (width - 1)) ∧
  bitValue state (carryWire width (width - 1)) = 0 ∧
  bitValue state (spareWire width (width - 1)) = 0 ∧
  bitValue state (ancillaWire width) = 0

theorem carryWire_lt (width bit : Nat) :
    carryWire width bit < adderWidth width := by
  have hmod := Nat.mod_lt bit (by omega : 0 < 2)
  simp only [carryWire, adderWidth]
  omega

theorem spareWire_lt (width bit : Nat) :
    spareWire width bit < adderWidth width := by
  exact carryWire_lt width (bit + 1)

theorem ancillaWire_lt (width : Nat) :
    ancillaWire width < adderWidth width := by
  simp [ancillaWire, adderWidth]

theorem carryWire_ne_spareWire (width bit : Nat) :
    carryWire width bit ≠ spareWire width bit := by
  intro h
  have hmod : bit % 2 = (bit + 1) % 2 := by
    simpa [carryWire, spareWire] using Nat.add_left_cancel h
  rcases Nat.mod_two_eq_zero_or_one bit with hb | hb <;>
    rw [Nat.add_mod, hb] at hmod <;> omega

@[simp] theorem carryWire_succ (width bit : Nat) :
    carryWire width (bit + 1) = spareWire width bit := rfl

@[simp] theorem spareWire_succ (width bit : Nat) :
    spareWire width (bit + 1) = carryWire width bit := by
  simp only [spareWire, carryWire]
  congr 1
  omega

theorem carryWire_ne_targetWire {width bit : Nat} (hbit : bit < width) :
    carryWire width bit ≠ targetWire bit := by
  simp [carryWire, targetWire]
  omega

theorem spareWire_ne_targetWire {width bit : Nat} (_hbit : bit < width) :
    spareWire width bit ≠ targetWire bit := by
  have hmod := Nat.mod_lt (bit + 1) (by omega : 0 < 2)
  simp [spareWire, carryWire, targetWire]
  omega

theorem ancillaWire_ne_targetWire {width bit : Nat} (hbit : bit < width) :
    ancillaWire width ≠ targetWire bit := by
  simp [ancillaWire, targetWire]
  omega

theorem carryWire_ne_ancillaWire (width bit : Nat) :
    carryWire width bit ≠ ancillaWire width := by
  have hmod := Nat.mod_lt bit (by omega : 0 < 2)
  simp [carryWire, ancillaWire]
  omega

theorem spareWire_ne_ancillaWire (width bit : Nat) :
    spareWire width bit ≠ ancillaWire width := by
  have hmod := Nat.mod_lt (bit + 1) (by omega : 0 < 2)
  simp [spareWire, carryWire, ancillaWire]
  omega

theorem addCarry_lt (constant input : Nat) : ∀ bit,
    addCarry constant input bit < 2 := by
  intro bit
  induction bit with
  | zero => simp [addCarry]
  | succ bit ih =>
      simp only [addCarry]
      have hi := bitValue_lt input bit
      have hc := bitValue_lt constant bit
      omega

theorem carryPrefixState_zero {original constant width : Nat}
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0) :
    CarryPrefixState original constant width 0 original := by
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, hspare, hancilla⟩
  · intro bit hbit
    omega
  · intro bit _ _
    rfl
  · intro bit hbit
    omega
  · intro bit _ _
    rfl
  · simpa [addCarry] using hcarry

theorem carryMajority {A K C : Nat}
    (hA : A < 2) (hK : K < 2) (hC : C < 2) :
    (C + (A + C) % 2 * ((K + C) % 2)) % 2 =
      (A + K + C) / 2 := by
  have ha : A = 0 ∨ A = 1 := by omega
  have hk : K = 0 ∨ K = 1 := by omega
  have hc : C = 0 ∨ C = 1 := by omega
  rcases ha with rfl | rfl <;>
    rcases hk with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rfl

theorem carryReconstructionIdentity {A K C : Nat}
    (hA : A < 2) (hK : K < 2) (hC : C < 2) :
    let sum := (A + K + C) % 2
    let next := (A + K + C) / 2
    let complement := (sum + 1) % 2
    (next + K + ((complement + K) % 2) * ((C + K) % 2)) % 2 = 0 := by
  have ha : A = 0 ∨ A = 1 := by omega
  have hk : K = 0 ∨ K = 1 := by omega
  have hc : C = 0 ∨ C = 1 := by omega
  rcases ha with rfl | rfl <;>
    rcases hk with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rfl

theorem carryReconstructionCancel {DPrev D A K C : Nat}
    (hDPrev : DPrev < 2) (hD : D < 2)
    (hA : A < 2) (hK : K < 2) (hC : C < 2) :
    let sum := (A + K + C) % 2
    let next := (A + K + C) / 2
    let complement := (sum + 1) % 2
    let factor := (complement + K) % 2
    let previousMixed := (DPrev + C) % 2
    let mixed := (D + next) % 2
    let reversed := (mixed + factor * previousMixed) % 2
    let shifted := (reversed + K) % 2
    (shifted + factor * ((DPrev + K) % 2)) % 2 = D := by
  have hdp : DPrev = 0 ∨ DPrev = 1 := by omega
  have hd : D = 0 ∨ D = 1 := by omega
  have ha : A = 0 ∨ A = 1 := by omega
  have hk : K = 0 ∨ K = 1 := by omega
  have hc : C = 0 ∨ C = 1 := by omega
  rcases hdp with rfl | rfl <;>
    rcases hd with rfl | rfl <;>
    rcases ha with rfl | rfl <;>
    rcases hk with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rfl

theorem bitValue_act_x_target (i q : Nat) :
    bitValue (RGate.act (.x q) i) q = (bitValue i q + 1) % 2 := by
  rw [Reversible.act_x_write, bitValue_write_self, Nat.mod_mod]

theorem bitValue_act_x_other {i q r : Nat} (h : r ≠ q) :
    bitValue (RGate.act (.x q) i) r = bitValue i r := by
  rw [Reversible.act_x_write, bitValue_write_ne h]

theorem bitValue_act_cx_target (i control target : Nat) :
    bitValue (RGate.act (.cx control target) i) target =
      (bitValue i target + bitValue i control) % 2 := by
  rw [Reversible.act_cx_write, bitValue_write_self, Nat.mod_mod]

theorem bitValue_act_cx_other {i control target q : Nat} (h : q ≠ target) :
    bitValue (RGate.act (.cx control target) i) q = bitValue i q := by
  rw [Reversible.act_cx_write, bitValue_write_ne h]

theorem bitValue_act_ccx_target (i x y target : Nat) :
    bitValue (RGate.act (.ccx x y target) i) target =
      (bitValue i target + bitValue i x * bitValue i y) % 2 := by
  rw [Reversible.act_ccx_write, bitValue_write_self, Nat.mod_mod]

theorem bitValue_act_ccx_other {i x y target q : Nat} (h : q ≠ target) :
    bitValue (RGate.act (.ccx x y target) i) q = bitValue i q := by
  rw [Reversible.act_ccx_write, bitValue_write_ne h]

theorem xorProductGates_target {x y target i : Nat}
    {invertX invertY : Bool}
    (hxy : x ≠ y) (hxt : x ≠ target) (hyt : y ≠ target) :
    bitValue (actGates
      (xorProductGates x y target invertX invertY) i) target =
      (bitValue i target +
        ((bitValue i x + boolBit invertX) % 2) *
        ((bitValue i y + boolBit invertY) % 2)) % 2 := by
  cases invertX <;> cases invertY
  · simp only [xorProductGates, boolBit, actGates_cons, actGates_nil]
    rw [bitValue_act_ccx_target]
    have hx : bitValue i x = 0 ∨ bitValue i x = 1 := by
      have := bitValue_lt i x; omega
    have hy : bitValue i y = 0 ∨ bitValue i y = 1 := by
      have := bitValue_lt i y; omega
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy]
  · simp only [xorProductGates, boolBit, actGates_cons, actGates_nil]
    rw [bitValue_act_x_other hyt.symm, bitValue_act_ccx_target,
      bitValue_act_x_other hyt.symm, bitValue_act_x_other hxy,
      bitValue_act_x_target]
    have hx : bitValue i x = 0 ∨ bitValue i x = 1 := by
      have := bitValue_lt i x; omega
    have hy : bitValue i y = 0 ∨ bitValue i y = 1 := by
      have := bitValue_lt i y; omega
    have ht : bitValue i target = 0 ∨ bitValue i target = 1 := by
      have := bitValue_lt i target; omega
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      rcases ht with ht | ht <;> simp [hx, hy, ht]
  · simp only [xorProductGates, boolBit, actGates_cons, actGates_nil]
    rw [bitValue_act_x_other hxt.symm, bitValue_act_ccx_target,
      bitValue_act_x_other hxt.symm, bitValue_act_x_target,
      bitValue_act_x_other hxy.symm]
    have hx : bitValue i x = 0 ∨ bitValue i x = 1 := by
      have := bitValue_lt i x; omega
    have hy : bitValue i y = 0 ∨ bitValue i y = 1 := by
      have := bitValue_lt i y; omega
    have ht : bitValue i target = 0 ∨ bitValue i target = 1 := by
      have := bitValue_lt i target; omega
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      rcases ht with ht | ht <;> simp [hx, hy, ht]
  · simp only [xorProductGates, boolBit, actGates_cons, actGates_nil]
    rw [bitValue_act_x_other hxt.symm,
      bitValue_act_x_other hyt.symm, bitValue_act_ccx_target,
      bitValue_act_x_other hyt.symm,
      bitValue_act_x_other hxy, bitValue_act_x_target,
      bitValue_act_x_other hxt.symm, bitValue_act_x_target,
      bitValue_act_x_other hxy.symm]
    have hx : bitValue i x = 0 ∨ bitValue i x = 1 := by
      have := bitValue_lt i x; omega
    have hy : bitValue i y = 0 ∨ bitValue i y = 1 := by
      have := bitValue_lt i y; omega
    have ht : bitValue i target = 0 ∨ bitValue i target = 1 := by
      have := bitValue_lt i target; omega
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      rcases ht with ht | ht <;> simp [hx, hy, ht]

theorem xorProductGates_other {x y target i q : Nat}
    {invertX invertY : Bool} (hxy : x ≠ y) (hq : q ≠ target) :
    bitValue (actGates
      (xorProductGates x y target invertX invertY) i) q =
      bitValue i q := by
  cases invertX <;> cases invertY
  · simp [xorProductGates, actGates, bitValue_act_ccx_other, hq]
  · simp only [xorProductGates, actGates_cons, actGates_nil]
    by_cases hqy : q = y
    · subst q
      rw [bitValue_act_x_target, bitValue_act_ccx_other hq,
        bitValue_act_x_target]
      have hy := bitValue_lt i y
      omega
    · rw [bitValue_act_x_other hqy, bitValue_act_ccx_other hq,
        bitValue_act_x_other hqy]
  · simp only [xorProductGates, actGates_cons, actGates_nil]
    by_cases hqx : q = x
    · subst q
      rw [bitValue_act_x_target, bitValue_act_ccx_other hq,
        bitValue_act_x_target]
      have hx := bitValue_lt i x
      omega
    · rw [bitValue_act_x_other hqx, bitValue_act_ccx_other hq,
        bitValue_act_x_other hqx]
  · simp only [xorProductGates, actGates_cons, actGates_nil]
    by_cases hqx : q = x
    · subst q
      rw [bitValue_act_x_target,
        bitValue_act_x_other hxy, bitValue_act_ccx_other hq,
        bitValue_act_x_other hxy, bitValue_act_x_target]
      have hx := bitValue_lt i x
      omega
    · by_cases hqy : q = y
      · subst q
        rw [bitValue_act_x_other hxy.symm, bitValue_act_x_target,
          bitValue_act_ccx_other hq, bitValue_act_x_target,
          bitValue_act_x_other hxy.symm]
        have hy := bitValue_lt i y
        omega
      · rw [bitValue_act_x_other hqx, bitValue_act_x_other hqy,
          bitValue_act_ccx_other hq, bitValue_act_x_other hqy,
          bitValue_act_x_other hqx]

@[simp] theorem boolBit_testBit (value bit : Nat) :
    boolBit (value.testBit bit) = bitValue value bit := by
  simp [boolBit, bitValue]

theorem bitValue_act_constantXorGates_inside
    {value wire width i bit : Nat} (hbit : bit < width) :
    bitValue (actGates (constantXorGates value wire width) i)
        (wire + bit) =
      (bitValue i (wire + bit) + bitValue value bit) % 2 := by
  unfold bitValue
  rw [act_constantXorGates, Nat.testBit_xor, Nat.testBit_shiftLeft,
    testBit_readField]
  simp only [show wire ≤ wire + bit by omega, decide_true,
    Bool.true_and, show wire + bit - wire = bit by omega, hbit]
  cases hi : i.testBit (wire + bit) <;>
    cases hv : value.testBit bit <;> simp [hv]

theorem bitValue_act_constantXorGates_outside
    {value wire width i q : Nat}
    (hq : q < wire ∨ wire + width ≤ q) :
    bitValue (actGates (constantXorGates value wire width) i) q =
      bitValue i q := by
  unfold bitValue
  rw [act_constantXorGates, Nat.testBit_xor, Nat.testBit_shiftLeft]
  rcases hq with hq | hq
  · simp [show ¬wire ≤ q by omega]
  · simp only [show wire ≤ q by omega, decide_true, Bool.true_and,
      testBit_readField]
    have hbit : ¬q - wire < width := by omega
    simp [hbit]

theorem bitValue_act_allOnesXorGates
    {wire width i bit : Nat} (hbit : bit < width) :
    bitValue
        (actGates (constantXorGates (2 ^ width - 1) wire width) i)
        (wire + bit) =
      (bitValue i (wire + bit) + 1) % 2 := by
  rw [bitValue_act_constantXorGates_inside hbit]
  simp [bitValue, Nat.testBit_two_pow_sub_one, hbit]

def carryReverseValue (original constant width bit : Nat) : Nat :=
  (bitValue original (dirtyWire width bit) +
      ((bitValue original (targetWire bit) + bitValue constant bit) % 2) *
        bitValue original (dirtyWire width (bit - 1))) % 2

def carryForwardValue (original constant width bit : Nat) : Nat :=
  (bitValue original (dirtyWire width bit) +
      ((bitValue original (targetWire bit) + bitValue constant bit) % 2) *
        ((bitValue original (dirtyWire width (bit - 1)) +
          bitValue constant bit) % 2)) % 2

theorem carryReverseStepGates_dirty {constant width bit i : Nat}
    (hpositive : 0 < bit) (hbit : bit < width) :
    bitValue (actGates (carryReverseStepGates constant width bit) i)
        (dirtyWire width bit) =
      carryReverseValue i constant width bit := by
  have hprevious : bit - 1 < width := by omega
  have hxy : targetWire bit ≠ dirtyWire width (bit - 1) :=
    by simp [targetWire, dirtyWire]; omega
  have hxt : targetWire bit ≠ dirtyWire width bit :=
    by simp [targetWire, dirtyWire]; omega
  have hyt : dirtyWire width (bit - 1) ≠ dirtyWire width bit := by
    simp [dirtyWire]
    omega
  rw [carryReverseStepGates,
    xorProductGates_target (i := i)
      (invertX := constant.testBit bit) (invertY := false) hxy hxt hyt]
  simp only [carryReverseValue, boolBit]
  have hconstant : (if constant.testBit bit = true then 1 else 0) =
      bitValue constant bit := by simp [bitValue]
  rw [hconstant]
  rw [show (if false = true then 1 else 0) = 0 by rfl, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (bitValue_lt i (dirtyWire width (bit - 1)))]

theorem carryForwardStepGates_dirty {constant width bit i : Nat}
    (hpositive : 0 < bit) (hbit : bit < width) :
    bitValue (actGates (carryForwardStepGates constant width bit) i)
        (dirtyWire width bit) =
      carryForwardValue i constant width bit := by
  have hprevious : bit - 1 < width := by omega
  have hxy : targetWire bit ≠ dirtyWire width (bit - 1) :=
    by simp [targetWire, dirtyWire]; omega
  have hxt : targetWire bit ≠ dirtyWire width bit :=
    by simp [targetWire, dirtyWire]; omega
  have hyt : dirtyWire width (bit - 1) ≠ dirtyWire width bit := by
    simp [dirtyWire]
    omega
  simpa [carryForwardStepGates, carryForwardValue] using
    (xorProductGates_target (i := i)
      (invertX := constant.testBit bit)
      (invertY := constant.testBit bit) hxy hxt hyt)

theorem carryReverseStepGates_other {constant width bit i q : Nat}
    (hpositive : 0 < bit) (hbit : bit < width)
    (hq : q ≠ dirtyWire width bit) :
    bitValue (actGates (carryReverseStepGates constant width bit) i) q =
      bitValue i q := by
  have hprevious : bit - 1 < width := by omega
  have hxy : targetWire bit ≠ dirtyWire width (bit - 1) :=
    by simp [targetWire, dirtyWire]; omega
  simpa [carryReverseStepGates] using
    (xorProductGates_other (i := i)
      (invertX := constant.testBit bit) (invertY := false) hxy hq)

theorem carryForwardStepGates_other {constant width bit i q : Nat}
    (hpositive : 0 < bit) (hbit : bit < width)
    (hq : q ≠ dirtyWire width bit) :
    bitValue (actGates (carryForwardStepGates constant width bit) i) q =
      bitValue i q := by
  have hprevious : bit - 1 < width := by omega
  have hxy : targetWire bit ≠ dirtyWire width (bit - 1) :=
    by simp [targetWire, dirtyWire]; omega
  simpa [carryForwardStepGates] using
    (xorProductGates_other (i := i)
      (invertX := constant.testBit bit)
      (invertY := constant.testBit bit) hxy hq)

theorem carryReverseGates_other {constant width count i q : Nat}
    (hcount : count < width)
    (hq : ∀ bit, 0 < bit → bit ≤ count → q ≠ dirtyWire width bit) :
    bitValue (actGates (carryReverseGates constant width count) i) q =
      bitValue i q := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      rw [carryReverseGates, actGates_append,
        ih (by omega) (fun bit hpositive hbit => hq bit hpositive (by omega)),
        carryReverseStepGates_other (by omega) hcount
          (hq (count + 1) (by omega) (by omega))]

theorem carryForwardGates_other {constant width count i q : Nat}
    (hcount : count < width)
    (hq : ∀ bit, 0 < bit → bit ≤ count → q ≠ dirtyWire width bit) :
    bitValue (actGates (carryForwardGates constant width count) i) q =
      bitValue i q := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      rw [carryForwardGates, actGates_append,
        carryForwardStepGates_other (by omega) hcount
          (hq (count + 1) (by omega) (by omega)),
        ih (by omega) (fun bit hpositive hbit => hq bit hpositive (by omega))]

theorem carryReverseGates_dirty {constant width count i bit : Nat}
    (hcount : count < width) (hpositive : 0 < bit) (hbit : bit ≤ count) :
    bitValue (actGates (carryReverseGates constant width count) i)
        (dirtyWire width bit) =
      carryReverseValue i constant width bit := by
  induction count generalizing i bit with
  | zero => omega
  | succ count ih =>
      rw [carryReverseGates, actGates_append]
      by_cases htop : bit = count + 1
      · subst bit
        rw [carryReverseGates_other (by omega)
          (fun other _ hother => by simp [dirtyWire]; omega),
          carryReverseStepGates_dirty (by omega) hcount]
      · have hbelow : bit ≤ count := by omega
        rw [ih (by omega) hpositive hbelow]
        unfold carryReverseValue
        rw [carryReverseStepGates_other (by omega) hcount
              (by simp [dirtyWire]; omega),
          carryReverseStepGates_other (by omega) hcount
              (by simp [targetWire, dirtyWire]; omega),
          carryReverseStepGates_other (by omega) hcount
              (by simp [dirtyWire]; omega)]

def carryShiftedValue (original constant width bit : Nat) : Nat :=
  let A := bitValue original (targetWire bit)
  let K := bitValue constant bit
  let C := addCarry constant original bit
  let sum := (A + K + C) % 2
  let next := (A + K + C) / 2
  let complement := (sum + 1) % 2
  let factor := (complement + K) % 2
  let previousMixed :=
    (bitValue original (dirtyWire width (bit - 1)) + C) % 2
  let mixed :=
    (bitValue original (dirtyWire width bit) + next) % 2
  let reversed := (mixed + factor * previousMixed) % 2
  (reversed + K) % 2

theorem carryForwardGates_restore
    {original constant width count state : Nat}
    (hcount : count < width)
    (htarget : ∀ bit, bit ≤ count →
      bitValue state (targetWire bit) =
        ((bitValue original (targetWire bit) + bitValue constant bit +
          addCarry constant original bit) % 2 + 1) % 2)
    (hzero : bitValue state (dirtyWire width 0) =
      bitValue original (dirtyWire width 0))
    (hshifted : ∀ bit, 0 < bit → bit ≤ count →
      bitValue state (dirtyWire width bit) =
        carryShiftedValue original constant width bit) :
    ∀ bit, bit ≤ count →
      bitValue (actGates (carryForwardGates constant width count) state)
          (dirtyWire width bit) =
        bitValue original (dirtyWire width bit) := by
  induction count generalizing state with
  | zero =>
      intro bit hbit
      have : bit = 0 := by omega
      subst bit
      exact hzero
  | succ count ih =>
      intro bit hbit
      let prior := actGates (carryForwardGates constant width count) state
      rw [carryForwardGates, actGates_append]
      by_cases htop : bit = count + 1
      · subst bit
        rw [carryForwardStepGates_dirty (by omega) hcount]
        unfold carryForwardValue
        have hpriorCurrent :
            bitValue prior (dirtyWire width (count + 1)) =
              bitValue state (dirtyWire width (count + 1)) := by
          simpa [prior] using carryForwardGates_other
            (constant := constant) (i := state) (q := dirtyWire width (count + 1))
            (by omega) (fun other _ hother => by simp [dirtyWire]; omega)
        have hpriorTarget :
            bitValue prior (targetWire (count + 1)) =
              bitValue state (targetWire (count + 1)) := by
          simpa [prior] using carryForwardGates_other
            (constant := constant) (i := state) (q := targetWire (count + 1))
            (by omega) (fun other _ _ => by simp [targetWire, dirtyWire]; omega)
        have hpriorPrevious :
            bitValue prior (dirtyWire width count) =
              bitValue original (dirtyWire width count) := by
          simpa [prior] using ih (by omega)
            (fun q hq => htarget q (by omega)) hzero
            (fun q hpositive hq => hshifted q hpositive (by omega))
            count (by omega)
        rw [hpriorCurrent, hpriorTarget,
          show count + 1 - 1 = count by omega, hpriorPrevious,
          hshifted (count + 1) (by omega) (by omega),
          htarget (count + 1) (by omega)]
        simpa [carryShiftedValue] using
          (carryReconstructionCancel
            (DPrev := bitValue original (dirtyWire width count))
            (D := bitValue original (dirtyWire width (count + 1)))
            (A := bitValue original (targetWire (count + 1)))
            (K := bitValue constant (count + 1))
            (C := addCarry constant original (count + 1))
            (bitValue_lt _ _) (bitValue_lt _ _) (bitValue_lt _ _)
            (bitValue_lt _ _) (addCarry_lt constant original (count + 1)))
      · have hbelow : bit ≤ count := by omega
        rw [carryForwardStepGates_other (by omega) hcount
              (by simp [dirtyWire]; omega)]
        exact ih (by omega) (fun q hq => htarget q (by omega)) hzero
          (fun q hpositive hq => hshifted q hpositive (by omega))
          bit hbelow

def carryBaseValue (state constant width : Nat) : Nat :=
  (bitValue state (dirtyWire width 0) +
      ((bitValue state (carryWire width 0) + bitValue constant 0) % 2) *
        ((bitValue state (targetWire 0) + bitValue constant 0) % 2)) % 2

theorem carryBaseGates_dirty {constant width state : Nat}
    (hwidth : 0 < width) :
    bitValue (actGates (carryBaseGates constant width) state)
        (dirtyWire width 0) =
      carryBaseValue state constant width := by
  have hxy : carryWire width 0 ≠ targetWire 0 := by
    simp [carryWire, targetWire]
    omega
  have hxt : carryWire width 0 ≠ dirtyWire width 0 := by
    simp [carryWire, dirtyWire]
    omega
  have hyt : targetWire 0 ≠ dirtyWire width 0 := by
    simp [targetWire, dirtyWire]
    omega
  rw [carryBaseGates,
    xorProductGates_target (i := state)
      (invertX := constant.testBit 0) (invertY := constant.testBit 0)
      hxy hxt hyt]
  change _ = carryBaseValue state constant width
  rw [boolBit_testBit]
  rfl

theorem carryBaseGates_other {constant width state q : Nat}
    (hwidth : 0 < width) (hq : q ≠ dirtyWire width 0) :
    bitValue (actGates (carryBaseGates constant width) state) q =
      bitValue state q := by
  have hxy : carryWire width 0 ≠ targetWire 0 := by
    simp [carryWire, targetWire]
    omega
  simpa [carryBaseGates] using
    (xorProductGates_other (i := state)
      (invertX := constant.testBit 0) (invertY := constant.testBit 0)
      hxy hq)

def CarryReconstructedState
    (original constant width state : Nat) : Prop :=
  2 ≤ width ∧
  (∀ bit, bit < width →
    bitValue state (targetWire bit) =
      (bitValue original (targetWire bit) + bitValue constant bit +
        addCarry constant original bit) % 2) ∧
  (∀ bit, bit < width →
    bitValue state (dirtyWire width bit) =
      bitValue original (dirtyWire width bit)) ∧
  bitValue state (carryWire width (width - 1)) = 0 ∧
  bitValue state (spareWire width (width - 1)) = 0 ∧
  bitValue state (ancillaWire width) = 0

theorem carryComplementedTarget {original constant width state bit : Nat}
    (hstate : CarryChainState original constant width state)
    (hbit : bit < width) :
    bitValue
        (actGates (constantXorGates (2 ^ width - 1) 0 width) state)
        (targetWire bit) =
      ((bitValue original (targetWire bit) + bitValue constant bit +
        addCarry constant original bit) % 2 + 1) % 2 := by
  rw [show bitValue
      (actGates (constantXorGates (2 ^ width - 1) 0 width) state)
      (targetWire bit) =
        (bitValue state (targetWire bit) + 1) % 2 by
      simpa [targetWire] using
        (bitValue_act_allOnesXorGates (wire := 0) (i := state) hbit)]
  rw [hstate.2.1 bit hbit]

theorem carryComplementedDirty {width state bit : Nat} :
    bitValue
        (actGates (constantXorGates (2 ^ width - 1) 0 width) state)
        (dirtyWire width bit) =
      bitValue state (dirtyWire width bit) := by
  apply bitValue_act_constantXorGates_outside
  right
  simp [dirtyWire]

theorem carryShiftedGates_dirty
    {original constant width state bit : Nat}
    (hstate : CarryChainState original constant width state)
    (hpositive : 0 < bit) (hbit : bit + 1 < width) :
    let complemented :=
      actGates (constantXorGates (2 ^ width - 1) 0 width) state
    let reversed :=
      actGates (carryReverseGates constant width (width - 2)) complemented
    let shifted :=
      actGates (constantXorGates constant width (width - 1)) reversed
    bitValue shifted (dirtyWire width bit) =
      carryShiftedValue original constant width bit := by
  let complemented :=
    actGates (constantXorGates (2 ^ width - 1) 0 width) state
  let reversed :=
    actGates (carryReverseGates constant width (width - 2)) complemented
  let shifted :=
    actGates (constantXorGates constant width (width - 1)) reversed
  have hchainDirty := hstate.2.2.1
  change bitValue shifted (dirtyWire width bit) = _
  rw [show dirtyWire width bit = width + bit by rfl,
    show shifted = actGates
      (constantXorGates constant width (width - 1)) reversed by rfl,
    bitValue_act_constantXorGates_inside (by omega)]
  change (bitValue reversed (dirtyWire width bit) +
    bitValue constant bit) % 2 = _
  rw [show reversed = actGates
      (carryReverseGates constant width (width - 2)) complemented by rfl,
    carryReverseGates_dirty (by omega) hpositive (by omega)]
  unfold carryReverseValue
  rw [show bitValue complemented (dirtyWire width bit) =
        bitValue state (dirtyWire width bit) by
      simpa [complemented] using carryComplementedDirty,
    show bitValue complemented (targetWire bit) =
        ((bitValue original (targetWire bit) + bitValue constant bit +
          addCarry constant original bit) % 2 + 1) % 2 by
      simpa [complemented] using carryComplementedTarget hstate (by omega),
    show bitValue complemented (dirtyWire width (bit - 1)) =
        bitValue state (dirtyWire width (bit - 1)) by
      simpa [complemented] using carryComplementedDirty]
  rw [hchainDirty bit hbit,
    hchainDirty (bit - 1) (by omega),
    show bit - 1 + 1 = bit by omega,
    show addCarry constant original (bit + 1) =
      (bitValue original (targetWire bit) + bitValue constant bit +
        addCarry constant original bit) / 2 by rfl]
  rfl

theorem carryChainState_carryZero {original constant width state : Nat}
    (hstate : CarryChainState original constant width state) :
    bitValue state (carryWire width 0) = 0 := by
  have hwidth := hstate.1
  have hcarry := hstate.2.2.2.2.1
  have hspare := hstate.2.2.2.2.2.1
  rcases Nat.mod_two_eq_zero_or_one (width - 1) with hmod | hmod
  · simpa [carryWire, hmod] using hcarry
  · have hwidthMod : width % 2 = 0 := by
      calc
        width % 2 = ((width - 1) + 1) % 2 := by
          congr 1
          omega
        _ = (((width - 1) % 2) + (1 % 2)) % 2 := by
          rw [Nat.add_mod]
        _ = 0 := by simp [hmod]
    change bitValue state (2 * width + ((width - 1 + 1) % 2)) = 0 at hspare
    rw [show width - 1 + 1 = width by omega, hwidthMod, Nat.add_zero]
      at hspare
    simpa [carryWire] using hspare

theorem addOneModTwo_twice {value : Nat} (hvalue : value < 2) :
    (((value + 1) % 2) + 1) % 2 = value := by
  have hcases : value = 0 ∨ value = 1 := by omega
  rcases hcases with rfl | rfl <;> rfl

theorem carryReconstructionGates_state
    {original constant width state : Nat}
    (hstate : CarryChainState original constant width state) :
    CarryReconstructedState original constant width
      (actGates (carryReconstructionGates constant width) state) := by
  let complemented :=
    actGates (constantXorGates (2 ^ width - 1) 0 width) state
  let reversed :=
    actGates (carryReverseGates constant width (width - 2)) complemented
  let shifted :=
    actGates (constantXorGates constant width (width - 1)) reversed
  let based := actGates (carryBaseGates constant width) shifted
  let forwarded :=
    actGates (carryForwardGates constant width (width - 2)) based
  let result :=
    actGates (constantXorGates (2 ^ width - 1) 0 width) forwarded
  have hwidth := hstate.1
  have hcomplementedTarget : ∀ bit, bit < width →
      bitValue complemented (targetWire bit) =
        ((bitValue original (targetWire bit) + bitValue constant bit +
          addCarry constant original bit) % 2 + 1) % 2 := by
    intro bit hbit
    simpa [complemented] using carryComplementedTarget hstate hbit
  have hreversedTarget : ∀ bit, bit < width →
      bitValue reversed (targetWire bit) =
        bitValue complemented (targetWire bit) := by
    intro bit hbit
    simpa [reversed] using carryReverseGates_other
      (constant := constant) (i := complemented) (q := targetWire bit)
      (by omega) (fun other _ _ => by
        simp [targetWire, dirtyWire]
        omega)
  have hshiftedTarget : ∀ bit, bit < width →
      bitValue shifted (targetWire bit) =
        bitValue complemented (targetWire bit) := by
    intro bit hbit
    rw [show shifted = actGates
      (constantXorGates constant width (width - 1)) reversed by rfl,
      bitValue_act_constantXorGates_outside (Or.inl (by
        simp [targetWire]
        omega)), hreversedTarget bit hbit]
  have hbasedTarget : ∀ bit, bit < width →
      bitValue based (targetWire bit) =
        bitValue complemented (targetWire bit) := by
    intro bit hbit
    rw [show based = actGates (carryBaseGates constant width) shifted by rfl,
      carryBaseGates_other (by omega) (by
        simp [targetWire, dirtyWire]
        omega), hshiftedTarget bit hbit]
  have hshiftedZero : bitValue shifted (dirtyWire width 0) =
      ((bitValue original (dirtyWire width 0) +
        addCarry constant original 1) % 2 + bitValue constant 0) % 2 := by
    rw [show dirtyWire width 0 = width + 0 by rfl,
      show shifted = actGates
        (constantXorGates constant width (width - 1)) reversed by rfl,
      bitValue_act_constantXorGates_inside (by omega)]
    change (bitValue reversed (dirtyWire width 0) +
      bitValue constant 0) % 2 = _
    rw [show reversed = actGates
        (carryReverseGates constant width (width - 2)) complemented by rfl,
      carryReverseGates_other (by omega) (fun bit hpositive _ => by
        simp [dirtyWire]
        omega),
      show bitValue complemented (dirtyWire width 0) =
          bitValue state (dirtyWire width 0) by
        simpa [complemented] using carryComplementedDirty,
      hstate.2.2.1 0 (by omega)]
    simp [dirtyWire]
  have hshiftedCarryZero : bitValue shifted (carryWire width 0) = 0 := by
    rw [show shifted = actGates
        (constantXorGates constant width (width - 1)) reversed by rfl,
      bitValue_act_constantXorGates_outside (Or.inr (by
        simp [carryWire]
        omega)),
      show reversed = actGates
        (carryReverseGates constant width (width - 2)) complemented by rfl,
      carryReverseGates_other (by omega) (fun bit _ _ => by
        simp [carryWire, dirtyWire]
        omega),
      show bitValue complemented (carryWire width 0) =
          bitValue state (carryWire width 0) by
        apply bitValue_act_constantXorGates_outside
        right
        simp [carryWire]
        omega,
      carryChainState_carryZero hstate]
  have hbasedZero : bitValue based (dirtyWire width 0) =
      bitValue original (dirtyWire width 0) := by
    rw [show based = actGates (carryBaseGates constant width) shifted by rfl,
      carryBaseGates_dirty (by omega)]
    unfold carryBaseValue
    rw [hshiftedZero, hshiftedCarryZero,
      hshiftedTarget 0 (by omega), hcomplementedTarget 0 (by omega)]
    simpa [addCarry, Nat.mul_comm, targetWire] using
      (carryReconstructionCancel
        (DPrev := 0)
        (D := bitValue original (dirtyWire width 0))
        (A := bitValue original (targetWire 0))
        (K := bitValue constant 0) (C := 0)
        (by omega) (bitValue_lt _ _) (bitValue_lt _ _)
        (bitValue_lt _ _) (by omega))
  have hbasedShifted : ∀ bit, 0 < bit → bit ≤ width - 2 →
      bitValue based (dirtyWire width bit) =
        carryShiftedValue original constant width bit := by
    intro bit hpositive hbit
    rw [show based = actGates (carryBaseGates constant width) shifted by rfl,
      carryBaseGates_other (by omega) (by simp [dirtyWire]; omega)]
    simpa [shifted, reversed, complemented] using
      carryShiftedGates_dirty hstate hpositive (by omega)
  have hforwardedDirty : ∀ bit, bit ≤ width - 2 →
      bitValue forwarded (dirtyWire width bit) =
        bitValue original (dirtyWire width bit) := by
    intro bit hbit
    simpa [forwarded] using carryForwardGates_restore
      (original := original) (constant := constant) (state := based)
      (by omega)
      (fun q hq => by
        rw [hbasedTarget q (by omega), hcomplementedTarget q (by omega)])
      hbasedZero hbasedShifted bit hbit
  have hforwardedTarget : ∀ bit, bit < width →
      bitValue forwarded (targetWire bit) =
        bitValue complemented (targetWire bit) := by
    intro bit hbit
    rw [show forwarded = actGates
        (carryForwardGates constant width (width - 2)) based by rfl,
      carryForwardGates_other (by omega) (fun other _ _ => by
        simp [targetWire, dirtyWire]
        omega), hbasedTarget bit hbit]
  have hforwardedTop :
      bitValue forwarded (dirtyWire width (width - 1)) =
        bitValue original (dirtyWire width (width - 1)) := by
    rw [show forwarded = actGates
        (carryForwardGates constant width (width - 2)) based by rfl,
      carryForwardGates_other (by omega) (fun bit _ hbit => by
        simp [dirtyWire]
        omega),
      show based = actGates (carryBaseGates constant width) shifted by rfl,
      carryBaseGates_other (by omega) (by simp [dirtyWire]; omega),
      show shifted = actGates
        (constantXorGates constant width (width - 1)) reversed by rfl,
      bitValue_act_constantXorGates_outside (Or.inr (by
        simp [dirtyWire])),
      show reversed = actGates
        (carryReverseGates constant width (width - 2)) complemented by rfl,
      carryReverseGates_other (by omega) (fun bit _ hbit => by
        simp [dirtyWire]
        omega),
      show bitValue complemented (dirtyWire width (width - 1)) =
          bitValue state (dirtyWire width (width - 1)) by
        simpa [complemented] using carryComplementedDirty,
      hstate.2.2.2.1]
  have hforwardedHigh : ∀ q, 2 * width ≤ q →
      bitValue forwarded q = bitValue state q := by
    intro q hq
    rw [show forwarded = actGates
        (carryForwardGates constant width (width - 2)) based by rfl,
      carryForwardGates_other (by omega) (fun bit _ _ => by
        simp [dirtyWire]
        omega),
      show based = actGates (carryBaseGates constant width) shifted by rfl,
      carryBaseGates_other (by omega) (by simp [dirtyWire]; omega),
      show shifted = actGates
        (constantXorGates constant width (width - 1)) reversed by rfl,
      bitValue_act_constantXorGates_outside (Or.inr (by omega)),
      show reversed = actGates
        (carryReverseGates constant width (width - 2)) complemented by rfl,
      carryReverseGates_other (by omega) (fun bit _ _ => by
        simp [dirtyWire]
        omega),
      show bitValue complemented q = bitValue state q by
        apply bitValue_act_constantXorGates_outside
        right
        omega]
  have hresultTarget : ∀ bit, bit < width →
      bitValue result (targetWire bit) =
        (bitValue original (targetWire bit) + bitValue constant bit +
          addCarry constant original bit) % 2 := by
    intro bit hbit
    rw [show bitValue result (targetWire bit) =
        (bitValue forwarded (targetWire bit) + 1) % 2 by
      simpa [result, targetWire] using
        (bitValue_act_allOnesXorGates (wire := 0) (i := forwarded) hbit),
      hforwardedTarget bit hbit, hcomplementedTarget bit hbit]
    apply addOneModTwo_twice
    exact Nat.mod_lt _ (by omega)
  have hresultDirty : ∀ bit, bit < width →
      bitValue result (dirtyWire width bit) =
        bitValue original (dirtyWire width bit) := by
    intro bit hbit
    rw [show bitValue result (dirtyWire width bit) =
        bitValue forwarded (dirtyWire width bit) by
      simpa [result] using
        (bitValue_act_constantXorGates_outside
          (value := 2 ^ width - 1) (wire := 0) (width := width)
          (i := forwarded) (q := dirtyWire width bit) (Or.inr (by
            simp [dirtyWire])))]
    by_cases htop : bit = width - 1
    · subst bit
      exact hforwardedTop
    · exact hforwardedDirty bit (by omega)
  have hresultHigh : ∀ q, 2 * width ≤ q →
      bitValue result q = bitValue state q := by
    intro q hq
    rw [show bitValue result q = bitValue forwarded q by
      simpa [result] using
        (bitValue_act_constantXorGates_outside
          (value := 2 ^ width - 1) (wire := 0) (width := width)
          (i := forwarded) (q := q) (Or.inr (by omega))),
      hforwardedHigh q hq]
  have hresultEq :
      actGates (carryReconstructionGates constant width) state = result := by
    rw [carryReconstructionGates]
    simp only [actGates_append]
    rfl
  rw [hresultEq]
  change CarryReconstructedState original constant width result
  refine ⟨hwidth, hresultTarget, hresultDirty, ?_, ?_, ?_⟩
  · rw [hresultHigh (carryWire width (width - 1)) (by
      simp [carryWire]), hstate.2.2.2.2.1]
  · rw [hresultHigh (spareWire width (width - 1)) (by
      have hmod := Nat.mod_lt (width - 1 + 1) (by omega : 0 < 2)
      simp [spareWire, carryWire]), hstate.2.2.2.2.2.1]
  · rw [hresultHigh (ancillaWire width) (by
      simp [ancillaWire]), hstate.2.2.2.2.2.2]

theorem carryCoreGates_bits {width bit i K : Nat}
    (hbit : bit < width)
    (hspare : bitValue i (spareWire width bit) = 0)
    (hancilla : bitValue i (ancillaWire width) = K)
    (hK : K < 2) :
    let j := actGates (carryCoreGates width bit) i
    bitValue j (targetWire bit) =
        (bitValue i (targetWire bit) + bitValue i (carryWire width bit)) % 2 ∧
      bitValue j (carryWire width bit) = bitValue i (carryWire width bit) ∧
      bitValue j (spareWire width bit) =
        (bitValue i (targetWire bit) + K +
          bitValue i (carryWire width bit)) / 2 ∧
      bitValue j (ancillaWire width) = K := by
  let target := targetWire bit
  let current := carryWire width bit
  let spare := spareWire width bit
  let ancilla := ancillaWire width
  have htc : target ≠ current := by
    exact (carryWire_ne_targetWire hbit).symm
  have hts : target ≠ spare := by
    exact (spareWire_ne_targetWire hbit).symm
  have hta : target ≠ ancilla := by
    exact (ancillaWire_ne_targetWire hbit).symm
  have hcs : current ≠ spare := carryWire_ne_spareWire width bit
  have hca : current ≠ ancilla := carryWire_ne_ancillaWire width bit
  have hsa : spare ≠ ancilla := spareWire_ne_ancillaWire width bit
  let i1 := RGate.act (.cx current ancilla) i
  let i2 := RGate.act (.cx current target) i1
  let i3 := RGate.act (.ccx target ancilla spare) i2
  let i4 := RGate.act (.cx current spare) i3
  let i5 := RGate.act (.cx current ancilla) i4
  have h1a : bitValue i1 ancilla =
      (K + bitValue i current) % 2 := by
    rw [show bitValue i1 ancilla =
      (bitValue i ancilla + bitValue i current) % 2 by
        simpa [i1] using bitValue_act_cx_target i current ancilla,
      hancilla]
  have h1t : bitValue i1 target = bitValue i target := by
    simpa [i1] using bitValue_act_cx_other
      (i := i) (control := current) (target := ancilla) hta
  have h1c : bitValue i1 current = bitValue i current := by
    simpa [i1] using bitValue_act_cx_other
      (i := i) (control := current) (target := ancilla) hca
  have h1s : bitValue i1 spare = 0 := by
    rw [show bitValue i1 spare = bitValue i spare by
      simpa [i1] using bitValue_act_cx_other
        (i := i) (control := current) (target := ancilla) hsa,
      hspare]
  have h2t : bitValue i2 target =
      (bitValue i target + bitValue i current) % 2 := by
    rw [show bitValue i2 target =
      (bitValue i1 target + bitValue i1 current) % 2 by
        simpa [i2] using bitValue_act_cx_target i1 current target,
      h1t, h1c]
  have h2a : bitValue i2 ancilla = bitValue i1 ancilla := by
    simpa [i2] using bitValue_act_cx_other
      (i := i1) (control := current) (target := target) hta.symm
  have h2c : bitValue i2 current = bitValue i1 current := by
    simpa [i2] using bitValue_act_cx_other
      (i := i1) (control := current) (target := target) htc.symm
  have h2s : bitValue i2 spare = bitValue i1 spare := by
    simpa [i2] using bitValue_act_cx_other
      (i := i1) (control := current) (target := target) hts.symm
  have h3s : bitValue i3 spare =
      (bitValue i2 spare + bitValue i2 target * bitValue i2 ancilla) % 2 := by
    simpa [i3] using bitValue_act_ccx_target i2 target ancilla spare
  have h3t : bitValue i3 target = bitValue i2 target := by
    simpa [i3] using bitValue_act_ccx_other
      (i := i2) (x := target) (y := ancilla) (target := spare) hts
  have h3a : bitValue i3 ancilla = bitValue i2 ancilla := by
    simpa [i3] using bitValue_act_ccx_other
      (i := i2) (x := target) (y := ancilla) (target := spare) hsa.symm
  have h3c : bitValue i3 current = bitValue i2 current := by
    simpa [i3] using bitValue_act_ccx_other
      (i := i2) (x := target) (y := ancilla) (target := spare) hcs
  have h4s : bitValue i4 spare =
      (bitValue i3 spare + bitValue i3 current) % 2 := by
    simpa [i4] using bitValue_act_cx_target i3 current spare
  have h4t : bitValue i4 target = bitValue i3 target := by
    simpa [i4] using bitValue_act_cx_other
      (i := i3) (control := current) (target := spare) hts
  have h4a : bitValue i4 ancilla = bitValue i3 ancilla := by
    simpa [i4] using bitValue_act_cx_other
      (i := i3) (control := current) (target := spare) hsa.symm
  have h4c : bitValue i4 current = bitValue i3 current := by
    simpa [i4] using bitValue_act_cx_other
      (i := i3) (control := current) (target := spare) hcs
  have h5a : bitValue i5 ancilla =
      (bitValue i4 ancilla + bitValue i4 current) % 2 := by
    simpa [i5] using bitValue_act_cx_target i4 current ancilla
  have h5t : bitValue i5 target = bitValue i4 target := by
    simpa [i5] using bitValue_act_cx_other
      (i := i4) (control := current) (target := ancilla) hta
  have h5s : bitValue i5 spare = bitValue i4 spare := by
    simpa [i5] using bitValue_act_cx_other
      (i := i4) (control := current) (target := ancilla) hsa
  have h5c : bitValue i5 current = bitValue i4 current := by
    simpa [i5] using bitValue_act_cx_other
      (i := i4) (control := current) (target := ancilla) hca
  change bitValue i5 target = _ ∧ bitValue i5 current = _ ∧
    bitValue i5 spare = _ ∧ bitValue i5 ancilla = _
  constructor
  · rw [h5t, h4t, h3t, h2t]
  constructor
  · rw [h5c, h4c, h3c, h2c, h1c]
  constructor
  · rw [h5s, h4s, h3s, h3c, h2s, h2t, h2a,
      h2c, h1s, h1a, h1c]
    have ha : bitValue i target = 0 ∨ bitValue i target = 1 := by
      have := bitValue_lt i target
      omega
    have hk : K = 0 ∨ K = 1 := by omega
    have hc : bitValue i current = 0 ∨ bitValue i current = 1 := by
      have := bitValue_lt i current
      omega
    rcases ha with ha | ha <;> rcases hk with hk | hk <;>
      rcases hc with hc | hc <;> simp [target, current, ha, hk, hc]
  · rw [h5a, h4a, h3a, h2a, h1a, h4c, h3c, h2c, h1c]
    have hc := bitValue_lt i current
    omega

theorem carryStepGates_bits {constant width bit i : Nat}
    (hbit : bit < width)
    (hspare : bitValue i (spareWire width bit) = 0)
    (hancilla : bitValue i (ancillaWire width) = 0) :
    let j := actGates (carryStepGates constant width bit) i
    bitValue j (targetWire bit) =
        (bitValue i (targetWire bit) + bitValue constant bit +
          bitValue i (carryWire width bit)) % 2 ∧
      bitValue j (carryWire width bit) = bitValue i (carryWire width bit) ∧
      bitValue j (spareWire width bit) =
        (bitValue i (targetWire bit) + bitValue constant bit +
          bitValue i (carryWire width bit)) / 2 ∧
      bitValue j (ancillaWire width) = 0 := by
  let target := targetWire bit
  let current := carryWire width bit
  let spare := spareWire width bit
  let ancilla := ancillaWire width
  have hta : target ≠ ancilla := (ancillaWire_ne_targetWire hbit).symm
  have hca : current ≠ ancilla := carryWire_ne_ancillaWire width bit
  have hsa : spare ≠ ancilla := spareWire_ne_ancillaWire width bit
  by_cases hk : constant.testBit bit = true
  · have hK : bitValue constant bit = 1 := by
      simp [bitValue, hk]
    let prepared := RGate.act (.x ancilla) i
    have hpreparedAncilla : bitValue prepared ancilla = 1 := by
      rw [show bitValue prepared ancilla = (bitValue i ancilla + 1) % 2 by
        simpa [prepared] using bitValue_act_x_target i ancilla,
        show bitValue i ancilla = 0 by simpa [ancilla] using hancilla]
    have hpreparedTarget : bitValue prepared target = bitValue i target := by
      simpa [prepared] using bitValue_act_x_other
        (i := i) (q := ancilla) hta
    have hpreparedCurrent : bitValue prepared current = bitValue i current := by
      simpa [prepared] using bitValue_act_x_other
        (i := i) (q := ancilla) hca
    have hpreparedSpare : bitValue prepared spare = 0 := by
      rw [show bitValue prepared spare = bitValue i spare by
        simpa [prepared] using bitValue_act_x_other
          (i := i) (q := ancilla) hsa,
        show bitValue i spare = 0 by simpa [spare] using hspare]
    let core := actGates (carryCoreGates width bit) prepared
    have hcore := carryCoreGates_bits hbit hpreparedSpare
      hpreparedAncilla (by omega : 1 < 2)
    change bitValue core target = _ ∧ bitValue core current = _ ∧
      bitValue core spare = _ ∧ bitValue core ancilla = 1 at hcore
    let clearedAncilla := RGate.act (.x ancilla) core
    let result := RGate.act (.x target) clearedAncilla
    have hresultTarget : bitValue result target =
        (bitValue core target + 1) % 2 := by
      rw [show bitValue result target =
        (bitValue clearedAncilla target + 1) % 2 by
          simpa [result] using bitValue_act_x_target clearedAncilla target,
        show bitValue clearedAncilla target = bitValue core target by
          simpa [clearedAncilla] using bitValue_act_x_other
            (i := core) (q := ancilla) hta]
    have hresultCurrent : bitValue result current = bitValue core current := by
      rw [show bitValue result current = bitValue clearedAncilla current by
        simpa [result] using bitValue_act_x_other
          (i := clearedAncilla) (q := target)
            (carryWire_ne_targetWire hbit),
        show bitValue clearedAncilla current = bitValue core current by
          simpa [clearedAncilla] using bitValue_act_x_other
            (i := core) (q := ancilla) hca]
    have hresultSpare : bitValue result spare = bitValue core spare := by
      rw [show bitValue result spare = bitValue clearedAncilla spare by
        simpa [result] using bitValue_act_x_other
          (i := clearedAncilla) (q := target)
            (spareWire_ne_targetWire hbit),
        show bitValue clearedAncilla spare = bitValue core spare by
          simpa [clearedAncilla] using bitValue_act_x_other
            (i := core) (q := ancilla) hsa]
    have hresultAncilla : bitValue result ancilla = 0 := by
      rw [show bitValue result ancilla = bitValue clearedAncilla ancilla by
        simpa [result] using bitValue_act_x_other
          (i := clearedAncilla) (q := target) hta.symm,
        show bitValue clearedAncilla ancilla =
          (bitValue core ancilla + 1) % 2 by
            simpa [clearedAncilla] using bitValue_act_x_target core ancilla,
        hcore.2.2.2]
    have hstep : actGates (carryStepGates constant width bit) i = result := by
      simp [carryStepGates, hk, result, clearedAncilla, core, prepared,
        target, ancilla, actGates_append, actGates]
    rw [hstep]
    change bitValue result target = _ ∧ bitValue result current = _ ∧
      bitValue result spare = _ ∧ bitValue result ancilla = _
    rw [hK]
    refine ⟨?_, ?_, ?_, hresultAncilla⟩
    · rw [hresultTarget, hcore.1, hpreparedTarget, hpreparedCurrent]
      have ha : bitValue i target = 0 ∨ bitValue i target = 1 := by
        have := bitValue_lt i target
        omega
      have hc : bitValue i current = 0 ∨ bitValue i current = 1 := by
        have := bitValue_lt i current
        omega
      rcases ha with ha | ha <;> rcases hc with hc | hc <;>
        simp [target, current, ha, hc]
    · rw [hresultCurrent, hcore.2.1, hpreparedCurrent]
    · rw [hresultSpare, hcore.2.2.1, hpreparedTarget, hpreparedCurrent]
  · have hkFalse : constant.testBit bit = false := Bool.eq_false_iff.mpr hk
    have hK : bitValue constant bit = 0 := by
      simp [bitValue, hkFalse]
    have hcore := carryCoreGates_bits hbit hspare hancilla
      (by omega : 0 < 2)
    change bitValue (actGates (carryCoreGates width bit) i) (targetWire bit) = _ ∧
      bitValue (actGates (carryCoreGates width bit) i) (carryWire width bit) = _ ∧
      bitValue (actGates (carryCoreGates width bit) i) (spareWire width bit) = _ ∧
      bitValue (actGates (carryCoreGates width bit) i) (ancillaWire width) = 0
        at hcore
    simpa [carryStepGates, hkFalse, hK, Nat.add_zero] using hcore

theorem targetWire_lt {width bit : Nat} (hbit : bit < width) :
    targetWire bit < adderWidth width := by
  simp [targetWire, adderWidth]
  omega

theorem dirtyWire_lt {width bit : Nat} (hbit : bit < width) :
    dirtyWire width bit < adderWidth width := by
  simp [dirtyWire, adderWidth]
  omega

theorem carryWire_ne_dirtyWire {width bit dirtyBit : Nat}
    (hdirty : dirtyBit < width) :
    carryWire width bit ≠ dirtyWire width dirtyBit := by
  have hmod := Nat.mod_lt bit (by omega : 0 < 2)
  simp [carryWire, dirtyWire]
  omega

theorem spareWire_ne_dirtyWire {width bit dirtyBit : Nat}
    (hdirty : dirtyBit < width) :
    spareWire width bit ≠ dirtyWire width dirtyBit := by
  exact carryWire_ne_dirtyWire (bit := bit + 1) hdirty

theorem ancillaWire_ne_dirtyWire {width dirtyBit : Nat}
    (hdirty : dirtyBit < width) :
    ancillaWire width ≠ dirtyWire width dirtyBit := by
  simp [ancillaWire, dirtyWire]
  omega

theorem targetWire_ne_carryWire {width targetBit carryBit : Nat}
    (htarget : targetBit < width) :
    targetWire targetBit ≠ carryWire width carryBit := by
  have hmod := Nat.mod_lt carryBit (by omega : 0 < 2)
  simp [targetWire, carryWire]
  omega

theorem targetWire_ne_spareWire {width targetBit carryBit : Nat}
    (htarget : targetBit < width) :
    targetWire targetBit ≠ spareWire width carryBit := by
  exact targetWire_ne_carryWire (carryBit := carryBit + 1) htarget

theorem targetWire_ne_ancillaWire {width targetBit : Nat}
    (htarget : targetBit < width) :
    targetWire targetBit ≠ ancillaWire width := by
  exact (ancillaWire_ne_targetWire htarget).symm

theorem dirtyWire_ne_targetWire {width dirtyBit targetBit : Nat}
    (_hdirty : dirtyBit < width) (htarget : targetBit < width) :
    dirtyWire width dirtyBit ≠ targetWire targetBit := by
  simp [dirtyWire, targetWire]
  omega

theorem dirtyWire_injective {width a b : Nat}
    (h : dirtyWire width a = dirtyWire width b) : a = b := by
  simp [dirtyWire] at h
  exact h

theorem carryCoreGates_wellFormed {width bit : Nat} (hbit : bit < width) :
    (carryCoreGates width bit).all
      (RGate.wellFormed (adderWidth width)) = true := by
  have ht := targetWire_lt hbit
  have hc := carryWire_lt width bit
  have hs := spareWire_lt width bit
  have ha := ancillaWire_lt width
  have htc := carryWire_ne_targetWire hbit
  have hts := spareWire_ne_targetWire hbit
  have hta := ancillaWire_ne_targetWire hbit
  have hcs := carryWire_ne_spareWire width bit
  have hca := carryWire_ne_ancillaWire width bit
  have hsa := spareWire_ne_ancillaWire width bit
  simp [carryCoreGates, RGate.wellFormed, ht, hc, hs, ha,
    htc, hts.symm, hta.symm, hcs, hca, hsa.symm]

theorem carryStepGates_wellFormed {constant width bit : Nat}
    (hbit : bit < width) :
    (carryStepGates constant width bit).all
      (RGate.wellFormed (adderWidth width)) = true := by
  have hcore := carryCoreGates_wellFormed hbit
  have ht := targetWire_lt hbit
  have ha := ancillaWire_lt width
  by_cases hk : constant.testBit bit = true
  · simp [carryStepGates, hk, hcore, RGate.wellFormed, ht, ha]
  · have hkFalse := Bool.eq_false_iff.mpr hk
    simp [carryStepGates, hkFalse, hcore]

theorem carryStepGates_testBit_other {constant width bit i q : Nat}
    (htarget : q ≠ targetWire bit)
    (hcurrent : q ≠ carryWire width bit)
    (hspare : q ≠ spareWire width bit)
    (hancilla : q ≠ ancillaWire width) :
    (actGates (carryStepGates constant width bit) i).testBit q =
      i.testBit q := by
  apply Reversible.testBit_actGates_of_outside
  intro gate hgate
  by_cases hk : constant.testBit bit = true
  · simp [carryStepGates, carryCoreGates, hk] at hgate
    rcases hgate with hgate | hgate | hgate | hgate | hgate | hgate | hgate | hgate <;>
      subst gate <;> simp [RGate.wires, htarget, hcurrent, hspare, hancilla]
  · have hkFalse := Bool.eq_false_iff.mpr hk
    simp [carryStepGates, carryCoreGates, hkFalse] at hgate
    rcases hgate with hgate | hgate | hgate | hgate | hgate <;>
      subst gate <;> simp [RGate.wires, htarget, hcurrent, hspare, hancilla]

theorem carryStepGates_bitValue_other {constant width bit i q : Nat}
    (htarget : q ≠ targetWire bit)
    (hcurrent : q ≠ carryWire width bit)
    (hspare : q ≠ spareWire width bit)
    (hancilla : q ≠ ancillaWire width) :
    bitValue (actGates (carryStepGates constant width bit) i) q =
      bitValue i q := by
  unfold bitValue
  rw [carryStepGates_testBit_other htarget hcurrent hspare hancilla]

theorem carryTopGates_bits {constant width i : Nat} (hwidth : 2 ≤ width) :
    let top := width - 1
    let j := actGates (carryTopGates constant width) i
    bitValue j (targetWire top) =
        (bitValue i (targetWire top) + bitValue constant top +
          bitValue i (carryWire width top)) % 2 ∧
      bitValue j (carryWire width top) =
        bitValue i (carryWire width top) := by
  let top := width - 1
  let target := targetWire top
  let current := carryWire width top
  have htop : top < width := by simp [top]; omega
  have hne : current ≠ target := carryWire_ne_targetWire htop
  by_cases hk : constant.testBit top = true
  · have hK : bitValue constant top = 1 := by simp [bitValue, hk]
    let prepared := RGate.act (.x target) i
    let result := RGate.act (.cx current target) prepared
    have hpreparedTarget : bitValue prepared target =
        (bitValue i target + 1) % 2 := by
      simpa [prepared] using bitValue_act_x_target i target
    have hpreparedCurrent : bitValue prepared current =
        bitValue i current := by
      simpa [prepared] using bitValue_act_x_other
        (i := i) (q := target) hne
    have hresultTarget : bitValue result target =
        (bitValue prepared target + bitValue prepared current) % 2 := by
      simpa [result] using bitValue_act_cx_target prepared current target
    have hresultCurrent : bitValue result current =
        bitValue prepared current := by
      simpa [result] using bitValue_act_cx_other
        (i := prepared) (control := current) (target := target) hne
    have hj : actGates (carryTopGates constant width) i = result := by
      simp [carryTopGates, hk, top, target, current, prepared, result,
        actGates]
    rw [hj]
    change bitValue result target =
        (bitValue i target + bitValue constant top +
          bitValue i current) % 2 ∧
      bitValue result current = bitValue i current
    constructor
    · rw [hK, hresultTarget, hpreparedTarget, hpreparedCurrent]
      have ha : bitValue i target = 0 ∨ bitValue i target = 1 := by
        have := bitValue_lt i target
        omega
      have hc : bitValue i current = 0 ∨ bitValue i current = 1 := by
        have := bitValue_lt i current
        omega
      rcases ha with ha | ha <;> rcases hc with hc | hc <;>
        simp [ha, hc]
    · rw [hresultCurrent, hpreparedCurrent]
  · have hkFalse : constant.testBit top = false := Bool.eq_false_iff.mpr hk
    have hK : bitValue constant top = 0 := by simp [bitValue, hkFalse]
    have hj : actGates (carryTopGates constant width) i =
        RGate.act (.cx current target) i := by
      simp [carryTopGates, hkFalse, top, target, current, actGates]
    rw [hj]
    change bitValue (RGate.act (.cx current target) i) target =
        (bitValue i target + bitValue constant top +
          bitValue i current) % 2 ∧
      bitValue (RGate.act (.cx current target) i) current =
        bitValue i current
    constructor
    · rw [hK, bitValue_act_cx_target]
      omega
    · exact bitValue_act_cx_other
        (i := i) (control := current) (target := target) hne

theorem carryTopGates_bitValue_other {constant width i q : Nat}
    (hq : q ≠ targetWire (width - 1)) :
    bitValue (actGates (carryTopGates constant width) i) q =
      bitValue i q := by
  let target := targetWire (width - 1)
  let current := carryWire width (width - 1)
  by_cases hk : constant.testBit (width - 1) = true
  · let prepared := RGate.act (.x target) i
    let result := RGate.act (.cx current target) prepared
    have hj : actGates (carryTopGates constant width) i = result := by
      simp [carryTopGates, hk, target, current, prepared, result, actGates]
    rw [hj]
    rw [show bitValue result q = bitValue prepared q by
        simpa [result] using bitValue_act_cx_other
          (i := prepared) (control := current) (target := target) hq,
      show bitValue prepared q = bitValue i q by
        simpa [prepared] using bitValue_act_x_other
          (i := i) (q := target) hq]
  · have hkFalse := Bool.eq_false_iff.mpr hk
    have hj : actGates (carryTopGates constant width) i =
        RGate.act (.cx current target) i := by
      simp [carryTopGates, hkFalse, target, current, actGates]
    rw [hj]
    simpa using bitValue_act_cx_other
      (i := i) (control := current) (target := target) hq

theorem carryTopGates_wellFormed {constant width : Nat}
    (hwidth : 2 ≤ width) :
    (carryTopGates constant width).all
      (RGate.wellFormed (adderWidth width)) = true := by
  have htop : width - 1 < width := by omega
  have ht := targetWire_lt htop
  have hc := carryWire_lt width (width - 1)
  have hne := carryWire_ne_targetWire htop
  by_cases hk : constant.testBit (width - 1) = true
  · simp [carryTopGates, hk, RGate.wellFormed, ht, hc, hne]
  · have hkFalse := Bool.eq_false_iff.mpr hk
    simp [carryTopGates, hkFalse, RGate.wellFormed, ht, hc, hne]

theorem xorProductGates_wellFormed
    {x y target total : Nat} {invertX invertY : Bool}
    (hx : x < total) (hy : y < total) (htarget : target < total)
    (hxy : x ≠ y) (hxt : x ≠ target) (hyt : y ≠ target) :
    (xorProductGates x y target invertX invertY).all
      (RGate.wellFormed total) = true := by
  cases invertX <;> cases invertY <;>
    simp [xorProductGates, RGate.wellFormed, hx, hy, htarget,
      hxy, hxt, hyt]

theorem carryReverseStepGates_wellFormed
    {constant width bit : Nat} (hpositive : 0 < bit) (hbit : bit < width) :
    (carryReverseStepGates constant width bit).all
      (RGate.wellFormed (adderWidth width)) = true := by
  apply xorProductGates_wellFormed
  · exact targetWire_lt hbit
  · exact dirtyWire_lt (by omega)
  · exact dirtyWire_lt hbit
  · simp [targetWire, dirtyWire]
    omega
  · simp [targetWire, dirtyWire]
    omega
  · simp [dirtyWire]
    omega

theorem carryForwardStepGates_wellFormed
    {constant width bit : Nat} (hpositive : 0 < bit) (hbit : bit < width) :
    (carryForwardStepGates constant width bit).all
      (RGate.wellFormed (adderWidth width)) = true := by
  apply xorProductGates_wellFormed
  · exact targetWire_lt hbit
  · exact dirtyWire_lt (by omega)
  · exact dirtyWire_lt hbit
  · simp [targetWire, dirtyWire]
    omega
  · simp [targetWire, dirtyWire]
    omega
  · simp [dirtyWire]
    omega

theorem carryReverseGates_wellFormed {constant width count : Nat}
    (hcount : count < width) :
    (carryReverseGates constant width count).all
      (RGate.wellFormed (adderWidth width)) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [carryReverseGates, List.all_append,
        carryReverseStepGates_wellFormed (by omega) hcount, ih (by omega)]
      rfl

theorem carryForwardGates_wellFormed {constant width count : Nat}
    (hcount : count < width) :
    (carryForwardGates constant width count).all
      (RGate.wellFormed (adderWidth width)) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [carryForwardGates, List.all_append, ih (by omega),
        carryForwardStepGates_wellFormed (by omega) hcount]
      rfl

theorem carryBaseGates_wellFormed {constant width : Nat}
    (hwidth : 0 < width) :
    (carryBaseGates constant width).all
      (RGate.wellFormed (adderWidth width)) = true := by
  apply xorProductGates_wellFormed
  · exact carryWire_lt width 0
  · exact targetWire_lt hwidth
  · exact dirtyWire_lt hwidth
  · simp [carryWire, targetWire]
    omega
  · simp [carryWire, dirtyWire]
    omega
  · simp [targetWire, dirtyWire]
    omega

theorem carryReconstructionGates_wellFormed {constant width : Nat}
    (hwidth : 2 ≤ width) :
    (carryReconstructionGates constant width).all
      (RGate.wellFormed (adderWidth width)) = true := by
  have hall : (constantXorGates (2 ^ width - 1) 0 width).all
      (RGate.wellFormed (adderWidth width)) = true :=
    constantXorGates_wellFormed (by simp [adderWidth]; omega)
  have hreverse := carryReverseGates_wellFormed
    (constant := constant) (width := width) (count := width - 2) (by omega)
  have hdirty : (constantXorGates constant width (width - 1)).all
      (RGate.wellFormed (adderWidth width)) = true :=
    constantXorGates_wellFormed (by simp [adderWidth]; omega)
  have hbase := carryBaseGates_wellFormed
    (constant := constant) (width := width) (by omega)
  have hforward := carryForwardGates_wellFormed
    (constant := constant) (width := width) (count := width - 2) (by omega)
  simp [carryReconstructionGates, hall, hreverse, hdirty, hbase, hforward]

theorem gateOps_basis_run {level w : Nat} (hl : 3 ≤ level)
    {gates : List RGate}
    (hwf : gates.all (RGate.wellFormed w) = true)
    (rec : List Bool) (creg input i : Nat) :
    runOps level w (gateOps gates)
        (Branch.mk rec creg (basis i) input) =
      [Branch.mk rec creg (basis (actGates gates i)) input] := by
  let r : RCircuit := { width := w, gates := gates }
  have hr : r.wellFormed = true := by
    simpa [r, RCircuit.wellFormed] using hwf
  rw [gateOps, Lookup3.gateOps_run]
  change [Branch.mk rec creg
    (run level (compile r) (basis i)) input] = _
  rw [run_compile_basis hl hr]
  rfl

theorem carryStepOps_zero_run {level constant width i : Nat}
    (hl : 3 ≤ level) (hwidth : 0 < width)
    (rec : List Bool) (creg input : Nat) :
    runOps level (adderWidth width) (carryStepOps constant width 0)
        (Branch.mk rec creg (basis i) input) =
      [Branch.mk rec creg
        (basis (actGates (carryStepGates constant width 0) i)) input] := by
  rw [carryStepOps, if_pos rfl, List.append_nil]
  exact gateOps_basis_run hl (carryStepGates_wellFormed hwidth) rec creg input i

theorem copiedIndex_value {value dirty i : Nat} (hne : value ≠ dirty) :
    (copiedIndex value dirty i).testBit value = i.testBit value := by
  rw [copiedIndex]
  split
  · rw [Semantics.testBit_xor_of_ne hne]
  · rfl

theorem copiedIndex_dirty {value dirty i : Nat} :
    (copiedIndex value dirty i).testBit dirty =
      Bool.xor (i.testBit dirty) (i.testBit value) := by
  rw [copiedIndex]
  cases hv : i.testBit value
  · simp
  · simp only [if_true, Semantics.testBit_xor_self]
    cases hd : i.testBit dirty <;> rfl

theorem copied_phase {value dirty i : Nat} (hne : value ≠ dirty) :
    Bool.xor ((copiedIndex value dirty i).testBit value)
        ((copiedIndex value dirty i).testBit dirty) =
      i.testBit dirty := by
  rw [copiedIndex_value hne, copiedIndex_dirty]
  cases hv : i.testBit value <;> cases hd : i.testBit dirty <;> rfl

theorem outputIndex_value {value dirty i : Nat} :
    (outputIndex value dirty i).testBit value = false := by
  rw [outputIndex, testBit_writeBit]

theorem outputIndex_dirty {value dirty i : Nat} (hne : value ≠ dirty) :
    (outputIndex value dirty i).testBit dirty =
      Bool.xor (i.testBit dirty) (i.testBit value) := by
  rw [outputIndex, testBit_writeBit_of_ne hne.symm, copiedIndex_dirty]

theorem outputIndex_other {value dirty i q : Nat}
    (hqv : q ≠ value) (hqd : q ≠ dirty) :
    (outputIndex value dirty i).testBit q = i.testBit q := by
  rw [outputIndex, testBit_writeBit_of_ne hqv, copiedIndex]
  split
  · rw [Semantics.testBit_xor_of_ne hqd]
  · rfl

theorem bitValue_outputIndex_value {value dirty i : Nat} :
    bitValue (outputIndex value dirty i) value = 0 := by
  simp [bitValue, outputIndex_value]

theorem bitValue_outputIndex_dirty {value dirty i : Nat}
    (hne : value ≠ dirty) :
    bitValue (outputIndex value dirty i) dirty =
      (bitValue i dirty + bitValue i value) % 2 := by
  unfold bitValue
  rw [outputIndex_dirty hne]
  cases hi : i.testBit dirty <;> cases hv : i.testBit value <;> rfl

theorem bitValue_outputIndex_other {value dirty i q : Nat}
    (hqv : q ≠ value) (hqd : q ≠ dirty) :
    bitValue (outputIndex value dirty i) q = bitValue i q := by
  unfold bitValue
  rw [outputIndex_other hqv hqd]

theorem carryStepOut_state {original constant width count state : Nat}
    (hstate : CarryPrefixState original constant width count state)
    (hcount : count < width) :
    CarryPrefixState original constant width (count + 1)
      (carryStepOut constant width count state) := by
  rcases hstate with ⟨_, htargetDone, htargetRest,
    hdirtyDone, hdirtyRest, hcurrent, hspare, hancilla⟩
  let j := actGates (carryStepGates constant width count) state
  have hstep := carryStepGates_bits (constant := constant)
    hcount hspare hancilla
  change bitValue j (targetWire count) = _ ∧
    bitValue j (carryWire width count) = _ ∧
    bitValue j (spareWire width count) = _ ∧
    bitValue j (ancillaWire width) = 0 at hstep
  cases count with
  | zero =>
      change CarryPrefixState original constant width 1 j
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, hstep.2.2.2⟩
      · intro bit hbit
        have hzero : bit = 0 := by omega
        subst bit
        rw [hstep.1, htargetRest 0 (by omega) hcount, hcurrent]
      · intro bit hbit hbitWidth
        have hother := carryStepGates_bitValue_other
          (constant := constant) (width := width) (bit := 0)
          (i := state) (q := targetWire bit)
          (by simp [targetWire]; omega)
          (targetWire_ne_carryWire hbitWidth)
          (targetWire_ne_spareWire hbitWidth)
          (targetWire_ne_ancillaWire hbitWidth)
        rw [show bitValue j (targetWire bit) =
            bitValue state (targetWire bit) by simpa [j] using hother,
          htargetRest bit (by omega) hbitWidth]
      · intro bit hbit
        omega
      · intro bit _ hbitWidth
        have hother := carryStepGates_bitValue_other
          (constant := constant) (width := width) (bit := 0)
          (i := state) (q := dirtyWire width bit)
          (dirtyWire_ne_targetWire hbitWidth hcount)
          (carryWire_ne_dirtyWire hbitWidth).symm
          (spareWire_ne_dirtyWire hbitWidth).symm
          (ancillaWire_ne_dirtyWire hbitWidth).symm
        rw [show bitValue j (dirtyWire width bit) =
            bitValue state (dirtyWire width bit) by simpa [j] using hother,
          hdirtyRest bit (by omega) hbitWidth]
      · rw [carryWire_succ, hstep.2.2.1,
          htargetRest 0 (by omega) hcount, hcurrent]
        rfl
      · rw [spareWire_succ, hstep.2.1, hcurrent]
        rfl
  | succ previous =>
      let value := carryWire width (previous + 1)
      let dirty := dirtyWire width previous
      let out := outputIndex value dirty j
      have hprevious : previous < width := by omega
      have hvalueDirty : value ≠ dirty :=
        carryWire_ne_dirtyWire hprevious
      change CarryPrefixState original constant width (previous + 2) out
      refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro bit hbit
        by_cases hnew : bit = previous + 1
        · subst bit
          have hout := bitValue_outputIndex_other
            (i := j) (q := targetWire (previous + 1))
            (value := value) (dirty := dirty)
            (targetWire_ne_carryWire hcount)
            (dirtyWire_ne_targetWire hprevious hcount).symm
          rw [show bitValue out (targetWire (previous + 1)) =
              bitValue j (targetWire (previous + 1)) by
                simpa [out] using hout,
            hstep.1,
            htargetRest (previous + 1) (by omega) hcount,
            hcurrent]
        · have hbitOld : bit < previous + 1 := by omega
          have hout := bitValue_outputIndex_other
            (i := j) (q := targetWire bit) (value := value) (dirty := dirty)
            (targetWire_ne_carryWire (by omega))
            (dirtyWire_ne_targetWire hprevious (by omega)).symm
          have hgate := carryStepGates_bitValue_other
            (constant := constant) (width := width) (bit := previous + 1)
            (i := state) (q := targetWire bit)
            (by simp [targetWire]; omega)
            (targetWire_ne_carryWire (by omega))
            (targetWire_ne_spareWire (by omega))
            (targetWire_ne_ancillaWire (by omega))
          rw [show bitValue out (targetWire bit) = bitValue j (targetWire bit) by
              simpa [out] using hout,
            show bitValue j (targetWire bit) = bitValue state (targetWire bit) by
              simpa [j] using hgate,
            htargetDone bit hbitOld]
      · intro bit hbit hbitWidth
        have hout := bitValue_outputIndex_other
          (i := j) (q := targetWire bit) (value := value) (dirty := dirty)
          (targetWire_ne_carryWire hbitWidth)
          (dirtyWire_ne_targetWire hprevious hbitWidth).symm
        have hgate := carryStepGates_bitValue_other
          (constant := constant) (width := width) (bit := previous + 1)
          (i := state) (q := targetWire bit)
          (by simp [targetWire]; omega)
          (targetWire_ne_carryWire hbitWidth)
          (targetWire_ne_spareWire hbitWidth)
          (targetWire_ne_ancillaWire hbitWidth)
        rw [show bitValue out (targetWire bit) = bitValue j (targetWire bit) by
            simpa [out] using hout,
          show bitValue j (targetWire bit) = bitValue state (targetWire bit) by
            simpa [j] using hgate,
          htargetRest bit (by omega) hbitWidth]
      · intro bit hbit
        by_cases hnew : bit = previous
        · subst bit
          have hgate := carryStepGates_bitValue_other
            (constant := constant) (width := width) (bit := previous + 1)
            (i := state) (q := dirty)
            (dirtyWire_ne_targetWire hprevious hcount)
            hvalueDirty.symm
            (spareWire_ne_dirtyWire hprevious).symm
            (ancillaWire_ne_dirtyWire hprevious).symm
          rw [show bitValue out dirty =
              (bitValue j dirty + bitValue j value) % 2 by
                simpa [out] using bitValue_outputIndex_dirty hvalueDirty,
            show bitValue j dirty = bitValue state dirty by
              simpa [j] using hgate,
            show bitValue j value = bitValue state value by
              simpa [j, value] using hstep.2.1,
            hdirtyRest previous (by omega) hprevious,
            show bitValue state value = addCarry constant original (previous + 1) by
              simpa [value] using hcurrent]
        · have hbitOld : bit + 1 < previous + 1 := by omega
          have hbitWidth : bit < width := by omega
          have hout := bitValue_outputIndex_other
            (i := j) (q := dirtyWire width bit) (value := value) (dirty := dirty)
            (carryWire_ne_dirtyWire hbitWidth).symm
            (by
              intro heq
              apply hnew
              exact dirtyWire_injective heq)
          have hgate := carryStepGates_bitValue_other
            (constant := constant) (width := width) (bit := previous + 1)
            (i := state) (q := dirtyWire width bit)
            (dirtyWire_ne_targetWire hbitWidth hcount)
            (carryWire_ne_dirtyWire hbitWidth).symm
            (spareWire_ne_dirtyWire hbitWidth).symm
            (ancillaWire_ne_dirtyWire hbitWidth).symm
          rw [show bitValue out (dirtyWire width bit) =
              bitValue j (dirtyWire width bit) by simpa [out] using hout,
            show bitValue j (dirtyWire width bit) =
              bitValue state (dirtyWire width bit) by simpa [j] using hgate,
            hdirtyDone bit hbitOld]
      · intro bit hbit hbitWidth
        have hneDirty : dirtyWire width bit ≠ dirty := by
          intro heq
          have heq' := dirtyWire_injective heq
          omega
        have hout := bitValue_outputIndex_other
          (i := j) (q := dirtyWire width bit) (value := value) (dirty := dirty)
          (carryWire_ne_dirtyWire hbitWidth).symm hneDirty
        have hgate := carryStepGates_bitValue_other
          (constant := constant) (width := width) (bit := previous + 1)
          (i := state) (q := dirtyWire width bit)
          (dirtyWire_ne_targetWire hbitWidth hcount)
          (carryWire_ne_dirtyWire hbitWidth).symm
          (spareWire_ne_dirtyWire hbitWidth).symm
          (ancillaWire_ne_dirtyWire hbitWidth).symm
        rw [show bitValue out (dirtyWire width bit) =
            bitValue j (dirtyWire width bit) by simpa [out] using hout,
          show bitValue j (dirtyWire width bit) =
            bitValue state (dirtyWire width bit) by simpa [j] using hgate,
          hdirtyRest bit (by omega) hbitWidth]
      · have hout := bitValue_outputIndex_other
          (i := j) (q := carryWire width (previous + 2))
          (value := value) (dirty := dirty)
          (by
            rw [show carryWire width (previous + 2) =
              spareWire width (previous + 1) by simp]
            exact (carryWire_ne_spareWire width (previous + 1)).symm)
          (by
            rw [show carryWire width (previous + 2) =
              spareWire width (previous + 1) by simp]
            exact spareWire_ne_dirtyWire hprevious)
        rw [show bitValue out (carryWire width (previous + 2)) =
            bitValue j (carryWire width (previous + 2)) by
              simpa [out] using hout,
          show carryWire width (previous + 2) =
            spareWire width (previous + 1) by simp,
          hstep.2.2.1,
          htargetRest (previous + 1) (by omega) hcount,
          hcurrent]
        rfl
      · rw [show spareWire width (previous + 2) = value by
            simp [value],
          show bitValue out value = 0 by
            simpa [out] using bitValue_outputIndex_value]
      · have hout := bitValue_outputIndex_other
          (i := j) (q := ancillaWire width) (value := value) (dirty := dirty)
          (carryWire_ne_ancillaWire width (previous + 1)).symm
          (ancillaWire_ne_dirtyWire hprevious)
        rw [show bitValue out (ancillaWire width) =
            bitValue j (ancillaWire width) by simpa [out] using hout,
          hstep.2.2.2]

theorem carryPrefixOut_state {original constant width count : Nat}
    (hcount : count ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0) :
    CarryPrefixState original constant width count
      (carryPrefixOut constant width count original) := by
  induction count with
  | zero =>
      simpa [carryPrefixOut] using
        carryPrefixState_zero (constant := constant)
          hcarry hspare hancilla
  | succ count ih =>
      rw [carryPrefixOut]
      exact carryStepOut_state (ih (by omega)) (by omega)

theorem carryTopOut_state {original constant width state : Nat}
    (hwidth : 2 ≤ width)
    (hstate : CarryPrefixState original constant width (width - 1) state) :
    CarryChainState original constant width
      (carryTopOut constant width state) := by
  rcases hstate with ⟨_, htargetDone, htargetRest,
    hdirtyDone, hdirtyRest, hcurrent, hspare, hancilla⟩
  let top := width - 1
  let previous := width - 2
  let value := carryWire width top
  let dirty := dirtyWire width previous
  let j := actGates (carryTopGates constant width) state
  let out := outputIndex value dirty j
  have htop : top < width := by simp [top]; omega
  have hprevious : previous < width := by simp [previous]; omega
  have htopBits := carryTopGates_bits
    (constant := constant) (i := state) hwidth
  change bitValue j (targetWire top) = _ ∧
    bitValue j value = bitValue state value at htopBits
  change CarryChainState original constant width out
  refine ⟨hwidth, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro bit hbit
    by_cases hb : bit = top
    · subst bit
      have hout := bitValue_outputIndex_other
        (i := j) (q := targetWire top) (value := value) (dirty := dirty)
        (targetWire_ne_carryWire htop)
        (dirtyWire_ne_targetWire hprevious htop).symm
      rw [show bitValue out (targetWire top) =
          bitValue j (targetWire top) by simpa [out] using hout,
        htopBits.1,
        htargetRest top (by simp [top]) htop,
        show bitValue state value = addCarry constant original top by
          simpa [value, top] using hcurrent]
    · have hbefore : bit < top := by omega
      have hj := carryTopGates_bitValue_other
        (constant := constant) (width := width) (i := state)
        (q := targetWire bit) (by simp [targetWire]; omega)
      have hout := bitValue_outputIndex_other
        (i := j) (q := targetWire bit) (value := value) (dirty := dirty)
        (targetWire_ne_carryWire hbit)
        (dirtyWire_ne_targetWire hprevious hbit).symm
      rw [show bitValue out (targetWire bit) =
          bitValue j (targetWire bit) by simpa [out] using hout,
        show bitValue j (targetWire bit) =
          bitValue state (targetWire bit) by simpa [j] using hj,
        htargetDone bit hbefore]
  · intro bit hbit
    by_cases hb : bit = previous
    · subst bit
      have hjDirty := carryTopGates_bitValue_other
        (constant := constant) (width := width) (i := state)
        (q := dirty) (dirtyWire_ne_targetWire hprevious htop)
      have hout := bitValue_outputIndex_dirty
        (i := j) (value := value) (dirty := dirty)
        (carryWire_ne_dirtyWire hprevious)
      rw [show bitValue out dirty = (bitValue j dirty +
          bitValue j value) % 2 by simpa [out] using hout,
        show bitValue j dirty = bitValue state dirty by
          simpa [j] using hjDirty,
        htopBits.2,
        show bitValue state dirty =
            bitValue original dirty by
          simpa [dirty, previous] using
            hdirtyRest previous (by omega) hprevious,
        show bitValue state value = addCarry constant original top by
          simpa [value, top] using hcurrent]
      rw [show previous + 1 = top by simp [previous, top]; omega]
    · have hbefore : bit + 1 < width - 1 := by
        simp [previous] at hb
        omega
      have hbitWidth : bit < width := by omega
      have hj := carryTopGates_bitValue_other
        (constant := constant) (width := width) (i := state)
        (q := dirtyWire width bit)
        (dirtyWire_ne_targetWire hbitWidth htop)
      have hout := bitValue_outputIndex_other
        (i := j) (q := dirtyWire width bit) (value := value)
        (dirty := dirty)
        (carryWire_ne_dirtyWire hbitWidth).symm
        (by
          intro heq
          have := dirtyWire_injective heq
          omega)
      rw [show bitValue out (dirtyWire width bit) =
          bitValue j (dirtyWire width bit) by simpa [out] using hout,
        show bitValue j (dirtyWire width bit) =
          bitValue state (dirtyWire width bit) by simpa [j] using hj,
        hdirtyDone bit hbefore]
  · have hlast : width - 1 < width := by omega
    have hj := carryTopGates_bitValue_other
      (constant := constant) (width := width) (i := state)
      (q := dirtyWire width (width - 1))
      (dirtyWire_ne_targetWire hlast htop)
    have hout := bitValue_outputIndex_other
      (i := j) (q := dirtyWire width (width - 1))
      (value := value) (dirty := dirty)
      (carryWire_ne_dirtyWire hlast).symm
      (by
        intro heq
        have := dirtyWire_injective heq
        omega)
    rw [show bitValue out (dirtyWire width (width - 1)) =
        bitValue j (dirtyWire width (width - 1)) by
          simpa [out] using hout,
      show bitValue j (dirtyWire width (width - 1)) =
        bitValue state (dirtyWire width (width - 1)) by
          simpa [j] using hj,
      hdirtyRest (width - 1) (by omega) hlast]
  · simpa [out, value] using
      (bitValue_outputIndex_value (value := value) (dirty := dirty) (i := j))
  · have hj := carryTopGates_bitValue_other
      (constant := constant) (width := width) (i := state)
      (q := spareWire width top) (spareWire_ne_targetWire htop)
    have hout := bitValue_outputIndex_other
      (i := j) (q := spareWire width top) (value := value) (dirty := dirty)
      (carryWire_ne_spareWire width top).symm
      (spareWire_ne_dirtyWire hprevious)
    rw [show bitValue out (spareWire width top) =
        bitValue j (spareWire width top) by simpa [out] using hout,
      show bitValue j (spareWire width top) =
        bitValue state (spareWire width top) by simpa [j] using hj,
      show bitValue state (spareWire width top) = 0 by
        simpa [top] using hspare]
  · have hj := carryTopGates_bitValue_other
      (constant := constant) (width := width) (i := state)
      (q := ancillaWire width) (ancillaWire_ne_targetWire htop)
    have hout := bitValue_outputIndex_other
      (i := j) (q := ancillaWire width) (value := value) (dirty := dirty)
      (carryWire_ne_ancillaWire width top).symm
      (ancillaWire_ne_dirtyWire hprevious)
    rw [show bitValue out (ancillaWire width) =
        bitValue j (ancillaWire width) by simpa [out] using hout,
      show bitValue j (ancillaWire width) =
        bitValue state (ancillaWire width) by simpa [j] using hj,
      hancilla]

theorem carryChainOut_state {original constant width : Nat}
    (hwidth : 2 ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0) :
    CarryChainState original constant width
      (carryChainOut constant width original) := by
  apply carryTopOut_state hwidth
  simpa [carryChainOut] using carryPrefixOut_state
    (original := original) (constant := constant) (width := width)
    (count := width - 1) (by omega) hcarry hspare hancilla

theorem correctionOps_run {level w value dirty i : Nat}
    (hl : 3 ≤ level) (hvalue : value < w) (hdirty : dirty < w)
    (hne : value ≠ dirty) (rec : List Bool) (creg input : Nat) :
    runOps level w (correctionOps value dirty)
        (Branch.mk rec creg (basis i) input) =
      [Branch.mk rec creg
        (Lookup.MeasuredUncompute.phaseScalar (deg level) (i.testBit dirty) •
          basis (i ^^^ (1 <<< value))) input] := by
  rw [correctionOps, runOps_cons, runOp_gate,
    Semantics.apply_x hvalue, List.flatMap_singleton,
    runOps_singleton, runOp_gate,
    Semantics.apply_z hdirty (by omega),
    Semantics.testBit_xor_of_ne hne.symm]
  cases hd : i.testBit dirty <;>
    simp [Lookup.MeasuredUncompute.phaseScalar, Vec.one_smul]

theorem measureCopiedOps_run {level w value dirty cbit i : Nat}
    (hl : 3 ≤ level) (hvalue : value < w) (hdirty : dirty < w)
    (hne : value ≠ dirty) (rec : List Bool) (creg input : Nat) :
    runOps level w (measureCopiedOps value dirty cbit)
        (Branch.mk rec creg (basis i) input) =
      [Branch.mk (false :: rec) (writeBit creg cbit false)
          (Algebra.Dy.invSqrt2 (deg level) • basis (outputIndex value dirty i)) input,
        Branch.mk (true :: rec) (writeBit creg cbit true)
          (Algebra.Dy.invSqrt2 (deg level) •
            (Lookup.MeasuredUncompute.phaseScalar (deg level) (i.testBit dirty) •
              basis (outputIndex value dirty i))) input] := by
  let j := copiedIndex value dirty i
  have hjValue : j.testBit value = i.testBit value := copiedIndex_value hne
  have hjDirty : j.testBit dirty =
      Bool.xor (i.testBit dirty) (i.testBit value) := copiedIndex_dirty
  have hphase : Lookup.MeasuredUncompute.measurementScalar (deg level)
        (Algebra.Dy.invSqrt2 (deg level)) (j.testBit value) *
        Lookup.MeasuredUncompute.phaseScalar (deg level) (j.testBit dirty) =
      Algebra.Dy.invSqrt2 (deg level) *
        Lookup.MeasuredUncompute.phaseScalar (deg level) (i.testBit dirty) := by
    rw [Lookup.BatchedUncompute.measurementScalar_eq_mul_phaseScalar,
      Algebra.Dy.mul_assoc, ← Lookup.BatchedUncompute.phaseScalar_xor,
      copied_phase hne]
  have hclear : writeBit j value false = outputIndex value dirty i := by
    rfl
  have hset : (writeBit j value true).testBit value = true :=
    testBit_writeBit _ _ _
  have htoggle : writeBit j value true ^^^ (1 <<< value) =
      outputIndex value dirty i := by
    rw [Lookup.MeasuredUncompute.xor_two_pow_eq_clear hset,
      writeBit_writeBit, hclear]
  have hdirtySet : (writeBit j value true).testBit dirty = j.testBit dirty := by
    rw [testBit_writeBit_of_ne hne.symm]
  rw [measureCopiedOps, runOps_cons, runOp_gate,
    Semantics.apply_cx hvalue hdirty hne,
    show (if i.testBit value then i ^^^ (1 <<< dirty) else i) = j from rfl,
    List.flatMap_singleton]
  change runOps level w
    ([.gate (.h value), .measure value cbit] ++
      [.branch (.localBit cbit) (correctionOps value dirty) []])
      (Branch.mk rec creg (basis j) input) = _
  rw [runOps_append, Lookup3.xMeasure_basis hl hvalue,
    List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    runOps_singleton, runOp_branch, CRef.read, testBit_writeBit,
    if_neg (by simp), runOps_nil,
    runOps_singleton, runOp_branch, CRef.read, testBit_writeBit,
    if_pos rfl]
  have hcorrection := correctionOps_run hl hvalue hdirty hne
    (true :: rec) (writeBit creg cbit true) input
    (i := writeBit j value true)
  rw [hdirtySet, htoggle] at hcorrection
  have hscaled :
      runOps level w (correctionOps value dirty)
        (Branch.mk (true :: rec) (writeBit creg cbit true)
          (Lookup.MeasuredUncompute.measurementScalar (deg level)
            (Algebra.Dy.invSqrt2 (deg level)) (j.testBit value) •
              basis (writeBit j value true)) input) =
        (runOps level w (correctionOps value dirty)
          (Branch.mk (true :: rec) (writeBit creg cbit true)
            (basis (writeBit j value true)) input)).map
          (smulBranch (Lookup.MeasuredUncompute.measurementScalar (deg level)
            (Algebra.Dy.invSqrt2 (deg level)) (j.testBit value))) := by
    change runOps level w (correctionOps value dirty)
      (smulBranch _ (Branch.mk (true :: rec) (writeBit creg cbit true)
        (basis (writeBit j value true)) input)) = _
    exact (runOps_smul level w).2 _ _ _
  rw [Lookup.MeasuredUncompute.measurementState]
  rw [hscaled, hcorrection]
  simp only [List.map_cons, List.map_nil, List.singleton_append, smulBranch]
  rw [Vec.smul_smul, Vec.smul_smul, hphase]
  simp [hclear]

theorem carryStepOps_succ_run {level constant width bit i : Nat}
    (hl : 3 ≤ level) (hbit : bit + 1 < width)
    (rec : List Bool) (creg input : Nat) :
    let value := carryWire width (bit + 1)
    let dirty := dirtyWire width bit
    let j := actGates (carryStepGates constant width (bit + 1)) i
    runOps level (adderWidth width) (carryStepOps constant width (bit + 1))
        (Branch.mk rec creg (basis i) input) =
      [Branch.mk (false :: rec) (writeBit creg bit false)
          (Algebra.Dy.invSqrt2 (deg level) •
            basis (outputIndex value dirty j)) input,
        Branch.mk (true :: rec) (writeBit creg bit true)
          (Algebra.Dy.invSqrt2 (deg level) •
            (Lookup.MeasuredUncompute.phaseScalar (deg level)
              (j.testBit dirty) • basis (outputIndex value dirty j))) input] := by
  let value := carryWire width (bit + 1)
  let dirty := dirtyWire width bit
  let j := actGates (carryStepGates constant width (bit + 1)) i
  have hwf := carryStepGates_wellFormed
    (constant := constant) (width := width) hbit
  have hvalue : value < adderWidth width := carryWire_lt width (bit + 1)
  have hdirty : dirty < adderWidth width := dirtyWire_lt (by omega)
  have hne : value ≠ dirty := carryWire_ne_dirtyWire (by omega)
  have hgates := gateOps_basis_run hl hwf rec creg input i
  rw [carryStepOps, if_neg (by omega), runOps_append, hgates,
    List.flatMap_singleton]
  exact measureCopiedOps_run hl hvalue hdirty hne rec creg input

theorem carryTopOps_run {level constant width i : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ width)
    (rec : List Bool) (creg input : Nat) :
    let value := carryWire width (width - 1)
    let dirty := dirtyWire width (width - 2)
    let j := actGates (carryTopGates constant width) i
    runOps level (adderWidth width) (carryTopOps constant width)
        (Branch.mk rec creg (basis i) input) =
      [Branch.mk (false :: rec) (writeBit creg (width - 2) false)
          (Algebra.Dy.invSqrt2 (deg level) •
            basis (outputIndex value dirty j)) input,
        Branch.mk (true :: rec) (writeBit creg (width - 2) true)
          (Algebra.Dy.invSqrt2 (deg level) •
            (Lookup.MeasuredUncompute.phaseScalar (deg level)
              (j.testBit dirty) • basis (outputIndex value dirty j))) input] := by
  let value := carryWire width (width - 1)
  let dirty := dirtyWire width (width - 2)
  let j := actGates (carryTopGates constant width) i
  have hwf := carryTopGates_wellFormed
    (constant := constant) hwidth
  have hvalue : value < adderWidth width := carryWire_lt width (width - 1)
  have hdirty : dirty < adderWidth width := dirtyWire_lt (by omega)
  have hne : value ≠ dirty := carryWire_ne_dirtyWire (by omega)
  have hgates := gateOps_basis_run hl hwf rec creg input i
  rw [carryTopOps, runOps_append, hgates, List.flatMap_singleton]
  exact measureCopiedOps_run hl hvalue hdirty hne rec creg input

theorem carryPrefixOps_mask {level constant width count original input : Nat}
    (hl : 3 ≤ level) (hcount : count ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (adderWidth width)
      (carryPrefixOps constant width count)
      (Branch.mk rec creg (basis original) input)) :
    b.state =
      Algebra.Dy.invSqrt2 (deg level) ^ (count - 1) •
        (Lookup.MeasuredUncompute.phaseScalar (deg level)
          (recordParity width (count - 1) b.creg original) •
          basis (carryPrefixOut constant width count original)) := by
  induction count generalizing rec creg b with
  | zero =>
      rw [carryPrefixOps, runOps_nil, List.mem_singleton] at hb
      subst b
      simp [carryPrefixOut, recordParity, Algebra.Dy.pow_zero_eq,
        Lookup.MeasuredUncompute.phaseScalar, Vec.one_smul]
  | succ count ih =>
      rw [carryPrefixOps, runOps_append, List.mem_flatMap] at hb
      obtain ⟨x, hx, hxb⟩ := hb
      have hxstate := ih (by omega) (rec := rec) (creg := creg) hx
      have hxinput : x.input = input :=
        input_runOps level (adderWidth width)
          (carryPrefixOps constant width count) hx
      let c := Algebra.Dy.invSqrt2 (deg level)
      let oldOut := carryPrefixOut constant width count original
      let oldPhase := Lookup.MeasuredUncompute.phaseScalar (deg level)
        (recordParity width (count - 1) x.creg original)
      let base := Branch.mk x.outcomes x.creg
        (basis oldOut : Vec (deg level)) input
      have hxe : x = smulBranch (c ^ (count - 1))
          (smulBranch oldPhase base) := by
        cases x with
        | mk outcomes xcreg state branchInput =>
            simp only [smulBranch, base] at hxinput ⊢
            subst branchInput
            rw [← hxstate]
      rw [hxe, (runOps_smul level (adderWidth width)).2,
        List.mem_map] at hxb
      obtain ⟨y, hy, rfl⟩ := hxb
      change y ∈ runOps level (adderWidth width)
        (carryStepOps constant width count)
        (smulBranch oldPhase base) at hy
      rw [(runOps_smul level (adderWidth width)).2,
        List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      cases count with
      | zero =>
          rw [carryStepOps_zero_run hl (by omega)
            x.outcomes x.creg input] at hz
          rw [List.mem_singleton] at hz
          subst z
          simp [smulBranch, c, oldPhase, oldOut,
            carryPrefixOut, carryStepOut, recordParity,
            Algebra.Dy.pow_zero_eq,
            Lookup.MeasuredUncompute.phaseScalar, Vec.one_smul]
      | succ bit =>
          let j := actGates (carryStepGates constant width (bit + 1)) oldOut
          have hstep := carryStepOps_succ_run
            (level := level) (constant := constant) (width := width)
            (bit := bit) (i := oldOut) hl (by omega)
            x.outcomes x.creg input
          rw [hstep] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          have hprior : bit + 1 - 1 = bit := by omega
          have hnext : bit + 1 + 1 - 1 = bit + 1 := by omega
          have hprefix := carryPrefixOut_state
            (original := original) (constant := constant)
            (width := width) (count := bit + 1) (by omega)
            hcarry hspare hancilla
          rcases hprefix with ⟨_, _, _, _, hdirtyRest, _, _, _⟩
          have holdDirty :
              bitValue oldOut (dirtyWire width bit) =
                bitValue original (dirtyWire width bit) := by
            exact hdirtyRest bit (by omega) (by omega)
          have hjDirtyValue :
              bitValue j (dirtyWire width bit) =
                bitValue original (dirtyWire width bit) := by
            rw [show bitValue j (dirtyWire width bit) =
                bitValue oldOut (dirtyWire width bit) by
              apply carryStepGates_bitValue_other
              · exact dirtyWire_ne_targetWire (by omega) (by omega)
              · exact (carryWire_ne_dirtyWire (by omega)).symm
              · exact (spareWire_ne_dirtyWire (by omega)).symm
              · exact (ancillaWire_ne_dirtyWire (by omega)).symm,
              holdDirty]
          have hjDirty : j.testBit (dirtyWire width bit) =
              original.testBit (dirtyWire width bit) :=
            testBit_eq_of_bitValue_eq hjDirtyValue
          have houtput :
              outputIndex (carryWire width (bit + 1))
                  (dirtyWire width bit) j =
                carryStepOut constant width (bit + 1) oldOut := by
            simp [carryStepOut, j]
          rcases hz with hz | hz
          · subst z
            simp only [smulBranch, Vec.smul_smul]
            rw [show outputIndex (carryWire width (bit + 1))
                (dirtyWire width bit)
                (actGates (carryStepGates constant width (bit + 1)) oldOut) =
              carryStepOut constant width (bit + 1) oldOut by
                simpa [j] using houtput]
            rw [hnext, recordParity,
              recordParity_writeBit_after (by omega),
              testBit_writeBit, Bool.and_false, Bool.xor_false]
            simp only [oldPhase, oldOut, c, carryPrefixOut, hprior]
            rw [Algebra.Dy.pow_succ]
            congr 1
            rw [Algebra.Dy.mul_comm
                (Lookup.MeasuredUncompute.phaseScalar (deg level)
                  (recordParity width bit x.creg original))
                (Algebra.Dy.invSqrt2 (deg level)),
              ← Algebra.Dy.mul_assoc]
          · subst z
            simp only [smulBranch, Vec.smul_smul]
            rw [show outputIndex (carryWire width (bit + 1))
                (dirtyWire width bit)
                (actGates (carryStepGates constant width (bit + 1)) oldOut) =
              carryStepOut constant width (bit + 1) oldOut by
                simpa [j] using houtput]
            rw [hnext, recordParity,
              recordParity_writeBit_after (by omega),
              testBit_writeBit, Bool.and_true, hjDirty,
              Lookup.BatchedUncompute.phaseScalar_xor]
            simp only [oldPhase, oldOut, c, dirtyWire,
              carryPrefixOut, hprior]
            rw [Algebra.Dy.pow_succ]
            congr 1
            let a := Algebra.Dy.invSqrt2 (deg level) ^ bit
            let p := Lookup.MeasuredUncompute.phaseScalar (deg level)
              (recordParity width bit x.creg original)
            let c' := Algebra.Dy.invSqrt2 (deg level)
            let q := Lookup.MeasuredUncompute.phaseScalar (deg level)
              (original.testBit (width + bit))
            change a * (p * (c' * q)) = (a * c') * (p * q)
            calc
              a * (p * (c' * q)) = (a * p) * (c' * q) :=
                (Algebra.Dy.mul_assoc _ _ _).symm
              _ = (c' * a) * (p * q) :=
                Lookup.BatchedUncompute.mul_four_reorder _ _ _ _
              _ = (a * c') * (p * q) := by
                rw [Algebra.Dy.mul_comm c' a]

theorem carryChainOps_mask {level constant width original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (adderWidth width)
      (carryChainOps constant width)
      (Branch.mk rec creg (basis original) input)) :
    b.state =
      Algebra.Dy.invSqrt2 (deg level) ^ (width - 1) •
        (Lookup.MeasuredUncompute.phaseScalar (deg level)
          (recordParity width (width - 1) b.creg original) •
          basis (carryChainOut constant width original)) := by
  rw [carryChainOps, runOps_append, List.mem_flatMap] at hb
  obtain ⟨x, hx, hxb⟩ := hb
  have hxstate := carryPrefixOps_mask
    (level := level) (constant := constant) (width := width)
    (count := width - 1) (original := original) (input := input)
    hl (by omega) hcarry hspare hancilla rec creg hx
  have hxinput : x.input = input :=
    input_runOps level (adderWidth width)
      (carryPrefixOps constant width (width - 1)) hx
  let c := Algebra.Dy.invSqrt2 (deg level)
  let prefixOut := carryPrefixOut constant width (width - 1) original
  let prefixPhase := Lookup.MeasuredUncompute.phaseScalar (deg level)
    (recordParity width (width - 2) x.creg original)
  let base := Branch.mk x.outcomes x.creg
    (basis prefixOut : Vec (deg level)) input
  have hprefixCount : width - 1 - 1 = width - 2 := by omega
  rw [hprefixCount] at hxstate
  have hxe : x = smulBranch (c ^ (width - 2))
      (smulBranch prefixPhase base) := by
    cases x with
    | mk outcomes xcreg state branchInput =>
        simp only [smulBranch, base] at hxinput ⊢
        subst branchInput
        rw [← hxstate]
  rw [hxe, (runOps_smul level (adderWidth width)).2,
    List.mem_map] at hxb
  obtain ⟨y, hy, rfl⟩ := hxb
  change y ∈ runOps level (adderWidth width) (carryTopOps constant width)
    (smulBranch prefixPhase base) at hy
  rw [(runOps_smul level (adderWidth width)).2, List.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have htop := carryTopOps_run
    (level := level) (constant := constant) (width := width)
    (i := prefixOut) hl hwidth x.outcomes x.creg input
  rw [htop] at hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  have hprefixState := carryPrefixOut_state
    (original := original) (constant := constant) (width := width)
    (count := width - 1) (by omega) hcarry hspare hancilla
  rcases hprefixState with ⟨_, _, _, _, hdirtyRest, _, _, _⟩
  have hprevious : width - 2 < width := by omega
  let j := actGates (carryTopGates constant width) prefixOut
  have hjDirtyValue :
      bitValue j (dirtyWire width (width - 2)) =
        bitValue original (dirtyWire width (width - 2)) := by
    rw [show bitValue j (dirtyWire width (width - 2)) =
        bitValue prefixOut (dirtyWire width (width - 2)) by
      apply carryTopGates_bitValue_other
      exact dirtyWire_ne_targetWire hprevious (by omega),
      hdirtyRest (width - 2) (by omega) hprevious]
  have hjDirty : j.testBit (dirtyWire width (width - 2)) =
      original.testBit (dirtyWire width (width - 2)) :=
    testBit_eq_of_bitValue_eq hjDirtyValue
  have houtput :
      outputIndex (carryWire width (width - 1))
          (dirtyWire width (width - 2)) j =
        carryChainOut constant width original := by
    rfl
  have hnewCount : width - 2 + 1 = width - 1 := by omega
  rcases hz with hz | hz
  · subst z
    simp only [smulBranch, Vec.smul_smul]
    rw [show outputIndex (carryWire width (width - 1))
        (dirtyWire width (width - 2))
        (actGates (carryTopGates constant width) prefixOut) =
      carryChainOut constant width original by simpa [j] using houtput]
    rw [← hnewCount, recordParity,
      recordParity_writeBit_after (by omega), testBit_writeBit,
      Bool.and_false, Bool.xor_false]
    simp only [prefixPhase, c]
    rw [Algebra.Dy.pow_succ]
    congr 1
    rw [Algebra.Dy.mul_comm
        (Lookup.MeasuredUncompute.phaseScalar (deg level)
          (recordParity width (width - 2) x.creg original))
        (Algebra.Dy.invSqrt2 (deg level)),
      ← Algebra.Dy.mul_assoc]
  · subst z
    simp only [smulBranch, Vec.smul_smul]
    rw [show outputIndex (carryWire width (width - 1))
        (dirtyWire width (width - 2))
        (actGates (carryTopGates constant width) prefixOut) =
      carryChainOut constant width original by simpa [j] using houtput]
    rw [← hnewCount, recordParity,
      recordParity_writeBit_after (by omega), testBit_writeBit,
      Bool.and_true, hjDirty,
      Lookup.BatchedUncompute.phaseScalar_xor]
    simp only [prefixPhase, c, dirtyWire]
    rw [Algebra.Dy.pow_succ]
    congr 1
    let a := Algebra.Dy.invSqrt2 (deg level) ^ (width - 2)
    let p := Lookup.MeasuredUncompute.phaseScalar (deg level)
      (recordParity width (width - 2) x.creg original)
    let c' := Algebra.Dy.invSqrt2 (deg level)
    let q := Lookup.MeasuredUncompute.phaseScalar (deg level)
      (original.testBit (width + (width - 2)))
    change a * (p * (c' * q)) = (a * c') * (p * q)
    calc
      a * (p * (c' * q)) = (a * p) * (c' * q) :=
        (Algebra.Dy.mul_assoc _ _ _).symm
      _ = (c' * a) * (p * q) :=
        Lookup.BatchedUncompute.mul_four_reorder _ _ _ _
      _ = (a * c') * (p * q) := by
        rw [Algebra.Dy.mul_comm c' a]

theorem measureCopiedOps_wellFormed {level w value dirty cbit cbits : Nat}
    (hl : 3 ≤ level) (hvalue : value < w) (hdirty : dirty < w)
    (hne : value ≠ dirty) (hcbit : cbit < cbits) :
    Program.opsWellFormed level w 0 cbits
      (measureCopiedOps value dirty cbit) = true := by
  simp [measureCopiedOps, correctionOps, Program.opsWellFormed,
    Program.opWellFormed, Gate.wellFormedAt, CRef.wellFormed,
    hvalue, hdirty, hne, hcbit]
  omega

theorem carryStepOps_wellFormed
    {level constant width bit cbits : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ width) (hbit : bit < width)
    (hcbit : bit = 0 ∨ bit - 1 < cbits) :
    Program.opsWellFormed level (adderWidth width) 0 cbits
      (carryStepOps constant width bit) = true := by
  rw [carryStepOps, Program.opsWellFormed_append]
  have hgates := Lookup3.gateOps_wellFormed
    (level := level) (w := adderWidth width)
    (iw := 0) (cw := cbits) hl
    (carryStepGates_wellFormed (constant := constant) hbit)
  have hgates' : Program.opsWellFormed level (adderWidth width) 0 cbits
      (gateOps (carryStepGates constant width bit)) = true := by
    simpa [gateOps] using hgates
  rw [hgates']
  by_cases hzero : bit = 0
  · simp [hzero, Program.opsWellFormed]
  · have hmeasure := measureCopiedOps_wellFormed
      (level := level) (w := adderWidth width)
      (value := carryWire width bit)
      (dirty := dirtyWire width (bit - 1))
      (cbit := bit - 1) (cbits := cbits) hl
      (carryWire_lt width bit)
      (by simp [dirtyWire, adderWidth]; omega)
      (by simp [carryWire, dirtyWire]; omega)
      (hcbit.resolve_left hzero)
    rw [if_neg hzero, hmeasure]
    rfl

theorem carryPrefixOps_wellFormed
    {level constant width count : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ width) (hcount : count ≤ width - 1) :
    Program.opsWellFormed level (adderWidth width) 0 (width - 1)
      (carryPrefixOps constant width count) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [carryPrefixOps, Program.opsWellFormed_append,
        ih (by omega), carryStepOps_wellFormed hl hwidth (by omega)
          (by omega)]
      rfl

theorem carryTopOps_wellFormed
    {level constant width : Nat} (hl : 3 ≤ level) (hwidth : 2 ≤ width) :
    Program.opsWellFormed level (adderWidth width) 0 (width - 1)
      (carryTopOps constant width) = true := by
  rw [carryTopOps, Program.opsWellFormed_append]
  have htop := Lookup3.gateOps_wellFormed
    (level := level) (w := adderWidth width)
    (iw := 0) (cw := width - 1) hl
    (carryTopGates_wellFormed (constant := constant) hwidth)
  have htop' : Program.opsWellFormed level (adderWidth width) 0 (width - 1)
      (gateOps (carryTopGates constant width)) = true := by
    simpa [gateOps] using htop
  have hmeasure := measureCopiedOps_wellFormed
    (level := level) (w := adderWidth width)
    (value := carryWire width (width - 1))
    (dirty := dirtyWire width (width - 2))
    (cbit := width - 2) (cbits := width - 1) hl
    (carryWire_lt width (width - 1))
    (by simp [dirtyWire, adderWidth]; omega)
    (by simp [carryWire, dirtyWire]; omega)
    (by omega)
  rw [htop', hmeasure]
  rfl

theorem carryChainOps_wellFormed
    {level constant width : Nat} (hl : 3 ≤ level) (hwidth : 2 ≤ width) :
    Program.opsWellFormed level (adderWidth width) 0 (width - 1)
      (carryChainOps constant width) = true := by
  rw [carryChainOps, Program.opsWellFormed_append,
    carryPrefixOps_wellFormed hl hwidth (by omega),
    carryTopOps_wellFormed hl hwidth]
  rfl

theorem phaseCorrectionOps_wellFormed
    {level w dirtyOffset count cbits : Nat}
    (hl : 3 ≤ level) (hfit : dirtyOffset + count ≤ w)
    (hcount : count ≤ cbits) :
    Program.opsWellFormed level w 0 cbits
      (phaseCorrectionOps dirtyOffset count) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [phaseCorrectionOps, Program.opsWellFormed_append,
        ih (by omega) (by omega)]
      simp [Program.opsWellFormed, Program.opWellFormed,
        CRef.wellFormed, Gate.wellFormedAt]
      omega

theorem constantAddOps_wellFormed
    {level constant width : Nat} (hl : 3 ≤ level) (hwidth : 2 ≤ width) :
    Program.opsWellFormed level (adderWidth width) 0 (width - 1)
      (constantAddOps constant width) = true := by
  rw [constantAddOps, Program.opsWellFormed_append,
    Program.opsWellFormed_append,
    carryChainOps_wellFormed hl hwidth]
  have hreconstruction := Lookup3.gateOps_wellFormed
    (level := level) (w := adderWidth width)
    (iw := 0) (cw := width - 1) hl
    (carryReconstructionGates_wellFormed
      (constant := constant) hwidth)
  have hreconstruction' :
      Program.opsWellFormed level (adderWidth width) 0 (width - 1)
        (gateOps (carryReconstructionGates constant width)) = true := by
    simpa [gateOps] using hreconstruction
  rw [hreconstruction',
    phaseCorrectionOps_wellFormed hl (by simp [adderWidth]; omega)
      (by omega)]
  rfl

theorem measureCopiedOps_measure (value dirty cbit : Nat) :
    Program.tallyOps Lookup3.measurementCost
      (measureCopiedOps value dirty cbit) = Range.point 1 := by
  simp [measureCopiedOps, correctionOps, Program.tallyOps,
    Program.tallyOp, Lookup3.measurementCost, Range.add, Range.choice,
    Range.point]

theorem measureCopiedOps_reset (value dirty cbit : Nat) :
    Program.tallyOps Lookup3.resetCost
      (measureCopiedOps value dirty cbit) = Range.point 0 := by
  simp [measureCopiedOps, correctionOps, Program.tallyOps,
    Program.tallyOp, Lookup3.resetCost, Range.add, Range.choice,
    Range.point]

theorem measureCopiedOps_toffoli (value dirty cbit : Nat) :
    Program.weighOps (fun g => if g.isCcz then 1 else 0)
      (measureCopiedOps value dirty cbit) = Range.point 0 := by
  simp [measureCopiedOps, correctionOps, Program.weighOps,
    Program.weighOp, Gate.isCcz, Range.add, Range.choice, Range.point]

theorem phaseCorrectionOps_run {level w dirtyOffset count i : Nat}
    (hl : 3 ≤ level) (hfit : dirtyOffset + count ≤ w)
    (rec : List Bool) (creg input : Nat) :
    runOps level w (phaseCorrectionOps dirtyOffset count)
        (Branch.mk rec creg (basis i) input) =
      [Branch.mk rec creg
        (Lookup.MeasuredUncompute.phaseScalar (deg level)
          (recordParity dirtyOffset count creg i) • basis i) input] := by
  induction count with
  | zero =>
      rw [phaseCorrectionOps, runOps_nil]
      simp [recordParity,
        Lookup.MeasuredUncompute.phaseScalar, Vec.one_smul]
  | succ count ih =>
      rw [phaseCorrectionOps, runOps_append, ih (by omega),
        List.flatMap_singleton]
      let phase := Lookup.MeasuredUncompute.phaseScalar (deg level)
        (recordParity dirtyOffset count creg i)
      let base := Branch.mk rec creg (basis i : Vec (deg level)) input
      change runOps level w
        [.branch (.localBit count)
          [.gate (.z (dirtyOffset + count))] []]
        (smulBranch phase base) = _
      rw [(runOps_smul level w).2, runOps_singleton, runOp_branch,
        CRef.read]
      by_cases hc : creg.testBit count = true
      · rw [if_pos hc, runOps_singleton, runOp_gate,
          Semantics.apply_z (by omega) (by omega), List.map_singleton]
        by_cases hi : i.testBit (dirtyOffset + count) = true
        · rw [if_pos hi]
          cases hp : recordParity dirtyOffset count creg i <;>
            simp [smulBranch, base, phase, recordParity, hc, hi, hp,
              Vec.smul_smul, Vec.one_smul, Algebra.Dy.one_mul,
              Algebra.Dy.neg_mul, Algebra.Dy.neg_neg,
              Lookup.MeasuredUncompute.phaseScalar]
        · rw [if_neg hi]
          have hi' : i.testBit (dirtyOffset + count) = false :=
            Bool.eq_false_iff.mpr hi
          simp [smulBranch, base, phase, recordParity, hc, hi']
      · rw [if_neg hc, runOps_nil, List.map_singleton]
        have hc' : creg.testBit count = false := Bool.eq_false_iff.mpr hc
        simp [smulBranch, base, phase, recordParity, hc']

theorem recordParity_congr {dirtyOffset count creg i j : Nat}
    (hbits : ∀ bit, bit < count →
      i.testBit (dirtyOffset + bit) = j.testBit (dirtyOffset + bit)) :
    recordParity dirtyOffset count creg i =
      recordParity dirtyOffset count creg j := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [recordParity, recordParity,
        ih (fun bit hbit => hbits bit (by omega)),
        hbits count (by omega)]

theorem reconstruction_recordParity
    {original constant width state creg : Nat}
    (hstate : CarryChainState original constant width state) :
    recordParity width (width - 1) creg
        (actGates (carryReconstructionGates constant width) state) =
      recordParity width (width - 1) creg original := by
  apply recordParity_congr
  intro bit hbit
  apply testBit_eq_of_bitValue_eq
  have hrestored := (carryReconstructionGates_state hstate).2.2.1
  simpa [dirtyWire] using hrestored bit (by omega)

theorem constantAddOps_mask {level constant width original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (adderWidth width)
      (constantAddOps constant width)
      (Branch.mk rec creg (basis original) input)) :
    b.state =
      Algebra.Dy.invSqrt2 (deg level) ^ (width - 1) •
        basis (actGates (carryReconstructionGates constant width)
          (carryChainOut constant width original)) := by
  rw [constantAddOps, runOps_append, List.mem_flatMap] at hb
  obtain ⟨x, hx, hxb⟩ := hb
  have hxstate := carryChainOps_mask
    (level := level) (constant := constant) (width := width)
    (original := original) (input := input)
    hl hwidth hcarry hspare hancilla rec creg hx
  have hxinput : x.input = input :=
    input_runOps level (adderWidth width)
      (carryChainOps constant width) hx
  let amplitude := Algebra.Dy.invSqrt2 (deg level) ^ (width - 1)
  let chainOut := carryChainOut constant width original
  let reconstructed :=
    actGates (carryReconstructionGates constant width) chainOut
  let phase := Lookup.MeasuredUncompute.phaseScalar (deg level)
    (recordParity width (width - 1) x.creg original)
  let base := Branch.mk x.outcomes x.creg
    (basis chainOut : Vec (deg level)) input
  have hxe : x = smulBranch amplitude (smulBranch phase base) := by
    cases x with
    | mk outcomes xcreg state branchInput =>
        simp only [smulBranch, amplitude, phase, chainOut, base]
          at hxinput ⊢
        subst branchInput
        rw [← hxstate]
  rw [hxe, (runOps_smul level (adderWidth width)).2,
    List.mem_map] at hxb
  obtain ⟨y, hy, rfl⟩ := hxb
  change y ∈ runOps level (adderWidth width)
    (gateOps (carryReconstructionGates constant width) ++
      phaseCorrectionOps width (width - 1))
    (smulBranch phase base) at hy
  rw [(runOps_smul level (adderWidth width)).2, List.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hgate := gateOps_basis_run hl
    (carryReconstructionGates_wellFormed
      (constant := constant) hwidth)
    x.outcomes x.creg input chainOut
  rw [runOps_append, hgate, List.flatMap_singleton,
    phaseCorrectionOps_run hl (by simp [adderWidth]; omega)] at hz
  rw [List.mem_singleton] at hz
  subst z
  have hchainState := carryChainOut_state
    (original := original) (constant := constant) (width := width)
    hwidth hcarry hspare hancilla
  have hparity : recordParity width (width - 1) x.creg reconstructed =
      recordParity width (width - 1) x.creg original := by
    simpa [reconstructed, chainOut] using
      reconstruction_recordParity (creg := x.creg) hchainState
  simp [smulBranch, amplitude, phase, reconstructed, chainOut,
    Vec.smul_smul, hparity,
    Lookup.BatchedUncompute.phaseScalar_mul_self, Vec.one_smul]

def controlledCarryCircuit (width : Nat) : RCircuit :=
  control (Adder.carryCircuit width)

theorem controlledCarryCircuit_wellFormed {width : Nat} (hwidth : 0 < width) :
    (controlledCarryCircuit width).wellFormed = true := by
  exact control_wellFormed (Adder.carryCircuit_wellFormed hwidth)

theorem controlledCarryCircuit_act {width i : Nat}
    (hwidth : 0 < width)
    (hscratch : i.testBit (2 * width + 3) = false) :
    act (controlledCarryCircuit width) i =
      if i.testBit (2 * width + 2) then
        writeField
          (writeField i width width
            ((readField i 0 width + readField i width width +
              bitValue i (2 * width)) % 2 ^ width))
          (2 * width + 1) 1
            ((bitValue i (2 * width + 1) +
              (readField i 0 width + readField i width width +
                bitValue i (2 * width)) / 2 ^ width) % 2)
      else i := by
  rw [controlledCarryCircuit, act_control
    (Adder.carryCircuit_wellFormed hwidth) (by
      simpa [Adder.carryCircuit] using hscratch)]
  change (if i.testBit (2 * width + 2) then
      act (Adder.carryCircuit width) i else i) = _
  by_cases hcontrol : i.testBit (2 * width + 2) = true
  · rw [if_pos hcontrol, if_pos hcontrol]
    exact Adder.carryCircuit_act hwidth
  · rw [if_neg hcontrol, if_neg hcontrol]

theorem controlledCarryOps_run {level width i : Nat}
    (hl : 3 ≤ level) (hwidth : 0 < width)
    (rec : List Bool) (creg input : Nat) :
    runOps level (2 * width + 4)
        (gateOps (controlledCarryCircuit width).gates)
        (Branch.mk rec creg (basis i) input) =
      [Branch.mk rec creg
        (basis (act (controlledCarryCircuit width) i)) input] := by
  apply gateOps_basis_run hl
  have hw : (controlledCarryCircuit width).width = 2 * width + 4 := by
    simp [controlledCarryCircuit, Reversible.control, Adder.carryCircuit]
  rw [← hw]
  simpa [RCircuit.wellFormed] using controlledCarryCircuit_wellFormed hwidth

def constantControlWire (width : Nat) : Nat := adderWidth width

def controlledCarryStepGates (constant width bit : Nat) : List RGate :=
  (if constant.testBit bit then
      [.cx (constantControlWire width) (ancillaWire width)]
    else []) ++
    carryCoreGates width bit ++
    if constant.testBit bit then
      [.cx (constantControlWire width) (ancillaWire width),
        .cx (constantControlWire width) (targetWire bit)]
    else []

def controlledCarryTopGates (constant width : Nat) : List RGate :=
  (if constant.testBit (width - 1) then
      [.cx (constantControlWire width) (targetWire (width - 1))]
    else []) ++
    [.cx (carryWire width (width - 1)) (targetWire (width - 1))]

theorem act_cx_eq_x_of_control_true {control target i : Nat}
    (hcontrol : i.testBit control = true) :
    RGate.act (.cx control target) i = RGate.act (.x target) i := by
  simp [RGate.act, hcontrol]

theorem act_cx_eq_self_of_control_false {control target i : Nat}
    (hcontrol : i.testBit control = false) :
    RGate.act (.cx control target) i = i := by
  simp [RGate.act, hcontrol]

theorem testBit_act_cx_control {control target i : Nat}
    (hne : control ≠ target) :
    (RGate.act (.cx control target) i).testBit control =
      i.testBit control := by
  cases hcontrol : i.testBit control with
  | false => simp [RGate.act, hcontrol]
  | true =>
      rw [act_cx_eq_x_of_control_true hcontrol]
      simpa [RGate.act, hcontrol] using RGate.testBit_xor_of_ne hne i

theorem testBit_act_x_other {control target i : Nat}
    (hne : control ≠ target) :
    (RGate.act (.x target) i).testBit control = i.testBit control := by
  exact RGate.testBit_xor_of_ne hne i

theorem testBit_act_ccx_other {control x y target i : Nat}
    (hcx : control ≠ x) (hcy : control ≠ y)
    (hct : control ≠ target) :
    (RGate.act (.ccx x y target) i).testBit control =
      i.testBit control := by
  apply RGate.testBit_act_of_not_mem
  simp [RGate.wires, hcx, hcy, hct]

theorem controlledCarryStepGates_act {constant width bit i : Nat}
    (hbit : bit < width) :
    actGates (controlledCarryStepGates constant width bit) i =
      actGates
        (carryStepGates
          (if i.testBit (constantControlWire width) then constant else 0)
          width bit) i := by
  have hcontrolTarget : constantControlWire width ≠ targetWire bit := by
    simp [constantControlWire, adderWidth, targetWire]
    omega
  have hcontrolAncilla : constantControlWire width ≠ ancillaWire width := by
    simp [constantControlWire, adderWidth, ancillaWire]
  have hcoreControl : ∀ j,
      (actGates (carryCoreGates width bit) j).testBit
          (constantControlWire width) =
        j.testBit (constantControlWire width) := by
    intro j
    apply Reversible.testBit_actGates_of_outside
    intro gate hgate
    have hmod := Nat.mod_lt bit (by omega : 0 < 2)
    have hmodSucc := Nat.mod_lt (bit + 1) (by omega : 0 < 2)
    simp [carryCoreGates] at hgate
    rcases hgate with hgate | hgate | hgate | hgate | hgate <;>
      subst gate <;>
      simp [RGate.wires, constantControlWire, adderWidth,
        targetWire, carryWire, spareWire, ancillaWire] <;> omega
  by_cases hk : constant.testBit bit = true
  · by_cases hc : i.testBit (constantControlWire width) = true
    · have hpre :
          (RGate.act (.x (ancillaWire width)) i).testBit
              (constantControlWire width) = true := by
        simpa [RGate.act, hc] using
          RGate.testBit_xor_of_ne hcontrolAncilla i
      have hafterCore :
          (actGates (carryCoreGates width bit)
              (RGate.act (.x (ancillaWire width)) i)).testBit
              (constantControlWire width) = true := by
        rw [hcoreControl, hpre]
      have hafterAncilla :
          (RGate.act (.x (ancillaWire width))
              (actGates (carryCoreGates width bit)
                (RGate.act (.x (ancillaWire width)) i))).testBit
              (constantControlWire width) = true := by
        have hpreserved :=
          RGate.testBit_xor_of_ne hcontrolAncilla
            (actGates (carryCoreGates width bit)
              (RGate.act (.x (ancillaWire width)) i))
        change
          (RGate.act (.x (ancillaWire width))
              (actGates (carryCoreGates width bit)
                (RGate.act (.x (ancillaWire width)) i))).testBit
              (constantControlWire width) =
            (actGates (carryCoreGates width bit)
              (RGate.act (.x (ancillaWire width)) i)).testBit
                (constantControlWire width) at hpreserved
        rw [hpreserved, hafterCore]
      simp only [controlledCarryStepGates, carryStepGates, hk, if_true,
        hc, actGates_append, actGates_cons, actGates_nil]
      rw [act_cx_eq_x_of_control_true hc,
        act_cx_eq_x_of_control_true hafterCore,
        act_cx_eq_x_of_control_true hafterAncilla]
    · have hc' : i.testBit (constantControlWire width) = false :=
        Bool.eq_false_iff.mpr hc
      have hafterCore :
          (actGates (carryCoreGates width bit) i).testBit
              (constantControlWire width) = false := by
        rw [hcoreControl, hc']
      simp only [controlledCarryStepGates, carryStepGates, hk, if_true,
        hc', Bool.false_eq_true, if_false, actGates_append,
        actGates_cons, actGates_nil, Nat.zero_testBit]
      rw [act_cx_eq_self_of_control_false hc',
        act_cx_eq_self_of_control_false hafterCore,
        act_cx_eq_self_of_control_false hafterCore]
  · have hk' : constant.testBit bit = false := Bool.eq_false_iff.mpr hk
    by_cases hc : i.testBit (constantControlWire width) = true
    · simp [controlledCarryStepGates, carryStepGates, hk', hc]
    · have hc' : i.testBit (constantControlWire width) = false :=
        Bool.eq_false_iff.mpr hc
      simp [controlledCarryStepGates, carryStepGates, hk', hc']

theorem controlledCarryTopGates_act {constant width i : Nat}
    (hwidth : 0 < width) :
    actGates (controlledCarryTopGates constant width) i =
      actGates
        (carryTopGates
          (if i.testBit (constantControlWire width) then constant else 0)
          width) i := by
  have hcontrolTarget :
      constantControlWire width ≠ targetWire (width - 1) := by
    simp [constantControlWire, adderWidth, targetWire]
    omega
  by_cases hk : constant.testBit (width - 1) = true
  · by_cases hc : i.testBit (constantControlWire width) = true
    · simp only [controlledCarryTopGates, carryTopGates, hk, if_true,
        hc, actGates_append, actGates_cons, actGates_nil]
      rw [act_cx_eq_x_of_control_true hc]
    · have hc' : i.testBit (constantControlWire width) = false :=
        Bool.eq_false_iff.mpr hc
      simp only [controlledCarryTopGates, carryTopGates, hk, if_true,
        hc', Bool.false_eq_true, if_false, actGates_append,
        actGates_cons, actGates_nil, Nat.zero_testBit]
      rw [act_cx_eq_self_of_control_false hc']
  · have hk' : constant.testBit (width - 1) = false :=
      Bool.eq_false_iff.mpr hk
    by_cases hc : i.testBit (constantControlWire width) = true
    · simp [controlledCarryTopGates, carryTopGates, hk', hc]
    · have hc' : i.testBit (constantControlWire width) = false :=
        Bool.eq_false_iff.mpr hc
      simp [controlledCarryTopGates, carryTopGates, hk', hc']

def controlledXorProductGates (control x y target : Nat)
    (invertX invertY : Bool) : List RGate :=
  (if invertX then [.cx control x] else []) ++
    (if invertY then [.cx control y] else []) ++
    [.ccx x y target] ++
    (if invertY then [.cx control y] else []) ++
    if invertX then [.cx control x] else []

theorem controlledXorProductGates_act
    {control x y target i : Nat} {invertX invertY : Bool}
    (hcx : control ≠ x) (hcy : control ≠ y)
    (hct : control ≠ target) :
    actGates
        (controlledXorProductGates control x y target invertX invertY) i =
      actGates (xorProductGates x y target
        (invertX && i.testBit control) (invertY && i.testBit control)) i := by
  cases invertX with
  | false =>
      cases invertY with
      | false => rfl
      | true =>
          cases hcontrol : i.testBit control with
          | false =>
              simp only [controlledXorProductGates, xorProductGates,
                Bool.false_and, Bool.true_and, if_false, if_true,
                Bool.false_eq_true, actGates_append, actGates_cons,
                actGates_nil]
              rw [act_cx_eq_self_of_control_false hcontrol]
              have hmiddle :
                  (RGate.act (.ccx x y target) i).testBit control = false := by
                rw [testBit_act_ccx_other hcx hcy hct, hcontrol]
              rw [act_cx_eq_self_of_control_false hmiddle]
          | true =>
              simp only [controlledXorProductGates, xorProductGates,
                Bool.false_and, Bool.true_and, if_false, if_true,
                Bool.false_eq_true, actGates_append, actGates_cons,
                actGates_nil]
              rw [act_cx_eq_x_of_control_true hcontrol]
              have hfirst :
                  (RGate.act (.x y) i).testBit control = true := by
                rw [testBit_act_x_other hcy, hcontrol]
              have hmiddle :
                  (RGate.act (.ccx x y target)
                    (RGate.act (.x y) i)).testBit control = true := by
                rw [testBit_act_ccx_other hcx hcy hct, hfirst]
              rw [act_cx_eq_x_of_control_true hmiddle]
  | true =>
      cases invertY with
      | false =>
          cases hcontrol : i.testBit control with
          | false =>
              simp only [controlledXorProductGates, xorProductGates,
                Bool.false_and, Bool.true_and, if_false, if_true,
                Bool.false_eq_true, actGates_append, actGates_cons,
                actGates_nil]
              rw [act_cx_eq_self_of_control_false hcontrol]
              have hmiddle :
                  (RGate.act (.ccx x y target) i).testBit control = false := by
                rw [testBit_act_ccx_other hcx hcy hct, hcontrol]
              rw [act_cx_eq_self_of_control_false hmiddle]
          | true =>
              simp only [controlledXorProductGates, xorProductGates,
                Bool.false_and, Bool.true_and, if_false, if_true,
                Bool.false_eq_true, actGates_append, actGates_cons,
                actGates_nil]
              rw [act_cx_eq_x_of_control_true hcontrol]
              have hfirst :
                  (RGate.act (.x x) i).testBit control = true := by
                rw [testBit_act_x_other hcx, hcontrol]
              have hmiddle :
                  (RGate.act (.ccx x y target)
                    (RGate.act (.x x) i)).testBit control = true := by
                rw [testBit_act_ccx_other hcx hcy hct, hfirst]
              rw [act_cx_eq_x_of_control_true hmiddle]
      | true =>
          cases hcontrol : i.testBit control with
          | false =>
              simp only [controlledXorProductGates, xorProductGates,
                Bool.true_and, if_true,
                actGates_append, actGates_cons, actGates_nil]
              rw [act_cx_eq_self_of_control_false hcontrol]
              rw [act_cx_eq_self_of_control_false hcontrol]
              have hmiddle :
                  (RGate.act (.ccx x y target) i).testBit control = false := by
                rw [testBit_act_ccx_other hcx hcy hct, hcontrol]
              rw [act_cx_eq_self_of_control_false hmiddle]
              rw [act_cx_eq_self_of_control_false hmiddle]
          | true =>
              simp only [controlledXorProductGates, xorProductGates,
                Bool.true_and, if_true,
                actGates_append, actGates_cons, actGates_nil]
              rw [act_cx_eq_x_of_control_true hcontrol]
              have hx :
                  (RGate.act (.x x) i).testBit control = true := by
                rw [testBit_act_x_other hcx, hcontrol]
              rw [act_cx_eq_x_of_control_true hx]
              have hxy :
                  (RGate.act (.x y) (RGate.act (.x x) i)).testBit control =
                    true := by
                rw [testBit_act_x_other hcy, hx]
              have hmiddle :
                  (RGate.act (.ccx x y target)
                    (RGate.act (.x y) (RGate.act (.x x) i))).testBit control =
                    true := by
                rw [testBit_act_ccx_other hcx hcy hct, hxy]
              rw [act_cx_eq_x_of_control_true hmiddle]
              have hpostY :
                  (RGate.act (.x y)
                    (RGate.act (.ccx x y target)
                      (RGate.act (.x y) (RGate.act (.x x) i)))).testBit
                      control = true := by
                rw [testBit_act_x_other hcy, hmiddle]
              rw [act_cx_eq_x_of_control_true hpostY]

theorem controlledXorProductGates_control
    {control x y target i : Nat} {invertX invertY : Bool}
    (hcx : control ≠ x) (hcy : control ≠ y)
    (hct : control ≠ target) :
    (actGates
        (controlledXorProductGates control x y target invertX invertY) i).testBit
        control = i.testBit control := by
  rw [controlledXorProductGates_act hcx hcy hct]
  apply Reversible.testBit_actGates_of_outside
  intro gate hgate
  cases hx : invertX && i.testBit control with
  | false =>
      cases hy : invertY && i.testBit control with
      | false =>
          simp [xorProductGates, hx, hy] at hgate
          subst gate
          simp [RGate.wires, hcx, hcy, hct]
      | true =>
          simp [xorProductGates, hx, hy] at hgate
          rcases hgate with hgate | hgate | hgate <;> subst gate <;>
            simp [RGate.wires, hcx, hcy, hct]
  | true =>
      cases hy : invertY && i.testBit control with
      | false =>
          simp [xorProductGates, hx, hy] at hgate
          rcases hgate with hgate | hgate | hgate <;> subst gate <;>
            simp [RGate.wires, hcx, hcy, hct]
      | true =>
          simp [xorProductGates, hx, hy] at hgate
          rcases hgate with hgate | hgate | hgate | hgate | hgate <;>
            subst gate <;> simp [RGate.wires, hcx, hcy, hct]

def selectedConstant (constant control i : Nat) : Nat :=
  if i.testBit control then constant else 0

theorem selectedConstant_testBit (constant control i bit : Nat) :
    (selectedConstant constant control i).testBit bit =
      (constant.testBit bit && i.testBit control) := by
  by_cases hcontrol : i.testBit control = true
  · rw [selectedConstant, if_pos hcontrol]
    simp [hcontrol]
  · have hcontrol' : i.testBit control = false :=
      Bool.eq_false_iff.mpr hcontrol
    rw [selectedConstant, if_neg hcontrol]
    simp [hcontrol', Nat.zero_testBit]

theorem controlledConstantXorGates_act
    {control constant target width i : Nat}
    (hcontrol : control < target ∨ target + width ≤ control) :
    actGates
        (Reversible.controlledXorGates control target width constant) i =
      actGates
        (constantXorGates (selectedConstant constant control i) target width) i := by
  rw [Reversible.controlledXorGates_act_xor hcontrol,
    act_constantXorGates]
  cases hc : bitValue i control with
  | zero =>
      have ht : i.testBit control = false := by
        exact (testBit_eq_false_iff_bitValue_eq_zero i control).mpr hc
      simp [selectedConstant, ht, readField_zero]
  | succ value =>
      have hlt := bitValue_lt i control
      have hone : value = 0 := by omega
      subst value
      have ht : i.testBit control = true := by
        exact (testBit_eq_true_iff_bitValue_eq_one i control).mpr hc
      simp [selectedConstant, ht]

theorem controlledConstantXorGates_control
    {control constant target width i : Nat}
    (hcontrol : control < target ∨ target + width ≤ control) :
    (actGates
        (Reversible.controlledXorGates control target width constant) i).testBit
      control = i.testBit control := by
  rw [controlledConstantXorGates_act hcontrol]
  apply Reversible.testBit_actGates_of_outside
  intro gate hgate hwire
  have hw := constantXorGates_wires gate hgate control hwire
  omega

def controlledCarryReverseStepGates (constant width bit : Nat) : List RGate :=
  controlledXorProductGates (constantControlWire width)
    (targetWire bit) (dirtyWire width (bit - 1)) (dirtyWire width bit)
    (constant.testBit bit) false

def controlledCarryForwardStepGates (constant width bit : Nat) : List RGate :=
  controlledXorProductGates (constantControlWire width)
    (targetWire bit) (dirtyWire width (bit - 1)) (dirtyWire width bit)
    (constant.testBit bit) (constant.testBit bit)

def controlledCarryReverseGates (constant width : Nat) : Nat → List RGate
  | 0 => []
  | count + 1 =>
      controlledCarryReverseStepGates constant width (count + 1) ++
        controlledCarryReverseGates constant width count

def controlledCarryForwardGates (constant width : Nat) : Nat → List RGate
  | 0 => []
  | count + 1 =>
      controlledCarryForwardGates constant width count ++
        controlledCarryForwardStepGates constant width (count + 1)

def controlledCarryBaseGates (constant width : Nat) : List RGate :=
  controlledXorProductGates (constantControlWire width)
    (carryWire width 0) (targetWire 0) (dirtyWire width 0)
    (constant.testBit 0) (constant.testBit 0)

def controlledCarryReconstructionGates (constant width : Nat) : List RGate :=
  constantXorGates (2 ^ width - 1) 0 width ++
    controlledCarryReverseGates constant width (width - 2) ++
    Reversible.controlledXorGates (constantControlWire width)
      width (width - 1) constant ++
    controlledCarryBaseGates constant width ++
    controlledCarryForwardGates constant width (width - 2) ++
    constantXorGates (2 ^ width - 1) 0 width

theorem controlledCarryReverseStepGates_act
    {constant width bit i : Nat} (hbit : bit < width) :
    actGates (controlledCarryReverseStepGates constant width bit) i =
      actGates
        (carryReverseStepGates
          (selectedConstant constant (constantControlWire width) i)
          width bit) i := by
  rw [controlledCarryReverseStepGates, carryReverseStepGates,
    controlledXorProductGates_act]
  · rw [selectedConstant_testBit]
    simp
  all_goals simp [constantControlWire, adderWidth, targetWire, dirtyWire]
  all_goals omega

theorem controlledCarryForwardStepGates_act
    {constant width bit i : Nat} (hbit : bit < width) :
    actGates (controlledCarryForwardStepGates constant width bit) i =
      actGates
        (carryForwardStepGates
          (selectedConstant constant (constantControlWire width) i)
          width bit) i := by
  rw [controlledCarryForwardStepGates, carryForwardStepGates,
    controlledXorProductGates_act]
  · rw [selectedConstant_testBit]
  all_goals simp [constantControlWire, adderWidth, targetWire, dirtyWire]
  all_goals omega

theorem controlledCarryBaseGates_act
    {constant width i : Nat} (hwidth : 0 < width) :
    actGates (controlledCarryBaseGates constant width) i =
      actGates
        (carryBaseGates
          (selectedConstant constant (constantControlWire width) i)
          width) i := by
  rw [controlledCarryBaseGates, carryBaseGates,
    controlledXorProductGates_act]
  · rw [selectedConstant_testBit]
  all_goals
    simp [constantControlWire, adderWidth, targetWire, dirtyWire,
      carryWire]
  all_goals omega

theorem selectedConstant_control_congr {constant control i j : Nat}
    (hcontrol : j.testBit control = i.testBit control) :
    selectedConstant constant control j = selectedConstant constant control i := by
  simp [selectedConstant, hcontrol]

theorem controlledCarryReverseStepGates_control
    {constant width bit i : Nat} (hbit : bit < width) :
    (actGates (controlledCarryReverseStepGates constant width bit) i).testBit
        (constantControlWire width) =
      i.testBit (constantControlWire width) := by
  apply controlledXorProductGates_control
  all_goals simp [constantControlWire, adderWidth, targetWire, dirtyWire]
  all_goals omega

theorem controlledCarryForwardStepGates_control
    {constant width bit i : Nat} (hbit : bit < width) :
    (actGates (controlledCarryForwardStepGates constant width bit) i).testBit
        (constantControlWire width) =
      i.testBit (constantControlWire width) := by
  apply controlledXorProductGates_control
  all_goals simp [constantControlWire, adderWidth, targetWire, dirtyWire]
  all_goals omega

theorem controlledCarryBaseGates_control
    {constant width i : Nat} (hwidth : 0 < width) :
    (actGates (controlledCarryBaseGates constant width) i).testBit
        (constantControlWire width) =
      i.testBit (constantControlWire width) := by
  apply controlledXorProductGates_control
  all_goals
    simp [constantControlWire, adderWidth, targetWire, dirtyWire,
      carryWire] <;> omega

theorem controlledCarryReverseGates_control {constant width count i : Nat}
    (hcount : count < width) :
    (actGates (controlledCarryReverseGates constant width count) i).testBit
        (constantControlWire width) =
      i.testBit (constantControlWire width) := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      rw [controlledCarryReverseGates, actGates_append,
        ih (by omega), controlledCarryReverseStepGates_control (by omega)]

theorem controlledCarryForwardGates_control {constant width count i : Nat}
    (hcount : count < width) :
    (actGates (controlledCarryForwardGates constant width count) i).testBit
        (constantControlWire width) =
      i.testBit (constantControlWire width) := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      rw [controlledCarryForwardGates, actGates_append,
        controlledCarryForwardStepGates_control (by omega), ih (by omega)]

theorem controlledCarryReverseGates_act {constant width count i : Nat}
    (hcount : count < width) :
    actGates (controlledCarryReverseGates constant width count) i =
      actGates
        (carryReverseGates
          (selectedConstant constant (constantControlWire width) i)
          width count) i := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      rw [controlledCarryReverseGates, carryReverseGates,
        actGates_append, actGates_append,
        controlledCarryReverseStepGates_act (by omega)]
      let j := actGates
        (carryReverseStepGates
          (selectedConstant constant (constantControlWire width) i)
          width (count + 1)) i
      have hcontrol : j.testBit (constantControlWire width) =
          i.testBit (constantControlWire width) := by
        rw [show j = actGates
          (controlledCarryReverseStepGates constant width (count + 1)) i by
            symm
            exact controlledCarryReverseStepGates_act (by omega)]
        exact controlledCarryReverseStepGates_control (by omega)
      rw [ih (by omega)]
      rw [selectedConstant_control_congr hcontrol]

theorem controlledCarryForwardGates_act {constant width count i : Nat}
    (hcount : count < width) :
    actGates (controlledCarryForwardGates constant width count) i =
      actGates
        (carryForwardGates
          (selectedConstant constant (constantControlWire width) i)
          width count) i := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      rw [controlledCarryForwardGates, carryForwardGates,
        actGates_append, actGates_append, ih (by omega)]
      let j := actGates
        (carryForwardGates
          (selectedConstant constant (constantControlWire width) i)
          width count) i
      have hcontrol : j.testBit (constantControlWire width) =
          i.testBit (constantControlWire width) := by
        rw [show j = actGates
          (controlledCarryForwardGates constant width count) i by
            symm
            exact ih (by omega)]
        exact controlledCarryForwardGates_control (by omega)
      rw [controlledCarryForwardStepGates_act (by omega),
        selectedConstant_control_congr hcontrol]

theorem constantXorGates_testBit_outside
    {value target width control i : Nat}
    (hcontrol : control < target ∨ target + width ≤ control) :
    (actGates (constantXorGates value target width) i).testBit control =
      i.testBit control := by
  apply Reversible.testBit_actGates_of_outside
  intro gate hgate hwire
  have hw := constantXorGates_wires gate hgate control hwire
  omega

theorem controlledCarryReconstructionGates_act
    {constant width i : Nat} (hwidth : 2 ≤ width) :
    actGates (controlledCarryReconstructionGates constant width) i =
      actGates
        (carryReconstructionGates
          (selectedConstant constant (constantControlWire width) i)
          width) i := by
  let control := constantControlWire width
  let selected := selectedConstant constant control i
  let first := actGates (constantXorGates (2 ^ width - 1) 0 width) i
  let reversed :=
    actGates (controlledCarryReverseGates constant width (width - 2)) first
  let shifted := actGates
    (Reversible.controlledXorGates control width (width - 1) constant)
    reversed
  let based := actGates (controlledCarryBaseGates constant width) shifted
  let forwarded :=
    actGates (controlledCarryForwardGates constant width (width - 2)) based
  have hfirstControl : first.testBit control = i.testBit control := by
    exact constantXorGates_testBit_outside (by
      simp [control, constantControlWire, adderWidth]
      omega)
  have hfirstSelected : selectedConstant constant control first = selected :=
    selectedConstant_control_congr hfirstControl
  have hreversed : reversed =
      actGates (carryReverseGates selected width (width - 2)) first := by
    rw [show reversed =
      actGates (controlledCarryReverseGates constant width (width - 2)) first
        by rfl,
      controlledCarryReverseGates_act (by omega), hfirstSelected]
  have hreversedControl : reversed.testBit control = i.testBit control := by
    rw [show reversed =
      actGates (controlledCarryReverseGates constant width (width - 2)) first
        by rfl,
      controlledCarryReverseGates_control (by omega), hfirstControl]
  have hreversedSelected :
      selectedConstant constant control reversed = selected :=
    selectedConstant_control_congr hreversedControl
  have hshifted : shifted =
      actGates (constantXorGates selected width (width - 1)) reversed := by
    rw [show shifted = actGates
      (Reversible.controlledXorGates control width (width - 1) constant)
      reversed by rfl,
      controlledConstantXorGates_act (by
        simp [control, constantControlWire, adderWidth]
        omega), hreversedSelected]
  have hshiftedControl : shifted.testBit control = i.testBit control := by
    rw [show shifted = actGates
      (Reversible.controlledXorGates control width (width - 1) constant)
      reversed by rfl,
      controlledConstantXorGates_control (by
        simp [control, constantControlWire, adderWidth]
        omega), hreversedControl]
  have hshiftedSelected : selectedConstant constant control shifted = selected :=
    selectedConstant_control_congr hshiftedControl
  have hbased : based = actGates (carryBaseGates selected width) shifted := by
    rw [show based = actGates
      (controlledCarryBaseGates constant width) shifted by rfl,
      controlledCarryBaseGates_act (by omega), hshiftedSelected]
  have hbasedControl : based.testBit control = i.testBit control := by
    rw [show based = actGates
      (controlledCarryBaseGates constant width) shifted by rfl,
      controlledCarryBaseGates_control (by omega), hshiftedControl]
  have hbasedSelected : selectedConstant constant control based = selected :=
    selectedConstant_control_congr hbasedControl
  have hforwarded : forwarded =
      actGates (carryForwardGates selected width (width - 2)) based := by
    rw [show forwarded = actGates
      (controlledCarryForwardGates constant width (width - 2)) based by rfl,
      controlledCarryForwardGates_act (by omega), hbasedSelected]
  rw [controlledCarryReconstructionGates, carryReconstructionGates]
  simp only [actGates_append]
  change actGates (constantXorGates (2 ^ width - 1) 0 width) forwarded =
    actGates (constantXorGates (2 ^ width - 1) 0 width)
      (actGates (carryForwardGates selected width (width - 2))
        (actGates (carryBaseGates selected width)
          (actGates (constantXorGates selected width (width - 1))
            (actGates (carryReverseGates selected width (width - 2)) first))))
  rw [hforwarded, hbased, hshifted, hreversed]

def controlledCarryStepOps (constant width bit : Nat) : List Op :=
  gateOps (controlledCarryStepGates constant width bit) ++
    if bit = 0 then []
    else measureCopiedOps (carryWire width bit) (dirtyWire width (bit - 1))
      (bit - 1)

def controlledCarryPrefixOps (constant width : Nat) : Nat → List Op
  | 0 => []
  | count + 1 =>
      controlledCarryPrefixOps constant width count ++
        controlledCarryStepOps constant width count

def controlledCarryTopOps (constant width : Nat) : List Op :=
  gateOps (controlledCarryTopGates constant width) ++
    measureCopiedOps (carryWire width (width - 1))
      (dirtyWire width (width - 2)) (width - 2)

def controlledCarryChainOps (constant width : Nat) : List Op :=
  controlledCarryPrefixOps constant width (width - 1) ++
    controlledCarryTopOps constant width

def controlledConstantAddOps (constant width : Nat) : List Op :=
  controlledCarryChainOps constant width ++
    (gateOps (controlledCarryReconstructionGates constant width) ++
      phaseCorrectionOps width (width - 1))

def controlledCarryStepOut (constant width bit i : Nat) : Nat :=
  let j := actGates (controlledCarryStepGates constant width bit) i
  if bit = 0 then j
  else outputIndex (carryWire width bit) (dirtyWire width (bit - 1)) j

def controlledCarryPrefixOut (constant width : Nat) : Nat → Nat → Nat
  | 0, i => i
  | count + 1, i =>
      controlledCarryStepOut constant width count
        (controlledCarryPrefixOut constant width count i)

def controlledCarryTopOut (constant width i : Nat) : Nat :=
  outputIndex (carryWire width (width - 1))
    (dirtyWire width (width - 2))
    (actGates (controlledCarryTopGates constant width) i)

def controlledCarryChainOut (constant width i : Nat) : Nat :=
  controlledCarryTopOut constant width
    (controlledCarryPrefixOut constant width (width - 1) i)

theorem controlledCarryStepGates_control {constant width bit i : Nat}
    (hbit : bit < width) :
    (actGates (controlledCarryStepGates constant width bit) i).testBit
        (constantControlWire width) =
      i.testBit (constantControlWire width) := by
  rw [controlledCarryStepGates_act hbit]
  apply testBit_eq_of_bitValue_eq
  apply carryStepGates_bitValue_other
  all_goals
    simp [constantControlWire, adderWidth, targetWire, carryWire,
      spareWire, ancillaWire] <;> omega

theorem controlledCarryTopGates_control {constant width i : Nat}
    (hwidth : 0 < width) :
    (actGates (controlledCarryTopGates constant width) i).testBit
        (constantControlWire width) =
      i.testBit (constantControlWire width) := by
  rw [controlledCarryTopGates_act hwidth]
  apply testBit_eq_of_bitValue_eq
  apply carryTopGates_bitValue_other
  simp [constantControlWire, adderWidth, targetWire]
  omega

theorem outputIndex_testBit_other {value dirty control i : Nat}
    (hvalue : control ≠ value) (hdirty : control ≠ dirty) :
    (outputIndex value dirty i).testBit control = i.testBit control := by
  exact outputIndex_other hvalue hdirty

theorem controlledCarryStepOut_control {constant width bit i : Nat}
    (hbit : bit < width) :
    (controlledCarryStepOut constant width bit i).testBit
        (constantControlWire width) =
      i.testBit (constantControlWire width) := by
  rw [controlledCarryStepOut]
  by_cases hzero : bit = 0
  · rw [if_pos hzero]
    exact controlledCarryStepGates_control hbit
  · rw [if_neg hzero, outputIndex_testBit_other]
    · exact controlledCarryStepGates_control hbit
    · simp [constantControlWire, adderWidth, carryWire]
      omega
    · simp [constantControlWire, adderWidth, dirtyWire]
      omega

theorem controlledCarryTopOut_control {constant width i : Nat}
    (hwidth : 2 ≤ width) :
    (controlledCarryTopOut constant width i).testBit
        (constantControlWire width) =
      i.testBit (constantControlWire width) := by
  rw [controlledCarryTopOut, outputIndex_testBit_other]
  · exact controlledCarryTopGates_control (by omega)
  · simp [constantControlWire, adderWidth, carryWire]
    omega
  · simp [constantControlWire, adderWidth, dirtyWire]
    omega

theorem controlledCarryStepOut_act {constant width bit i : Nat}
    (hbit : bit < width) :
    controlledCarryStepOut constant width bit i =
      carryStepOut
        (selectedConstant constant (constantControlWire width) i)
        width bit i := by
  simp only [controlledCarryStepOut, carryStepOut]
  rw [controlledCarryStepGates_act hbit]
  rfl

theorem controlledCarryTopOut_act {constant width i : Nat}
    (hwidth : 2 ≤ width) :
    controlledCarryTopOut constant width i =
      carryTopOut
        (selectedConstant constant (constantControlWire width) i)
        width i := by
  simp only [controlledCarryTopOut, carryTopOut]
  rw [controlledCarryTopGates_act (by omega)]
  rfl

theorem controlledCarryPrefixOut_control
    {constant width count i : Nat} (hcount : count ≤ width) :
    (controlledCarryPrefixOut constant width count i).testBit
        (constantControlWire width) =
      i.testBit (constantControlWire width) := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      rw [controlledCarryPrefixOut,
        controlledCarryStepOut_control (by omega), ih (by omega)]

theorem controlledCarryPrefixOut_act
    {constant width count i : Nat} (hcount : count ≤ width) :
    controlledCarryPrefixOut constant width count i =
      carryPrefixOut
        (selectedConstant constant (constantControlWire width) i)
        width count i := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
      have hcontrol := controlledCarryPrefixOut_control
        (constant := constant) (i := i) (by omega : count ≤ width)
      rw [ih (by omega)] at hcontrol
      rw [controlledCarryPrefixOut, carryPrefixOut,
        controlledCarryStepOut_act (by omega), ih (by omega)]
      rw [selectedConstant_control_congr hcontrol]

theorem controlledCarryChainOut_control {constant width i : Nat}
    (hwidth : 2 ≤ width) :
    (controlledCarryChainOut constant width i).testBit
        (constantControlWire width) =
      i.testBit (constantControlWire width) := by
  rw [controlledCarryChainOut, controlledCarryTopOut_control hwidth,
    controlledCarryPrefixOut_control (by omega)]

theorem controlledCarryChainOut_act {constant width i : Nat}
    (hwidth : 2 ≤ width) :
    controlledCarryChainOut constant width i =
      carryChainOut
        (selectedConstant constant (constantControlWire width) i)
        width i := by
  have hcontrol := controlledCarryPrefixOut_control
    (constant := constant) (i := i) (by omega : width - 1 ≤ width)
  rw [controlledCarryPrefixOut_act (by omega)] at hcontrol
  rw [controlledCarryChainOut, carryChainOut,
    controlledCarryTopOut_act hwidth,
    controlledCarryPrefixOut_act (by omega)]
  rw [selectedConstant_control_congr hcontrol]

theorem controlledCarryPrefixOut_state
    {original constant width count : Nat}
    (hcount : count ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0) :
    CarryPrefixState original
      (selectedConstant constant (constantControlWire width) original)
      width count
      (controlledCarryPrefixOut constant width count original) := by
  rw [controlledCarryPrefixOut_act hcount]
  exact carryPrefixOut_state hcount hcarry hspare hancilla

theorem controlledCarryChainOut_state
    {original constant width : Nat}
    (hwidth : 2 ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0) :
    CarryChainState original
      (selectedConstant constant (constantControlWire width) original)
      width (controlledCarryChainOut constant width original) := by
  rw [controlledCarryChainOut_act hwidth]
  exact carryChainOut_state hwidth hcarry hspare hancilla

theorem carryCoreGates_wellFormed_succ {width bit : Nat}
    (hbit : bit < width) :
    (carryCoreGates width bit).all
      (RGate.wellFormed (2 * width + 4)) = true := by
  apply List.all_eq_true.mpr
  intro gate hgate
  apply RGate.wellFormed_mono
    (w := adderWidth width) (by simp [adderWidth])
  exact List.all_eq_true.mp (carryCoreGates_wellFormed hbit) gate hgate

theorem controlledCarryStepGates_wellFormed
    {constant width bit : Nat} (hbit : bit < width) :
    (controlledCarryStepGates constant width bit).all
      (RGate.wellFormed (2 * width + 4)) = true := by
  have hcore := carryCoreGates_wellFormed_succ hbit
  have hcontrol : constantControlWire width < 2 * width + 4 := by
    simp [constantControlWire, adderWidth]
  have htarget : targetWire bit < 2 * width + 4 := by
    simp [targetWire]
    omega
  have hancilla : ancillaWire width < 2 * width + 4 := by
    simp [ancillaWire]
  have hcontrolTarget : constantControlWire width ≠ targetWire bit := by
    simp [constantControlWire, adderWidth, targetWire]
    omega
  have hcontrolAncilla :
      constantControlWire width ≠ ancillaWire width := by
    simp [constantControlWire, adderWidth, ancillaWire]
  by_cases hk : constant.testBit bit = true
  · simp [controlledCarryStepGates, hk, hcore, RGate.wellFormed,
      hcontrol, htarget, hancilla, hcontrolTarget, hcontrolAncilla]
  · have hk' : constant.testBit bit = false := Bool.eq_false_iff.mpr hk
    simp [controlledCarryStepGates, hk', hcore]

theorem controlledCarryTopGates_wellFormed
    {constant width : Nat} (hwidth : 2 ≤ width) :
    (controlledCarryTopGates constant width).all
      (RGate.wellFormed (2 * width + 4)) = true := by
  have hcontrol : constantControlWire width < 2 * width + 4 := by
    simp [constantControlWire, adderWidth]
  have htarget : targetWire (width - 1) < 2 * width + 4 := by
    simp [targetWire]
    omega
  have hcarry : carryWire width (width - 1) < 2 * width + 4 := by
    have h := carryWire_lt width (width - 1)
    simp [adderWidth] at h ⊢
    omega
  have hcontrolTarget :
      constantControlWire width ≠ targetWire (width - 1) := by
    simp [constantControlWire, adderWidth, targetWire]
    omega
  have hcarryTarget :
      carryWire width (width - 1) ≠ targetWire (width - 1) :=
    carryWire_ne_targetWire (by omega)
  by_cases hk : constant.testBit (width - 1) = true
  · simp [controlledCarryTopGates, hk, RGate.wellFormed,
      hcontrol, htarget, hcarry, hcontrolTarget, hcarryTarget]
  · have hk' : constant.testBit (width - 1) = false :=
      Bool.eq_false_iff.mpr hk
    simp [controlledCarryTopGates, hk', RGate.wellFormed,
      htarget, hcarry, hcarryTarget]

theorem controlledXorProductGates_wellFormed
    {control x y target total : Nat} {invertX invertY : Bool}
    (hcontrol : control < total) (hx : x < total) (hy : y < total)
    (htarget : target < total)
    (hcx : control ≠ x) (hcy : control ≠ y)
    (hxy : x ≠ y) (hxt : x ≠ target) (hyt : y ≠ target) :
    (controlledXorProductGates control x y target invertX invertY).all
      (RGate.wellFormed total) = true := by
  cases invertX <;> cases invertY <;>
    simp [controlledXorProductGates, RGate.wellFormed,
      hcontrol, hx, hy, htarget, hcx, hcy, hxy, hxt, hyt]

theorem controlledCarryReverseStepGates_wellFormed
    {constant width bit : Nat} (hpositive : 0 < bit) (hbit : bit < width) :
    (controlledCarryReverseStepGates constant width bit).all
      (RGate.wellFormed (2 * width + 4)) = true := by
  apply controlledXorProductGates_wellFormed
  all_goals
    simp [constantControlWire, adderWidth, targetWire, dirtyWire] <;> omega

theorem controlledCarryForwardStepGates_wellFormed
    {constant width bit : Nat} (hpositive : 0 < bit) (hbit : bit < width) :
    (controlledCarryForwardStepGates constant width bit).all
      (RGate.wellFormed (2 * width + 4)) = true := by
  apply controlledXorProductGates_wellFormed
  all_goals
    simp [constantControlWire, adderWidth, targetWire, dirtyWire] <;> omega

theorem controlledCarryBaseGates_wellFormed
    {constant width : Nat} (hwidth : 0 < width) :
    (controlledCarryBaseGates constant width).all
      (RGate.wellFormed (2 * width + 4)) = true := by
  apply controlledXorProductGates_wellFormed
  all_goals
    simp [constantControlWire, adderWidth, targetWire, dirtyWire,
      carryWire] <;> omega

theorem controlledCarryReverseGates_wellFormed
    {constant width count : Nat} (hcount : count < width) :
    (controlledCarryReverseGates constant width count).all
      (RGate.wellFormed (2 * width + 4)) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [controlledCarryReverseGates, List.all_append,
        controlledCarryReverseStepGates_wellFormed (by omega) (by omega),
        ih (by omega)]
      rfl

theorem controlledCarryForwardGates_wellFormed
    {constant width count : Nat} (hcount : count < width) :
    (controlledCarryForwardGates constant width count).all
      (RGate.wellFormed (2 * width + 4)) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [controlledCarryForwardGates, List.all_append, ih (by omega),
        controlledCarryForwardStepGates_wellFormed (by omega) (by omega)]
      rfl

theorem controlledCarryReconstructionGates_wellFormed
    {constant width : Nat} (hwidth : 2 ≤ width) :
    (controlledCarryReconstructionGates constant width).all
      (RGate.wellFormed (2 * width + 4)) = true := by
  have hall : (constantXorGates (2 ^ width - 1) 0 width).all
      (RGate.wellFormed (2 * width + 4)) = true :=
    constantXorGates_wellFormed (by omega)
  have hreverse := controlledCarryReverseGates_wellFormed
    (constant := constant) (width := width) (count := width - 2) (by omega)
  have hcontrolled :
      (Reversible.controlledXorGates (constantControlWire width)
        width (width - 1) constant).all
          (RGate.wellFormed (2 * width + 4)) = true := by
    apply Reversible.controlledXorGates_wellFormed
    · right
      simp [constantControlWire, adderWidth]
      omega
    · simp [constantControlWire, adderWidth]
    · omega
  have hbase := controlledCarryBaseGates_wellFormed
    (constant := constant) (width := width) (by omega)
  have hforward := controlledCarryForwardGates_wellFormed
    (constant := constant) (width := width) (count := width - 2) (by omega)
  simp [controlledCarryReconstructionGates, hall, hreverse, hcontrolled,
    hbase, hforward]

theorem controlledCarryStepOps_zero_run
    {level constant width i : Nat}
    (hl : 3 ≤ level) (hwidth : 0 < width)
    (rec : List Bool) (creg input : Nat) :
    runOps level (2 * width + 4) (controlledCarryStepOps constant width 0)
        (Branch.mk rec creg (basis i) input) =
      [Branch.mk rec creg
        (basis (actGates (controlledCarryStepGates constant width 0) i))
        input] := by
  rw [controlledCarryStepOps, if_pos rfl, List.append_nil]
  exact gateOps_basis_run hl
    (controlledCarryStepGates_wellFormed hwidth) rec creg input i

theorem controlledCarryStepOps_succ_run
    {level constant width bit i : Nat}
    (hl : 3 ≤ level) (hbit : bit + 1 < width)
    (rec : List Bool) (creg input : Nat) :
    let value := carryWire width (bit + 1)
    let dirty := dirtyWire width bit
    let j := actGates (controlledCarryStepGates constant width (bit + 1)) i
    runOps level (2 * width + 4)
        (controlledCarryStepOps constant width (bit + 1))
        (Branch.mk rec creg (basis i) input) =
      [Branch.mk (false :: rec) (writeBit creg bit false)
          (Algebra.Dy.invSqrt2 (deg level) •
            basis (outputIndex value dirty j)) input,
        Branch.mk (true :: rec) (writeBit creg bit true)
          (Algebra.Dy.invSqrt2 (deg level) •
            (Lookup.MeasuredUncompute.phaseScalar (deg level)
              (j.testBit dirty) • basis (outputIndex value dirty j))) input] := by
  let value := carryWire width (bit + 1)
  let dirty := dirtyWire width bit
  let j := actGates (controlledCarryStepGates constant width (bit + 1)) i
  have hwf := controlledCarryStepGates_wellFormed
    (constant := constant) (width := width) hbit
  have hvalue : value < 2 * width + 4 := by
    exact lt_of_lt_of_le (carryWire_lt width (bit + 1)) (by
      simp [adderWidth])
  have hdirty : dirty < 2 * width + 4 := by
    simp [dirty, dirtyWire]
    omega
  have hne : value ≠ dirty := carryWire_ne_dirtyWire (by omega)
  have hgates := gateOps_basis_run hl hwf rec creg input i
  rw [controlledCarryStepOps, if_neg (by omega), runOps_append,
    hgates, List.flatMap_singleton]
  exact measureCopiedOps_run hl hvalue hdirty hne rec creg input

theorem controlledCarryTopOps_run {level constant width i : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ width)
    (rec : List Bool) (creg input : Nat) :
    let value := carryWire width (width - 1)
    let dirty := dirtyWire width (width - 2)
    let j := actGates (controlledCarryTopGates constant width) i
    runOps level (2 * width + 4) (controlledCarryTopOps constant width)
        (Branch.mk rec creg (basis i) input) =
      [Branch.mk (false :: rec) (writeBit creg (width - 2) false)
          (Algebra.Dy.invSqrt2 (deg level) •
            basis (outputIndex value dirty j)) input,
        Branch.mk (true :: rec) (writeBit creg (width - 2) true)
          (Algebra.Dy.invSqrt2 (deg level) •
            (Lookup.MeasuredUncompute.phaseScalar (deg level)
              (j.testBit dirty) • basis (outputIndex value dirty j))) input] := by
  let value := carryWire width (width - 1)
  let dirty := dirtyWire width (width - 2)
  let j := actGates (controlledCarryTopGates constant width) i
  have hwf := controlledCarryTopGates_wellFormed
    (constant := constant) hwidth
  have hvalue : value < 2 * width + 4 := by
    exact lt_of_lt_of_le (carryWire_lt width (width - 1)) (by
      simp [adderWidth])
  have hdirty : dirty < 2 * width + 4 := by
    simp [dirty, dirtyWire]
    omega
  have hne : value ≠ dirty := carryWire_ne_dirtyWire (by omega)
  have hgates := gateOps_basis_run hl hwf rec creg input i
  rw [controlledCarryTopOps, runOps_append, hgates,
    List.flatMap_singleton]
  exact measureCopiedOps_run hl hvalue hdirty hne rec creg input

theorem controlledCarryPrefixOps_mask
    {level constant width count original input : Nat}
    (hl : 3 ≤ level) (hcount : count ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (2 * width + 4)
      (controlledCarryPrefixOps constant width count)
      (Branch.mk rec creg (basis original) input)) :
    b.state =
      Algebra.Dy.invSqrt2 (deg level) ^ (count - 1) •
        (Lookup.MeasuredUncompute.phaseScalar (deg level)
          (recordParity width (count - 1) b.creg original) •
          basis (controlledCarryPrefixOut constant width count original)) := by
  induction count generalizing rec creg b with
  | zero =>
      rw [controlledCarryPrefixOps, runOps_nil, List.mem_singleton] at hb
      subst b
      simp [controlledCarryPrefixOut, recordParity,
        Algebra.Dy.pow_zero_eq,
        Lookup.MeasuredUncompute.phaseScalar, Vec.one_smul]
  | succ count ih =>
      rw [controlledCarryPrefixOps, runOps_append, List.mem_flatMap] at hb
      obtain ⟨x, hx, hxb⟩ := hb
      have hxstate := ih (by omega) (rec := rec) (creg := creg) hx
      have hxinput : x.input = input :=
        input_runOps level (2 * width + 4)
          (controlledCarryPrefixOps constant width count) hx
      let c := Algebra.Dy.invSqrt2 (deg level)
      let oldOut := controlledCarryPrefixOut constant width count original
      let oldPhase := Lookup.MeasuredUncompute.phaseScalar (deg level)
        (recordParity width (count - 1) x.creg original)
      let base := Branch.mk x.outcomes x.creg
        (basis oldOut : Vec (deg level)) input
      have hxe : x = smulBranch (c ^ (count - 1))
          (smulBranch oldPhase base) := by
        cases x with
        | mk outcomes xcreg state branchInput =>
            simp only [smulBranch, base] at hxinput ⊢
            subst branchInput
            rw [← hxstate]
      rw [hxe, (runOps_smul level (2 * width + 4)).2,
        List.mem_map] at hxb
      obtain ⟨y, hy, rfl⟩ := hxb
      change y ∈ runOps level (2 * width + 4)
        (controlledCarryStepOps constant width count)
        (smulBranch oldPhase base) at hy
      rw [(runOps_smul level (2 * width + 4)).2,
        List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      cases count with
      | zero =>
          rw [controlledCarryStepOps_zero_run hl (by omega)
            x.outcomes x.creg input] at hz
          rw [List.mem_singleton] at hz
          subst z
          simp [smulBranch, c, oldPhase, oldOut,
            controlledCarryPrefixOut, controlledCarryStepOut, recordParity,
            Algebra.Dy.pow_zero_eq,
            Lookup.MeasuredUncompute.phaseScalar, Vec.one_smul]
      | succ bit =>
          let j := actGates
            (controlledCarryStepGates constant width (bit + 1)) oldOut
          have hstep := controlledCarryStepOps_succ_run
            (level := level) (constant := constant) (width := width)
            (bit := bit) (i := oldOut) hl (by omega)
            x.outcomes x.creg input
          rw [hstep] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          have hprior : bit + 1 - 1 = bit := by omega
          have hnext : bit + 1 + 1 - 1 = bit + 1 := by omega
          have hprefix := controlledCarryPrefixOut_state
            (original := original) (constant := constant)
            (width := width) (count := bit + 1) (by omega)
            hcarry hspare hancilla
          rcases hprefix with ⟨_, _, _, _, hdirtyRest, _, _, _⟩
          have holdDirty :
              bitValue oldOut (dirtyWire width bit) =
                bitValue original (dirtyWire width bit) := by
            exact hdirtyRest bit (by omega) (by omega)
          have hjDirtyValue :
              bitValue j (dirtyWire width bit) =
                bitValue original (dirtyWire width bit) := by
            rw [show bitValue j (dirtyWire width bit) =
                bitValue oldOut (dirtyWire width bit) by
              rw [show j = actGates
                  (carryStepGates
                    (selectedConstant constant (constantControlWire width)
                      oldOut)
                    width (bit + 1)) oldOut by
                exact controlledCarryStepGates_act (by omega)]
              apply carryStepGates_bitValue_other
              · exact dirtyWire_ne_targetWire (by omega) (by omega)
              · exact (carryWire_ne_dirtyWire (by omega)).symm
              · exact (spareWire_ne_dirtyWire (by omega)).symm
              · exact (ancillaWire_ne_dirtyWire (by omega)).symm,
              holdDirty]
          have hjDirty : j.testBit (dirtyWire width bit) =
              original.testBit (dirtyWire width bit) :=
            testBit_eq_of_bitValue_eq hjDirtyValue
          have houtput :
              outputIndex (carryWire width (bit + 1))
                  (dirtyWire width bit) j =
                controlledCarryStepOut constant width (bit + 1) oldOut := by
            simp [controlledCarryStepOut, j]
          rcases hz with hz | hz
          · subst z
            simp only [smulBranch, Vec.smul_smul]
            rw [show outputIndex (carryWire width (bit + 1))
                (dirtyWire width bit)
                (actGates
                  (controlledCarryStepGates constant width (bit + 1))
                  oldOut) =
              controlledCarryStepOut constant width (bit + 1) oldOut by
                simpa [j] using houtput]
            rw [hnext, recordParity,
              recordParity_writeBit_after (by omega),
              testBit_writeBit, Bool.and_false, Bool.xor_false]
            simp only [oldPhase, oldOut, c, controlledCarryPrefixOut, hprior]
            rw [Algebra.Dy.pow_succ]
            congr 1
            rw [Algebra.Dy.mul_comm
                (Lookup.MeasuredUncompute.phaseScalar (deg level)
                  (recordParity width bit x.creg original))
                (Algebra.Dy.invSqrt2 (deg level)),
              ← Algebra.Dy.mul_assoc]
          · subst z
            simp only [smulBranch, Vec.smul_smul]
            rw [show outputIndex (carryWire width (bit + 1))
                (dirtyWire width bit)
                (actGates
                  (controlledCarryStepGates constant width (bit + 1))
                  oldOut) =
              controlledCarryStepOut constant width (bit + 1) oldOut by
                simpa [j] using houtput]
            rw [hnext, recordParity,
              recordParity_writeBit_after (by omega),
              testBit_writeBit, Bool.and_true, hjDirty,
              Lookup.BatchedUncompute.phaseScalar_xor]
            simp only [oldPhase, oldOut, c, dirtyWire,
              controlledCarryPrefixOut, hprior]
            rw [Algebra.Dy.pow_succ]
            congr 1
            let a := Algebra.Dy.invSqrt2 (deg level) ^ bit
            let p := Lookup.MeasuredUncompute.phaseScalar (deg level)
              (recordParity width bit x.creg original)
            let c' := Algebra.Dy.invSqrt2 (deg level)
            let q := Lookup.MeasuredUncompute.phaseScalar (deg level)
              (original.testBit (width + bit))
            change a * (p * (c' * q)) = (a * c') * (p * q)
            calc
              a * (p * (c' * q)) = (a * p) * (c' * q) :=
                (Algebra.Dy.mul_assoc _ _ _).symm
              _ = (c' * a) * (p * q) :=
                Lookup.BatchedUncompute.mul_four_reorder _ _ _ _
              _ = (a * c') * (p * q) := by
                rw [Algebra.Dy.mul_comm c' a]

theorem controlledCarryChainOps_mask
    {level constant width original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (2 * width + 4)
      (controlledCarryChainOps constant width)
      (Branch.mk rec creg (basis original) input)) :
    b.state =
      Algebra.Dy.invSqrt2 (deg level) ^ (width - 1) •
        (Lookup.MeasuredUncompute.phaseScalar (deg level)
          (recordParity width (width - 1) b.creg original) •
          basis (controlledCarryChainOut constant width original)) := by
  rw [controlledCarryChainOps, runOps_append, List.mem_flatMap] at hb
  obtain ⟨x, hx, hxb⟩ := hb
  have hxstate := controlledCarryPrefixOps_mask
    (level := level) (constant := constant) (width := width)
    (count := width - 1) (original := original) (input := input)
    hl (by omega) hcarry hspare hancilla rec creg hx
  have hxinput : x.input = input :=
    input_runOps level (2 * width + 4)
      (controlledCarryPrefixOps constant width (width - 1)) hx
  let c := Algebra.Dy.invSqrt2 (deg level)
  let prefixOut :=
    controlledCarryPrefixOut constant width (width - 1) original
  let prefixPhase := Lookup.MeasuredUncompute.phaseScalar (deg level)
    (recordParity width (width - 2) x.creg original)
  let base := Branch.mk x.outcomes x.creg
    (basis prefixOut : Vec (deg level)) input
  have hprefixCount : width - 1 - 1 = width - 2 := by omega
  rw [hprefixCount] at hxstate
  have hxe : x = smulBranch (c ^ (width - 2))
      (smulBranch prefixPhase base) := by
    cases x with
    | mk outcomes xcreg state branchInput =>
        simp only [smulBranch, base] at hxinput ⊢
        subst branchInput
        rw [← hxstate]
  rw [hxe, (runOps_smul level (2 * width + 4)).2,
    List.mem_map] at hxb
  obtain ⟨y, hy, rfl⟩ := hxb
  change y ∈ runOps level (2 * width + 4)
    (controlledCarryTopOps constant width)
    (smulBranch prefixPhase base) at hy
  rw [(runOps_smul level (2 * width + 4)).2, List.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have htop := controlledCarryTopOps_run
    (level := level) (constant := constant) (width := width)
    (i := prefixOut) hl hwidth x.outcomes x.creg input
  rw [htop] at hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  have hprefixState := controlledCarryPrefixOut_state
    (original := original) (constant := constant) (width := width)
    (count := width - 1) (by omega) hcarry hspare hancilla
  rcases hprefixState with ⟨_, _, _, _, hdirtyRest, _, _, _⟩
  have hprevious : width - 2 < width := by omega
  let j := actGates (controlledCarryTopGates constant width) prefixOut
  have hjDirtyValue :
      bitValue j (dirtyWire width (width - 2)) =
        bitValue original (dirtyWire width (width - 2)) := by
    rw [show bitValue j (dirtyWire width (width - 2)) =
        bitValue prefixOut (dirtyWire width (width - 2)) by
      rw [show j = actGates
          (carryTopGates
            (selectedConstant constant (constantControlWire width) prefixOut)
            width) prefixOut by
        exact controlledCarryTopGates_act (by omega)]
      apply carryTopGates_bitValue_other
      exact dirtyWire_ne_targetWire hprevious (by omega),
      hdirtyRest (width - 2) (by omega) hprevious]
  have hjDirty : j.testBit (dirtyWire width (width - 2)) =
      original.testBit (dirtyWire width (width - 2)) :=
    testBit_eq_of_bitValue_eq hjDirtyValue
  have houtput :
      outputIndex (carryWire width (width - 1))
          (dirtyWire width (width - 2)) j =
        controlledCarryChainOut constant width original := by
    rfl
  have hnewCount : width - 2 + 1 = width - 1 := by omega
  rcases hz with hz | hz
  · subst z
    simp only [smulBranch, Vec.smul_smul]
    rw [show outputIndex (carryWire width (width - 1))
        (dirtyWire width (width - 2))
        (actGates (controlledCarryTopGates constant width) prefixOut) =
      controlledCarryChainOut constant width original by
        simpa [j] using houtput]
    rw [← hnewCount, recordParity,
      recordParity_writeBit_after (by omega), testBit_writeBit,
      Bool.and_false, Bool.xor_false]
    simp only [prefixPhase, c]
    rw [Algebra.Dy.pow_succ]
    congr 1
    rw [Algebra.Dy.mul_comm
        (Lookup.MeasuredUncompute.phaseScalar (deg level)
          (recordParity width (width - 2) x.creg original))
        (Algebra.Dy.invSqrt2 (deg level)),
      ← Algebra.Dy.mul_assoc]
  · subst z
    simp only [smulBranch, Vec.smul_smul]
    rw [show outputIndex (carryWire width (width - 1))
        (dirtyWire width (width - 2))
        (actGates (controlledCarryTopGates constant width) prefixOut) =
      controlledCarryChainOut constant width original by
        simpa [j] using houtput]
    rw [← hnewCount, recordParity,
      recordParity_writeBit_after (by omega), testBit_writeBit,
      Bool.and_true, hjDirty,
      Lookup.BatchedUncompute.phaseScalar_xor]
    simp only [prefixPhase, c, dirtyWire]
    rw [Algebra.Dy.pow_succ]
    congr 1
    let a := Algebra.Dy.invSqrt2 (deg level) ^ (width - 2)
    let p := Lookup.MeasuredUncompute.phaseScalar (deg level)
      (recordParity width (width - 2) x.creg original)
    let c' := Algebra.Dy.invSqrt2 (deg level)
    let q := Lookup.MeasuredUncompute.phaseScalar (deg level)
      (original.testBit (width + (width - 2)))
    change a * (p * (c' * q)) = (a * c') * (p * q)
    calc
      a * (p * (c' * q)) = (a * p) * (c' * q) :=
        (Algebra.Dy.mul_assoc _ _ _).symm
      _ = (c' * a) * (p * q) :=
        Lookup.BatchedUncompute.mul_four_reorder _ _ _ _
      _ = (a * c') * (p * q) := by
        rw [Algebra.Dy.mul_comm c' a]

theorem controlledReconstruction_recordParity
    {original constant width creg : Nat}
    (hwidth : 2 ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0) :
    recordParity width (width - 1) creg
        (actGates (controlledCarryReconstructionGates constant width)
          (controlledCarryChainOut constant width original)) =
      recordParity width (width - 1) creg original := by
  let state := controlledCarryChainOut constant width original
  have hcontrol : state.testBit (constantControlWire width) =
      original.testBit (constantControlWire width) :=
    controlledCarryChainOut_control hwidth
  have hstate := controlledCarryChainOut_state
    (original := original) (constant := constant) hwidth
    hcarry hspare hancilla
  rw [show actGates (controlledCarryReconstructionGates constant width) state =
      actGates
        (carryReconstructionGates
          (selectedConstant constant (constantControlWire width) original)
          width) state by
    rw [controlledCarryReconstructionGates_act hwidth]
    exact congrArg
      (fun selected => actGates (carryReconstructionGates selected width) state)
      (selectedConstant_control_congr hcontrol)]
  exact reconstruction_recordParity hstate

theorem controlledConstantAddOps_mask
    {level constant width original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (2 * width + 4)
      (controlledConstantAddOps constant width)
      (Branch.mk rec creg (basis original) input)) :
    b.state =
      Algebra.Dy.invSqrt2 (deg level) ^ (width - 1) •
        basis
          (actGates (controlledCarryReconstructionGates constant width)
            (controlledCarryChainOut constant width original)) := by
  rw [controlledConstantAddOps, runOps_append, List.mem_flatMap] at hb
  obtain ⟨x, hx, hxb⟩ := hb
  have hxstate := controlledCarryChainOps_mask
    (level := level) (constant := constant) (width := width)
    (original := original) (input := input)
    hl hwidth hcarry hspare hancilla rec creg hx
  have hxinput : x.input = input :=
    input_runOps level (2 * width + 4)
      (controlledCarryChainOps constant width) hx
  let amplitude := Algebra.Dy.invSqrt2 (deg level) ^ (width - 1)
  let chainOut := controlledCarryChainOut constant width original
  let reconstructed :=
    actGates (controlledCarryReconstructionGates constant width) chainOut
  let phase := Lookup.MeasuredUncompute.phaseScalar (deg level)
    (recordParity width (width - 1) x.creg original)
  let base := Branch.mk x.outcomes x.creg
    (basis chainOut : Vec (deg level)) input
  have hxe : x = smulBranch amplitude (smulBranch phase base) := by
    cases x with
    | mk outcomes xcreg state branchInput =>
        simp only [smulBranch, amplitude, phase, chainOut, base]
          at hxinput ⊢
        subst branchInput
        rw [← hxstate]
  rw [hxe, (runOps_smul level (2 * width + 4)).2,
    List.mem_map] at hxb
  obtain ⟨y, hy, rfl⟩ := hxb
  change y ∈ runOps level (2 * width + 4)
    (gateOps (controlledCarryReconstructionGates constant width) ++
      phaseCorrectionOps width (width - 1))
    (smulBranch phase base) at hy
  rw [(runOps_smul level (2 * width + 4)).2, List.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hgate := gateOps_basis_run hl
    (controlledCarryReconstructionGates_wellFormed
      (constant := constant) hwidth)
    x.outcomes x.creg input chainOut
  rw [runOps_append, hgate, List.flatMap_singleton,
    phaseCorrectionOps_run hl (by omega)] at hz
  rw [List.mem_singleton] at hz
  subst z
  have hparity : recordParity width (width - 1) x.creg reconstructed =
      recordParity width (width - 1) x.creg original := by
    simpa [reconstructed, chainOut] using
      controlledReconstruction_recordParity
        (constant := constant) (creg := x.creg) hwidth
        hcarry hspare hancilla
  simp [smulBranch, amplitude, phase, reconstructed, chainOut,
    Vec.smul_smul, hparity,
    Lookup.BatchedUncompute.phaseScalar_mul_self, Vec.one_smul]

theorem controlledCarryStepOps_wellFormed
    {level constant width bit cbits : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ width) (hbit : bit < width)
    (hcbit : bit = 0 ∨ bit - 1 < cbits) :
    Program.opsWellFormed level (2 * width + 4) 0 cbits
      (controlledCarryStepOps constant width bit) = true := by
  rw [controlledCarryStepOps, Program.opsWellFormed_append]
  have hgates := Lookup3.gateOps_wellFormed
    (level := level) (w := 2 * width + 4)
    (iw := 0) (cw := cbits) hl
    (controlledCarryStepGates_wellFormed
      (constant := constant) hbit)
  have hgates' : Program.opsWellFormed level (2 * width + 4) 0 cbits
      (gateOps (controlledCarryStepGates constant width bit)) = true := by
    simpa [gateOps] using hgates
  rw [hgates']
  by_cases hzero : bit = 0
  · simp [hzero, Program.opsWellFormed]
  · have hmeasure := measureCopiedOps_wellFormed
      (level := level) (w := 2 * width + 4)
      (value := carryWire width bit)
      (dirty := dirtyWire width (bit - 1))
      (cbit := bit - 1) (cbits := cbits) hl
      (lt_of_lt_of_le (carryWire_lt width bit) (by
        simp [adderWidth]))
      (by simp [dirtyWire]; omega)
      (by simp [carryWire, dirtyWire]; omega)
      (hcbit.resolve_left hzero)
    rw [if_neg hzero, hmeasure]
    rfl

theorem controlledCarryPrefixOps_wellFormed
    {level constant width count : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ width)
    (hcount : count ≤ width - 1) :
    Program.opsWellFormed level (2 * width + 4) 0 (width - 1)
      (controlledCarryPrefixOps constant width count) = true := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [controlledCarryPrefixOps, Program.opsWellFormed_append,
        ih (by omega), controlledCarryStepOps_wellFormed
          hl hwidth (by omega) (by omega)]
      rfl

theorem controlledCarryTopOps_wellFormed
    {level constant width : Nat} (hl : 3 ≤ level) (hwidth : 2 ≤ width) :
    Program.opsWellFormed level (2 * width + 4) 0 (width - 1)
      (controlledCarryTopOps constant width) = true := by
  rw [controlledCarryTopOps, Program.opsWellFormed_append]
  have htop := Lookup3.gateOps_wellFormed
    (level := level) (w := 2 * width + 4)
    (iw := 0) (cw := width - 1) hl
    (controlledCarryTopGates_wellFormed
      (constant := constant) hwidth)
  have htop' : Program.opsWellFormed level (2 * width + 4) 0 (width - 1)
      (gateOps (controlledCarryTopGates constant width)) = true := by
    simpa [gateOps] using htop
  have hmeasure := measureCopiedOps_wellFormed
    (level := level) (w := 2 * width + 4)
    (value := carryWire width (width - 1))
    (dirty := dirtyWire width (width - 2))
    (cbit := width - 2) (cbits := width - 1) hl
    (lt_of_lt_of_le (carryWire_lt width (width - 1)) (by
      simp [adderWidth]))
    (by simp [dirtyWire]; omega)
    (by simp [carryWire, dirtyWire]; omega)
    (by omega)
  rw [htop', hmeasure]
  rfl

theorem controlledCarryChainOps_wellFormed
    {level constant width : Nat} (hl : 3 ≤ level) (hwidth : 2 ≤ width) :
    Program.opsWellFormed level (2 * width + 4) 0 (width - 1)
      (controlledCarryChainOps constant width) = true := by
  rw [controlledCarryChainOps, Program.opsWellFormed_append,
    controlledCarryPrefixOps_wellFormed hl hwidth (by omega),
    controlledCarryTopOps_wellFormed hl hwidth]
  rfl

theorem controlledConstantAddOps_wellFormed
    {level constant width : Nat} (hl : 3 ≤ level) (hwidth : 2 ≤ width) :
    Program.opsWellFormed level (2 * width + 4) 0 (width - 1)
      (controlledConstantAddOps constant width) = true := by
  rw [controlledConstantAddOps, Program.opsWellFormed_append,
    Program.opsWellFormed_append,
    controlledCarryChainOps_wellFormed hl hwidth]
  have hreconstruction := Lookup3.gateOps_wellFormed
    (level := level) (w := 2 * width + 4)
    (iw := 0) (cw := width - 1) hl
    (controlledCarryReconstructionGates_wellFormed
      (constant := constant) hwidth)
  have hreconstruction' :
      Program.opsWellFormed level (2 * width + 4) 0 (width - 1)
        (gateOps (controlledCarryReconstructionGates constant width)) =
          true := by
    simpa [gateOps] using hreconstruction
  rw [hreconstruction',
    phaseCorrectionOps_wellFormed hl (by omega) (by omega)]
  rfl

theorem controlledCarryReconstructionGates_state
    {original constant width : Nat}
    (hwidth : 2 ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0) :
    CarryReconstructedState original
      (selectedConstant constant (constantControlWire width) original)
      width
      (actGates (controlledCarryReconstructionGates constant width)
        (controlledCarryChainOut constant width original)) := by
  let state := controlledCarryChainOut constant width original
  have hcontrol : state.testBit (constantControlWire width) =
      original.testBit (constantControlWire width) :=
    controlledCarryChainOut_control hwidth
  have hchain := controlledCarryChainOut_state
    (original := original) (constant := constant) hwidth
    hcarry hspare hancilla
  rw [show actGates (controlledCarryReconstructionGates constant width) state =
      actGates
        (carryReconstructionGates
          (selectedConstant constant (constantControlWire width) original)
          width) state by
    rw [controlledCarryReconstructionGates_act hwidth]
    exact congrArg
      (fun selected => actGates (carryReconstructionGates selected width) state)
      (selectedConstant_control_congr hcontrol)]
  exact carryReconstructionGates_state hchain

theorem controlledConstantAddOps_reconstructed
    {level constant width original input : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ width)
    (hcarry : bitValue original (carryWire width 0) = 0)
    (hspare : bitValue original (spareWire width 0) = 0)
    (hancilla : bitValue original (ancillaWire width) = 0)
    (rec : List Bool) (creg : Nat) {b : Branch (deg level)}
    (hb : b ∈ runOps level (2 * width + 4)
      (controlledConstantAddOps constant width)
      (Branch.mk rec creg (basis original) input)) :
    let result :=
      actGates (controlledCarryReconstructionGates constant width)
        (controlledCarryChainOut constant width original)
    b.state = Algebra.Dy.invSqrt2 (deg level) ^ (width - 1) •
        basis result ∧
      CarryReconstructedState original
        (selectedConstant constant (constantControlWire width) original)
        width result := by
  refine ⟨controlledConstantAddOps_mask hl hwidth hcarry hspare hancilla
      rec creg hb, ?_⟩
  exact controlledCarryReconstructionGates_state
    hwidth hcarry hspare hancilla

end VQ.Curve.PackedModularProduct
