/-
Unary-iteration QROM with measurement-erased selectors.
-/
import VQ.Lookup.Spec
import VQ.Program.OfCircuit
import VQ.Program.Realise
import VQ.Reversible.ControlledConstant

namespace VQ.Lookup.Unary

open Algebra Reversible Semantics

def selectorWidth (addressWidth : Nat) : Nat := addressWidth + 1

def circuitLayout (addressWidth outputWidth : Nat) : Layout :=
  Lookup.layout addressWidth outputWidth (selectorWidth addressWidth)

def outputOffset (addressWidth : Nat) : Nat := addressWidth

def selectorOffset (addressWidth outputWidth : Nat) : Nat :=
  addressWidth + outputWidth

def selectorWire (addressWidth outputWidth depth : Nat) : Nat :=
  selectorOffset addressWidth outputWidth + depth

def width (addressWidth outputWidth : Nat) : Nat :=
  (circuitLayout addressWidth outputWidth).width

def gateOps (gates : List RGate) : List Op :=
  (gates.flatMap compileGate).map Op.gate

def gateCircuit (addressWidth outputWidth : Nat) (gates : List RGate) : RCircuit :=
  { width := width addressWidth outputWidth, gates := gates }

def negativeAndGates (address parent child : Nat) : List RGate :=
  [.x address, .ccx parent address child, .x address]

def negativeAndOut (address parent child i : Nat) : Nat :=
  writeField i child 1
    ((bitValue i child + bitValue i parent *
      if bitValue i address = 0 then 1 else 0) % 2)

def leafOps (table : List Nat) (addressWidth outputWidth row depth : Nat) : List Op :=
  gateOps (controlledXorGates (selectorWire addressWidth outputWidth depth)
    (outputOffset addressWidth) outputWidth (Lookup.value table outputWidth row))

def nodeOps (table : List Nat) (addressWidth outputWidth : Nat) :
    Nat → Nat → Nat → List Op
  | row, depth, 0 => leafOps table addressWidth outputWidth row depth
  | row, depth, remaining + 1 =>
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      gateOps (negativeAndGates remaining parent child) ++
        nodeOps table addressWidth outputWidth row (depth + 1) remaining ++
        gateOps [.cx parent child] ++
        nodeOps table addressWidth outputWidth (row + 2 ^ remaining)
          (depth + 1) remaining ++
        andUncomputeClean parent remaining child 0

def nodePre (addressWidth outputWidth depth remaining i : Nat) : Prop :=
  readField i (selectorWire addressWidth outputWidth (depth + 1)) remaining = 0

def nodeTarget (table : List Nat) (addressWidth outputWidth row depth remaining i : Nat) : Nat :=
  if i.testBit (selectorWire addressWidth outputWidth depth) then
    writeField i (outputOffset addressWidth) outputWidth
      (Lookup.output addressWidth outputWidth (selectorWidth addressWidth) i ^^^
        Lookup.value table outputWidth (row + readField i 0 remaining))
  else i

def nodeEval (table : List Nat) (addressWidth outputWidth : Nat) :
    Nat → Nat → Nat → Nat → Nat
  | row, depth, 0, i => nodeTarget table addressWidth outputWidth row depth 0 i
  | row, depth, remaining + 1, i =>
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      let i₁ := negativeAndOut remaining parent child i
      let i₂ := nodeEval table addressWidth outputWidth row (depth + 1) remaining i₁
      let i₃ := RGate.act (.cx parent child) i₂
      let i₄ := nodeEval table addressWidth outputWidth (row + 2 ^ remaining)
        (depth + 1) remaining i₃
      writeBit i₄ child false

def lookupOps (table : List Nat) (addressWidth outputWidth : Nat) : List Op :=
  gateOps [.x (selectorWire addressWidth outputWidth 0)] ++
    nodeOps table addressWidth outputWidth 0 0 addressWidth ++
    gateOps [.x (selectorWire addressWidth outputWidth 0)]

def lookupProgram (table : List Nat) (addressWidth outputWidth : Nat) : Program :=
  { width := width addressWidth outputWidth
    cbits := if addressWidth = 0 then 0 else 1
    ops := lookupOps table addressWidth outputWidth }

def rootWire (addressWidth outputWidth : Nat) : Nat :=
  selectorWire addressWidth outputWidth 0

def lookupEval (table : List Nat) (addressWidth outputWidth i : Nat) : Nat :=
  let root := rootWire addressWidth outputWidth
  RGate.act (.x root)
    (nodeEval table addressWidth outputWidth 0 0 addressWidth
      (RGate.act (.x root) i))

theorem width_eq (addressWidth outputWidth : Nat) :
    width addressWidth outputWidth = 2 * addressWidth + outputWidth + 1 := by
  simp [width, circuitLayout, Lookup.layout, selectorWidth, Layout.width]
  omega

theorem gateOps_implements {level input addressWidth outputWidth : Nat}
    (hl : 3 ≤ level) {gates : List RGate}
    (hwf : (gateCircuit addressWidth outputWidth gates).wellFormed = true)
    (c : Dy (deg level)) :
    ImplementsU level (width addressWidth outputWidth) input (fun _ => True)
      (actGates gates) c (gateOps gates) := by
  have h := implementsU_gates hl
    (input := input) (r := gateCircuit addressWidth outputWidth gates) rfl hwf c
  change ImplementsU level (width addressWidth outputWidth) input (fun _ => True)
    (actGates gates) c ((gates.flatMap compileGate).map Op.gate) at h
  exact h

theorem negativeAndGates_wellFormed
    {addressWidth outputWidth depth remaining : Nat}
    (hshape : depth + (remaining + 1) = addressWidth) :
    (gateCircuit addressWidth outputWidth
      (negativeAndGates remaining
        (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1)))).wellFormed = true := by
  simp [gateCircuit, RCircuit.wellFormed, negativeAndGates, RGate.wellFormed,
    width_eq, selectorWire, selectorOffset]
  omega

theorem negativeAndGates_act {address parent child i : Nat}
    (hap : address ≠ parent) (hac : address ≠ child)
    (hpc : parent ≠ child) :
    actGates (negativeAndGates address parent child) i =
      negativeAndOut address parent child i := by
  let j := writeField i address 1 ((bitValue i address + 1) % 2)
  let u := (bitValue j child + bitValue j parent * bitValue j address) % 2
  let k := writeField j child 1 u
  have e1 : RGate.act (.x address) i = j := by
    simp only [j, act_x_write]
  have hjAddress : bitValue j address = ((bitValue i address + 1) % 2) % 2 :=
    bitValue_write_self _ _ _
  have hjParent : bitValue j parent = bitValue i parent :=
    bitValue_write_ne hap.symm
  have hjChild : bitValue j child = bitValue i child :=
    bitValue_write_ne hac.symm
  have e2 : RGate.act (.ccx parent address child) j = k := by
    simp only [k, u]
    rw [act_ccx_write, hjAddress, hjParent, hjChild]
  have hkAddress : bitValue k address = bitValue j address :=
    bitValue_write_ne hac
  have haddress := bitValue_lt i address
  have hrestore : ((((bitValue i address + 1) % 2) % 2 + 1) % 2) =
      bitValue i address := by omega
  have hu : u = (bitValue i child + bitValue i parent *
      if bitValue i address = 0 then 1 else 0) % 2 := by
    unfold u
    rw [hjAddress, hjParent, hjChild]
    by_cases hz : bitValue i address = 0
    · simp [hz]
    · have ho : bitValue i address = 1 := by omega
      simp [ho]
  rw [negativeAndGates, actGates_cons, actGates_cons, actGates_cons,
    actGates_nil, e1, e2, act_x_write, hkAddress, hjAddress, hrestore]
  change writeField (writeField j child 1 u) address 1
    (bitValue i address) = _
  rw [writeField_comm (show child + 1 ≤ address ∨
      address + 1 ≤ child by omega)]
  simp only [j, writeField_writeField]
  rw [show writeField i address 1 (bitValue i address) = i by
      exact write_of_bitValue (by omega), negativeAndOut, hu]

theorem negativeAndOut_child (address parent child i : Nat) :
    bitValue (negativeAndOut address parent child i) child =
      (bitValue i child + bitValue i parent *
        if bitValue i address = 0 then 1 else 0) % 2 := by
  simp [negativeAndOut, bitValue_write_self]

theorem negativeAndOut_ne {address parent child i q : Nat} (hne : q ≠ child) :
    bitValue (negativeAndOut address parent child i) q = bitValue i q :=
  bitValue_write_ne hne

theorem switchGates_wellFormed
    {addressWidth outputWidth depth remaining : Nat}
    (hshape : depth + (remaining + 1) = addressWidth) :
    (gateCircuit addressWidth outputWidth
      [.cx (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1))]).wellFormed = true := by
  simp [gateCircuit, RCircuit.wellFormed, RGate.wellFormed,
    width_eq, selectorWire, selectorOffset]
  omega

theorem leafGates_wellFormed
    {addressWidth outputWidth depth : Nat} (hdepth : depth = addressWidth) (word : Nat) :
    (gateCircuit addressWidth outputWidth
      (controlledXorGates (selectorWire addressWidth outputWidth depth)
        (outputOffset addressWidth) outputWidth word)).wellFormed = true := by
  rw [gateCircuit, RCircuit.wellFormed]
  exact controlledXorGates_wellFormed
    (Or.inr (by simp [selectorWire, selectorOffset, outputOffset]))
    (by simp [selectorWire, selectorOffset, width_eq, hdepth]; omega)
    (by simp [outputOffset, width_eq]; omega)

theorem leafGates_act_at {table : List Nat} {addressWidth outputWidth row depth i : Nat} :
    actGates
        (controlledXorGates (selectorWire addressWidth outputWidth depth)
          (outputOffset addressWidth) outputWidth
          (Lookup.value table outputWidth row)) i =
      nodeTarget table addressWidth outputWidth row depth 0 i := by
  rw [controlledXorGates_act outputWidth (outputOffset addressWidth)
    (Lookup.value table outputWidth row) i
    (Or.inr (by simp [selectorWire, selectorOffset, outputOffset]))]
  rw [nodeTarget, readField_size_zero, Nat.add_zero]
  by_cases hs : i.testBit (selectorWire addressWidth outputWidth depth) = true
  · rw [if_pos hs]
    have hb : bitValue i (selectorWire addressWidth outputWidth depth) = 1 :=
      (testBit_eq_true_iff_bitValue_eq_one _ _).mp hs
    rw [hb, Nat.one_mul]
    rfl
  · rw [if_neg hs]
    have hb : bitValue i (selectorWire addressWidth outputWidth depth) = 0 := by
      rw [← testBit_eq_false_iff_bitValue_eq_zero]
      cases hbit : i.testBit (selectorWire addressWidth outputWidth depth) <;>
        simp_all
    rw [hb, Nat.zero_mul, Nat.xor_zero, writeField_read]

theorem leafGates_act {table : List Nat} {addressWidth outputWidth row depth i : Nat}
    (_hdepth : depth = addressWidth) :
    actGates
        (controlledXorGates (selectorWire addressWidth outputWidth depth)
          (outputOffset addressWidth) outputWidth
          (Lookup.value table outputWidth row)) i =
      nodeTarget table addressWidth outputWidth row depth 0 i :=
  leafGates_act_at

theorem nodeTarget_readField_of_disjoint
    (table : List Nat) (addressWidth outputWidth row depth remaining i off len : Nat)
    (hdis : outputOffset addressWidth + outputWidth ≤ off ∨
      off + len ≤ outputOffset addressWidth) :
    readField (nodeTarget table addressWidth outputWidth row depth remaining i) off len =
      readField i off len := by
  unfold nodeTarget
  split
  · rw [readField_writeField_of_disjoint hdis]
  · rfl

theorem nodeTarget_bitValue_of_ne
    (table : List Nat) (addressWidth outputWidth row depth remaining i q : Nat)
    (hq : q < outputOffset addressWidth ∨
      outputOffset addressWidth + outputWidth ≤ q) :
    bitValue (nodeTarget table addressWidth outputWidth row depth remaining i) q =
      bitValue i q := by
  unfold nodeTarget
  split
  · exact bitValue_write_out hq
  · rfl

theorem nodeTarget_lt {table : List Nat} {addressWidth outputWidth row depth remaining i : Nat}
    (hi : i < 2 ^ width addressWidth outputWidth) :
    nodeTarget table addressWidth outputWidth row depth remaining i <
      2 ^ width addressWidth outputWidth := by
  unfold nodeTarget
  split
  · exact writeField_lt (by simp [outputOffset, width_eq]; omega) hi
  · exact hi

theorem writeBit_false_eq_writeField (i q : Nat) :
    writeBit i q false = writeField i q 1 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b = q
  · subst b
    rw [testBit_writeBit, testBit_writeField_inside (Nat.le_refl _) (by omega)]
    simp
  · rw [testBit_writeBit_of_ne hb,
      testBit_writeField_outside (by omega)]

theorem nodePre_child_clear
    {addressWidth outputWidth depth remaining i : Nat}
    (hpre : nodePre addressWidth outputWidth depth (remaining + 1) i) :
    bitValue i (selectorWire addressWidth outputWidth (depth + 1)) = 0 := by
  rw [← readField_one]
  exact readField_sub_zero (Nat.le_refl _) (by omega) hpre

theorem nodePre_tail
    {addressWidth outputWidth depth remaining i : Nat}
    (hpre : nodePre addressWidth outputWidth depth (remaining + 1) i) :
    nodePre addressWidth outputWidth (depth + 1) remaining i := by
  apply readField_sub_zero
    (off := selectorWire addressWidth outputWidth (depth + 1))
    (len := remaining + 1)
  · simp [selectorWire]
  · simp only [selectorWire]
    omega
  · exact hpre

theorem nodePre_negativeAndOut_tail
    {addressWidth outputWidth depth remaining i : Nat}
    (hpre : nodePre addressWidth outputWidth depth (remaining + 1) i) :
    nodePre addressWidth outputWidth (depth + 1) remaining
      (negativeAndOut remaining
        (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1)) i) := by
  rw [nodePre, negativeAndOut,
    readField_writeField_of_disjoint (Or.inl (by
      simp only [selectorWire]
      omega))]
  exact nodePre_tail hpre

theorem nodePre_nodeTarget
    {table : List Nat} {addressWidth outputWidth row depth remaining i : Nat}
    (hpre : nodePre addressWidth outputWidth depth remaining i) :
    nodePre addressWidth outputWidth depth remaining
      (nodeTarget table addressWidth outputWidth row depth remaining i) := by
  rw [nodePre, nodeTarget_readField_of_disjoint]
  · exact hpre
  · left
    simp [selectorWire, selectorOffset, outputOffset]

private theorem nodeStep_eq_target
    {table : List Nat} {addressWidth outputWidth row depth remaining i : Nat}
    (haddress : remaining < addressWidth)
    (hpre : nodePre addressWidth outputWidth depth (remaining + 1) i) :
    let parent := selectorWire addressWidth outputWidth depth
    let child := selectorWire addressWidth outputWidth (depth + 1)
    let i₁ := negativeAndOut remaining parent child i
    let i₂ := nodeTarget table addressWidth outputWidth row (depth + 1) remaining i₁
    let i₃ := RGate.act (.cx parent child) i₂
    let i₄ := nodeTarget table addressWidth outputWidth (row + 2 ^ remaining)
      (depth + 1) remaining i₃
    writeBit i₄ child false =
      nodeTarget table addressWidth outputWidth row depth (remaining + 1) i := by
  dsimp only
  let parent := selectorWire addressWidth outputWidth depth
  let child := selectorWire addressWidth outputWidth (depth + 1)
  let i₁ := negativeAndOut remaining parent child i
  let i₂ := nodeTarget table addressWidth outputWidth row (depth + 1) remaining i₁
  let i₃ := RGate.act (.cx parent child) i₂
  let i₄ := nodeTarget table addressWidth outputWidth (row + 2 ^ remaining)
    (depth + 1) remaining i₃
  change writeBit i₄ child false = _
  have hchildValue := nodePre_child_clear hpre
  have hchild : i.testBit child = false :=
    (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr hchildValue
  have hparentChild : parent ≠ child := by simp [parent, child, selectorWire]
  have haddressChild : remaining ≠ child := by
    simp [child, selectorWire, selectorOffset]
    omega
  have houtputChild : outputOffset addressWidth + outputWidth ≤ child := by
    simp [child, selectorWire, selectorOffset, outputOffset]
  have houtputParent : outputOffset addressWidth + outputWidth ≤ parent := by
    simp [parent, selectorWire, selectorOffset, outputOffset]
  have haddressOutput : remaining < outputOffset addressWidth := by
    simp [outputOffset]
    exact haddress
  have hreadHigh := readField_high i 0 remaining
  simp only [Nat.zero_add] at hreadHigh
  cases hp : i.testBit parent with
  | false =>
      have hi₁ : i₁ = i := by
        dsimp only [i₁]
        rw [negativeAndOut, hchildValue]
        simp [bitValue, hp]
        exact write_of_bitValue (by simp [bitValue, hchild])
      have hi₂ : i₂ = i := by
        dsimp only [i₂]
        rw [hi₁, nodeTarget, if_neg (by simpa [child] using hchild)]
      have hi₃ : i₃ = i := by
        dsimp only [i₃]
        rw [hi₂]
        simp [RGate.act, hp]
      have hi₄ : i₄ = i := by
        dsimp only [i₄]
        rw [hi₃, nodeTarget, if_neg (by simpa [child] using hchild)]
      rw [hi₄, writeBit_self hchild]
      simp [nodeTarget, parent, hp]
  | true =>
      cases ha : i.testBit remaining with
      | false =>
          have hi₁ : i₁ = writeField i child 1 1 := by
            dsimp only [i₁]
            rw [negativeAndOut, hchildValue]
            simp [bitValue, hp, ha]
          have hi₁Child : i₁.testBit child = true := by
            rw [hi₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
            simp
          have hi₁Output : Lookup.output addressWidth outputWidth
              (selectorWidth addressWidth) i₁ =
              Lookup.output addressWidth outputWidth (selectorWidth addressWidth) i := by
            rw [hi₁]
            simpa [Lookup.output, Lookup.layout, Layout.read, Layout.offset,
              Layout.size, outputOffset] using
              (readField_writeField_of_disjoint (Or.inr houtputChild) :
                readField (writeField i child 1 1) addressWidth outputWidth =
                  readField i addressWidth outputWidth)
          have hi₁Address : readField i₁ 0 remaining = readField i 0 remaining := by
            rw [hi₁]
            exact readField_writeField_of_disjoint (Or.inr (by
              simp [child, selectorWire, selectorOffset]
              omega))
          let valueLeft := Lookup.output addressWidth outputWidth
              (selectorWidth addressWidth) i ^^^
            Lookup.value table outputWidth (row + readField i 0 remaining)
          have hi₂ : i₂ = writeField i₁ (outputOffset addressWidth)
              outputWidth valueLeft := by
            dsimp only [i₂]
            rw [nodeTarget, if_pos (by simpa [child] using hi₁Child),
              hi₁Output, hi₁Address]
          have hi₂Parent : i₂.testBit parent = true := by
            rw [hi₂, testBit_writeField_outside (Or.inr houtputParent), hi₁,
              testBit_writeField_outside (Or.inl (by
                simp [parent, child, selectorWire])), hp]
          have hi₂Child : bitValue i₂ child = 1 := by
            rw [← testBit_eq_true_iff_bitValue_eq_one, hi₂]
            exact testBit_writeField_outside (Or.inr houtputChild) |>.trans hi₁Child
          have hi₂ParentValue : bitValue i₂ parent = 1 :=
            (testBit_eq_true_iff_bitValue_eq_one _ _).mp hi₂Parent
          have hi₃ : i₃ = writeField i (outputOffset addressWidth)
              outputWidth valueLeft := by
            dsimp only [i₃]
            rw [act_cx_write, hi₂Child, hi₂ParentValue]
            simp
            rw [hi₂, hi₁,
              writeField_comm (Or.inr houtputChild), writeField_writeField]
            exact write_of_bitValue (by
              rw [bitValue_write_out (Or.inr houtputChild)]
              simp [bitValue, hchild])
          have hi₃Child : i₃.testBit child = false := by
            rw [hi₃, testBit_writeField_outside (Or.inr houtputChild), hchild]
          have hi₄ : i₄ = i₃ := by
            dsimp only [i₄]
            rw [nodeTarget, if_neg (by simpa [child] using hi₃Child)]
          rw [hi₄, writeBit_self hi₃Child, hi₃]
          rw [nodeTarget, if_pos (by simpa [parent] using hp), hreadHigh]
          have haddressValue : bitValue i remaining = 0 :=
            (testBit_eq_false_iff_bitValue_eq_zero _ _).mp ha
          rw [haddressValue, Nat.mul_zero, Nat.add_zero]
      | true =>
          have hi₁ : i₁ = i := by
            dsimp only [i₁]
            rw [negativeAndOut, hchildValue]
            simp [bitValue, hp, ha]
            exact write_of_bitValue (by simp [bitValue, hchild])
          have hi₂ : i₂ = i := by
            dsimp only [i₂]
            rw [hi₁, nodeTarget, if_neg (by simpa [child] using hchild)]
          have hi₃ : i₃ = writeField i child 1 1 := by
            dsimp only [i₃]
            rw [act_cx_write, hi₂]
            have hpv : bitValue i parent = 1 :=
              (testBit_eq_true_iff_bitValue_eq_one _ _).mp hp
            have hcv : bitValue i child = 0 :=
              (testBit_eq_false_iff_bitValue_eq_zero _ _).mp hchild
            rw [hpv, hcv]
          have hi₃Child : i₃.testBit child = true := by
            rw [hi₃, testBit_writeField_inside (Nat.le_refl _) (by omega)]
            simp
          have hi₃Output : Lookup.output addressWidth outputWidth
              (selectorWidth addressWidth) i₃ =
              Lookup.output addressWidth outputWidth (selectorWidth addressWidth) i := by
            rw [hi₃]
            simpa [Lookup.output, Lookup.layout, Layout.read, Layout.offset,
              Layout.size, outputOffset] using
              (readField_writeField_of_disjoint (Or.inr houtputChild) :
                readField (writeField i child 1 1) addressWidth outputWidth =
                  readField i addressWidth outputWidth)
          have hi₃Address : readField i₃ 0 remaining = readField i 0 remaining := by
            rw [hi₃]
            exact readField_writeField_of_disjoint (Or.inr (by
              simp [child, selectorWire, selectorOffset]
              omega))
          let valueRight := Lookup.output addressWidth outputWidth
              (selectorWidth addressWidth) i ^^^
            Lookup.value table outputWidth
              (row + 2 ^ remaining + readField i 0 remaining)
          have hi₄ : i₄ = writeField i₃ (outputOffset addressWidth)
              outputWidth valueRight := by
            dsimp only [i₄]
            rw [nodeTarget, if_pos (by simpa [child] using hi₃Child),
              hi₃Output, hi₃Address]
          rw [hi₄, writeBit_false_eq_writeField, hi₃,
            writeField_comm (Or.inr houtputChild), writeField_writeField]
          rw [show writeField
              (writeField i (outputOffset addressWidth) outputWidth valueRight)
              child 1 0 =
              writeField i (outputOffset addressWidth) outputWidth valueRight by
            exact write_of_bitValue (by
              rw [bitValue_write_out (Or.inr houtputChild)]
              simp [bitValue, hchild])]
          rw [nodeTarget, if_pos (by simpa [parent] using hp), hreadHigh]
          have haddressValue : bitValue i remaining = 1 :=
            (testBit_eq_true_iff_bitValue_eq_one _ _).mp ha
          rw [haddressValue, Nat.mul_one]
          dsimp only [valueRight]
          rw [show row + 2 ^ remaining + readField i 0 remaining =
              row + (readField i 0 remaining + 2 ^ remaining) by omega]

theorem nodeEval_eq_target_le
    (table : List Nat) (addressWidth outputWidth row depth : Nat) :
    ∀ remaining i, remaining ≤ addressWidth →
      nodePre addressWidth outputWidth depth remaining i →
      nodeEval table addressWidth outputWidth row depth remaining i =
        nodeTarget table addressWidth outputWidth row depth remaining i := by
  intro remaining
  induction remaining generalizing row depth with
  | zero =>
      intro i _ _
      rfl
  | succ remaining ih =>
      intro i haddress hpre
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      let i₁ := negativeAndOut remaining parent child i
      let i₂ := nodeEval table addressWidth outputWidth row (depth + 1) remaining i₁
      let i₃ := RGate.act (.cx parent child) i₂
      have hleftPre : nodePre addressWidth outputWidth (depth + 1) remaining i₁ := by
        simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre
      have hleft := ih (row := row) (depth := depth + 1) i₁ (by omega) hleftPre
      have hleftTargetPre : nodePre addressWidth outputWidth (depth + 1) remaining
          (nodeTarget table addressWidth outputWidth row (depth + 1) remaining i₁) :=
        nodePre_nodeTarget hleftPre
      have hrightPre : nodePre addressWidth outputWidth (depth + 1) remaining
          (RGate.act (.cx parent child)
            (nodeTarget table addressWidth outputWidth row (depth + 1) remaining i₁)) := by
        rw [act_cx_write, nodePre,
          readField_writeField_of_disjoint (Or.inl (by
            simp only [child, selectorWire]
            omega))]
        exact hleftTargetPre
      have hright := ih (row := row + 2 ^ remaining) (depth := depth + 1)
        (RGate.act (.cx parent child)
          (nodeTarget table addressWidth outputWidth row (depth + 1) remaining i₁))
        (by omega) hrightPre
      rw [nodeEval]
      change writeBit
        (nodeEval table addressWidth outputWidth (row + 2 ^ remaining)
          (depth + 1) remaining
          (RGate.act (.cx parent child)
            (nodeEval table addressWidth outputWidth row (depth + 1) remaining i₁)))
        child false = _
      rw [hleft, hright]
      exact nodeStep_eq_target (by omega) hpre

theorem nodeEval_eq_target
    (table : List Nat) (addressWidth outputWidth row depth : Nat)
    (remaining i : Nat) (hshape : depth + remaining = addressWidth)
    (hpre : nodePre addressWidth outputWidth depth remaining i) :
    nodeEval table addressWidth outputWidth row depth remaining i =
      nodeTarget table addressWidth outputWidth row depth remaining i :=
  nodeEval_eq_target_le table addressWidth outputWidth row depth remaining i (by omega) hpre

private theorem nodeBeforeUncompute_and
    {table : List Nat} {addressWidth outputWidth row depth remaining i : Nat}
    (haddress : remaining < addressWidth)
    (hpre : nodePre addressWidth outputWidth depth (remaining + 1) i) :
    let parent := selectorWire addressWidth outputWidth depth
    let child := selectorWire addressWidth outputWidth (depth + 1)
    let i₁ := negativeAndOut remaining parent child i
    let i₂ := nodeTarget table addressWidth outputWidth row (depth + 1) remaining i₁
    let i₃ := RGate.act (.cx parent child) i₂
    let i₄ := nodeTarget table addressWidth outputWidth (row + 2 ^ remaining)
      (depth + 1) remaining i₃
    i₄.testBit child = (i₄.testBit parent && i₄.testBit remaining) := by
  dsimp only
  let parent := selectorWire addressWidth outputWidth depth
  let child := selectorWire addressWidth outputWidth (depth + 1)
  let i₁ := negativeAndOut remaining parent child i
  let i₂ := nodeTarget table addressWidth outputWidth row (depth + 1) remaining i₁
  let i₃ := RGate.act (.cx parent child) i₂
  let i₄ := nodeTarget table addressWidth outputWidth (row + 2 ^ remaining)
    (depth + 1) remaining i₃
  change i₄.testBit child = (i₄.testBit parent && i₄.testBit remaining)
  have hchildValue := nodePre_child_clear hpre
  have hremainingChild : remaining ≠ child := by
    simp [child, selectorWire, selectorOffset]
    omega
  have hparentChild : parent ≠ child := by
    simp [parent, child, selectorWire]
  have hparentOutput : outputOffset addressWidth + outputWidth ≤ parent := by
    simp [parent, selectorWire, selectorOffset, outputOffset]
  have hchildOutput : outputOffset addressWidth + outputWidth ≤ child := by
    simp [child, selectorWire, selectorOffset, outputOffset]
  have hremainingOutput : remaining < outputOffset addressWidth := by
    simp [outputOffset]
    omega
  have hi₁Child : bitValue i₁ child =
      bitValue i parent * (if bitValue i remaining = 0 then 1 else 0) := by
    dsimp only [i₁]
    rw [negativeAndOut_child, hchildValue, Nat.zero_add]
    apply Nat.mod_eq_of_lt
    have hp := bitValue_lt i parent
    by_cases hz : bitValue i remaining = 0 <;> simp [hz] <;> omega
  have hi₁Parent : bitValue i₁ parent = bitValue i parent := by
    exact negativeAndOut_ne hparentChild
  have hi₁Remaining : bitValue i₁ remaining = bitValue i remaining := by
    exact negativeAndOut_ne hremainingChild
  have hi₂Child : bitValue i₂ child = bitValue i₁ child := by
    exact nodeTarget_bitValue_of_ne _ _ _ _ _ _ _ _ (Or.inr hchildOutput)
  have hi₂Parent : bitValue i₂ parent = bitValue i₁ parent := by
    exact nodeTarget_bitValue_of_ne _ _ _ _ _ _ _ _ (Or.inr hparentOutput)
  have hi₂Remaining : bitValue i₂ remaining = bitValue i₁ remaining := by
    exact nodeTarget_bitValue_of_ne _ _ _ _ _ _ _ _ (Or.inl hremainingOutput)
  have hi₃Child : bitValue i₃ child =
      (bitValue i₂ child + bitValue i₂ parent) % 2 := by
    dsimp only [i₃]
    rw [act_cx_write, bitValue_write_self, Nat.mod_mod]
  have hi₃Parent : bitValue i₃ parent = bitValue i₂ parent := by
    dsimp only [i₃]
    rw [act_cx_write]
    exact bitValue_write_ne hparentChild
  have hi₃Remaining : bitValue i₃ remaining = bitValue i₂ remaining := by
    dsimp only [i₃]
    rw [act_cx_write]
    exact bitValue_write_ne hremainingChild
  have hi₄Child : bitValue i₄ child = bitValue i₃ child := by
    exact nodeTarget_bitValue_of_ne _ _ _ _ _ _ _ _ (Or.inr hchildOutput)
  have hi₄Parent : bitValue i₄ parent = bitValue i₃ parent := by
    exact nodeTarget_bitValue_of_ne _ _ _ _ _ _ _ _ (Or.inr hparentOutput)
  have hi₄Remaining : bitValue i₄ remaining = bitValue i₃ remaining := by
    exact nodeTarget_bitValue_of_ne _ _ _ _ _ _ _ _ (Or.inl hremainingOutput)
  have hvalue : bitValue i₄ child = bitValue i₄ parent * bitValue i₄ remaining := by
    rw [hi₄Child, hi₃Child, hi₂Child, hi₁Child,
      hi₄Parent, hi₃Parent, hi₂Parent, hi₁Parent,
      hi₄Remaining, hi₃Remaining, hi₂Remaining, hi₁Remaining]
    have hp := bitValue_lt i parent
    have ha := bitValue_lt i remaining
    by_cases hz : bitValue i remaining = 0
    · rcases (by omega : bitValue i parent = 0 ∨ bitValue i parent = 1) with h | h <;>
        simp [hz, h]
    · have ho : bitValue i remaining = 1 := by omega
      rcases (by omega : bitValue i parent = 0 ∨ bitValue i parent = 1) with h | h <;>
        simp [ho, h]
  unfold bitValue at hvalue
  cases hc : i₄.testBit child <;>
    cases hp : i₄.testBit parent <;>
    cases ha : i₄.testBit remaining <;>
    simp_all

private theorem negativeAndOut_lt
    {addressWidth outputWidth depth remaining i : Nat}
    (hshape : depth + (remaining + 1) = addressWidth)
    (hi : i < 2 ^ width addressWidth outputWidth) :
    negativeAndOut remaining
        (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1)) i <
      2 ^ width addressWidth outputWidth := by
  rw [← negativeAndGates_act
    (show remaining ≠ selectorWire addressWidth outputWidth depth by
      simp [selectorWire, selectorOffset]; omega)
    (show remaining ≠ selectorWire addressWidth outputWidth (depth + 1) by
      simp [selectorWire, selectorOffset]; omega)
    (show selectorWire addressWidth outputWidth depth ≠
        selectorWire addressWidth outputWidth (depth + 1) by
      simp [selectorWire])]
  exact Reversible.act_lt (negativeAndGates_wellFormed hshape) hi

private theorem nodeEval_lt
    {table : List Nat} {addressWidth outputWidth row depth remaining i : Nat}
    (hshape : depth + remaining = addressWidth)
    (hi : i < 2 ^ width addressWidth outputWidth)
    (hpre : nodePre addressWidth outputWidth depth remaining i) :
    nodeEval table addressWidth outputWidth row depth remaining i <
      2 ^ width addressWidth outputWidth := by
  rw [nodeEval_eq_target table addressWidth outputWidth row depth remaining i hshape hpre]
  exact nodeTarget_lt hi

private theorem switchOut_lt
    {addressWidth outputWidth depth remaining i : Nat}
    (hshape : depth + (remaining + 1) = addressWidth)
    (hi : i < 2 ^ width addressWidth outputWidth) :
    actGates
        [.cx (selectorWire addressWidth outputWidth depth)
          (selectorWire addressWidth outputWidth (depth + 1))] i <
      2 ^ width addressWidth outputWidth := by
  exact Reversible.act_lt (switchGates_wellFormed hshape) hi

private theorem rootGate_wellFormed (addressWidth outputWidth : Nat) :
    (gateCircuit addressWidth outputWidth [.x (rootWire addressWidth outputWidth)]).wellFormed =
      true := by
  simp [gateCircuit, RCircuit.wellFormed, RGate.wellFormed, rootWire,
    selectorWire, selectorOffset, width_eq]
  omega

private theorem rootOut_lt
    {addressWidth outputWidth i : Nat}
    (hi : i < 2 ^ width addressWidth outputWidth) :
    RGate.act (.x (rootWire addressWidth outputWidth)) i <
      2 ^ width addressWidth outputWidth := by
  exact Reversible.act_lt (rootGate_wellFormed addressWidth outputWidth) hi

private theorem workspace_readField
    {addressWidth outputWidth i : Nat}
    (hclear : Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0) :
    readField i (selectorOffset addressWidth outputWidth) (selectorWidth addressWidth) = 0 := by
  simpa [Lookup.workspace, Lookup.layout, Layout.read, Layout.offset, Layout.size,
    selectorOffset] using hclear

private theorem workspace_root_zero
    {addressWidth outputWidth i : Nat}
    (hclear : Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0) :
    bitValue i (rootWire addressWidth outputWidth) = 0 := by
  rw [← readField_one]
  apply readField_sub_zero
    (off := selectorOffset addressWidth outputWidth)
    (len := selectorWidth addressWidth)
  · simp [rootWire, selectorWire]
  · simp [rootWire, selectorWire, selectorWidth]
  · exact workspace_readField hclear

private theorem rootOut_nodePre
    {addressWidth outputWidth i : Nat}
    (hclear : Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0) :
    nodePre addressWidth outputWidth 0 addressWidth
      (RGate.act (.x (rootWire addressWidth outputWidth)) i) := by
  have htail : readField i
      (selectorWire addressWidth outputWidth 1) addressWidth = 0 := by
    apply readField_sub_zero
      (off := selectorOffset addressWidth outputWidth)
      (len := selectorWidth addressWidth)
    · simp [selectorWire]
    · simp [selectorWire, selectorWidth]
      omega
    · exact workspace_readField hclear
  rw [nodePre, act_x_write,
    readField_writeField_of_disjoint (Or.inl (by
      simp [rootWire, selectorWire]))]
  exact htail

private theorem lookupEval_eq_xorOutput
    {table : List Nat} {addressWidth outputWidth i : Nat}
    (hclear : Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0) :
    lookupEval table addressWidth outputWidth i =
      Lookup.xorOutput table addressWidth outputWidth (selectorWidth addressWidth) i := by
  let root := rootWire addressWidth outputWidth
  let j := RGate.act (.x root) i
  have hrootZero : bitValue i root = 0 := by
    simpa [root] using workspace_root_zero hclear
  have hj : j = writeField i root 1 1 := by
    dsimp only [j]
    rw [act_x_write, hrootZero]
  have hjRoot : j.testBit root = true := by
    rw [hj, testBit_writeField_inside (Nat.le_refl _) (by omega)]
    simp
  have hjOutput : Lookup.output addressWidth outputWidth (selectorWidth addressWidth) j =
      Lookup.output addressWidth outputWidth (selectorWidth addressWidth) i := by
    unfold Lookup.output
    rw [hj, Lookup.layout, Layout.read,
      readField_writeField_of_disjoint (Or.inr (by
        simp [root, rootWire, selectorWire, selectorOffset, Layout.offset, Layout.size]))]
    rfl
  have hjAddress : readField j 0 addressWidth =
      Lookup.address addressWidth outputWidth (selectorWidth addressWidth) i := by
    rw [hj, readField_writeField_of_disjoint (Or.inr (by
      simp [root, rootWire, selectorWire, selectorOffset]))]
    rfl
  have hpre : nodePre addressWidth outputWidth 0 addressWidth j := by
    simpa [j, root] using rootOut_nodePre hclear
  have heval := nodeEval_eq_target table addressWidth outputWidth 0 0 addressWidth j
    (by omega) hpre
  rw [lookupEval]
  change RGate.act (.x root)
    (nodeEval table addressWidth outputWidth 0 0 addressWidth j) = _
  rw [heval, nodeTarget, if_pos (by simpa [root, rootWire] using hjRoot),
    Nat.zero_add, hjOutput, hjAddress, act_x_write]
  have hnodeRoot : bitValue
      (writeField j (outputOffset addressWidth) outputWidth
        (Lookup.output addressWidth outputWidth (selectorWidth addressWidth) i ^^^
          Lookup.value table outputWidth
            (Lookup.address addressWidth outputWidth (selectorWidth addressWidth) i))) root = 1 := by
    rw [bitValue_write_out (Or.inr (by
      simp [root, rootWire, selectorWire, selectorOffset, outputOffset]))]
    exact (testBit_eq_true_iff_bitValue_eq_one _ _).mp hjRoot
  rw [hnodeRoot]
  simp
  rw [writeField_comm (Or.inl (by
      simp [root, rootWire, selectorWire, selectorOffset, outputOffset])),
    hj, writeField_writeField]
  rw [show writeField i root 1 0 = i by
    exact write_of_bitValue (by simpa using hrootZero.symm)]
  rfl

theorem nodeOps_implements {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth row depth : Nat) :
    ∀ remaining, depth + remaining = addressWidth →
    ImplementsU level (width addressWidth outputWidth) input
      (nodePre addressWidth outputWidth depth remaining)
      (nodeEval table addressWidth outputWidth row depth remaining)
      (Dy.invSqrt2 (deg level))
      (nodeOps table addressWidth outputWidth row depth remaining) := by
  intro remaining
  induction remaining generalizing row depth with
  | zero =>
      intro hshape
      have hdepth : depth = addressWidth := by omega
      have h := gateOps_implements (input := input) (addressWidth := addressWidth)
        (outputWidth := outputWidth) hl
        (leafGates_wellFormed (outputWidth := outputWidth) (depth := depth) hdepth
          (Lookup.value table outputWidth row))
        (Dy.invSqrt2 (deg level))
      intro i hi _ rec cr b hb
      simp only [nodeOps, leafOps] at hb
      have hs := h i hi trivial rec cr b hb
      rw [leafGates_act (table := table) (addressWidth := addressWidth)
        (outputWidth := outputWidth) (row := row) (depth := depth) hdepth] at hs
      simpa [nodeEval] using hs
  | succ remaining ih =>
      intro hshape
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      let i₁ := fun i => negativeAndOut remaining parent child i
      let i₂ := fun i => nodeEval table addressWidth outputWidth row
        (depth + 1) remaining (i₁ i)
      let i₃ := fun i => RGate.act (.cx parent child) (i₂ i)
      let i₄ := fun i => nodeEval table addressWidth outputWidth
        (row + 2 ^ remaining) (depth + 1) remaining (i₃ i)
      have hnegAll := gateOps_implements (input := input) (addressWidth := addressWidth)
        (outputWidth := outputWidth) hl
        (negativeAndGates_wellFormed (outputWidth := outputWidth) hshape)
        (Dy.invSqrt2 (deg level))
      have hneg : ImplementsU level (width addressWidth outputWidth) input
          (nodePre addressWidth outputWidth depth (remaining + 1))
          (negativeAndOut remaining
            (selectorWire addressWidth outputWidth depth)
            (selectorWire addressWidth outputWidth (depth + 1)))
          (Dy.invSqrt2 (deg level))
          (gateOps (negativeAndGates remaining
            (selectorWire addressWidth outputWidth depth)
            (selectorWire addressWidth outputWidth (depth + 1)))) := by
        intro i hi _ rec cr b hb
        have hs := hnegAll i hi trivial rec cr b hb
        rw [negativeAndGates_act
          (show remaining ≠ selectorWire addressWidth outputWidth depth by
            simp [selectorWire, selectorOffset]; omega)
          (show remaining ≠ selectorWire addressWidth outputWidth (depth + 1) by
            simp [selectorWire, selectorOffset]; omega)
          (show selectorWire addressWidth outputWidth depth ≠
              selectorWire addressWidth outputWidth (depth + 1) by
            simp [selectorWire])] at hs
        exact hs
      have hleft := ih (row := row) (depth := depth + 1) (by omega)
      have hnegLeft := hneg.append hleft
        (fun i hi _ => by
          simpa [i₁, parent, child] using negativeAndOut_lt hshape hi)
        (fun _ _ hpre => by
          simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre)
      have hswitch := gateOps_implements (input := input) (addressWidth := addressWidth)
        (outputWidth := outputWidth) hl
        (switchGates_wellFormed (outputWidth := outputWidth) hshape)
        (Dy.invSqrt2 (deg level))
      have hthroughSwitch := hnegLeft.append hswitch
        (fun i hi hpre => by
          have hpre₁ : nodePre addressWidth outputWidth (depth + 1) remaining (i₁ i) := by
            simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre
          simpa [i₂] using nodeEval_lt (by omega) (negativeAndOut_lt hshape hi) hpre₁)
        (fun _ _ _ => trivial)
      have hright := ih (row := row + 2 ^ remaining) (depth := depth + 1) (by omega)
      have hthroughRight := hthroughSwitch.append hright
        (fun i hi hpre => by
          have hpre₁ : nodePre addressWidth outputWidth (depth + 1) remaining (i₁ i) := by
            simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre
          have hi₂ := nodeEval_lt (table := table) (row := row) (by omega)
            (negativeAndOut_lt hshape hi) hpre₁
          simpa [i₂, i₃, actGates] using switchOut_lt hshape hi₂)
        (fun i _ hpre => by
          have hpre₁ : nodePre addressWidth outputWidth (depth + 1) remaining (i₁ i) := by
            simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre
          have htargetPre : nodePre addressWidth outputWidth (depth + 1) remaining
              (nodeTarget table addressWidth outputWidth row (depth + 1) remaining (i₁ i)) :=
            nodePre_nodeTarget hpre₁
          have heval := nodeEval_eq_target table addressWidth outputWidth row
            (depth + 1) remaining (i₁ i) (by omega) hpre₁
          rw [nodePre]
          simp only [actGates_cons, actGates_nil]
          rw [act_cx_write,
            readField_writeField_of_disjoint (Or.inl (by
              simp only [selectorWire]
              omega)), heval]
          exact htargetPre)
      have herase := implementsU_andUncomputeClean (input := input)
        (w := width addressWidth outputWidth) hl
        (a := parent) (b := remaining) (c := child) (m := 0)
        (by simp [parent, selectorWire, selectorOffset, width_eq]; omega)
        (by simp [width_eq]; omega)
        (by simp [child, selectorWire, selectorOffset, width_eq]; omega)
        (by simp [parent, selectorWire, selectorOffset]; omega)
        (by simp [parent, child, selectorWire])
        (by simp [child, selectorWire, selectorOffset]; omega)
      have hall := hthroughRight.append herase
        (fun i hi hpre => by
          have hpre₁ : nodePre addressWidth outputWidth (depth + 1) remaining (i₁ i) := by
            simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre
          have hi₁ : i₁ i < 2 ^ width addressWidth outputWidth := by
            simpa [i₁, parent, child] using negativeAndOut_lt hshape hi
          have hi₂ : i₂ i < 2 ^ width addressWidth outputWidth := by
            exact nodeEval_lt (by omega) hi₁ hpre₁
          have hi₃ : i₃ i < 2 ^ width addressWidth outputWidth := by
            simpa [i₂, i₃, actGates] using switchOut_lt hshape hi₂
          have hrightPre : nodePre addressWidth outputWidth (depth + 1) remaining (i₃ i) := by
            have htargetPre : nodePre addressWidth outputWidth (depth + 1) remaining
                (nodeTarget table addressWidth outputWidth row (depth + 1) remaining (i₁ i)) :=
              nodePre_nodeTarget hpre₁
            have heval := nodeEval_eq_target table addressWidth outputWidth row
              (depth + 1) remaining (i₁ i) (by omega) hpre₁
            rw [nodePre]
            simp only [i₃, i₂]
            rw [act_cx_write,
              readField_writeField_of_disjoint (Or.inl (by
                simp only [child, selectorWire]
                omega)), heval]
            exact htargetPre
          exact nodeEval_lt (by omega) hi₃ hrightPre)
        (fun i _ hpre => by
          have heqLeft := nodeEval_eq_target table addressWidth outputWidth row
            (depth + 1) remaining (i₁ i) (by omega)
            (by simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre)
          have hrightPre : nodePre addressWidth outputWidth (depth + 1) remaining (i₃ i) := by
            have hpre₁ : nodePre addressWidth outputWidth (depth + 1) remaining (i₁ i) := by
              simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre
            have htargetPre : nodePre addressWidth outputWidth (depth + 1) remaining
                (nodeTarget table addressWidth outputWidth row (depth + 1) remaining (i₁ i)) :=
              nodePre_nodeTarget hpre₁
            rw [nodePre]
            simp only [i₃, i₂]
            rw [act_cx_write,
              readField_writeField_of_disjoint (Or.inl (by
                simp only [child, selectorWire]
                omega)), heqLeft]
            exact htargetPre
          have heqRight := nodeEval_eq_target table addressWidth outputWidth
            (row + 2 ^ remaining) (depth + 1) remaining (i₃ i) (by omega) hrightPre
          change (i₄ i).testBit child =
            ((i₄ i).testBit parent && (i₄ i).testBit remaining)
          simp only [i₄]
          rw [heqRight]
          simp only [i₃, i₂]
          rw [heqLeft]
          simpa [i₁, parent, child]
            using nodeBeforeUncompute_and (table := table) (row := row) (by omega) hpre)
      simpa [nodeOps, nodeEval, i₁, i₂, i₃, i₄, parent, child,
        actGates, List.append_assoc, Function.comp_def] using hall

theorem lookup_implements {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    ImplementsU level (width addressWidth outputWidth) input
      (fun i => Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0)
      (Lookup.xorOutput table addressWidth outputWidth (selectorWidth addressWidth))
      (Dy.invSqrt2 (deg level))
      (lookupOps table addressWidth outputWidth) := by
  have hrootAll := gateOps_implements (input := input)
    (addressWidth := addressWidth) (outputWidth := outputWidth) hl
    (rootGate_wellFormed addressWidth outputWidth) (Dy.invSqrt2 (deg level))
  have hroot : ImplementsU level (width addressWidth outputWidth) input
      (fun _ => True) (fun i => RGate.act (.x (rootWire addressWidth outputWidth)) i)
      (Dy.invSqrt2 (deg level))
      (gateOps [.x (rootWire addressWidth outputWidth)]) := by
    simpa [actGates] using hrootAll
  have hstart := hroot.mono
    (dom' := fun i =>
      Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0)
    (fun _ _ => trivial)
  have hnode := nodeOps_implements (input := input) hl table addressWidth outputWidth 0 0
    addressWidth (by omega)
  have hthroughNode := hstart.append hnode
    (fun _ hi _ => rootOut_lt hi)
    (fun _ _ hclear => rootOut_nodePre hclear)
  have hall := hthroughNode.append hroot
    (fun i hi hclear =>
      nodeEval_lt (table := table) (row := 0) (depth := 0) (remaining := addressWidth)
        (by omega) (rootOut_lt hi) (rootOut_nodePre hclear))
    (fun _ _ _ => trivial)
  have heval : ImplementsU level (width addressWidth outputWidth) input
      (fun i => Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0)
      (lookupEval table addressWidth outputWidth)
      (Dy.invSqrt2 (deg level)) (lookupOps table addressWidth outputWidth) := by
    change ImplementsU level (width addressWidth outputWidth) input
      (fun i => Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0)
      (lookupEval table addressWidth outputWidth) (Dy.invSqrt2 (deg level))
      (gateOps [.x (rootWire addressWidth outputWidth)] ++
        (nodeOps table addressWidth outputWidth 0 0 addressWidth ++
          gateOps [.x (rootWire addressWidth outputWidth)])) at hall
    simpa [lookupOps, rootWire, List.append_assoc] using hall
  intro i hi hclear rec cr b hb
  have hs := heval i hi hclear rec cr b hb
  rw [lookupEval_eq_xorOutput hclear] at hs
  exact hs

private theorem gateOps_implements_width {level input w : Nat}
    (hl : 3 ≤ level) {gates : List RGate}
    (hwf : ({ width := w, gates := gates } : RCircuit).wellFormed = true)
    (c : Dy (deg level)) :
    ImplementsU level w input (fun _ => True) (actGates gates) c (gateOps gates) := by
  have h := implementsU_gates hl (input := input)
    (r := ({ width := w, gates := gates } : RCircuit)) rfl hwf c
  change ImplementsU level w input (fun _ => True) (actGates gates) c
    ((gates.flatMap compileGate).map Op.gate) at h
  exact h

private theorem negativeAndGates_wellFormed_width
    {addressWidth outputWidth selectorCount depth remaining : Nat}
    (haddress : remaining < addressWidth) (hchild : depth + 1 < selectorCount) :
    ({ width := (Lookup.layout addressWidth outputWidth selectorCount).width,
       gates := negativeAndGates remaining
        (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1)) } : RCircuit).wellFormed = true := by
  simp [RCircuit.wellFormed, negativeAndGates, RGate.wellFormed, Lookup.layout,
    Layout.width, selectorWire, selectorOffset]
  omega

private theorem switchGates_wellFormed_width
    {addressWidth outputWidth selectorCount depth : Nat}
    (hchild : depth + 1 < selectorCount) :
    ({ width := (Lookup.layout addressWidth outputWidth selectorCount).width,
       gates := [.cx (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1))] } : RCircuit).wellFormed = true := by
  simp [RCircuit.wellFormed, RGate.wellFormed, Lookup.layout, Layout.width,
    selectorWire, selectorOffset]
  omega

private theorem leafGates_wellFormed_width
    {addressWidth outputWidth selectorCount depth word : Nat}
    (hselector : depth < selectorCount) :
    ({ width := (Lookup.layout addressWidth outputWidth selectorCount).width,
       gates := controlledXorGates (selectorWire addressWidth outputWidth depth)
        (outputOffset addressWidth) outputWidth word } : RCircuit).wellFormed = true := by
  rw [RCircuit.wellFormed]
  exact controlledXorGates_wellFormed
    (Or.inr (by simp [selectorWire, selectorOffset, outputOffset]))
    (by simp [selectorWire, selectorOffset, Lookup.layout, Layout.width]; omega)
    (by simp [outputOffset, Lookup.layout, Layout.width])

private theorem nodeTarget_lt_width
    {table : List Nat} {addressWidth outputWidth selectorCount row depth remaining i : Nat}
    (hi : i < 2 ^ (Lookup.layout addressWidth outputWidth selectorCount).width) :
    nodeTarget table addressWidth outputWidth row depth remaining i <
      2 ^ (Lookup.layout addressWidth outputWidth selectorCount).width := by
  unfold nodeTarget
  split
  · exact writeField_lt (by simp [outputOffset, Lookup.layout, Layout.width]) hi
  · exact hi

private theorem negativeAndOut_lt_width
    {addressWidth outputWidth selectorCount depth remaining i : Nat}
    (haddress : remaining < addressWidth) (hchild : depth + 1 < selectorCount)
    (hi : i < 2 ^ (Lookup.layout addressWidth outputWidth selectorCount).width) :
    negativeAndOut remaining
        (selectorWire addressWidth outputWidth depth)
        (selectorWire addressWidth outputWidth (depth + 1)) i <
      2 ^ (Lookup.layout addressWidth outputWidth selectorCount).width := by
  rw [← negativeAndGates_act
    (show remaining ≠ selectorWire addressWidth outputWidth depth by
      simp [selectorWire, selectorOffset]; omega)
    (show remaining ≠ selectorWire addressWidth outputWidth (depth + 1) by
      simp [selectorWire, selectorOffset]; omega)
    (show selectorWire addressWidth outputWidth depth ≠
        selectorWire addressWidth outputWidth (depth + 1) by
      simp [selectorWire])]
  exact Reversible.act_lt (negativeAndGates_wellFormed_width haddress hchild) hi

private theorem switchOut_lt_width
    {addressWidth outputWidth selectorCount depth i : Nat}
    (hchild : depth + 1 < selectorCount)
    (hi : i < 2 ^ (Lookup.layout addressWidth outputWidth selectorCount).width) :
    actGates [.cx (selectorWire addressWidth outputWidth depth)
      (selectorWire addressWidth outputWidth (depth + 1))] i <
      2 ^ (Lookup.layout addressWidth outputWidth selectorCount).width := by
  exact Reversible.act_lt (switchGates_wellFormed_width hchild) hi

private theorem nodeEval_lt_width
    {table : List Nat} {addressWidth outputWidth selectorCount row depth remaining i : Nat}
    (haddress : remaining ≤ addressWidth)
    (hi : i < 2 ^ (Lookup.layout addressWidth outputWidth selectorCount).width)
    (hpre : nodePre addressWidth outputWidth depth remaining i) :
    nodeEval table addressWidth outputWidth row depth remaining i <
      2 ^ (Lookup.layout addressWidth outputWidth selectorCount).width := by
  rw [nodeEval_eq_target_le table addressWidth outputWidth row depth remaining i haddress hpre]
  exact nodeTarget_lt_width hi

private theorem nodeOps_implements_width {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth selectorCount row depth : Nat) :
    ∀ remaining, remaining ≤ addressWidth → depth + remaining < selectorCount →
    ImplementsU level (Lookup.layout addressWidth outputWidth selectorCount).width input
      (nodePre addressWidth outputWidth depth remaining)
      (nodeEval table addressWidth outputWidth row depth remaining)
      (Dy.invSqrt2 (deg level))
      (nodeOps table addressWidth outputWidth row depth remaining) := by
  intro remaining
  induction remaining generalizing row depth with
  | zero =>
      intro _ hselector
      have h := gateOps_implements_width (input := input)
        (w := (Lookup.layout addressWidth outputWidth selectorCount).width) hl
        (leafGates_wellFormed_width (addressWidth := addressWidth)
          (outputWidth := outputWidth) (depth := depth)
          (word := Lookup.value table outputWidth row)
          (by omega)) (Dy.invSqrt2 (deg level))
      intro i hi _ rec cr b hb
      simp only [nodeOps, leafOps] at hb
      have hs := h i hi trivial rec cr b hb
      rw [leafGates_act_at (table := table) (addressWidth := addressWidth)
        (outputWidth := outputWidth) (row := row) (depth := depth)] at hs
      simpa [nodeEval] using hs
  | succ remaining ih =>
      intro haddress hselector
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      let i₁ := fun i => negativeAndOut remaining parent child i
      let i₂ := fun i => nodeEval table addressWidth outputWidth row
        (depth + 1) remaining (i₁ i)
      let i₃ := fun i => RGate.act (.cx parent child) (i₂ i)
      let i₄ := fun i => nodeEval table addressWidth outputWidth
        (row + 2 ^ remaining) (depth + 1) remaining (i₃ i)
      have hbit : remaining < addressWidth := by omega
      have hchild : depth + 1 < selectorCount := by omega
      have hnegAll := gateOps_implements_width (input := input)
        (w := (Lookup.layout addressWidth outputWidth selectorCount).width) hl
        (negativeAndGates_wellFormed_width (outputWidth := outputWidth) hbit hchild)
        (Dy.invSqrt2 (deg level))
      have hneg : ImplementsU level
          (Lookup.layout addressWidth outputWidth selectorCount).width input
          (nodePre addressWidth outputWidth depth (remaining + 1))
          (negativeAndOut remaining
            (selectorWire addressWidth outputWidth depth)
            (selectorWire addressWidth outputWidth (depth + 1)))
          (Dy.invSqrt2 (deg level))
          (gateOps (negativeAndGates remaining
            (selectorWire addressWidth outputWidth depth)
            (selectorWire addressWidth outputWidth (depth + 1)))) := by
        intro i hi _ rec cr b hb
        have hs := hnegAll i hi trivial rec cr b hb
        rw [negativeAndGates_act
          (show remaining ≠ selectorWire addressWidth outputWidth depth by
            simp [selectorWire, selectorOffset]; omega)
          (show remaining ≠ selectorWire addressWidth outputWidth (depth + 1) by
            simp [selectorWire, selectorOffset]; omega)
          (show selectorWire addressWidth outputWidth depth ≠
              selectorWire addressWidth outputWidth (depth + 1) by
            simp [selectorWire])] at hs
        exact hs
      have hleft := ih (row := row) (depth := depth + 1) (by omega) (by omega)
      have hnegLeft := hneg.append hleft
        (fun i hi _ => by
          simpa [i₁, parent, child] using
            negativeAndOut_lt_width hbit hchild hi)
        (fun _ _ hpre => by
          simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre)
      have hswitch := gateOps_implements_width (input := input)
        (w := (Lookup.layout addressWidth outputWidth selectorCount).width) hl
        (switchGates_wellFormed_width (addressWidth := addressWidth)
          (outputWidth := outputWidth) hchild) (Dy.invSqrt2 (deg level))
      have hthroughSwitch := hnegLeft.append hswitch
        (fun i hi hpre => by
          have hpre₁ : nodePre addressWidth outputWidth (depth + 1) remaining (i₁ i) := by
            simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre
          simpa [i₂] using nodeEval_lt_width (by omega)
            (negativeAndOut_lt_width hbit hchild hi) hpre₁)
        (fun _ _ _ => trivial)
      have hright := ih (row := row + 2 ^ remaining) (depth := depth + 1)
        (by omega) (by omega)
      have hthroughRight := hthroughSwitch.append hright
        (fun i hi hpre => by
          have hpre₁ : nodePre addressWidth outputWidth (depth + 1) remaining (i₁ i) := by
            simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre
          have hi₂ := nodeEval_lt_width (table := table) (row := row) (by omega)
            (negativeAndOut_lt_width hbit hchild hi) hpre₁
          simpa [i₂, i₃, actGates] using switchOut_lt_width hchild hi₂)
        (fun i _ hpre => by
          have hpre₁ : nodePre addressWidth outputWidth (depth + 1) remaining (i₁ i) := by
            simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre
          have htargetPre : nodePre addressWidth outputWidth (depth + 1) remaining
              (nodeTarget table addressWidth outputWidth row (depth + 1) remaining (i₁ i)) :=
            nodePre_nodeTarget hpre₁
          have heval := nodeEval_eq_target_le table addressWidth outputWidth row
            (depth + 1) remaining (i₁ i) (by omega) hpre₁
          rw [nodePre]
          simp only [actGates_cons, actGates_nil]
          rw [act_cx_write,
            readField_writeField_of_disjoint (Or.inl (by
              simp only [selectorWire]
              omega)), heval]
          exact htargetPre)
      have herase := implementsU_andUncomputeClean (input := input)
        (w := (Lookup.layout addressWidth outputWidth selectorCount).width) hl
        (a := parent) (b := remaining) (c := child) (m := 0)
        (by simp [parent, selectorWire, selectorOffset, Lookup.layout, Layout.width]; omega)
        (by simp [Lookup.layout, Layout.width]; omega)
        (by simp [child, selectorWire, selectorOffset, Lookup.layout, Layout.width]; omega)
        (by simp [parent, selectorWire, selectorOffset]; omega)
        (by simp [parent, child, selectorWire])
        (by simp [child, selectorWire, selectorOffset]; omega)
      have hall := hthroughRight.append herase
        (fun i hi hpre => by
          have hpre₁ : nodePre addressWidth outputWidth (depth + 1) remaining (i₁ i) := by
            simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre
          have hi₁ : i₁ i <
              2 ^ (Lookup.layout addressWidth outputWidth selectorCount).width := by
            simpa [i₁, parent, child] using negativeAndOut_lt_width hbit hchild hi
          have hi₂ : i₂ i <
              2 ^ (Lookup.layout addressWidth outputWidth selectorCount).width := by
            exact nodeEval_lt_width (by omega) hi₁ hpre₁
          have hi₃ : i₃ i <
              2 ^ (Lookup.layout addressWidth outputWidth selectorCount).width := by
            simpa [i₂, i₃, actGates] using switchOut_lt_width hchild hi₂
          have hrightPre : nodePre addressWidth outputWidth (depth + 1) remaining (i₃ i) := by
            have htargetPre : nodePre addressWidth outputWidth (depth + 1) remaining
                (nodeTarget table addressWidth outputWidth row (depth + 1) remaining (i₁ i)) :=
              nodePre_nodeTarget hpre₁
            have heval := nodeEval_eq_target_le table addressWidth outputWidth row
              (depth + 1) remaining (i₁ i) (by omega) hpre₁
            rw [nodePre]
            simp only [i₃, i₂]
            rw [act_cx_write,
              readField_writeField_of_disjoint (Or.inl (by
                simp only [child, selectorWire]
                omega)), heval]
            exact htargetPre
          exact nodeEval_lt_width (by omega) hi₃ hrightPre)
        (fun i _ hpre => by
          have heqLeft := nodeEval_eq_target_le table addressWidth outputWidth row
            (depth + 1) remaining (i₁ i) (by omega)
            (by simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre)
          have hrightPre : nodePre addressWidth outputWidth (depth + 1) remaining (i₃ i) := by
            have hpre₁ : nodePre addressWidth outputWidth (depth + 1) remaining (i₁ i) := by
              simpa [i₁, parent, child] using nodePre_negativeAndOut_tail hpre
            have htargetPre : nodePre addressWidth outputWidth (depth + 1) remaining
                (nodeTarget table addressWidth outputWidth row (depth + 1) remaining (i₁ i)) :=
              nodePre_nodeTarget hpre₁
            rw [nodePre]
            simp only [i₃, i₂]
            rw [act_cx_write,
              readField_writeField_of_disjoint (Or.inl (by
                simp only [child, selectorWire]
                omega)), heqLeft]
            exact htargetPre
          have heqRight := nodeEval_eq_target_le table addressWidth outputWidth
            (row + 2 ^ remaining) (depth + 1) remaining (i₃ i) (by omega) hrightPre
          change (i₄ i).testBit child =
            ((i₄ i).testBit parent && (i₄ i).testBit remaining)
          simp only [i₄]
          rw [heqRight]
          simp only [i₃, i₂]
          rw [heqLeft]
          simpa [i₁, parent, child]
            using nodeBeforeUncompute_and (table := table) (row := row) hbit hpre)
      simpa [nodeOps, nodeEval, i₁, i₂, i₃, i₄, parent, child,
        actGates, List.append_assoc, Function.comp_def] using hall

theorem gateOps_toffoli (gates : List RGate) :
    Program.weighOps (fun g ↦ if g.isCcz then 1 else 0) (gateOps gates) =
      Range.point (gates.countP RGate.isCcx) := by
  rw [gateOps, Program.weighOps_gateMap_countP]
  apply congrArg Range.point
  have h := toffoliCount_compile ({ width := 0, gates := gates } : RCircuit)
  change (gates.flatMap compileGate).countP Gate.isCcz =
    gates.countP RGate.isCcx at h
  exact h

theorem negativeAndGates_ccx (address parent child : Nat) :
    (negativeAndGates address parent child).countP RGate.isCcx = 1 := by
  rfl

theorem andUncomputeClean_toffoli (a b c m : Nat) :
    Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
      (andUncomputeClean a b c m) = Range.point 0 := by
  simp [andUncomputeClean, andUncompute, Circuit.cz, Program.weighOps,
    Program.weighOp, Range.add, Range.choice, Range.point, Gate.isCcz]

theorem nodeOps_toffoli (table : List Nat) (addressWidth outputWidth row depth : Nat) :
    ∀ remaining,
      Program.weighOps (fun g ↦ if g.isCcz then 1 else 0)
        (nodeOps table addressWidth outputWidth row depth remaining) =
          Range.point (2 ^ remaining - 1) := by
  intro remaining
  induction remaining generalizing row depth with
  | zero =>
      simp [nodeOps, leafOps, gateOps_toffoli, controlledXorGates_ccx]
  | succ remaining ih =>
      rw [nodeOps]
      have hpow := Nat.two_pow_pos remaining
      simp only [Program.weighOps_append, gateOps_toffoli,
        negativeAndGates_ccx, ih, andUncomputeClean_toffoli]
      simp [Range.add, Range.point, Nat.pow_succ, RGate.isCcx]
      omega

theorem lookup_toffoliCount (table : List Nat) (addressWidth outputWidth : Nat) :
    (lookupProgram table addressWidth outputWidth).toffoliCount =
      Range.point (2 ^ addressWidth - 1) := by
  simp only [Program.toffoliCount, lookupProgram, lookupOps,
    Program.weighOps_append, gateOps_toffoli, nodeOps_toffoli]
  simp [Range.add, Range.point, RGate.isCcx]

private theorem opsWellFormed_gateMap (level w iw cw : Nat) (gates : List Gate) :
    Program.opsWellFormed level w iw cw (gates.map Op.gate) =
      gates.all (Gate.wellFormedAt level w) := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
      simp [Program.opsWellFormed, Program.opWellFormed, ih]

theorem gateOps_wellFormed {level addressWidth outputWidth iw cw : Nat}
    (hl : 3 ≤ level) {gates : List RGate}
    (hwf : (gateCircuit addressWidth outputWidth gates).wellFormed = true) :
    Program.opsWellFormed level (width addressWidth outputWidth) iw cw
      (gateOps gates) = true := by
  rw [gateOps, opsWellFormed_gateMap]
  change (compile (gateCircuit addressWidth outputWidth gates)).wellFormedAt level = true
  exact wellFormedAt_compile (RCircuit.wellFormedAt_of_wellFormed hl hwf)

private theorem gateOps_wellFormed_width {level w iw cw : Nat}
    (hl : 3 ≤ level) {gates : List RGate}
    (hwf : ({ width := w, gates := gates } : RCircuit).wellFormed = true) :
    Program.opsWellFormed level w iw cw (gateOps gates) = true := by
  rw [gateOps, opsWellFormed_gateMap]
  change (compile ({ width := w, gates := gates } : RCircuit)).wellFormedAt level = true
  exact wellFormedAt_compile (RCircuit.wellFormedAt_of_wellFormed hl hwf)

private theorem andUncomputeClean_wellFormed
    {level w iw cw a b c m : Nat} (hl : 3 ≤ level)
    (haw : a < w) (hbw : b < w) (hcw : c < w)
    (hm : m < cw) (hab : a ≠ b) :
    Program.opsWellFormed level w iw cw (andUncomputeClean a b c m) = true := by
  simp [andUncomputeClean, andUncompute, Circuit.cz, Program.opsWellFormed,
    Program.opWellFormed, CRef.wellFormed, Gate.wellFormedAt, hl, haw, hbw, hcw,
    hm, hab]

theorem nodeOps_wellFormed {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth row depth : Nat) :
    ∀ remaining, depth + remaining = addressWidth →
      Program.opsWellFormed level (width addressWidth outputWidth) 0
        (if addressWidth = 0 then 0 else 1)
        (nodeOps table addressWidth outputWidth row depth remaining) = true := by
  intro remaining
  induction remaining generalizing row depth with
  | zero =>
      intro hshape
      have hdepth : depth = addressWidth := by omega
      exact gateOps_wellFormed hl
        (leafGates_wellFormed (outputWidth := outputWidth) (depth := depth) hdepth
          (Lookup.value table outputWidth row))
  | succ remaining ih =>
      intro hshape
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      have haddress : addressWidth ≠ 0 := by omega
      have hnegative := gateOps_wellFormed (iw := 0)
        (cw := if addressWidth = 0 then 0 else 1) hl
        (negativeAndGates_wellFormed (outputWidth := outputWidth) hshape)
      have hleft := ih (row := row) (depth := depth + 1) (by omega)
      have hswitch := gateOps_wellFormed (iw := 0)
        (cw := if addressWidth = 0 then 0 else 1) hl
        (switchGates_wellFormed (outputWidth := outputWidth) hshape)
      have hright := ih (row := row + 2 ^ remaining) (depth := depth + 1) (by omega)
      have herase := andUncomputeClean_wellFormed
        (w := width addressWidth outputWidth) (iw := 0)
        (cw := if addressWidth = 0 then 0 else 1)
        (a := parent) (b := remaining) (c := child) (m := 0) hl
        (by simp [parent, selectorWire, selectorOffset, width_eq]; omega)
        (by simp [width_eq]; omega)
        (by simp [child, selectorWire, selectorOffset, width_eq]; omega)
        (by simp [haddress])
        (by simp [parent, selectorWire, selectorOffset]; omega)
      rw [nodeOps, Program.opsWellFormed_append, Program.opsWellFormed_append,
        Program.opsWellFormed_append, Program.opsWellFormed_append,
        hnegative, hleft, hswitch, hright, herase]
      rfl

private theorem nodeOps_wellFormed_width {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth selectorCount iw cw row depth : Nat) :
    ∀ remaining, remaining ≤ addressWidth → depth + remaining < selectorCount →
      (remaining ≠ 0 → 0 < cw) →
      Program.opsWellFormed level
        (Lookup.layout addressWidth outputWidth selectorCount).width iw cw
        (nodeOps table addressWidth outputWidth row depth remaining) = true := by
  intro remaining
  induction remaining generalizing row depth with
  | zero =>
      intro _ hselector _
      exact gateOps_wellFormed_width hl
        (leafGates_wellFormed_width (addressWidth := addressWidth)
          (outputWidth := outputWidth) (depth := depth)
          (word := Lookup.value table outputWidth row) (by omega))
  | succ remaining ih =>
      intro haddress hselector hc
      let parent := selectorWire addressWidth outputWidth depth
      let child := selectorWire addressWidth outputWidth (depth + 1)
      have hbit : remaining < addressWidth := by omega
      have hchild : depth + 1 < selectorCount := by omega
      have hcw : 0 < cw := hc (by omega)
      have hnegative := gateOps_wellFormed_width (iw := iw) (cw := cw) hl
        (negativeAndGates_wellFormed_width (outputWidth := outputWidth) hbit hchild)
      have hleft := ih (row := row) (depth := depth + 1) (by omega) (by omega)
        (fun _ ↦ hcw)
      have hswitch := gateOps_wellFormed_width (iw := iw) (cw := cw) hl
        (switchGates_wellFormed_width (addressWidth := addressWidth)
          (outputWidth := outputWidth) hchild)
      have hright := ih (row := row + 2 ^ remaining) (depth := depth + 1)
        (by omega) (by omega) (fun _ ↦ hcw)
      have herase := andUncomputeClean_wellFormed
        (w := (Lookup.layout addressWidth outputWidth selectorCount).width)
        (iw := iw) (cw := cw) (a := parent) (b := remaining) (c := child) (m := 0) hl
        (by simp [parent, selectorWire, selectorOffset, Lookup.layout, Layout.width]; omega)
        (by simp [Lookup.layout, Layout.width]; omega)
        (by simp [child, selectorWire, selectorOffset, Lookup.layout, Layout.width]; omega)
        (by omega)
        (by simp [parent, selectorWire, selectorOffset]; omega)
      rw [nodeOps, Program.opsWellFormed_append, Program.opsWellFormed_append,
        Program.opsWellFormed_append, Program.opsWellFormed_append,
        hnegative, hleft, hswitch, hright, herase]
      rfl

theorem lookupProgram_wellFormed {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    (lookupProgram table addressWidth outputWidth).wellFormed level = true := by
  have hroot := gateOps_wellFormed (iw := 0)
    (cw := if addressWidth = 0 then 0 else 1) hl
    (rootGate_wellFormed addressWidth outputWidth)
  have hnode := nodeOps_wellFormed hl table addressWidth outputWidth 0 0
    addressWidth (by omega)
  have hroot' : Program.opsWellFormed level (width addressWidth outputWidth) 0
      (if addressWidth = 0 then 0 else 1)
      (gateOps [.x (selectorWire addressWidth outputWidth 0)]) = true := by
    simpa [rootWire] using hroot
  change Program.opsWellFormed level (width addressWidth outputWidth) 0
    (if addressWidth = 0 then 0 else 1) (lookupOps table addressWidth outputWidth) = true
  rw [lookupOps, Program.opsWellFormed_append, Program.opsWellFormed_append,
    hroot', hnode]
  rfl

def lookupSpec (table : List Nat) (addressWidth outputWidth : Nat) : RegSpec where
  width := width addressWidth outputWidth
  Pre i := Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0
  Post i j := j =
    Lookup.xorOutput table addressWidth outputWidth (selectorWidth addressWidth) i

theorem xorOutput_lt
    {table : List Nat} {addressWidth outputWidth i : Nat}
    (hi : i < 2 ^ width addressWidth outputWidth) :
    Lookup.xorOutput table addressWidth outputWidth (selectorWidth addressWidth) i <
      2 ^ width addressWidth outputWidth := by
  exact writeField_lt (by simp [Lookup.layout, Layout.offset, Layout.size, width_eq]; omega) hi

theorem lookupProgram_realisesAt {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    RealisesAt level 0 (lookupSpec table addressWidth outputWidth)
      (lookupProgram table addressWidth outputWidth) := by
  have hwf := lookupProgram_wellFormed hl table addressWidth outputWidth
  refine realisesAt_of_implementsU rfl hwf (Nat.two_pow_pos 0)
    (out := Lookup.xorOutput table addressWidth outputWidth (selectorWidth addressWidth))
    (c := Dy.invSqrt2 (deg level)) ?_ ?_ ?_
  · simpa [lookupProgram, lookupSpec] using
      (lookup_implements (input := 0) hl table addressWidth outputWidth)
  · intro i hi _
    exact ⟨rfl, xorOutput_lt hi⟩
  · intro i hi _
    exact totalProb_basis level (lookupProgram table addressWidth outputWidth) hwf 0
      (by simpa [lookupProgram, lookupSpec] using hi)

namespace Rootless

def selectorWidth (addressWidth : Nat) : Nat := addressWidth

def circuitLayout (addressWidth outputWidth : Nat) : Layout :=
  Lookup.layout addressWidth outputWidth (selectorWidth addressWidth)

def width (addressWidth outputWidth : Nat) : Nat :=
  (circuitLayout addressWidth outputWidth).width

def selector (addressWidth outputWidth : Nat) : Nat :=
  selectorWire addressWidth outputWidth 0

def negativeCopyGates (address target : Nat) : List RGate :=
  [.x address, .cx address target, .x address]

def lookupOps (table : List Nat) : Nat → Nat → List Op
  | 0, outputWidth =>
      gateOps (constantXorGates (Lookup.value table outputWidth 0)
        (outputOffset 0) outputWidth)
  | addressWidth + 1, outputWidth =>
      let root := selector (addressWidth + 1) outputWidth
      gateOps (negativeCopyGates addressWidth root) ++
        nodeOps table (addressWidth + 1) outputWidth 0 0 addressWidth ++
        gateOps [.x root] ++
        nodeOps table (addressWidth + 1) outputWidth (2 ^ addressWidth) 0 addressWidth ++
        gateOps [.cx addressWidth root]

def lookupProgram (table : List Nat) (addressWidth outputWidth : Nat) : Program :=
  { width := width addressWidth outputWidth
    cbits := if addressWidth ≤ 1 then 0 else 1
    ops := lookupOps table addressWidth outputWidth }

def rootEval (table : List Nat) (addressWidth outputWidth i : Nat) : Nat :=
  let root := selector (addressWidth + 1) outputWidth
  let i₁ := actGates (negativeCopyGates addressWidth root) i
  let i₂ := nodeEval table (addressWidth + 1) outputWidth 0 0 addressWidth i₁
  let i₃ := RGate.act (.x root) i₂
  let i₄ := nodeEval table (addressWidth + 1) outputWidth (2 ^ addressWidth) 0 addressWidth i₃
  RGate.act (.cx addressWidth root) i₄

theorem width_eq (addressWidth outputWidth : Nat) :
    width addressWidth outputWidth = 2 * addressWidth + outputWidth := by
  simp [width, circuitLayout, selectorWidth, Lookup.layout, Layout.width]
  omega

private theorem negativeCopyGates_act {address target i : Nat}
    (hat : address ≠ target) (hclear : bitValue i target = 0) :
    actGates (negativeCopyGates address target) i =
      writeField i target 1 (if bitValue i address = 0 then 1 else 0) := by
  let j := writeField i address 1 ((bitValue i address + 1) % 2)
  let u := (bitValue j target + bitValue j address) % 2
  let k := writeField j target 1 u
  have e1 : RGate.act (.x address) i = j := by
    simp only [j, act_x_write]
  have hjAddress : bitValue j address = ((bitValue i address + 1) % 2) % 2 :=
    bitValue_write_self _ _ _
  have hjTarget : bitValue j target = bitValue i target :=
    bitValue_write_ne hat.symm
  have e2 : RGate.act (.cx address target) j = k := by
    simp only [k, u]
    rw [act_cx_write, hjTarget, hjAddress]
  have hkAddress : bitValue k address = bitValue j address :=
    bitValue_write_ne hat
  have ha := bitValue_lt i address
  have hrestore : ((((bitValue i address + 1) % 2) % 2 + 1) % 2) =
      bitValue i address := by omega
  have hu : u = if bitValue i address = 0 then 1 else 0 := by
    unfold u
    rw [hjTarget, hjAddress, hclear, Nat.zero_add]
    by_cases hz : bitValue i address = 0
    · simp [hz]
    · have ho : bitValue i address = 1 := by omega
      simp [ho]
  rw [negativeCopyGates, actGates_cons, actGates_cons, actGates_cons,
    actGates_nil, e1, e2, act_x_write, hkAddress, hjAddress, hrestore]
  change writeField (writeField j target 1 u) address 1 (bitValue i address) = _
  rw [writeField_comm (show target + 1 ≤ address ∨
      address + 1 ≤ target by omega)]
  simp only [j, writeField_writeField]
  rw [show writeField i address 1 (bitValue i address) = i by
      exact write_of_bitValue (by omega), hu]

private theorem workspace_readField
    {addressWidth outputWidth i : Nat}
    (hclear : Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0) :
    readField i (selectorOffset addressWidth outputWidth) addressWidth = 0 := by
  simpa [Lookup.workspace, Lookup.layout, Layout.read, Layout.offset, Layout.size,
    selectorOffset, selectorWidth] using hclear

private theorem selector_zero
    {addressWidth outputWidth i : Nat} (haddress : 0 < addressWidth)
    (hclear : Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0) :
    bitValue i (selector addressWidth outputWidth) = 0 := by
  rw [← readField_one]
  apply readField_sub_zero
    (off := selectorOffset addressWidth outputWidth) (len := addressWidth)
  · simp [selector, selectorWire]
  · simp [selector, selectorWire]
    omega
  · exact workspace_readField hclear

private theorem nodePre_of_workspace
    {addressWidth outputWidth depth remaining i : Nat}
    (hfit : depth + 1 + remaining ≤ addressWidth)
    (hclear : Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0) :
    nodePre addressWidth outputWidth depth remaining i := by
  apply readField_sub_zero
    (off := selectorOffset addressWidth outputWidth) (len := addressWidth)
  · simp [selectorWire]
  · simp [selectorWire]
    omega
  · exact workspace_readField hclear

private theorem rootEval_eq_xorOutput
    {table : List Nat} {addressWidth outputWidth i : Nat}
    (hclear : Lookup.workspace (addressWidth + 1) outputWidth
      (selectorWidth (addressWidth + 1)) i = 0) :
    rootEval table addressWidth outputWidth i =
      Lookup.xorOutput table (addressWidth + 1) outputWidth
        (selectorWidth (addressWidth + 1)) i := by
  let total := addressWidth + 1
  let root := selector total outputWidth
  let i₁ := actGates (negativeCopyGates addressWidth root) i
  let i₂ := nodeEval table total outputWidth 0 0 addressWidth i₁
  let i₃ := RGate.act (.x root) i₂
  let i₄ := nodeEval table total outputWidth (2 ^ addressWidth) 0 addressWidth i₃
  have haddressRoot : addressWidth ≠ root := by
    simp [root, total, selector, selectorWire, selectorOffset]
    omega
  have hrootValue : bitValue i root = 0 := by
    simpa [root, total] using selector_zero (addressWidth := total) (by omega) hclear
  have hi₁ : i₁ = writeField i root 1
      (if bitValue i addressWidth = 0 then 1 else 0) := by
    dsimp only [i₁]
    exact negativeCopyGates_act haddressRoot hrootValue
  have hleftPre : nodePre total outputWidth 0 addressWidth i₁ := by
    rw [hi₁, nodePre,
      readField_writeField_of_disjoint (Or.inl (by
        simp [root, total, selector, selectorWire]))]
    simpa [nodePre, total] using nodePre_of_workspace
      (addressWidth := total) (outputWidth := outputWidth) (depth := 0)
      (remaining := addressWidth) (by omega) hclear
  have heqLeft := nodeEval_eq_target_le table total outputWidth 0 0 addressWidth i₁
    (by omega) hleftPre
  have hrightPre : nodePre total outputWidth 0 addressWidth i₃ := by
    have htargetPre : nodePre total outputWidth 0 addressWidth
        (nodeTarget table total outputWidth 0 0 addressWidth i₁) :=
      nodePre_nodeTarget hleftPre
    rw [nodePre]
    simp only [i₃, i₂]
    rw [act_x_write,
      readField_writeField_of_disjoint (Or.inl (by
        simp [root, total, selector, selectorWire])), heqLeft]
    simpa [nodePre] using htargetPre
  have heqRight := nodeEval_eq_target_le table total outputWidth
    (2 ^ addressWidth) 0 addressWidth i₃ (by omega) hrightPre
  rw [rootEval]
  change RGate.act (.cx addressWidth root)
    (nodeEval table total outputWidth (2 ^ addressWidth) 0 addressWidth
      (RGate.act (.x root)
        (nodeEval table total outputWidth 0 0 addressWidth i₁))) = _
  rw [heqRight]
  simp only [i₃, i₂]
  rw [heqLeft]
  have houtputRoot : outputOffset total + outputWidth ≤ root := by
    simp [root, total, selector, selectorWire, selectorOffset, outputOffset]
  have haddressOutput : addressWidth < outputOffset total := by
    simp [total, outputOffset]
  have hreadHigh := readField_high i 0 addressWidth
  simp only [Nat.zero_add] at hreadHigh
  cases ha : i.testBit addressWidth with
  | false =>
      have haddressValue : bitValue i addressWidth = 0 :=
        (testBit_eq_false_iff_bitValue_eq_zero _ _).mp ha
      have hi₁' : i₁ = writeField i root 1 1 := by
        rw [hi₁, haddressValue]
        simp
      have hi₁Root : i₁.testBit root = true := by
        rw [hi₁', testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp
      have hi₁Output : Lookup.output total outputWidth (Unary.selectorWidth total) i₁ =
          Lookup.output total outputWidth (Unary.selectorWidth total) i := by
        rw [hi₁']
        simpa [Lookup.output, Lookup.layout, Layout.read, Layout.offset, Layout.size,
          outputOffset] using
          (readField_writeField_of_disjoint (Or.inr houtputRoot) :
            readField (writeField i root 1 1) total outputWidth =
              readField i total outputWidth)
      have hi₁Address : readField i₁ 0 addressWidth = readField i 0 addressWidth := by
        rw [hi₁']
        exact readField_writeField_of_disjoint (Or.inr (by
          simp [root, total, selector, selectorWire, selectorOffset]
          omega))
      let valueLeft := Lookup.output total outputWidth (Unary.selectorWidth total) i ^^^
        Lookup.value table outputWidth (readField i 0 addressWidth)
      have hi₂ : nodeTarget table total outputWidth 0 0 addressWidth i₁ =
          writeField i₁ (outputOffset total) outputWidth valueLeft := by
        rw [nodeTarget, if_pos (by simpa [root, selector] using hi₁Root),
          Nat.zero_add, hi₁Output, hi₁Address]
      have hi₃ : RGate.act (.x root)
          (nodeTarget table total outputWidth 0 0 addressWidth i₁) =
          writeField i (outputOffset total) outputWidth valueLeft := by
        rw [act_x_write, hi₂]
        have hrootAfter : bitValue
            (writeField i₁ (outputOffset total) outputWidth valueLeft) root = 1 := by
          rw [bitValue_write_out (Or.inr houtputRoot)]
          exact (testBit_eq_true_iff_bitValue_eq_one _ _).mp hi₁Root
        rw [hrootAfter]
        simp
        rw [hi₁', writeField_comm (Or.inl houtputRoot), writeField_writeField]
        rw [show writeField i root 1 0 = i by
          exact write_of_bitValue (by simpa using hrootValue.symm)]
      have hi₃Root : (writeField i (outputOffset total) outputWidth valueLeft).testBit root =
          false := by
        rw [testBit_writeField_outside (Or.inr houtputRoot)]
        exact (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr hrootValue
      rw [hi₃, nodeTarget, if_neg (by simpa [root, selector] using hi₃Root),
        act_cx_write]
      rw [bitValue_write_out (Or.inl haddressOutput),
        bitValue_write_out (Or.inr houtputRoot), haddressValue, hrootValue]
      simp only [Nat.zero_add]
      rw [write_of_bitValue (by
        rw [bitValue_write_out (Or.inr houtputRoot)]
        simpa using hrootValue.symm)]
      simp only [Lookup.xorOutput, Lookup.output, Lookup.address, Lookup.layout,
        Layout.write, Layout.read, Layout.offset, Layout.size]
      rw [hreadHigh, haddressValue, Nat.mul_zero, Nat.add_zero]
      rfl
  | true =>
      have haddressValue : bitValue i addressWidth = 1 :=
        (testBit_eq_true_iff_bitValue_eq_one _ _).mp ha
      have hi₁' : i₁ = i := by
        rw [hi₁, haddressValue]
        exact write_of_bitValue (by simpa using hrootValue.symm)
      have hi₂ : nodeTarget table total outputWidth 0 0 addressWidth i₁ = i := by
        rw [hi₁', nodeTarget, if_neg (by
          have hr := (testBit_eq_false_iff_bitValue_eq_zero _ _).mpr
            (by simpa [root, selector] using hrootValue)
          simp [hr])]
      have hi₃ : RGate.act (.x root)
          (nodeTarget table total outputWidth 0 0 addressWidth i₁) =
          writeField i root 1 1 := by
        rw [hi₂, act_x_write, hrootValue]
      have hi₃Root : (writeField i root 1 1).testBit root = true := by
        rw [testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp
      have hi₃Output : Lookup.output total outputWidth (Unary.selectorWidth total)
          (writeField i root 1 1) =
          Lookup.output total outputWidth (Unary.selectorWidth total) i := by
        simpa [Lookup.output, Lookup.layout, Layout.read, Layout.offset, Layout.size,
          outputOffset] using
          (readField_writeField_of_disjoint (Or.inr houtputRoot) :
            readField (writeField i root 1 1) total outputWidth =
              readField i total outputWidth)
      have hi₃Address : readField (writeField i root 1 1) 0 addressWidth =
          readField i 0 addressWidth := by
        exact readField_writeField_of_disjoint (Or.inr (by
          simp [root, total, selector, selectorWire, selectorOffset]
          omega))
      let valueRight := Lookup.output total outputWidth (Unary.selectorWidth total) i ^^^
        Lookup.value table outputWidth (2 ^ addressWidth + readField i 0 addressWidth)
      have hi₄ : nodeTarget table total outputWidth (2 ^ addressWidth) 0 addressWidth
          (writeField i root 1 1) =
          writeField (writeField i root 1 1) (outputOffset total) outputWidth valueRight := by
        rw [nodeTarget, if_pos (by simpa [root, selector] using hi₃Root),
          hi₃Output, hi₃Address]
      rw [hi₃, hi₄, act_cx_write]
      have hrootAfter : bitValue
          (writeField (writeField i root 1 1) (outputOffset total) outputWidth valueRight) root =
          1 := by
        rw [bitValue_write_out (Or.inr houtputRoot), bitValue_write_self]
      have haddressAfter : bitValue
          (writeField (writeField i root 1 1) (outputOffset total) outputWidth valueRight)
            addressWidth = 1 := by
        rw [bitValue_write_out (Or.inl haddressOutput),
          bitValue_write_ne haddressRoot, haddressValue]
      rw [haddressAfter, hrootAfter]
      simp
      rw [writeField_comm (Or.inl houtputRoot), writeField_writeField]
      rw [show writeField i root 1 0 = i by
        exact write_of_bitValue (by simpa using hrootValue.symm)]
      simp only [Lookup.xorOutput, Lookup.output, Lookup.address, Lookup.layout,
        Layout.write, Layout.read, Layout.offset, Layout.size]
      rw [hreadHigh, haddressValue, Nat.mul_one]
      dsimp only [valueRight, outputOffset]
      rw [show 2 ^ addressWidth + readField i 0 addressWidth =
          readField i 0 addressWidth + 2 ^ addressWidth by omega]
      rfl

private theorem negativeCopyGates_wellFormed
    (addressWidth outputWidth : Nat) :
    ({ width := width (addressWidth + 1) outputWidth,
       gates := negativeCopyGates addressWidth
        (selector (addressWidth + 1) outputWidth) } : RCircuit).wellFormed = true := by
  simp [RCircuit.wellFormed, negativeCopyGates, RGate.wellFormed, width_eq,
    selector, selectorWire, selectorOffset]
  omega

private theorem rootXGates_wellFormed
    (addressWidth outputWidth : Nat) :
    ({ width := width (addressWidth + 1) outputWidth,
       gates := [.x (selector (addressWidth + 1) outputWidth)] } : RCircuit).wellFormed =
      true := by
  simp [RCircuit.wellFormed, RGate.wellFormed, width_eq, selector, selectorWire,
    selectorOffset]

private theorem rootCxGates_wellFormed
    (addressWidth outputWidth : Nat) :
    ({ width := width (addressWidth + 1) outputWidth,
       gates := [.cx addressWidth (selector (addressWidth + 1) outputWidth)] } : RCircuit).wellFormed =
      true := by
  simp [RCircuit.wellFormed, RGate.wellFormed, width_eq, selector, selectorWire,
    selectorOffset]
  omega

private theorem constantGates_wellFormed (table : List Nat) (outputWidth : Nat) :
    ({ width := width 0 outputWidth,
       gates := constantXorGates (Lookup.value table outputWidth 0)
        (outputOffset 0) outputWidth } : RCircuit).wellFormed = true := by
  rw [RCircuit.wellFormed]
  exact constantXorGates_wellFormed (by simp [width_eq, outputOffset])

private theorem negativeCopy_nodePre
    {addressWidth outputWidth i : Nat}
    (hclear : Lookup.workspace (addressWidth + 1) outputWidth
      (selectorWidth (addressWidth + 1)) i = 0) :
    nodePre (addressWidth + 1) outputWidth 0 addressWidth
      (actGates (negativeCopyGates addressWidth
        (selector (addressWidth + 1) outputWidth)) i) := by
  let total := addressWidth + 1
  let root := selector total outputWidth
  have haddressRoot : addressWidth ≠ root := by
    simp [root, total, selector, selectorWire, selectorOffset]
    omega
  have hrootValue : bitValue i root = 0 := by
    simpa [root, total] using selector_zero (addressWidth := total) (by omega) hclear
  rw [negativeCopyGates_act haddressRoot hrootValue, nodePre,
    readField_writeField_of_disjoint (Or.inl (by
      simp [root, total, selector, selectorWire]))]
  simpa [nodePre, total] using nodePre_of_workspace
    (addressWidth := total) (outputWidth := outputWidth) (depth := 0)
    (remaining := addressWidth) (by omega) hclear

private theorem leftRootX_nodePre
    {table : List Nat} {addressWidth outputWidth i : Nat}
    (hclear : Lookup.workspace (addressWidth + 1) outputWidth
      (selectorWidth (addressWidth + 1)) i = 0) :
    nodePre (addressWidth + 1) outputWidth 0 addressWidth
      (RGate.act (.x (selector (addressWidth + 1) outputWidth))
        (nodeEval table (addressWidth + 1) outputWidth 0 0 addressWidth
          (actGates (negativeCopyGates addressWidth
            (selector (addressWidth + 1) outputWidth)) i))) := by
  let total := addressWidth + 1
  let root := selector total outputWidth
  let i₁ := actGates (negativeCopyGates addressWidth root) i
  have hleftPre : nodePre total outputWidth 0 addressWidth i₁ := by
    simpa [total, root, i₁] using
      (negativeCopy_nodePre hclear)
  have heqLeft := nodeEval_eq_target_le table total outputWidth 0 0 addressWidth i₁
    (by omega) hleftPre
  have htargetPre : nodePre total outputWidth 0 addressWidth
      (nodeTarget table total outputWidth 0 0 addressWidth i₁) :=
    nodePre_nodeTarget hleftPre
  rw [nodePre, act_x_write,
    readField_writeField_of_disjoint (Or.inl (by
      simp [selector, selectorWire])), heqLeft]
  simpa [nodePre] using htargetPre

private theorem negativeCopy_lt
    {addressWidth outputWidth i : Nat}
    (hi : i < 2 ^ width (addressWidth + 1) outputWidth) :
    actGates (negativeCopyGates addressWidth
      (selector (addressWidth + 1) outputWidth)) i <
        2 ^ width (addressWidth + 1) outputWidth := by
  exact Reversible.act_lt (negativeCopyGates_wellFormed addressWidth outputWidth) hi

private theorem rootX_lt
    {addressWidth outputWidth i : Nat}
    (hi : i < 2 ^ width (addressWidth + 1) outputWidth) :
    RGate.act (.x (selector (addressWidth + 1) outputWidth)) i <
      2 ^ width (addressWidth + 1) outputWidth := by
  exact Reversible.act_lt (rootXGates_wellFormed addressWidth outputWidth) hi

private theorem zeroEval_eq_xorOutput
    (table : List Nat) (outputWidth i : Nat) :
    actGates (constantXorGates (Lookup.value table outputWidth 0)
      (outputOffset 0) outputWidth) i =
        Lookup.xorOutput table 0 outputWidth (selectorWidth 0) i := by
  rw [act_constantXorGates, ← writeField_xor_value]
  simp [Lookup.xorOutput, Lookup.output, Lookup.address, Lookup.layout,
    Layout.write, Layout.read, Layout.offset, Layout.size, outputOffset, selectorWidth,
    readField_zero]
  rw [Nat.mod_one]

theorem lookup_implements {level input : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    ImplementsU level (width addressWidth outputWidth) input
      (fun i ↦ Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0)
      (Lookup.xorOutput table addressWidth outputWidth (selectorWidth addressWidth))
      (Dy.invSqrt2 (deg level)) (lookupOps table addressWidth outputWidth) := by
  cases addressWidth with
  | zero =>
      have hall := gateOps_implements_width (input := input)
        (w := width 0 outputWidth) hl (constantGates_wellFormed table outputWidth)
        (Dy.invSqrt2 (deg level))
      intro i hi _ rec cr b hb
      have hs := hall i hi trivial rec cr b (by simpa [lookupOps] using hb)
      rw [zeroEval_eq_xorOutput] at hs
      exact hs
  | succ addressWidth =>
      let total := addressWidth + 1
      let root := selector total outputWidth
      let i₁ := fun i ↦ actGates (negativeCopyGates addressWidth root) i
      let i₂ := fun i ↦ nodeEval table total outputWidth 0 0 addressWidth (i₁ i)
      let i₃ := fun i ↦ RGate.act (.x root) (i₂ i)
      let i₄ := fun i ↦ nodeEval table total outputWidth
        (2 ^ addressWidth) 0 addressWidth (i₃ i)
      have hnegativeAll := gateOps_implements_width (input := input)
        (w := width total outputWidth) hl
        (by simpa [total, root] using negativeCopyGates_wellFormed addressWidth outputWidth)
        (Dy.invSqrt2 (deg level))
      have hnegative := hnegativeAll.mono
        (dom' := fun i ↦ Lookup.workspace total outputWidth (selectorWidth total) i = 0)
        (fun _ _ ↦ trivial)
      have hleft := nodeOps_implements_width (input := input) hl table total outputWidth
        (selectorWidth total) 0 0 addressWidth (by omega) (by simp [selectorWidth, total])
      have hthroughLeft := hnegative.append hleft
        (fun i hi _ ↦ by simpa [i₁, total, root] using negativeCopy_lt hi)
        (fun _ _ hclear ↦ by
          simpa [i₁, total, root] using negativeCopy_nodePre hclear)
      have hxAll := gateOps_implements_width (input := input)
        (w := width total outputWidth) hl
        (by simpa [total, root] using rootXGates_wellFormed addressWidth outputWidth)
        (Dy.invSqrt2 (deg level))
      have hx : ImplementsU level (width total outputWidth) input (fun _ ↦ True)
          (fun i ↦ RGate.act (.x root) i) (Dy.invSqrt2 (deg level))
          (gateOps [.x root]) := by
        simpa [actGates] using hxAll
      have hthroughX := hthroughLeft.append hx
        (fun i hi hclear ↦ by
          have hpre := negativeCopy_nodePre hclear
          simpa [width, circuitLayout] using
            (nodeEval_lt_width (selectorCount := selectorWidth total) (by omega)
              (by simpa [i₁, total, root, width, circuitLayout] using negativeCopy_lt hi)
              (by simpa [i₁, total, root] using hpre)))
        (fun _ _ _ ↦ trivial)
      have hright := nodeOps_implements_width (input := input) hl table total outputWidth
        (selectorWidth total) (2 ^ addressWidth) 0 addressWidth (by omega)
        (by simp [selectorWidth, total])
      have hthroughRight := hthroughX.append hright
        (fun i hi hclear ↦ by
          have hpre := negativeCopy_nodePre hclear
          have hi₁ : i₁ i < 2 ^ width total outputWidth := by
            simpa [i₁, total, root] using negativeCopy_lt hi
          have hi₂ : i₂ i < 2 ^ width total outputWidth := by
            exact nodeEval_lt_width (selectorCount := selectorWidth total) (by omega) hi₁
              (by simpa [i₁, total, root] using hpre)
          simpa [i₂, i₃, total, root, width, circuitLayout] using rootX_lt hi₂)
        (fun _ _ hclear ↦ by
          simpa [i₁, i₂, i₃, total, root] using
            leftRootX_nodePre (table := table) hclear)
      have hcxAll := gateOps_implements_width (input := input)
        (w := width total outputWidth) hl
        (by simpa [total, root] using rootCxGates_wellFormed addressWidth outputWidth)
        (Dy.invSqrt2 (deg level))
      have hcx : ImplementsU level (width total outputWidth) input (fun _ ↦ True)
          (fun i ↦ RGate.act (.cx addressWidth root) i) (Dy.invSqrt2 (deg level))
          (gateOps [.cx addressWidth root]) := by
        simpa [actGates] using hcxAll
      have hall := hthroughRight.append hcx
        (fun i hi hclear ↦ by
          have hpre₁ := negativeCopy_nodePre hclear
          have hi₁ : i₁ i < 2 ^ width total outputWidth := by
            simpa [i₁, total, root] using negativeCopy_lt hi
          have hi₂ : i₂ i < 2 ^ width total outputWidth := by
            exact nodeEval_lt_width (selectorCount := selectorWidth total) (by omega) hi₁
              (by simpa [i₁, total, root] using hpre₁)
          have hi₃ : i₃ i < 2 ^ width total outputWidth := by
            simpa [i₂, i₃, total, root] using rootX_lt hi₂
          have hpre₃ := leftRootX_nodePre (table := table) hclear
          simpa [width, circuitLayout] using
            (nodeEval_lt_width (selectorCount := selectorWidth total) (by omega) hi₃
              (by simpa [i₁, i₂, i₃, total, root] using hpre₃)))
        (fun _ _ _ ↦ trivial)
      have heval : ImplementsU level (width total outputWidth) input
          (fun i ↦ Lookup.workspace total outputWidth (selectorWidth total) i = 0)
          (rootEval table addressWidth outputWidth) (Dy.invSqrt2 (deg level))
          (lookupOps table total outputWidth) := by
        change ImplementsU level (width total outputWidth) input
          (fun i ↦ Lookup.workspace total outputWidth (selectorWidth total) i = 0)
          (fun i ↦ RGate.act (.cx addressWidth (selector total outputWidth))
            (nodeEval table total outputWidth (2 ^ addressWidth) 0 addressWidth
              (RGate.act (.x (selector total outputWidth))
                (nodeEval table total outputWidth 0 0 addressWidth
                  (actGates (negativeCopyGates addressWidth
                    (selector total outputWidth)) i)))))
          (Dy.invSqrt2 (deg level)) (lookupOps table total outputWidth)
        simpa [lookupOps, total, root, i₁, i₂, i₃, i₄, actGates,
          List.append_assoc, Function.comp_def] using hall
      intro i hi hclear rec cr b hb
      have hs := heval i hi hclear rec cr b hb
      rw [rootEval_eq_xorOutput hclear] at hs
      exact hs

theorem lookup_toffoliCount (table : List Nat) (addressWidth outputWidth : Nat) :
    (lookupProgram table addressWidth outputWidth).toffoliCount =
      Range.point (2 ^ addressWidth - 2) := by
  cases addressWidth with
  | zero =>
      simp [Program.toffoliCount, lookupProgram, lookupOps, gateOps_toffoli,
        constantXorGates_no_ccx, Range.point]
  | succ addressWidth =>
      have hpow := Nat.two_pow_pos addressWidth
      simp only [Program.toffoliCount, lookupProgram, lookupOps,
        Program.weighOps_append, gateOps_toffoli, nodeOps_toffoli]
      simp [negativeCopyGates, RGate.isCcx, Range.add, Range.point, Nat.pow_succ]
      omega

theorem lookup_toffoliCount_hi_le
    (table : List Nat) (addressWidth outputWidth : Nat) :
    (lookupProgram table addressWidth outputWidth).toffoliCount.hi ≤
      2 ^ addressWidth - 1 := by
  rw [lookup_toffoliCount]
  simp [Range.point]
  have hpow := Nat.two_pow_pos addressWidth
  omega

theorem lookupProgram_wellFormed {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    (lookupProgram table addressWidth outputWidth).wellFormed level = true := by
  cases addressWidth with
  | zero =>
      have hconstant := gateOps_wellFormed_width (iw := 0) (cw := 0) hl
        (constantGates_wellFormed table outputWidth)
      simpa [Program.wellFormed, lookupProgram, lookupOps] using hconstant
  | succ addressWidth =>
      let total := addressWidth + 1
      let root := selector total outputWidth
      let cbits := if total ≤ 1 then 0 else 1
      have hnegative := gateOps_wellFormed_width (iw := 0) (cw := cbits) hl
        (by simpa [total, root] using negativeCopyGates_wellFormed addressWidth outputWidth)
      have hnodeLeft := nodeOps_wellFormed_width hl table total outputWidth
        (selectorWidth total) 0 cbits 0 0 addressWidth (by omega)
        (by simp [selectorWidth, total]) (by
          intro hpositive
          have htotal : ¬ total ≤ 1 := by
            simp [total]
            omega
          simp [cbits, htotal])
      have hx := gateOps_wellFormed_width (iw := 0) (cw := cbits) hl
        (by simpa [total, root] using rootXGates_wellFormed addressWidth outputWidth)
      have hnodeRight := nodeOps_wellFormed_width hl table total outputWidth
        (selectorWidth total) 0 cbits (2 ^ addressWidth) 0 addressWidth (by omega)
        (by simp [selectorWidth, total]) (by
          intro hpositive
          have htotal : ¬ total ≤ 1 := by
            simp [total]
            omega
          simp [cbits, htotal])
      have hcx := gateOps_wellFormed_width (iw := 0) (cw := cbits) hl
        (by simpa [total, root] using rootCxGates_wellFormed addressWidth outputWidth)
      have hnodeLeft' : Program.opsWellFormed level (width total outputWidth) 0 cbits
          (nodeOps table total outputWidth 0 0 addressWidth) = true := by
        simpa [width, circuitLayout] using hnodeLeft
      have hnodeRight' : Program.opsWellFormed level (width total outputWidth) 0 cbits
          (nodeOps table total outputWidth (2 ^ addressWidth) 0 addressWidth) = true := by
        simpa [width, circuitLayout] using hnodeRight
      change Program.opsWellFormed level (width total outputWidth) 0 cbits
        (lookupOps table total outputWidth) = true
      rw [lookupOps, Program.opsWellFormed_append, Program.opsWellFormed_append,
        Program.opsWellFormed_append, Program.opsWellFormed_append,
        hnegative, hnodeLeft', hx, hnodeRight', hcx]
      rfl

def lookupSpec (table : List Nat) (addressWidth outputWidth : Nat) : RegSpec where
  width := width addressWidth outputWidth
  Pre i := Lookup.workspace addressWidth outputWidth (selectorWidth addressWidth) i = 0
  Post i j := j =
    Lookup.xorOutput table addressWidth outputWidth (selectorWidth addressWidth) i

theorem xorOutput_lt
    {table : List Nat} {addressWidth outputWidth i : Nat}
    (hi : i < 2 ^ width addressWidth outputWidth) :
    Lookup.xorOutput table addressWidth outputWidth (selectorWidth addressWidth) i <
      2 ^ width addressWidth outputWidth := by
  exact writeField_lt
    (by simp [Lookup.layout, Layout.offset, Layout.size, width_eq]; omega) hi

theorem lookupProgram_realisesAt {level : Nat} (hl : 3 ≤ level)
    (table : List Nat) (addressWidth outputWidth : Nat) :
    RealisesAt level 0 (lookupSpec table addressWidth outputWidth)
      (lookupProgram table addressWidth outputWidth) := by
  have hwf := lookupProgram_wellFormed hl table addressWidth outputWidth
  refine realisesAt_of_implementsU rfl hwf (Nat.two_pow_pos 0)
    (out := Lookup.xorOutput table addressWidth outputWidth (selectorWidth addressWidth))
    (c := Dy.invSqrt2 (deg level)) ?_ ?_ ?_
  · simpa [lookupProgram, lookupSpec] using
      (lookup_implements (input := 0) hl table addressWidth outputWidth)
  · intro i hi _
    exact ⟨rfl, xorOutput_lt hi⟩
  · intro i hi _
    exact totalProb_basis level (lookupProgram table addressWidth outputWidth) hwf 0
      (by simpa [lookupProgram, lookupSpec] using hi)

end Rootless

end VQ.Lookup.Unary
