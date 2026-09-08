/-
Endpoint-controlled arithmetic on physically big-endian work slices.
-/
import VQ.Euclid.Interval
import VQ.Euclid.SerialBigEndian

namespace VQ
namespace Euclid
namespace IntervalBigEndian

open Reversible

def baseMajBackward (workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | top, m + 1 =>
      Interval.baseMajAt (top - 1) workWidth endpointWidth ++
        baseMajBackward workWidth endpointWidth (top - 1) m

def baseUmaForward (workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      Interval.baseUmaAt j workWidth endpointWidth ++
        baseUmaForward workWidth endpointWidth (j + 1) m

def adderMajBackward (workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | top, m + 1 =>
      Adder.maj (Interval.targetOffset workWidth + top - 1)
          (Interval.sourceOffset + top - 1)
          (Interval.carryWire workWidth endpointWidth) ++
        adderMajBackward workWidth endpointWidth (top - 1) m

def adderUmaForward (workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      Adder.uma (Interval.sourceOffset + j)
          (Interval.targetOffset workWidth + j)
          (Interval.carryWire workWidth endpointWidth) ++
        adderUmaForward workWidth endpointWidth (j + 1) m

def activeGates (left right workWidth endpointWidth : Nat) : List RGate :=
  baseMajBackward workWidth endpointWidth (right + 1)
      (right - left + 1) ++
    [.cx (Interval.carryWire workWidth endpointWidth)
      (Interval.signWire workWidth endpointWidth)] ++
  baseUmaForward workWidth endpointWidth left (right - left + 1)

def idealGates (left right workWidth endpointWidth : Nat) : List RGate :=
  let width := right - left + 1
  (SerialBigEndian.gates width).map (RGate.map
    (place (Interval.arithmeticLayout width)
      (Interval.arithmeticWiring left workWidth endpointWidth)))

def selectedMajBackward (left right workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | top, m + 1 =>
      Interval.selectedMajAt left right (top - 1) workWidth endpointWidth ++
        selectedMajBackward left right workWidth endpointWidth (top - 1) m

def selectedUmaForward (left right workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      Interval.selectedUmaAt left right j workWidth endpointWidth ++
        selectedUmaForward left right workWidth endpointWidth (j + 1) m

def selectedGates (left right workWidth endpointWidth : Nat) : List RGate :=
  selectedMajBackward left right workWidth endpointWidth workWidth
      workWidth ++
    [.cx (Interval.carryWire workWidth endpointWidth)
      (Interval.signWire workWidth endpointWidth)] ++
  selectedUmaForward left right workWidth endpointWidth 0 workWidth

def fixedFirstScan (left right workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | top, m + 1 =>
      Interval.fixedToggle right (top - 1) workWidth endpointWidth ++
      Interval.majAt (top - 1) workWidth endpointWidth ++
      Interval.fixedToggle left (top - 1) workWidth endpointWidth ++
      fixedFirstScan left right workWidth endpointWidth (top - 1) m

def fixedSecondScan (left right workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      Interval.fixedToggle left j workWidth endpointWidth ++
      Interval.umaAt j workWidth endpointWidth ++
      Interval.fixedToggle right j workWidth endpointWidth ++
      fixedSecondScan left right workWidth endpointWidth (j + 1) m

def fixedGates (left right workWidth endpointWidth : Nat) : List RGate :=
  fixedFirstScan left right workWidth endpointWidth workWidth workWidth ++
    [.cx (Interval.carryWire workWidth endpointWidth)
      (Interval.signWire workWidth endpointWidth)] ++
  fixedSecondScan left right workWidth endpointWidth 0 workWidth

def firstScan (workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | top, m + 1 =>
      Interval.rightToggle (top - 1) workWidth endpointWidth ++
      Interval.majAt (top - 1) workWidth endpointWidth ++
      Interval.leftToggle (top - 1) workWidth endpointWidth ++
      firstScan workWidth endpointWidth (top - 1) m

def secondScan (workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      Interval.leftToggle j workWidth endpointWidth ++
      Interval.umaAt j workWidth endpointWidth ++
      Interval.rightToggle j workWidth endpointWidth ++
      secondScan workWidth endpointWidth (j + 1) m

def gates (workWidth endpointWidth : Nat) : List RGate :=
  firstScan workWidth endpointWidth workWidth workWidth ++
    [.cx (Interval.carryWire workWidth endpointWidth)
      (Interval.signWire workWidth endpointWidth)] ++
  secondScan workWidth endpointWidth 0 workWidth

def circuit (workWidth endpointWidth : Nat) : RCircuit :=
  { width := (Interval.layout workWidth endpointWidth).width,
    gates := gates workWidth endpointWidth }

theorem baseMajBackward_eq_adderMajBackward
    {workWidth endpointWidth I : Nat} : ∀ m top,
    m ≤ top → top ≤ workWidth →
    actGates (baseMajBackward workWidth endpointWidth top m) I =
      actGates (adderMajBackward workWidth endpointWidth top m) I := by
  intro m
  induction m generalizing I with
  | zero => intro top _ _; rfl
  | succ m ih =>
      intro top hmt htop
      simp only [baseMajBackward, adderMajBackward, actGates_append]
      rw [Interval.baseMajAt_eq_adderMajAt (j := top - 1) (by omega)]
      rw [ih (top := top - 1) (by omega) (by omega)]
      congr 4 <;> omega

theorem baseUmaForward_eq_adderUmaForward
    {workWidth endpointWidth I : Nat} : ∀ m j,
    j + m ≤ workWidth →
    actGates (baseUmaForward workWidth endpointWidth j m) I =
      actGates (adderUmaForward workWidth endpointWidth j m) I := by
  intro m
  induction m generalizing I with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [baseUmaForward, adderUmaForward, actGates_append]
      rw [Interval.baseUmaAt_eq_adderUmaAt (by omega),
        ih (j := j + 1) (by omega)]

theorem map_serial_majBackward
    {left width workWidth endpointWidth : Nat} : ∀ m top,
    m ≤ top → top ≤ width →
    (SerialBigEndian.majBackward width top m).map
        (RGate.map
          (place (Interval.arithmeticLayout width)
            (Interval.arithmeticWiring left workWidth endpointWidth))) =
      adderMajBackward workWidth endpointWidth (left + top) m := by
  intro m
  induction m with
  | zero => intro top _ _; rfl
  | succ m ih =>
      intro top hmt htop
      simp only [SerialBigEndian.majBackward, List.map_append,
        adderMajBackward]
      rw [show width + top - 1 = width + (top - 1) by omega]
      rw [Interval.map_serial_maj (k := top - 1) (by omega),
        ih (top - 1) (by omega) (by omega)]
      congr 4 <;> omega

theorem map_serial_umaForward
    {left width workWidth endpointWidth : Nat} : ∀ m j,
    j + m ≤ width →
    (SerialBigEndian.umaForward width j m).map
        (RGate.map
          (place (Interval.arithmeticLayout width)
            (Interval.arithmeticWiring left workWidth endpointWidth))) =
      adderUmaForward workWidth endpointWidth (left + j) m := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [SerialBigEndian.umaForward, List.map_append,
        adderUmaForward]
      rw [Interval.map_serial_uma (k := j) (by omega),
        ih (j + 1) (by omega)]
      rw [show left + (j + 1) = left + j + 1 by omega]

theorem idealGates_eq_adderGates
    {left right workWidth endpointWidth : Nat} (hLR : left ≤ right) :
    idealGates left right workWidth endpointWidth =
      adderMajBackward workWidth endpointWidth (right + 1)
          (right - left + 1) ++
        [.cx (Interval.carryWire workWidth endpointWidth)
          (Interval.signWire workWidth endpointWidth)] ++
      adderUmaForward workWidth endpointWidth left
        (right - left + 1) := by
  let width := right - left + 1
  have hwidth : 0 < width := by
    dsimp [width]
    omega
  have htop : left + width = right + 1 := by
    dsimp [width]
    omega
  simp only [idealGates, SerialBigEndian.gates_eq_chains,
    List.map_append, List.map_cons, List.map_nil, RGate.map]
  rw [map_serial_majBackward width width (by omega) (by omega),
    map_serial_umaForward width 0 (by omega),
    Interval.place_arithmetic_carry,
    Interval.place_arithmetic_sign]
  simp only [Nat.add_zero, htop, width]

theorem activeGates_eq_ideal
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    actGates (activeGates left right workWidth endpointWidth) I =
      actGates (idealGates left right workWidth endpointWidth) I := by
  let width := right - left + 1
  have htop : right + 1 ≤ workWidth := by omega
  have hspan : left + width ≤ workWidth := by
    dsimp [width]
    omega
  rw [idealGates_eq_adderGates hLR]
  simp only [activeGates, actGates_append]
  rw [baseMajBackward_eq_adderMajBackward
      (I := I) (m := width) (top := right + 1) (by omega) htop]
  let middle := actGates
    [.cx (Interval.carryWire workWidth endpointWidth)
      (Interval.signWire workWidth endpointWidth)]
    (actGates
      (adderMajBackward workWidth endpointWidth (right + 1) width) I)
  change actGates
      (baseUmaForward workWidth endpointWidth left width) middle =
    actGates
      (adderUmaForward workWidth endpointWidth left width) middle
  exact baseUmaForward_eq_adderUmaForward
    (I := middle) (m := width) (j := left) hspan

theorem selectedMajBackward_split
    (left right workWidth endpointWidth base a b : Nat) :
    selectedMajBackward left right workWidth endpointWidth
        (base + a + b) (a + b) =
      selectedMajBackward left right workWidth endpointWidth
          (base + a + b) a ++
      selectedMajBackward left right workWidth endpointWidth
          (base + b) b := by
  induction a generalizing base with
  | zero => simp [selectedMajBackward]
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega,
        show base + (a + 1) + b = (base + a + b) + 1 by omega]
      simp only [selectedMajBackward, Nat.add_sub_cancel]
      rw [ih (base := base), List.append_assoc]

theorem selectedUmaForward_split
    (left right workWidth endpointWidth j a b : Nat) :
    selectedUmaForward left right workWidth endpointWidth j (a + b) =
      selectedUmaForward left right workWidth endpointWidth j a ++
      selectedUmaForward left right workWidth endpointWidth (j + a) b := by
  induction a generalizing j with
  | zero => simp [selectedUmaForward]
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega]
      simp only [selectedUmaForward]
      rw [ih (j := j + 1), List.append_assoc]
      simp only [show j + 1 + a = j + (a + 1) by omega]

theorem selectedMajBackward_above
    {left right workWidth endpointWidth : Nat} : ∀ m top,
    m ≤ top → right + m < top →
    selectedMajBackward left right workWidth endpointWidth top m =
      Interval.disabledBackward workWidth endpointWidth top m := by
  intro m
  induction m with
  | zero => intro top _ _; rfl
  | succ m ih =>
      intro top hmt hright
      have hj : ¬(left ≤ top - 1 ∧ top - 1 ≤ right) := by omega
      rw [selectedMajBackward, Interval.disabledBackward,
        Interval.selectedMajAt, if_neg hj,
        ih (top - 1) (by omega) (by omega)]

theorem selectedMajBackward_inside
    {left right workWidth endpointWidth : Nat} : ∀ m top,
    m ≤ top → left + m ≤ top → top ≤ right + 1 →
    selectedMajBackward left right workWidth endpointWidth top m =
      baseMajBackward workWidth endpointWidth top m := by
  intro m
  induction m with
  | zero => intro top _ _ _; rfl
  | succ m ih =>
      intro top hmt hleft hright
      have hj : left ≤ top - 1 ∧ top - 1 ≤ right := by omega
      rw [selectedMajBackward, baseMajBackward,
        Interval.selectedMajAt, if_pos hj,
        ih (top - 1) (by omega) (by omega) (by omega)]

theorem selectedMajBackward_below
    {left right workWidth endpointWidth : Nat} : ∀ m top,
    m ≤ top → top ≤ left →
    selectedMajBackward left right workWidth endpointWidth top m =
      Interval.disabledBackward workWidth endpointWidth top m := by
  intro m
  induction m with
  | zero => intro top _ _; rfl
  | succ m ih =>
      intro top hmt hleft
      have hj : ¬(left ≤ top - 1 ∧ top - 1 ≤ right) := by omega
      rw [selectedMajBackward, Interval.disabledBackward,
        Interval.selectedMajAt, if_neg hj,
        ih (top - 1) (by omega) (by omega)]

theorem selectedUmaForward_below
    {left right workWidth endpointWidth : Nat} : ∀ m j,
    j + m ≤ left →
    selectedUmaForward left right workWidth endpointWidth j m =
      Interval.disabledForward workWidth endpointWidth j m := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      have hj : ¬(left ≤ j ∧ j ≤ right) := by omega
      simp [selectedUmaForward, Interval.selectedUmaAt,
        Interval.disabledForward, hj, ih (j + 1) (by omega)]

theorem selectedUmaForward_inside
    {left right workWidth endpointWidth : Nat} : ∀ m j,
    left ≤ j → j + m ≤ right + 1 →
    selectedUmaForward left right workWidth endpointWidth j m =
      baseUmaForward workWidth endpointWidth j m := by
  intro m
  induction m with
  | zero => intro j _ _; rfl
  | succ m ih =>
      intro j hleft hright
      have hj : left ≤ j ∧ j ≤ right := by omega
      simp [selectedUmaForward, Interval.selectedUmaAt,
        baseUmaForward, hj, ih (j + 1) (by omega) (by omega)]

theorem selectedUmaForward_above
    {left right workWidth endpointWidth : Nat} : ∀ m j,
    right < j →
    selectedUmaForward left right workWidth endpointWidth j m =
      Interval.disabledForward workWidth endpointWidth j m := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hright
      have hj : ¬(left ≤ j ∧ j ≤ right) := by omega
      simp [selectedUmaForward, Interval.selectedUmaAt,
        Interval.disabledForward, hj, ih (j + 1) (by omega)]

theorem selectedMajBackward_decompose
    {left right workWidth endpointWidth : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    selectedMajBackward left right workWidth endpointWidth
        workWidth workWidth =
      Interval.disabledBackward workWidth endpointWidth workWidth
          (workWidth - (right + 1)) ++
      baseMajBackward workWidth endpointWidth (right + 1)
          (right - left + 1) ++
      Interval.disabledBackward workWidth endpointWidth left left := by
  let n := right - left + 1
  let u := workWidth - (right + 1)
  have hLn : left + n = right + 1 := by
    dsimp [n]
    omega
  have hsum : u + n + left = workWidth := by
    dsimp [n, u]
    omega
  have habove := selectedMajBackward_above
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) u workWidth (by omega) (by
      dsimp [u]
      omega)
  have hinside := selectedMajBackward_inside
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) n (right + 1)
    (by omega) (by omega) (by omega)
  have hbelow := selectedMajBackward_below
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) left left (by omega) (by omega)
  have hsplit₁ :
      selectedMajBackward left right workWidth endpointWidth
          workWidth workWidth =
        selectedMajBackward left right workWidth endpointWidth
            workWidth u ++
        selectedMajBackward left right workWidth endpointWidth
            (n + left) (n + left) := by
    have hs := selectedMajBackward_split left right workWidth endpointWidth
      0 u (n + left)
    simpa only [Nat.zero_add,
      show u + (n + left) = workWidth by omega,
      show u + n + left = workWidth by omega] using hs
  have hsplit₂ :
      selectedMajBackward left right workWidth endpointWidth
          (n + left) (n + left) =
        selectedMajBackward left right workWidth endpointWidth
            (right + 1) n ++
        selectedMajBackward left right workWidth endpointWidth left left := by
    have hs := selectedMajBackward_split left right workWidth endpointWidth
      0 n left
    simpa only [Nat.zero_add, hLn,
      show n + left = right + 1 by omega] using hs
  rw [hsplit₁, hsplit₂, habove, hinside, hbelow]
  simp only [n, u, List.append_assoc]

theorem selectedUmaForward_decompose
    {left right workWidth endpointWidth : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    selectedUmaForward left right workWidth endpointWidth 0 workWidth =
      Interval.disabledForward workWidth endpointWidth 0 left ++
      baseUmaForward workWidth endpointWidth left (right - left + 1) ++
      Interval.disabledForward workWidth endpointWidth (right + 1)
        (workWidth - (right + 1)) := by
  let n := right - left + 1
  let u := workWidth - (right + 1)
  have hLn : left + n = right + 1 := by
    dsimp [n]
    omega
  have hsum : left + n + u = workWidth := by
    dsimp [n, u]
    omega
  have hbelow := selectedUmaForward_below
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) left 0 (by omega)
  have hinside := selectedUmaForward_inside
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) n left (by omega) (by omega)
  have habove := selectedUmaForward_above
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) u (right + 1) (by omega)
  have hsplit₁ :
      selectedUmaForward left right workWidth endpointWidth 0 workWidth =
        selectedUmaForward left right workWidth endpointWidth 0 left ++
        selectedUmaForward left right workWidth endpointWidth left (n + u) := by
    have hs := selectedUmaForward_split left right workWidth endpointWidth
      0 left (n + u)
    rw [Nat.zero_add] at hs
    simpa only [show left + (n + u) = workWidth by omega] using hs
  have hsplit₂ :
      selectedUmaForward left right workWidth endpointWidth left (n + u) =
        selectedUmaForward left right workWidth endpointWidth left n ++
        selectedUmaForward left right workWidth endpointWidth
          (right + 1) u := by
    have hs := selectedUmaForward_split left right workWidth endpointWidth
      left n u
    simpa only [hLn] using hs
  rw [hsplit₁, hsplit₂, hbelow, hinside, habove]
  simp only [n, u, List.append_assoc]

theorem idealGates_act
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    actGates (idealGates left right workWidth endpointWidth) I =
      writeField
        (writeField I (Interval.targetOffset workWidth + left)
          (right - left + 1)
          (reverseBits (right - left + 1)
            ((reverseBits (right - left + 1)
                (readField I (Interval.targetOffset workWidth + left)
                  (right - left + 1)) +
              reverseBits (right - left + 1)
                (readField I (Interval.sourceOffset + left)
                  (right - left + 1)) +
              bitValue I (Interval.carryWire workWidth endpointWidth)) %
                2 ^ (right - left + 1))))
        (Interval.signWire workWidth endpointWidth) 1
          ((bitValue I (Interval.signWire workWidth endpointWidth) +
            (reverseBits (right - left + 1)
                (readField I (Interval.targetOffset workWidth + left)
                  (right - left + 1)) +
              reverseBits (right - left + 1)
                (readField I (Interval.sourceOffset + left)
                  (right - left + 1)) +
              bitValue I (Interval.carryWire workWidth endpointWidth)) /
                2 ^ (right - left + 1)) % 2) := by
  let width := right - left + 1
  let L := Interval.arithmeticLayout width
  let W := Interval.arithmeticWiring left workWidth endpointWidth
  let gathered := gatherBits (place L W) L.width I
  have hwidth : 0 < width := by
    dsimp [width]
    omega
  have hTarget : readField gathered 0 width =
      readField I (Interval.targetOffset workWidth + left) width := by
    have hr := readField_gatherBits L W 0 I
      (by simp [W, Interval.arithmeticWiring])
    simpa [gathered, L, W, Interval.arithmeticLayout,
      Interval.arithmeticWiring, Layout.offset, Layout.size] using hr
  have hSource : readField gathered width width =
      readField I (Interval.sourceOffset + left) width := by
    have hr := readField_gatherBits L W 1 I
      (by simp [W, Interval.arithmeticWiring])
    simpa [gathered, L, W, Interval.arithmeticLayout,
      Interval.arithmeticWiring, Layout.offset, Layout.size] using hr
  have hCarry : bitValue gathered (2 * width) =
      bitValue I (Interval.carryWire workWidth endpointWidth) := by
    rw [← readField_one, ← readField_one]
    have hr := readField_gatherBits L W 2 I
      (by simp [W, Interval.arithmeticWiring])
    simpa [gathered, L, W, Interval.arithmeticLayout,
      Interval.arithmeticWiring, Layout.offset, Layout.size,
      show width + width = 2 * width by omega] using hr
  have hSign : bitValue gathered (2 * width + 1) =
      bitValue I (Interval.signWire workWidth endpointWidth) := by
    rw [← readField_one, ← readField_one]
    have hr := readField_gatherBits L W 3 I
      (by simp [W, Interval.arithmeticWiring])
    simpa [gathered, L, W, Interval.arithmeticLayout,
      Interval.arithmeticWiring, Layout.offset, Layout.size,
      show width + (width + 1) = 2 * width + 1 by omega] using hr
  change actGates
      ((SerialBigEndian.gates width).map
        (RGate.map (place L W))) I = _
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 0) (k₂ := 3)
      (v₁ := reverseBits width
        ((reverseBits width
            (readField I (Interval.targetOffset workWidth + left) width) +
          reverseBits width
            (readField I (Interval.sourceOffset + left) width) +
          bitValue I (Interval.carryWire workWidth endpointWidth)) %
            2 ^ width))
      (v₂ := (bitValue I (Interval.signWire workWidth endpointWidth) +
        (reverseBits width
            (readField I (Interval.targetOffset workWidth + left) width) +
          reverseBits width
            (readField I (Interval.sourceOffset + left) width) +
          bitValue I (Interval.carryWire workWidth endpointWidth)) /
            2 ^ width) % 2)
      (Interval.arithmetic_disjoint hLR hR)
      (by simp [L, W, Interval.arithmeticLayout,
        Interval.arithmeticWiring])
      (by simp [L, Interval.arithmeticLayout])
      (by simp [L, Interval.arithmeticLayout])
      (by decide)
  · intro g hg
    simpa [L, Interval.arithmeticLayout, Layout.width,
      SerialBigEndian.circuit,
      show width + (width + 2) = 2 * width + 2 by omega] using
      RCircuit.wellFormed_mem
        (SerialBigEndian.circuit_wellFormed width) hg
  · have hlocal := SerialBigEndian.gates_act
      (width := width) (i := gathered) hwidth
      (by simpa [gathered, L, Interval.arithmeticLayout, Layout.width,
          show width + (width + 2) = 2 * width + 2 by omega] using
          gatherBits_lt (place L W) L.width I)
    rw [hlocal, hTarget, hSource, hCarry, hSign]
    simp [gathered, L, Interval.arithmeticLayout, Layout.write,
      Layout.offset, Layout.size,
      show width + (width + 1) = 2 * width + 1 by omega]

theorem idealGates_preserves_carry
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    bitValue (actGates
        (idealGates left right workWidth endpointWidth) I)
        (Interval.carryWire workWidth endpointWidth) =
      bitValue I (Interval.carryWire workWidth endpointWidth) := by
  rw [idealGates_act hLR hR]
  rw [bitValue_write_ne (by
      simp [Interval.carryWire, Interval.signWire, Interval.outerWire]),
    bitValue_write_out (by
      simp [Interval.targetOffset, Interval.carryWire,
        Interval.outerWire]
      omega)]

theorem activeGates_preserves_carry
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    bitValue (actGates
        (activeGates left right workWidth endpointWidth) I)
        (Interval.carryWire workWidth endpointWidth) =
      bitValue I (Interval.carryWire workWidth endpointWidth) := by
  rw [activeGates_eq_ideal hLR hR,
    idealGates_preserves_carry hLR hR]

theorem disabledBackward_forward_cancel
    {j m workWidth endpointWidth I : Nat}
    (hbound : j + m ≤ workWidth) :
    actGates (Interval.disabledForward workWidth endpointWidth j m)
        (actGates
          (Interval.disabledBackward workWidth endpointWidth (j + m) m) I) =
      I := by
  induction m generalizing I with
  | zero => rfl
  | succ m ih =>
      rw [Interval.disabledForward_snoc, actGates_append]
      have htop : j + (m + 1) - 1 = j + m := by omega
      rw [show Interval.disabledBackward workWidth endpointWidth
          (j + (m + 1)) (m + 1) =
        Interval.disabledAt (j + m) workWidth endpointWidth ++
          Interval.disabledBackward workWidth endpointWidth (j + m) m by
        simp [Interval.disabledBackward, htop]]
      simp only [actGates_append]
      rw [ih (I := actGates
          (Interval.disabledAt (j + m) workWidth endpointWidth) I)
          (by omega),
        Interval.disabledAt_involutive (by omega)]

theorem disabledForward_sign_comm
    {m j workWidth endpointWidth I : Nat}
    (hbound : j + m ≤ workWidth) :
    actGates [.cx (Interval.carryWire workWidth endpointWidth)
        (Interval.signWire workWidth endpointWidth)]
        (actGates
          (Interval.disabledForward workWidth endpointWidth j m) I) =
      actGates (Interval.disabledForward workWidth endpointWidth j m)
        (actGates [.cx (Interval.carryWire workWidth endpointWidth)
          (Interval.signWire workWidth endpointWidth)] I) := by
  induction m generalizing j I with
  | zero => rfl
  | succ m ih =>
      simp only [Interval.disabledForward, actGates_append]
      rw [ih (j := j + 1)
          (I := actGates
            (Interval.disabledAt j workWidth endpointWidth) I) (by omega),
        Interval.disabledAt_sign_comm (by omega)]

theorem disabled_reverse_sign_sandwich
    {j m workWidth endpointWidth I : Nat}
    (hbound : j + m ≤ workWidth) :
    actGates
        (Interval.disabledBackward workWidth endpointWidth (j + m) m ++
          [.cx (Interval.carryWire workWidth endpointWidth)
            (Interval.signWire workWidth endpointWidth)] ++
          Interval.disabledForward workWidth endpointWidth j m) I =
      actGates [.cx (Interval.carryWire workWidth endpointWidth)
        (Interval.signWire workWidth endpointWidth)] I := by
  simp only [actGates_append]
  rw [← disabledForward_sign_comm
      (m := m) (j := j)
      (I := actGates
        (Interval.disabledBackward workWidth endpointWidth (j + m) m) I)
      hbound,
    disabledBackward_forward_cancel hbound]

theorem selectedGates_eq_active_of_carry
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth)
    (hcarry : bitValue I
      (Interval.carryWire workWidth endpointWidth) = 0)
    (hfinal : bitValue
      (actGates (activeGates left right workWidth endpointWidth) I)
        (Interval.carryWire workWidth endpointWidth) = 0) :
    actGates (selectedGates left right workWidth endpointWidth) I =
      actGates (activeGates left right workWidth endpointWidth) I := by
  let n := right - left + 1
  let u := workWidth - (right + 1)
  let highBackward := Interval.disabledBackward workWidth endpointWidth
    workWidth u
  let maj := baseMajBackward workWidth endpointWidth (right + 1) n
  let lowBackward := Interval.disabledBackward workWidth endpointWidth left left
  let sign : List RGate := [.cx
    (Interval.carryWire workWidth endpointWidth)
    (Interval.signWire workWidth endpointWidth)]
  let lowForward := Interval.disabledForward workWidth endpointWidth 0 left
  let uma := baseUmaForward workWidth endpointWidth left n
  let highForward := Interval.disabledForward workWidth endpointWidth
    (right + 1) u
  have hfirst := selectedMajBackward_decompose
    (endpointWidth := endpointWidth) hLR hR
  have hsecond := selectedUmaForward_decompose
    (endpointWidth := endpointWidth) hLR hR
  change selectedMajBackward left right workWidth endpointWidth
      workWidth workWidth =
    highBackward ++ maj ++ lowBackward at hfirst
  change selectedUmaForward left right workWidth endpointWidth 0 workWidth =
    lowForward ++ uma ++ highForward at hsecond
  have hhigh := Interval.disabledBackward_identity_of_carry_clear
    (workWidth := workWidth) (endpointWidth := endpointWidth)
    (I := I) u workWidth hcarry
  change actGates highBackward I = I at hhigh
  have hlow := disabled_reverse_sign_sandwich
    (j := 0) (m := left) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (I := actGates maj I) (by omega)
  have hlow' : actGates (lowBackward ++ sign ++ lowForward)
      (actGates maj I) = actGates sign (actGates maj I) := by
    simpa [lowBackward, sign, lowForward] using hlow
  have hlowNested :
      actGates lowForward
          (actGates sign (actGates lowBackward (actGates maj I))) =
        actGates sign (actGates maj I) := by
    simpa only [actGates_append] using hlow'
  have hactive :
      actGates (activeGates left right workWidth endpointWidth) I =
        actGates uma (actGates sign (actGates maj I)) := by
    dsimp [activeGates, n, maj, sign, uma]
    simp only [actGates_append]
  have hhighForward := Interval.disabledForward_identity_of_carry_clear
    (workWidth := workWidth) (endpointWidth := endpointWidth)
    (I := actGates uma (actGates sign (actGates maj I)))
    u (right + 1) (by
      rw [← hactive]
      exact hfinal)
  change actGates highForward
      (actGates uma (actGates sign (actGates maj I))) =
    actGates uma (actGates sign (actGates maj I)) at hhighForward
  simp only [selectedGates, hfirst, hsecond, actGates_append]
  rw [hhigh, hlowNested, hhighForward]
  exact hactive.symm

theorem selectedMajBackward_writeAccumulator
    {left right workWidth endpointWidth I v : Nat} : ∀ m top,
    m ≤ top → top ≤ workWidth →
    actGates
        (selectedMajBackward left right workWidth endpointWidth top m)
        (writeField I (Interval.accumulatorWire workWidth endpointWidth) 1 v) =
      writeField
        (actGates
          (selectedMajBackward left right workWidth endpointWidth top m) I)
        (Interval.accumulatorWire workWidth endpointWidth) 1 v := by
  intro m
  induction m generalizing I with
  | zero => intro top _ _; rfl
  | succ m ih =>
      intro top hmt htop
      simp only [selectedMajBackward, actGates_append]
      rw [Interval.selectedMajAt_writeAccumulator (by omega),
        ih (top := top - 1) (by omega) (by omega)]

theorem selectedUmaForward_writeAccumulator
    {left right workWidth endpointWidth I v : Nat} : ∀ m j,
    j + m ≤ workWidth →
    actGates
        (selectedUmaForward left right workWidth endpointWidth j m)
        (writeField I (Interval.accumulatorWire workWidth endpointWidth) 1 v) =
      writeField
        (actGates
          (selectedUmaForward left right workWidth endpointWidth j m) I)
        (Interval.accumulatorWire workWidth endpointWidth) 1 v := by
  intro m
  induction m generalizing I with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [selectedUmaForward, actGates_append]
      rw [Interval.selectedUmaAt_writeAccumulator (by omega),
        ih (j := j + 1) (by omega)]

theorem fixedFirstStep_act
    {left right j workWidth endpointWidth I : Nat}
    (hLR : left ≤ right)
    (hj : j < workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) =
        Interval.scanAccumulator left right (j + 1)) :
    actGates
        (Interval.fixedToggle right j workWidth endpointWidth ++
          Interval.majAt j workWidth endpointWidth ++
          Interval.fixedToggle left j workWidth endpointWidth) I =
      writeField
        (actGates
          (Interval.selectedMajAt left right j workWidth endpointWidth) I)
        (Interval.accumulatorWire workWidth endpointWidth) 1
        (Interval.scanAccumulator left right j) := by
  let active := if left ≤ j ∧ j ≤ right then 1 else 0
  let i₁ := actGates
    (Interval.fixedToggle right j workWidth endpointWidth) I
  have hi₁ : i₁ = writeField I
      (Interval.accumulatorWire workWidth endpointWidth) 1 active := by
    rw [show i₁ = actGates
      (Interval.fixedToggle right j workWidth endpointWidth) I from rfl,
      Interval.fixedToggle_act, hacc,
      Interval.scanAccumulator_right_reverse hLR]
  have hs₁ : Interval.Stable left right workWidth endpointWidth i₁ :=
    Interval.fixedToggle_preserves_stable h
  have hcell : actGates
      (Interval.majAt j workWidth endpointWidth) i₁ =
    actGates
      (Interval.selectedMajAt left right j workWidth endpointWidth) i₁ := by
    rw [Interval.majAt_reduces hj hs₁.cellScratchClear]
    by_cases hselected : left ≤ j ∧ j ≤ right
    · have htest : i₁.testBit
          (Interval.accumulatorWire workWidth endpointWidth) = true := by
        rw [hi₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp [active, hselected]
      rw [if_pos htest]
      simp [Interval.selectedMajAt, hselected]
    · have htest : i₁.testBit
          (Interval.accumulatorWire workWidth endpointWidth) = false := by
        rw [hi₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp [active, hselected]
      have hnot : ¬i₁.testBit
          (Interval.accumulatorWire workWidth endpointWidth) = true := by
        rw [htest]
        decide
      rw [if_neg hnot]
      simp [Interval.selectedMajAt, hselected]
  let i₂ := actGates (Interval.majAt j workWidth endpointWidth) i₁
  have hi₂ : i₂ = writeField
      (actGates
        (Interval.selectedMajAt left right j workWidth endpointWidth) I)
      (Interval.accumulatorWire workWidth endpointWidth) 1 active := by
    rw [show i₂ = actGates
        (Interval.majAt j workWidth endpointWidth) i₁ from rfl,
      hcell, hi₁, Interval.selectedMajAt_writeAccumulator hj]
  have hactive : active < 2 := by
    dsimp [active]
    by_cases hselected : left ≤ j ∧ j ≤ right <;> simp [hselected]
  simp only [actGates_append]
  change actGates
    (Interval.fixedToggle left j workWidth endpointWidth) i₂ = _
  rw [Interval.fixedToggle_act, hi₂, bitValue_write_self,
    Nat.mod_eq_of_lt hactive, Interval.scanAccumulator_left_reverse hLR,
    writeField_writeField]

theorem fixedSecondStep_act
    {left right j workWidth endpointWidth I : Nat}
    (hLR : left ≤ right)
    (hj : j < workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) =
        Interval.scanAccumulator left right j) :
    actGates
        (Interval.fixedToggle left j workWidth endpointWidth ++
          Interval.umaAt j workWidth endpointWidth ++
          Interval.fixedToggle right j workWidth endpointWidth) I =
      writeField
        (actGates
          (Interval.selectedUmaAt left right j workWidth endpointWidth) I)
        (Interval.accumulatorWire workWidth endpointWidth) 1
        (Interval.scanAccumulator left right (j + 1)) := by
  let active := if left ≤ j ∧ j ≤ right then 1 else 0
  let i₁ := actGates
    (Interval.fixedToggle left j workWidth endpointWidth) I
  have hi₁ : i₁ = writeField I
      (Interval.accumulatorWire workWidth endpointWidth) 1 active := by
    rw [show i₁ = actGates
      (Interval.fixedToggle left j workWidth endpointWidth) I from rfl,
      Interval.fixedToggle_act, hacc,
      Interval.scanAccumulator_left hLR]
  have hs₁ : Interval.Stable left right workWidth endpointWidth i₁ :=
    Interval.fixedToggle_preserves_stable h
  have hcell : actGates
      (Interval.umaAt j workWidth endpointWidth) i₁ =
    actGates
      (Interval.selectedUmaAt left right j workWidth endpointWidth) i₁ := by
    rw [Interval.umaAt_reduces hj hs₁.cellScratchClear]
    by_cases hselected : left ≤ j ∧ j ≤ right
    · have htest : i₁.testBit
          (Interval.accumulatorWire workWidth endpointWidth) = true := by
        rw [hi₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp [active, hselected]
      rw [if_pos htest]
      simp [Interval.selectedUmaAt, hselected]
    · have htest : i₁.testBit
          (Interval.accumulatorWire workWidth endpointWidth) = false := by
        rw [hi₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp [active, hselected]
      have hnot : ¬i₁.testBit
          (Interval.accumulatorWire workWidth endpointWidth) = true := by
        rw [htest]
        decide
      rw [if_neg hnot]
      simp [Interval.selectedUmaAt, hselected]
  let i₂ := actGates (Interval.umaAt j workWidth endpointWidth) i₁
  have hi₂ : i₂ = writeField
      (actGates
        (Interval.selectedUmaAt left right j workWidth endpointWidth) I)
      (Interval.accumulatorWire workWidth endpointWidth) 1 active := by
    rw [show i₂ = actGates
        (Interval.umaAt j workWidth endpointWidth) i₁ from rfl,
      hcell, hi₁, Interval.selectedUmaAt_writeAccumulator hj]
  have hactive : active < 2 := by
    dsimp [active]
    by_cases hselected : left ≤ j ∧ j ≤ right <;> simp [hselected]
  simp only [actGates_append]
  change actGates
    (Interval.fixedToggle right j workWidth endpointWidth) i₂ = _
  rw [Interval.fixedToggle_act, hi₂, bitValue_write_self,
    Nat.mod_eq_of_lt hactive, Interval.scanAccumulator_right hLR,
    writeField_writeField]

theorem fixedFirstScan_act
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right)
    (h : Interval.Stable left right workWidth endpointWidth I) :
    ∀ m top, m ≤ top → top ≤ workWidth →
    bitValue I (Interval.accumulatorWire workWidth endpointWidth) =
      Interval.scanAccumulator left right top →
    actGates
        (fixedFirstScan left right workWidth endpointWidth top m) I =
      writeField
        (actGates
          (selectedMajBackward left right workWidth endpointWidth top m) I)
        (Interval.accumulatorWire workWidth endpointWidth) 1
        (Interval.scanAccumulator left right (top - m)) := by
  intro m
  induction m generalizing I with
  | zero =>
      intro top _ _ hacc
      rw [fixedFirstScan, selectedMajBackward, actGates_nil,
        Nat.sub_zero, ← hacc, ← readField_one, writeField_read]
  | succ m ih =>
      intro top hmt htop hacc
      let j := top - 1
      let stepGates :=
        Interval.fixedToggle right j workWidth endpointWidth ++
          Interval.majAt j workWidth endpointWidth ++
          Interval.fixedToggle left j workWidth endpointWidth
      let stepState := actGates stepGates I
      have hstep : stepState = writeField
          (actGates
            (Interval.selectedMajAt left right j workWidth endpointWidth) I)
          (Interval.accumulatorWire workWidth endpointWidth) 1
          (Interval.scanAccumulator left right j) := by
        apply fixedFirstStep_act hLR (by omega) h
        have hjtop : j + 1 = top := by
          dsimp [j]
          omega
        rw [hjtop]
        exact hacc
      have hsStep : Interval.Stable left right workWidth endpointWidth
          stepState := by
        dsimp [stepState, stepGates]
        simp only [actGates_append]
        exact Interval.fixedToggle_preserves_stable
          (Interval.majAt_preserves_stable (by omega)
            (Interval.fixedToggle_preserves_stable h))
      have hscan : Interval.scanAccumulator left right j < 2 := by
        unfold Interval.scanAccumulator
        by_cases hs : left < j ∧ j ≤ right <;> simp [hs]
      have haccStep : bitValue stepState
          (Interval.accumulatorWire workWidth endpointWidth) =
          Interval.scanAccumulator left right j := by
        rw [hstep, bitValue_write_self, Nat.mod_eq_of_lt hscan]
      rw [show fixedFirstScan left right workWidth endpointWidth top (m + 1) =
          stepGates ++ fixedFirstScan left right workWidth endpointWidth j m
        from rfl,
        actGates_append,
        ih hsStep j (by omega) (by omega) haccStep,
        hstep,
        selectedMajBackward_writeAccumulator
          (m := m) (top := j) (by omega) (by omega),
        show selectedMajBackward left right workWidth endpointWidth
            top (m + 1) =
          Interval.selectedMajAt left right j workWidth endpointWidth ++
            selectedMajBackward left right workWidth endpointWidth j m
          from rfl,
        actGates_append,
        writeField_writeField]
      congr 2
      omega

theorem fixedSecondScan_act
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right)
    (h : Interval.Stable left right workWidth endpointWidth I) :
    ∀ m j, j + m ≤ workWidth →
    bitValue I (Interval.accumulatorWire workWidth endpointWidth) =
      Interval.scanAccumulator left right j →
    actGates
        (fixedSecondScan left right workWidth endpointWidth j m) I =
      writeField
        (actGates
          (selectedUmaForward left right workWidth endpointWidth j m) I)
        (Interval.accumulatorWire workWidth endpointWidth) 1
        (Interval.scanAccumulator left right (j + m)) := by
  intro m
  induction m generalizing I with
  | zero =>
      intro j _ hacc
      rw [fixedSecondScan, selectedUmaForward, actGates_nil, Nat.add_zero,
        ← hacc, ← readField_one, writeField_read]
  | succ m ih =>
      intro j hbound hacc
      let stepGates :=
        Interval.fixedToggle left j workWidth endpointWidth ++
          Interval.umaAt j workWidth endpointWidth ++
          Interval.fixedToggle right j workWidth endpointWidth
      let stepState := actGates stepGates I
      have hstep : stepState = writeField
          (actGates
            (Interval.selectedUmaAt left right j workWidth endpointWidth) I)
          (Interval.accumulatorWire workWidth endpointWidth) 1
          (Interval.scanAccumulator left right (j + 1)) := by
        exact fixedSecondStep_act hLR (by omega) h hacc
      have hsStep : Interval.Stable left right workWidth endpointWidth
          stepState := by
        dsimp [stepState, stepGates]
        simp only [actGates_append]
        exact Interval.fixedToggle_preserves_stable
          (Interval.umaAt_preserves_stable (by omega)
            (Interval.fixedToggle_preserves_stable h))
      have hscan : Interval.scanAccumulator left right (j + 1) < 2 := by
        unfold Interval.scanAccumulator
        by_cases hs : left < j + 1 ∧ j + 1 ≤ right <;> simp [hs]
      have haccStep : bitValue stepState
          (Interval.accumulatorWire workWidth endpointWidth) =
          Interval.scanAccumulator left right (j + 1) := by
        rw [hstep, bitValue_write_self, Nat.mod_eq_of_lt hscan]
      rw [show fixedSecondScan left right workWidth endpointWidth j (m + 1) =
          stepGates ++
            fixedSecondScan left right workWidth endpointWidth (j + 1) m
        from rfl,
        actGates_append,
        ih hsStep (j + 1) (by omega) haccStep,
        hstep,
        selectedUmaForward_writeAccumulator
          (m := m) (j := j + 1) (by omega),
        show selectedUmaForward left right workWidth endpointWidth j (m + 1) =
          Interval.selectedUmaAt left right j workWidth endpointWidth ++
            selectedUmaForward left right workWidth endpointWidth (j + 1) m
          from rfl,
        actGates_append,
        writeField_writeField]
      congr 2
      omega

theorem selectedMajBackward_preserves_stable
    {left right workWidth endpointWidth I : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I) :
    ∀ m top, m ≤ top → top ≤ workWidth →
    Interval.Stable left right workWidth endpointWidth
      (actGates
        (selectedMajBackward left right workWidth endpointWidth top m) I) := by
  intro m
  induction m generalizing I with
  | zero => intro top _ _; exact h
  | succ m ih =>
      intro top hmt htop
      simp only [selectedMajBackward, actGates_append]
      exact ih
        (Interval.selectedMajAt_preserves_stable (by omega) h)
        (top - 1) (by omega) (by omega)

theorem selectedUmaForward_preserves_stable
    {left right workWidth endpointWidth I : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I) :
    ∀ m j, j + m ≤ workWidth →
    Interval.Stable left right workWidth endpointWidth
      (actGates
        (selectedUmaForward left right workWidth endpointWidth j m) I) := by
  intro m
  induction m generalizing I with
  | zero => intro j _; exact h
  | succ m ih =>
      intro j hbound
      simp only [selectedUmaForward, actGates_append]
      exact ih
        (Interval.selectedUmaAt_preserves_stable (by omega) h)
        (j + 1) (by omega)

theorem fixedFirstScan_preserves_stable
    {left right workWidth endpointWidth I : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I) :
    ∀ m top, m ≤ top → top ≤ workWidth →
    Interval.Stable left right workWidth endpointWidth
      (actGates
        (fixedFirstScan left right workWidth endpointWidth top m) I) := by
  intro m
  induction m generalizing I with
  | zero => intro top _ _; exact h
  | succ m ih =>
      intro top hmt htop
      simp only [fixedFirstScan, actGates_append]
      exact ih
        (Interval.fixedToggle_preserves_stable
          (Interval.majAt_preserves_stable (by omega)
            (Interval.fixedToggle_preserves_stable h)))
        (top - 1) (by omega) (by omega)

theorem fixedSecondScan_preserves_stable
    {left right workWidth endpointWidth I : Nat}
    (h : Interval.Stable left right workWidth endpointWidth I) :
    ∀ m j, j + m ≤ workWidth →
    Interval.Stable left right workWidth endpointWidth
      (actGates
        (fixedSecondScan left right workWidth endpointWidth j m) I) := by
  intro m
  induction m generalizing I with
  | zero => intro j _; exact h
  | succ m ih =>
      intro j hbound
      simp only [fixedSecondScan, actGates_append]
      exact ih
        (Interval.fixedToggle_preserves_stable
          (Interval.umaAt_preserves_stable (by omega)
            (Interval.fixedToggle_preserves_stable h)))
        (j + 1) (by omega)

theorem fixedGates_eq_selected
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right)
    (hR : right < workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0) :
    actGates (fixedGates left right workWidth endpointWidth) I =
      actGates (selectedGates left right workWidth endpointWidth) I := by
  let firstSelected :=
    selectedMajBackward left right workWidth endpointWidth workWidth workWidth
  have hIclear : writeField I
      (Interval.accumulatorWire workWidth endpointWidth) 1 0 = I := by
    rw [show 0 = bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) from hacc.symm,
      ← readField_one, writeField_read]
  have hfirstWrite := selectedMajBackward_writeAccumulator
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (I := I) (v := 0)
    workWidth workWidth (by omega) (by omega)
  change actGates firstSelected
      (writeField I (Interval.accumulatorWire workWidth endpointWidth) 1 0) =
    writeField (actGates firstSelected I)
      (Interval.accumulatorWire workWidth endpointWidth) 1 0 at hfirstWrite
  rw [hIclear] at hfirstWrite
  have hfirst := fixedFirstScan_act hLR h workWidth workWidth
    (by omega) (by omega) (by
      rw [hacc, Interval.scanAccumulator_width hR])
  simp only [Nat.sub_self] at hfirst
  change actGates
      (fixedFirstScan left right workWidth endpointWidth
        workWidth workWidth) I =
    writeField (actGates firstSelected I)
      (Interval.accumulatorWire workWidth endpointWidth) 1
      (Interval.scanAccumulator left right 0) at hfirst
  rw [Interval.scanAccumulator_zero, ← hfirstWrite] at hfirst
  let i₁ := actGates firstSelected I
  have hs₁ : Interval.Stable left right workWidth endpointWidth i₁ :=
    selectedMajBackward_preserves_stable h workWidth workWidth
      (by omega) (by omega)
  have hi₁acc : bitValue i₁
      (Interval.accumulatorWire workWidth endpointWidth) = 0 := by
    have hb := congrArg
      (fun J => bitValue J
        (Interval.accumulatorWire workWidth endpointWidth)) hfirstWrite
    rw [bitValue_write_self] at hb
    simpa using hb
  let i₂ := actGates
    [.cx (Interval.carryWire workWidth endpointWidth)
      (Interval.signWire workWidth endpointWidth)] i₁
  have hs₂ : Interval.Stable left right workWidth endpointWidth i₂ :=
    Interval.signGate_preserves_stable hs₁
  have hi₂acc : bitValue i₂
      (Interval.accumulatorWire workWidth endpointWidth) = 0 := by
    rw [show i₂ = actGates
      [.cx (Interval.carryWire workWidth endpointWidth)
        (Interval.signWire workWidth endpointWidth)] i₁ from rfl,
      actGates_cons, actGates_nil, act_cx_write,
      bitValue_write_ne (by
        simp [Interval.signWire, Interval.accumulatorWire,
          Interval.outerWire])]
    exact hi₁acc
  let secondSelected :=
    selectedUmaForward left right workWidth endpointWidth 0 workWidth
  have hi₂clear : writeField i₂
      (Interval.accumulatorWire workWidth endpointWidth) 1 0 = i₂ := by
    rw [show 0 = bitValue i₂
      (Interval.accumulatorWire workWidth endpointWidth) from hi₂acc.symm,
      ← readField_one, writeField_read]
  have hsecondWrite := selectedUmaForward_writeAccumulator
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (I := i₂) (v := 0)
    workWidth 0 (by omega)
  change actGates secondSelected
      (writeField i₂ (Interval.accumulatorWire workWidth endpointWidth) 1 0) =
    writeField (actGates secondSelected i₂)
      (Interval.accumulatorWire workWidth endpointWidth) 1 0 at hsecondWrite
  rw [hi₂clear] at hsecondWrite
  have hsecond := fixedSecondScan_act hLR hs₂ workWidth 0
    (by omega) (by rw [hi₂acc, Interval.scanAccumulator_zero])
  simp only [Nat.zero_add] at hsecond
  change actGates
      (fixedSecondScan left right workWidth endpointWidth 0 workWidth) i₂ =
    writeField (actGates secondSelected i₂)
      (Interval.accumulatorWire workWidth endpointWidth) 1
      (Interval.scanAccumulator left right workWidth) at hsecond
  rw [Interval.scanAccumulator_width hR, ← hsecondWrite] at hsecond
  simp only [fixedGates, selectedGates, actGates_append]
  rw [hfirst]
  change actGates
      (fixedSecondScan left right workWidth endpointWidth 0 workWidth) i₂ = _
  exact hsecond

theorem firstScan_eq_fixed
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (h : Interval.Stable left right workWidth endpointWidth I) :
    ∀ m top, m ≤ top → top ≤ workWidth →
    actGates (firstScan workWidth endpointWidth top m) I =
      actGates
        (fixedFirstScan left right workWidth endpointWidth top m) I := by
  intro m
  induction m generalizing I with
  | zero => intro top _ _; rfl
  | succ m ih =>
      intro top hmt htop
      let j := top - 1
      simp only [firstScan, fixedFirstScan, actGates_append]
      have hright := Interval.rightToggle_eq_fixed
        (j := j) (workWidth := workWidth)
        (endpointWidth := endpointWidth) (I := I) (by omega) h
      rw [hright]
      let i₁ := actGates
        (Interval.fixedToggle right j workWidth endpointWidth) I
      have hs₁ : Interval.Stable left right workWidth endpointWidth i₁ :=
        Interval.fixedToggle_preserves_stable h
      let i₂ := actGates (Interval.majAt j workWidth endpointWidth) i₁
      have hs₂ : Interval.Stable left right workWidth endpointWidth i₂ :=
        Interval.majAt_preserves_stable (by omega) hs₁
      have hleft := Interval.leftToggle_eq_fixed
        (j := j) (workWidth := workWidth)
        (endpointWidth := endpointWidth) (I := i₂) (by omega) hs₂
      change actGates (firstScan workWidth endpointWidth j m)
          (actGates (Interval.leftToggle j workWidth endpointWidth) i₂) = _
      rw [hleft]
      have hs₃ : Interval.Stable left right workWidth endpointWidth
          (actGates
            (Interval.fixedToggle left j workWidth endpointWidth) i₂) :=
        Interval.fixedToggle_preserves_stable hs₂
      exact ih hs₃ j (by omega) (by omega)

theorem secondScan_eq_fixed
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (h : Interval.Stable left right workWidth endpointWidth I) :
    ∀ m j, j + m ≤ workWidth →
    actGates (secondScan workWidth endpointWidth j m) I =
      actGates
        (fixedSecondScan left right workWidth endpointWidth j m) I := by
  intro m
  induction m generalizing I with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [secondScan, fixedSecondScan, actGates_append]
      have hleft := Interval.leftToggle_eq_fixed
        (j := j) (workWidth := workWidth)
        (endpointWidth := endpointWidth) (I := I) (by omega) h
      rw [hleft]
      let i₁ := actGates
        (Interval.fixedToggle left j workWidth endpointWidth) I
      have hs₁ : Interval.Stable left right workWidth endpointWidth i₁ :=
        Interval.fixedToggle_preserves_stable h
      let i₂ := actGates (Interval.umaAt j workWidth endpointWidth) i₁
      have hs₂ : Interval.Stable left right workWidth endpointWidth i₂ :=
        Interval.umaAt_preserves_stable (by omega) hs₁
      have hright := Interval.rightToggle_eq_fixed
        (j := j) (workWidth := workWidth)
        (endpointWidth := endpointWidth) (I := i₂) (by omega) hs₂
      change actGates (secondScan workWidth endpointWidth (j + 1) m)
          (actGates (Interval.rightToggle j workWidth endpointWidth) i₂) = _
      rw [hright]
      have hs₃ : Interval.Stable left right workWidth endpointWidth
          (actGates
            (Interval.fixedToggle right j workWidth endpointWidth) i₂) :=
        Interval.fixedToggle_preserves_stable hs₂
      exact ih hs₃ (j + 1) (by omega)

theorem gates_eq_fixed
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (h : Interval.Stable left right workWidth endpointWidth I) :
    actGates (gates workWidth endpointWidth) I =
      actGates (fixedGates left right workWidth endpointWidth) I := by
  simp only [gates, fixedGates, actGates_append]
  have hfirst := firstScan_eq_fixed hwidth h workWidth workWidth
    (by omega) (by omega)
  rw [hfirst]
  let i₁ := actGates
    (fixedFirstScan left right workWidth endpointWidth
      workWidth workWidth) I
  have hs₁ : Interval.Stable left right workWidth endpointWidth i₁ :=
    fixedFirstScan_preserves_stable h workWidth workWidth
      (by omega) (by omega)
  let i₂ := actGates
    [.cx (Interval.carryWire workWidth endpointWidth)
      (Interval.signWire workWidth endpointWidth)] i₁
  have hs₂ : Interval.Stable left right workWidth endpointWidth i₂ :=
    Interval.signGate_preserves_stable hs₁
  have hsecond := secondScan_eq_fixed hwidth hs₂ workWidth 0 (by omega)
  change actGates (secondScan workWidth endpointWidth 0 workWidth) i₂ = _
  exact hsecond

theorem gates_eq_selected
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (hLR : left ≤ right)
    (hR : right < workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0) :
    actGates (gates workWidth endpointWidth) I =
      actGates (selectedGates left right workWidth endpointWidth) I := by
  rw [gates_eq_fixed hwidth h,
    fixedGates_eq_selected hLR hR h hacc]

theorem gates_act
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (hLR : left ≤ right) (hR : right < workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hcarry : bitValue I
      (Interval.carryWire workWidth endpointWidth) = 0) :
    actGates (gates workWidth endpointWidth) I =
      writeField
        (writeField I (Interval.targetOffset workWidth + left)
          (right - left + 1)
          (reverseBits (right - left + 1)
            ((reverseBits (right - left + 1)
                (readField I (Interval.targetOffset workWidth + left)
                  (right - left + 1)) +
              reverseBits (right - left + 1)
                (readField I (Interval.sourceOffset + left)
                  (right - left + 1)) +
              bitValue I (Interval.carryWire workWidth endpointWidth)) %
                2 ^ (right - left + 1))))
        (Interval.signWire workWidth endpointWidth) 1
          ((bitValue I (Interval.signWire workWidth endpointWidth) +
            (reverseBits (right - left + 1)
                (readField I (Interval.targetOffset workWidth + left)
                  (right - left + 1)) +
              reverseBits (right - left + 1)
                (readField I (Interval.sourceOffset + left)
                  (right - left + 1)) +
              bitValue I (Interval.carryWire workWidth endpointWidth)) /
                2 ^ (right - left + 1)) % 2) := by
  have hactiveCarry : bitValue
      (actGates (activeGates left right workWidth endpointWidth) I)
        (Interval.carryWire workWidth endpointWidth) = 0 := by
    rw [activeGates_preserves_carry hLR hR, hcarry]
  rw [gates_eq_selected hwidth hLR hR h hacc,
    selectedGates_eq_active_of_carry hLR hR hcarry hactiveCarry,
    activeGates_eq_ideal hLR hR,
    idealGates_act hLR hR]

theorem firstScan_wellFormed (workWidth endpointWidth : Nat) :
    ∀ m top, m ≤ top → top ≤ workWidth →
    (firstScan workWidth endpointWidth top m).all
      (RGate.wellFormed
        (Interval.layout workWidth endpointWidth).width) = true := by
  intro m
  induction m with
  | zero => intro top _ _; rfl
  | succ m ih =>
      intro top hmt htop
      simp only [firstScan, List.all_append, Bool.and_eq_true]
      exact ⟨⟨⟨Interval.endpointGates_wellFormed
          (Or.inr rfl) (Or.inr rfl),
        Interval.majAt_wellFormed (by omega)⟩,
        Interval.endpointGates_wellFormed (Or.inl rfl) (Or.inl rfl)⟩,
        ih (top - 1) (by omega) (by omega)⟩

theorem secondScan_wellFormed (workWidth endpointWidth : Nat) :
    ∀ m j, j + m ≤ workWidth →
    (secondScan workWidth endpointWidth j m).all
      (RGate.wellFormed
        (Interval.layout workWidth endpointWidth).width) = true := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [secondScan, List.all_append, Bool.and_eq_true]
      exact ⟨⟨⟨Interval.endpointGates_wellFormed
          (Or.inl rfl) (Or.inl rfl),
        Interval.umaAt_wellFormed (by omega)⟩,
        Interval.endpointGates_wellFormed (Or.inr rfl) (Or.inr rfl)⟩,
        ih (j + 1) (by omega)⟩

theorem circuit_wellFormed (workWidth endpointWidth : Nat) :
    (circuit workWidth endpointWidth).wellFormed = true := by
  change (gates workWidth endpointWidth).all
    (RGate.wellFormed
      (Interval.layout workWidth endpointWidth).width) = true
  simp only [gates, List.all_append, Bool.and_eq_true]
  refine ⟨⟨firstScan_wellFormed workWidth endpointWidth
      workWidth workWidth (by omega) (by omega), ?_⟩,
    secondScan_wellFormed workWidth endpointWidth workWidth 0 (by omega)⟩
  simp [RGate.wellFormed, Interval.layout_width, Interval.carryWire,
    Interval.signWire, Interval.outerWire]
  omega

theorem gates_reverse_forward (workWidth endpointWidth I : Nat) :
    actGates (gates workWidth endpointWidth).reverse
        (actGates (gates workWidth endpointWidth) I) = I := by
  exact actGates_reverse
    (w := (circuit workWidth endpointWidth).width)
    (circuit_wellFormed workWidth endpointWidth) I

theorem firstScan_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (Interval.outerWire workWidth endpointWidth) = false)
    (hcarry : bitValue I
      (Interval.carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I
      (Interval.leftFlagWire workWidth endpointWidth) = 0)
    (hrightFlag : bitValue I
      (Interval.rightFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (Interval.selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0)
    (hcell : I.testBit
      (Interval.cellScratchWire workWidth endpointWidth) = false) :
    ∀ m top, m ≤ top → top ≤ workWidth →
    actGates (firstScan workWidth endpointWidth top m) I = I := by
  intro m
  induction m with
  | zero => intro top _ _; rfl
  | succ m ih =>
      intro top hmt htop
      simp only [firstScan, actGates_append]
      rw [Interval.rightToggle_identity_of_outer_clear
          houter hrightFlag hselector,
        Interval.majAt_identity_of_control_clear
          (by omega) hcarry hacc hcell,
        Interval.leftToggle_identity_of_outer_clear
          houter hleftFlag hselector,
        ih (top - 1) (by omega) (by omega)]

theorem secondScan_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (Interval.outerWire workWidth endpointWidth) = false)
    (hcarry : bitValue I
      (Interval.carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I
      (Interval.leftFlagWire workWidth endpointWidth) = 0)
    (hrightFlag : bitValue I
      (Interval.rightFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (Interval.selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0)
    (hcell : I.testBit
      (Interval.cellScratchWire workWidth endpointWidth) = false) :
    ∀ m j, j + m ≤ workWidth →
    actGates (secondScan workWidth endpointWidth j m) I = I := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [secondScan, actGates_append]
      rw [Interval.leftToggle_identity_of_outer_clear
          houter hleftFlag hselector,
        Interval.umaAt_identity_of_control_clear
          (by omega) hcarry hacc hcell,
        Interval.rightToggle_identity_of_outer_clear
          houter hrightFlag hselector,
        ih (j + 1) (by omega)]

theorem gates_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (Interval.outerWire workWidth endpointWidth) = false)
    (hcarry : bitValue I
      (Interval.carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I
      (Interval.leftFlagWire workWidth endpointWidth) = 0)
    (hrightFlag : bitValue I
      (Interval.rightFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (Interval.selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0)
    (hcell : I.testBit
      (Interval.cellScratchWire workWidth endpointWidth) = false) :
    actGates (gates workWidth endpointWidth) I = I := by
  have hfirst := firstScan_identity_of_outer_clear houter hcarry hacc
    hleftFlag hrightFlag hselector hcell workWidth workWidth
    (by omega) (by omega)
  have hcarryTest : I.testBit
      (Interval.carryWire workWidth endpointWidth) = false := by
    unfold bitValue at hcarry
    cases hbit : I.testBit (Interval.carryWire workWidth endpointWidth) <;>
      simp_all
  have hsign : actGates
      [.cx (Interval.carryWire workWidth endpointWidth)
        (Interval.signWire workWidth endpointWidth)] I = I := by
    simp [actGates, RGate.act, hcarryTest]
  have hsecond := secondScan_identity_of_outer_clear houter hcarry hacc
    hleftFlag hrightFlag hselector hcell workWidth 0 (by omega)
  simp only [gates, actGates_append]
  rw [hfirst, hsign, hsecond]

theorem gates_reverse_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (Interval.outerWire workWidth endpointWidth) = false)
    (hcarry : bitValue I
      (Interval.carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I
      (Interval.leftFlagWire workWidth endpointWidth) = 0)
    (hrightFlag : bitValue I
      (Interval.rightFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (Interval.selectorScratchOffset workWidth endpointWidth)
        endpointWidth = 0)
    (hcell : I.testBit
      (Interval.cellScratchWire workWidth endpointWidth) = false) :
    actGates (gates workWidth endpointWidth).reverse I = I := by
  have hforward := gates_identity_of_outer_clear houter hcarry hacc
    hleftFlag hrightFlag hselector hcell
  have hinverse := gates_reverse_forward workWidth endpointWidth I
  rw [hforward] at hinverse
  exact hinverse

theorem gates_reverse_act
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (hLR : left ≤ right) (hR : right < workWidth)
    (h : Interval.Stable left right workWidth endpointWidth I)
    (hacc : bitValue I
      (Interval.accumulatorWire workWidth endpointWidth) = 0)
    (hcarry : bitValue I
      (Interval.carryWire workWidth endpointWidth) = 0) :
    actGates (gates workWidth endpointWidth).reverse I =
      writeField
        (writeField I (Interval.targetOffset workWidth + left)
          (right - left + 1)
          (reverseBits (right - left + 1)
            (Adder.difference (right - left + 1)
              (reverseBits (right - left + 1)
                (readField I (Interval.sourceOffset + left)
                  (right - left + 1)))
              (reverseBits (right - left + 1)
                (readField I (Interval.targetOffset workWidth + left)
                  (right - left + 1))))))
        (Interval.signWire workWidth endpointWidth) 1
          ((bitValue I (Interval.signWire workWidth endpointWidth) +
            Adder.borrow
              (reverseBits (right - left + 1)
                (readField I (Interval.sourceOffset + left)
                  (right - left + 1)))
              (reverseBits (right - left + 1)
                (readField I (Interval.targetOffset workWidth + left)
                  (right - left + 1)))) % 2) := by
  let width := right - left + 1
  let target := Interval.targetOffset workWidth + left
  let source := Interval.sourceOffset + left
  let sign := Interval.signWire workWidth endpointWidth
  let aPhys := readField I source width
  let bPhys := readField I target width
  let a := reverseBits width aPhys
  let b := reverseBits width bPhys
  let s := bitValue I sign
  let x := Adder.difference width a b
  let xPhys := reverseBits width x
  let br := Adder.borrow a b
  let j := writeField (writeField I target width xPhys)
    sign 1 ((s + br) % 2)
  have hSourceTarget : source + width ≤ target := by
    dsimp [source, target, width]
    simp [Interval.sourceOffset, Interval.targetOffset]
    omega
  have haPhys : aPhys < 2 ^ width := readField_lt I source width
  have hbPhys : bPhys < 2 ^ width := readField_lt I target width
  have ha : a < 2 ^ width := reverseBits_lt width aPhys
  have hb : b < 2 ^ width := reverseBits_lt width bPhys
  have hs : s < 2 := bitValue_lt I sign
  have hspec : (a + x) % 2 ^ width = b ∧
      (a + x) / 2 ^ width = Adder.borrow a b := by
    simpa [x, Adder.difference] using
      Adder.difference_add (a := a) (b := b)
        (Nat.two_pow_pos width) ha hb
  have hx : x < 2 ^ width := Nat.mod_lt _ (Nat.two_pow_pos width)
  have hxPhys : xPhys < 2 ^ width := reverseBits_lt width x
  have hjTarget : readField j target width = xPhys := by
    simp only [j]
    rw [readField_writeField_of_disjoint (by
        right
        simp [sign, target, Interval.signWire, Interval.targetOffset,
          Interval.outerWire]
        omega),
      readField_writeField_self hxPhys]
  have hjSource : readField j source width = aPhys := by
    simp only [j]
    rw [readField_writeField_of_disjoint (by
        right
        simp [sign, source, Interval.signWire, Interval.sourceOffset,
          Interval.outerWire]
        omega),
      readField_writeField_of_disjoint (Or.inr hSourceTarget)]
  have hjCarry : bitValue j
      (Interval.carryWire workWidth endpointWidth) = 0 := by
    simp only [j]
    rw [bitValue_write_ne (by
        simp [sign, Interval.signWire, Interval.carryWire,
          Interval.outerWire]),
      bitValue_write_out (by
        right
        simp [target, Interval.targetOffset, Interval.carryWire,
          Interval.outerWire]
        omega),
      hcarry]
  have hjAccumulator : bitValue j
      (Interval.accumulatorWire workWidth endpointWidth) = 0 := by
    simp only [j]
    rw [bitValue_write_ne (by
        simp [sign, Interval.signWire, Interval.accumulatorWire,
          Interval.outerWire]),
      bitValue_write_out (by
        right
        simp [target, Interval.targetOffset, Interval.accumulatorWire,
          Interval.outerWire]
        omega),
      hacc]
  have hjSign : bitValue j sign = (s + br) % 2 := by
    simp only [j]
    rw [bitValue_write_self]
    omega
  have hjStable : Interval.Stable left right workWidth endpointWidth j :=
    (h.writeTargetInterval hLR hR).writeSign
  have hsign : (((s + br) % 2 + br) % 2) = s := by
    unfold br Adder.borrow
    by_cases hlt : b < a <;> simp [hlt] <;> omega
  have hrestore : writeField (writeField j target width bPhys) sign 1 s = I := by
    simp only [j]
    rw [writeField_comm
        (i := writeField I target width xPhys)
        (o₁ := sign) (n₁ := 1) (v := (s + br) % 2)
        (o₂ := target) (n₂ := width) (u := bPhys)
        (Or.inr (by
          simp [sign, target, Interval.signWire, Interval.targetOffset,
            Interval.outerWire]
          omega)),
      writeField_writeField]
    rw [writeField_writeField,
      show bPhys = readField I target width from rfl,
      writeField_read]
    change writeField I sign 1 (bitValue I sign) = I
    rw [← readField_one, writeField_read]
  have hfwd := gates_act
    (I := j) hwidth hLR hR hjStable hjAccumulator hjCarry
  change actGates (gates workWidth endpointWidth) j =
    writeField
      (writeField j target width
        (reverseBits width
          ((reverseBits width (readField j target width) +
            reverseBits width (readField j source width) +
            bitValue j (Interval.carryWire workWidth endpointWidth)) %
              2 ^ width)))
      sign 1
        ((bitValue j sign +
          (reverseBits width (readField j target width) +
            reverseBits width (readField j source width) +
            bitValue j (Interval.carryWire workWidth endpointWidth)) /
              2 ^ width) % 2) at hfwd
  rw [hjTarget, hjSource,
    reverseBits_involutive hx,
    show reverseBits width aPhys = a from rfl,
    hjCarry, Nat.add_zero,
    show x + a = a + x by omega,
    hspec.1,
    reverseBits_involutive hbPhys,
    hjSign, hspec.2, hsign] at hfwd
  change actGates (gates workWidth endpointWidth) j =
    writeField (writeField j target width bPhys) sign 1 s at hfwd
  rw [hrestore] at hfwd
  have hinv := actGates_reverse
    (w := (circuit workWidth endpointWidth).width)
    (circuit_wellFormed workWidth endpointWidth) j
  change actGates (gates workWidth endpointWidth).reverse
    (actGates (gates workWidth endpointWidth) j) = j at hinv
  rw [hfwd] at hinv
  simpa [j, xPhys, x, br, a, b, aPhys, bPhys, s, target, source,
    sign, width] using hinv

theorem firstScan_length_le (workWidth endpointWidth : Nat) :
    ∀ m top, (firstScan workWidth endpointWidth top m).length ≤
      m * (16 * endpointWidth + 11) := by
  intro m
  induction m with
  | zero => intro top; simp [firstScan]
  | succ m ih =>
      intro top
      simp only [firstScan, List.length_append]
      have hl : (Interval.leftToggle (top - 1) workWidth endpointWidth).length ≤
          8 * endpointWidth + 3 :=
        Interval.endpointGates_length_le (top - 1) workWidth endpointWidth
          (Interval.leftOffset workWidth)
          (Interval.leftFlagWire workWidth endpointWidth)
      have hr : (Interval.rightToggle (top - 1) workWidth endpointWidth).length ≤
          8 * endpointWidth + 3 :=
        Interval.endpointGates_length_le (top - 1) workWidth endpointWidth
          (Interval.rightOffset workWidth endpointWidth)
          (Interval.rightFlagWire workWidth endpointWidth)
      have hm : (Interval.majAt (top - 1) workWidth endpointWidth).length = 5 := by
        simp [Interval.majAt, CellPlaced.gates, Cell.maj_length]
      have hi := ih (top - 1)
      have hmul : (m + 1) * (16 * endpointWidth + 11) =
          m * (16 * endpointWidth + 11) +
            (16 * endpointWidth + 11) := by
        simp [Nat.add_mul]
      rw [hm, hmul]
      omega

theorem secondScan_length_le (workWidth endpointWidth : Nat) :
    ∀ m j, (secondScan workWidth endpointWidth j m).length ≤
      m * (16 * endpointWidth + 12) := by
  intro m
  induction m with
  | zero => intro j; simp [secondScan]
  | succ m ih =>
      intro j
      simp only [secondScan, List.length_append]
      have hl : (Interval.leftToggle j workWidth endpointWidth).length ≤
          8 * endpointWidth + 3 :=
        Interval.endpointGates_length_le j workWidth endpointWidth
          (Interval.leftOffset workWidth)
          (Interval.leftFlagWire workWidth endpointWidth)
      have hr : (Interval.rightToggle j workWidth endpointWidth).length ≤
          8 * endpointWidth + 3 :=
        Interval.endpointGates_length_le j workWidth endpointWidth
          (Interval.rightOffset workWidth endpointWidth)
          (Interval.rightFlagWire workWidth endpointWidth)
      have hu : (Interval.umaAt j workWidth endpointWidth).length = 6 := by
        simp [Interval.umaAt, CellPlaced.gates, Cell.uma_length]
      have hi := ih (j + 1)
      have hmul : (m + 1) * (16 * endpointWidth + 12) =
          m * (16 * endpointWidth + 12) +
            (16 * endpointWidth + 12) := by
        simp [Nat.add_mul]
      rw [hu, hmul]
      omega

theorem gates_length_le (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).length ≤
      workWidth * (32 * endpointWidth + 23) + 1 := by
  simp only [gates, List.length_append, List.length_cons, List.length_nil]
  have h₁ := firstScan_length_le workWidth endpointWidth workWidth workWidth
  have h₂ := secondScan_length_le workWidth endpointWidth workWidth 0
  have hmul : workWidth * (32 * endpointWidth + 23) =
      workWidth * (16 * endpointWidth + 11) +
        workWidth * (16 * endpointWidth + 12) := by
    have hinner : 32 * endpointWidth + 23 =
        (16 * endpointWidth + 11) + (16 * endpointWidth + 12) := by
      omega
    rw [hinner, Nat.mul_add]
  rw [hmul]
  omega

theorem firstScan_ccx_le (workWidth endpointWidth : Nat) :
    ∀ m top,
    (firstScan workWidth endpointWidth top m).countP RGate.isCcx ≤
      m * (8 * endpointWidth + 5) := by
  intro m
  induction m with
  | zero => intro top; simp [firstScan]
  | succ m ih =>
      intro top
      simp only [firstScan, List.countP_append]
      have hl : (Interval.leftToggle (top - 1) workWidth endpointWidth).countP
          RGate.isCcx ≤ 4 * endpointWidth + 1 :=
        Interval.endpointGates_ccx_le (top - 1) workWidth endpointWidth
          (Interval.leftOffset workWidth)
          (Interval.leftFlagWire workWidth endpointWidth)
      have hr : (Interval.rightToggle (top - 1) workWidth endpointWidth).countP
          RGate.isCcx ≤ 4 * endpointWidth + 1 :=
        Interval.endpointGates_ccx_le (top - 1) workWidth endpointWidth
          (Interval.rightOffset workWidth endpointWidth)
          (Interval.rightFlagWire workWidth endpointWidth)
      have hm : (Interval.majAt (top - 1) workWidth endpointWidth).countP
          RGate.isCcx = 3 := by
        rw [Interval.majAt, CellPlaced.gates,
          countP_map_gates (fun g => RGate.isCcx_map _ g)]
        exact Cell.maj_ccx
      have hi := ih (top - 1)
      have hmul : (m + 1) * (8 * endpointWidth + 5) =
          m * (8 * endpointWidth + 5) +
            (8 * endpointWidth + 5) := by
        simp [Nat.add_mul]
      rw [hm, hmul]
      omega

theorem secondScan_ccx_le (workWidth endpointWidth : Nat) :
    ∀ m j,
    (secondScan workWidth endpointWidth j m).countP RGate.isCcx ≤
      m * (8 * endpointWidth + 6) := by
  intro m
  induction m with
  | zero => intro j; simp [secondScan]
  | succ m ih =>
      intro j
      simp only [secondScan, List.countP_append]
      have hl : (Interval.leftToggle j workWidth endpointWidth).countP
          RGate.isCcx ≤ 4 * endpointWidth + 1 :=
        Interval.endpointGates_ccx_le j workWidth endpointWidth
          (Interval.leftOffset workWidth)
          (Interval.leftFlagWire workWidth endpointWidth)
      have hr : (Interval.rightToggle j workWidth endpointWidth).countP
          RGate.isCcx ≤ 4 * endpointWidth + 1 :=
        Interval.endpointGates_ccx_le j workWidth endpointWidth
          (Interval.rightOffset workWidth endpointWidth)
          (Interval.rightFlagWire workWidth endpointWidth)
      have hu : (Interval.umaAt j workWidth endpointWidth).countP
          RGate.isCcx = 4 := by
        rw [Interval.umaAt, CellPlaced.gates,
          countP_map_gates (fun g => RGate.isCcx_map _ g)]
        exact Cell.uma_ccx
      have hi := ih (j + 1)
      have hmul : (m + 1) * (8 * endpointWidth + 6) =
          m * (8 * endpointWidth + 6) +
            (8 * endpointWidth + 6) := by
        simp [Nat.add_mul]
      rw [hu, hmul]
      omega

theorem gates_ccx_le (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).countP RGate.isCcx ≤
      workWidth * (16 * endpointWidth + 11) := by
  simp only [gates, List.countP_append, List.countP_cons, List.countP_nil,
    RGate.isCcx, Bool.false_eq_true, if_false, Nat.add_zero]
  have h₁ := firstScan_ccx_le workWidth endpointWidth workWidth workWidth
  have h₂ := secondScan_ccx_le workWidth endpointWidth workWidth 0
  have hmul : workWidth * (16 * endpointWidth + 11) =
      workWidth * (8 * endpointWidth + 5) +
        workWidth * (8 * endpointWidth + 6) := by
    have hinner : 16 * endpointWidth + 11 =
        (8 * endpointWidth + 5) + (8 * endpointWidth + 6) := by
      omega
    rw [hinner, Nat.mul_add]
  rw [hmul]
  omega

end IntervalBigEndian
end Euclid
end VQ
