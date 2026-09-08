/-
Full-window endpoint-controlled arithmetic for the packed Euclidean work
registers.
-/
import VQ.Euclid.CellPlaced
import VQ.Euclid.Endpoint
import VQ.Euclid.Serial

namespace VQ
namespace Euclid
namespace Interval

open Reversible

def layout (workWidth endpointWidth : Nat) : Layout :=
  [workWidth, workWidth, endpointWidth, endpointWidth,
    1, 1, 1, 1, 1, 1, endpointWidth, 1]

def sourceOffset : Nat := 0
def targetOffset (workWidth : Nat) : Nat := workWidth
def leftOffset (workWidth : Nat) : Nat := 2 * workWidth
def rightOffset (workWidth endpointWidth : Nat) : Nat :=
  2 * workWidth + endpointWidth
def outerWire (workWidth endpointWidth : Nat) : Nat :=
  2 * workWidth + 2 * endpointWidth
def signWire (workWidth endpointWidth : Nat) : Nat :=
  outerWire workWidth endpointWidth + 1
def carryWire (workWidth endpointWidth : Nat) : Nat :=
  outerWire workWidth endpointWidth + 2
def accumulatorWire (workWidth endpointWidth : Nat) : Nat :=
  outerWire workWidth endpointWidth + 3
def leftFlagWire (workWidth endpointWidth : Nat) : Nat :=
  outerWire workWidth endpointWidth + 4
def rightFlagWire (workWidth endpointWidth : Nat) : Nat :=
  outerWire workWidth endpointWidth + 5
def selectorScratchOffset (workWidth endpointWidth : Nat) : Nat :=
  outerWire workWidth endpointWidth + 6
def cellScratchWire (workWidth endpointWidth : Nat) : Nat :=
  selectorScratchOffset workWidth endpointWidth + endpointWidth

def endpointWiring (workWidth endpointWidth endpoint flag : Nat) : Wiring :=
  [endpoint, outerWire workWidth endpointWidth,
    accumulatorWire workWidth endpointWidth, flag,
    selectorScratchOffset workWidth endpointWidth]

def endpointGates (value workWidth endpointWidth endpoint flag : Nat) :
    List RGate :=
  (Endpoint.circuit value endpointWidth).gates.map
    (RGate.map (place (Endpoint.layout endpointWidth)
      (endpointWiring workWidth endpointWidth endpoint flag)))

def leftToggle (value workWidth endpointWidth : Nat) : List RGate :=
  endpointGates value workWidth endpointWidth
    (leftOffset workWidth) (leftFlagWire workWidth endpointWidth)

def rightToggle (value workWidth endpointWidth : Nat) : List RGate :=
  endpointGates value workWidth endpointWidth
    (rightOffset workWidth endpointWidth) (rightFlagWire workWidth endpointWidth)

def cellWiring (j workWidth endpointWidth : Nat) : Wiring :=
  CellPlaced.wiring (targetOffset workWidth + j) (sourceOffset + j)
    (carryWire workWidth endpointWidth)
    (accumulatorWire workWidth endpointWidth)
    (cellScratchWire workWidth endpointWidth)

def majAt (j workWidth endpointWidth : Nat) : List RGate :=
  CellPlaced.gates Cell.majGates (targetOffset workWidth + j)
    (sourceOffset + j) (carryWire workWidth endpointWidth)
    (accumulatorWire workWidth endpointWidth)
    (cellScratchWire workWidth endpointWidth)

def umaAt (j workWidth endpointWidth : Nat) : List RGate :=
  CellPlaced.gates Cell.umaGates (targetOffset workWidth + j)
    (sourceOffset + j) (carryWire workWidth endpointWidth)
    (accumulatorWire workWidth endpointWidth)
    (cellScratchWire workWidth endpointWidth)

def baseMajAt (j workWidth endpointWidth : Nat) : List RGate :=
  CellPlaced.gates Cell.baseMajGates (targetOffset workWidth + j)
    (sourceOffset + j) (carryWire workWidth endpointWidth)
    (accumulatorWire workWidth endpointWidth)
    (cellScratchWire workWidth endpointWidth)

def baseUmaAt (j workWidth endpointWidth : Nat) : List RGate :=
  CellPlaced.gates Cell.baseUmaGates (targetOffset workWidth + j)
    (sourceOffset + j) (carryWire workWidth endpointWidth)
    (accumulatorWire workWidth endpointWidth)
    (cellScratchWire workWidth endpointWidth)

def disabledAt (j workWidth endpointWidth : Nat) : List RGate :=
  CellPlaced.gates Cell.disabledGates (targetOffset workWidth + j)
    (sourceOffset + j) (carryWire workWidth endpointWidth)
    (accumulatorWire workWidth endpointWidth)
    (cellScratchWire workWidth endpointWidth)

def coreLayout : Layout := [1, 1, 1]

def coreWiring (j workWidth endpointWidth : Nat) : Wiring :=
  [targetOffset workWidth + j, sourceOffset + j,
    carryWire workWidth endpointWidth]

def coreGates (gs : List RGate) (j workWidth endpointWidth : Nat) :
    List RGate :=
  gs.map (RGate.map (place coreLayout
    (coreWiring j workWidth endpointWidth)))

theorem baseMajAt_eq_core (j workWidth endpointWidth : Nat) :
    baseMajAt j workWidth endpointWidth =
      coreGates Cell.baseMajGates j workWidth endpointWidth := by
  simp [baseMajAt, CellPlaced.gates, coreGates, Cell.baseMajGates,
    CellPlaced.layout, CellPlaced.wiring, coreLayout, coreWiring, place]
  simp [RGate.map, Cell.targetWire, Cell.sourceWire, Cell.carryWire]

theorem baseUmaAt_eq_core (j workWidth endpointWidth : Nat) :
    baseUmaAt j workWidth endpointWidth =
      coreGates Cell.baseUmaGates j workWidth endpointWidth := by
  simp [baseUmaAt, CellPlaced.gates, coreGates, Cell.baseUmaGates,
    CellPlaced.layout, CellPlaced.wiring, coreLayout, coreWiring, place]
  simp [RGate.map, Cell.targetWire, Cell.sourceWire, Cell.carryWire]

theorem disabledAt_eq_core (j workWidth endpointWidth : Nat) :
    disabledAt j workWidth endpointWidth =
      coreGates Cell.disabledGates j workWidth endpointWidth := by
  simp [disabledAt, CellPlaced.gates, coreGates, Cell.disabledGates,
    CellPlaced.layout, CellPlaced.wiring, coreLayout, coreWiring, place]
  simp [RGate.map, Cell.targetWire, Cell.sourceWire, Cell.carryWire]

def fixedToggle (endpoint j workWidth endpointWidth : Nat) : List RGate :=
  if j = endpoint then [.x (accumulatorWire workWidth endpointWidth)] else []

def fixedFirstScan (left right workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      fixedToggle left j workWidth endpointWidth ++
      majAt j workWidth endpointWidth ++
      fixedToggle right j workWidth endpointWidth ++
      fixedFirstScan left right workWidth endpointWidth (j + 1) m

def fixedSecondScan (left right workWidth endpointWidth : Nat) :
    Nat → List RGate
  | 0 => []
  | m + 1 =>
      fixedToggle right m workWidth endpointWidth ++
      umaAt m workWidth endpointWidth ++
      fixedToggle left m workWidth endpointWidth ++
      fixedSecondScan left right workWidth endpointWidth m

def fixedGates (left right workWidth endpointWidth : Nat) : List RGate :=
  fixedFirstScan left right workWidth endpointWidth 0 workWidth ++
    [.cx (carryWire workWidth endpointWidth)
      (signWire workWidth endpointWidth)] ++
  fixedSecondScan left right workWidth endpointWidth workWidth

def scanAccumulator (left right j : Nat) : Nat :=
  if left < j ∧ j ≤ right then 1 else 0

def selectedMajAt (left right j workWidth endpointWidth : Nat) :
    List RGate :=
  if left ≤ j ∧ j ≤ right then
    baseMajAt j workWidth endpointWidth
  else disabledAt j workWidth endpointWidth

def selectedUmaAt (left right j workWidth endpointWidth : Nat) :
    List RGate :=
  if left ≤ j ∧ j ≤ right then
    baseUmaAt j workWidth endpointWidth
  else disabledAt j workWidth endpointWidth

def selectedFirstScan (left right workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      selectedMajAt left right j workWidth endpointWidth ++
      selectedFirstScan left right workWidth endpointWidth (j + 1) m

def selectedSecondScan (left right workWidth endpointWidth : Nat) :
    Nat → List RGate
  | 0 => []
  | m + 1 =>
      selectedUmaAt left right m workWidth endpointWidth ++
      selectedSecondScan left right workWidth endpointWidth m

def selectedGates (left right workWidth endpointWidth : Nat) : List RGate :=
  selectedFirstScan left right workWidth endpointWidth 0 workWidth ++
    [.cx (carryWire workWidth endpointWidth)
      (signWire workWidth endpointWidth)] ++
  selectedSecondScan left right workWidth endpointWidth workWidth

def disabledForward (workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      disabledAt j workWidth endpointWidth ++
      disabledForward workWidth endpointWidth (j + 1) m

def baseMajForward (workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      baseMajAt j workWidth endpointWidth ++
      baseMajForward workWidth endpointWidth (j + 1) m

def selectedBackward (left right workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | top, m + 1 =>
      selectedUmaAt left right (top - 1) workWidth endpointWidth ++
      selectedBackward left right workWidth endpointWidth (top - 1) m

def disabledBackward (workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | top, m + 1 =>
      disabledAt (top - 1) workWidth endpointWidth ++
      disabledBackward workWidth endpointWidth (top - 1) m

def baseUmaBackward (workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | top, m + 1 =>
      baseUmaAt (top - 1) workWidth endpointWidth ++
      baseUmaBackward workWidth endpointWidth (top - 1) m

def activeGates (left right workWidth endpointWidth : Nat) : List RGate :=
  baseMajForward workWidth endpointWidth left (right - left + 1) ++
    [.cx (carryWire workWidth endpointWidth)
      (signWire workWidth endpointWidth)] ++
  baseUmaBackward workWidth endpointWidth (right + 1)
    (right - left + 1)

def arithmeticLayout (width : Nat) : Layout := [width, width, 1, 1]

def arithmeticWiring (left workWidth endpointWidth : Nat) : Wiring :=
  [targetOffset workWidth + left, sourceOffset + left,
    carryWire workWidth endpointWidth, signWire workWidth endpointWidth]

def idealGates (left right workWidth endpointWidth : Nat) : List RGate :=
  let width := right - left + 1
  (Serial.carryGates width).map (RGate.map
    (place (arithmeticLayout width)
      (arithmeticWiring left workWidth endpointWidth)))

def adderMajForward (workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      Adder.maj (targetOffset workWidth + j) (sourceOffset + j)
          (carryWire workWidth endpointWidth) ++
      adderMajForward workWidth endpointWidth (j + 1) m

def adderUmaBackward (workWidth endpointWidth : Nat) :
    Nat → Nat → List RGate
  | _, 0 => []
  | top, m + 1 =>
      Adder.uma (sourceOffset + top - 1) (targetOffset workWidth + top - 1)
          (carryWire workWidth endpointWidth) ++
      adderUmaBackward workWidth endpointWidth (top - 1) m

theorem selectedFirstScan_split
    (left right workWidth endpointWidth j a b : Nat) :
    selectedFirstScan left right workWidth endpointWidth j (a + b) =
      selectedFirstScan left right workWidth endpointWidth j a ++
      selectedFirstScan left right workWidth endpointWidth (j + a) b := by
  induction a generalizing j with
  | zero => simp [selectedFirstScan]
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega]
      simp only [selectedFirstScan]
      rw [ih (j := j + 1), List.append_assoc]
      simp only [show j + 1 + a = j + (a + 1) by omega]

theorem selectedSecondScan_eq_backward
    (left right workWidth endpointWidth : Nat) : ∀ m,
    selectedSecondScan left right workWidth endpointWidth m =
      selectedBackward left right workWidth endpointWidth m m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      simp [selectedSecondScan, selectedBackward, ih]

theorem selectedBackward_split
    (left right workWidth endpointWidth base a b : Nat) :
    selectedBackward left right workWidth endpointWidth
        (base + a + b) (a + b) =
      selectedBackward left right workWidth endpointWidth
          (base + a + b) a ++
      selectedBackward left right workWidth endpointWidth (base + b) b := by
  induction a generalizing base with
  | zero => simp [selectedBackward]
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega,
        show base + (a + 1) + b = (base + a + b) + 1 by omega]
      simp only [selectedBackward, Nat.add_sub_cancel]
      rw [ih (base := base), List.append_assoc]

theorem selectedFirstScan_below
    {left right workWidth endpointWidth : Nat} : ∀ m j,
    j + m ≤ left →
    selectedFirstScan left right workWidth endpointWidth j m =
      disabledForward workWidth endpointWidth j m := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      have hj : ¬(left ≤ j ∧ j ≤ right) := by omega
      simp [selectedFirstScan, selectedMajAt, disabledForward, hj,
        ih (j + 1) (by omega)]

theorem selectedFirstScan_inside
    {left right workWidth endpointWidth : Nat} : ∀ m j,
    left ≤ j → j + m ≤ right + 1 →
    selectedFirstScan left right workWidth endpointWidth j m =
      baseMajForward workWidth endpointWidth j m := by
  intro m
  induction m with
  | zero => intro j _ _; rfl
  | succ m ih =>
      intro j hleft hright
      have hj : left ≤ j ∧ j ≤ right := by omega
      simp [selectedFirstScan, selectedMajAt, baseMajForward, hj,
        ih (j + 1) (by omega) (by omega)]

theorem selectedFirstScan_above
    {left right workWidth endpointWidth : Nat} : ∀ m j,
    right < j →
    selectedFirstScan left right workWidth endpointWidth j m =
      disabledForward workWidth endpointWidth j m := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hright
      have hj : ¬(left ≤ j ∧ j ≤ right) := by omega
      simp [selectedFirstScan, selectedMajAt, disabledForward, hj,
        ih (j + 1) (by omega)]

theorem selectedBackward_above
    {left right workWidth endpointWidth : Nat} : ∀ m top,
    m ≤ top → right + m < top →
    selectedBackward left right workWidth endpointWidth top m =
      disabledBackward workWidth endpointWidth top m := by
  intro m
  induction m with
  | zero => intro top _ _; rfl
  | succ m ih =>
      intro top hmt hright
      have htop : 0 < top := by omega
      have hj : ¬(left ≤ top - 1 ∧ top - 1 ≤ right) := by omega
      rw [selectedBackward, disabledBackward, selectedUmaAt, if_neg hj,
        ih (top - 1) (by omega) (by omega)]

theorem selectedBackward_inside
    {left right workWidth endpointWidth : Nat} : ∀ m top,
    m ≤ top → left + m ≤ top → top ≤ right + 1 →
    selectedBackward left right workWidth endpointWidth top m =
      baseUmaBackward workWidth endpointWidth top m := by
  intro m
  induction m with
  | zero => intro top _ _ _; rfl
  | succ m ih =>
      intro top hmt hleft hright
      have htop : 0 < top := by omega
      have hj : left ≤ top - 1 ∧ top - 1 ≤ right := by omega
      rw [selectedBackward, baseUmaBackward, selectedUmaAt, if_pos hj,
        ih (top - 1) (by omega) (by omega) (by omega)]

theorem selectedBackward_below
    {left right workWidth endpointWidth : Nat} : ∀ m top,
    m ≤ top → top ≤ left →
    selectedBackward left right workWidth endpointWidth top m =
      disabledBackward workWidth endpointWidth top m := by
  intro m
  induction m with
  | zero => intro top _ _; rfl
  | succ m ih =>
      intro top hmt hleft
      have htop : 0 < top := by omega
      have hj : ¬(left ≤ top - 1 ∧ top - 1 ≤ right) := by omega
      rw [selectedBackward, disabledBackward, selectedUmaAt, if_neg hj,
        ih (top - 1) (by omega) (by omega)]

theorem selectedFirstScan_decompose
    {left right workWidth endpointWidth : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    selectedFirstScan left right workWidth endpointWidth 0 workWidth =
      disabledForward workWidth endpointWidth 0 left ++
      baseMajForward workWidth endpointWidth left (right - left + 1) ++
      disabledForward workWidth endpointWidth (right + 1)
        (workWidth - (right + 1)) := by
  let n := right - left + 1
  let u := workWidth - (right + 1)
  have hLn : left + n = right + 1 := by
    dsimp [n]
    omega
  have hsum : left + n + u = workWidth := by
    dsimp [n, u]
    omega
  have hbelow := selectedFirstScan_below
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) left 0 (by omega)
  have hinside := selectedFirstScan_inside
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) n left (by omega) (by omega)
  have habove := selectedFirstScan_above
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) u (right + 1) (by omega)
  have hsplit₁ :
      selectedFirstScan left right workWidth endpointWidth 0 workWidth =
        selectedFirstScan left right workWidth endpointWidth 0 left ++
        selectedFirstScan left right workWidth endpointWidth left (n + u) := by
    have hs := selectedFirstScan_split left right workWidth endpointWidth
      0 left (n + u)
    rw [Nat.zero_add] at hs
    simpa only [show left + (n + u) = workWidth by omega] using hs
  have hsplit₂ :
      selectedFirstScan left right workWidth endpointWidth left (n + u) =
        selectedFirstScan left right workWidth endpointWidth left n ++
        selectedFirstScan left right workWidth endpointWidth (right + 1) u := by
    have hs := selectedFirstScan_split left right workWidth endpointWidth
      left n u
    simpa only [hLn] using hs
  rw [hsplit₁, hsplit₂, hbelow, hinside, habove]
  simp only [n, u, List.append_assoc]

theorem selectedSecondScan_decompose
    {left right workWidth endpointWidth : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    selectedSecondScan left right workWidth endpointWidth workWidth =
      disabledBackward workWidth endpointWidth workWidth
          (workWidth - (right + 1)) ++
      baseUmaBackward workWidth endpointWidth (right + 1)
          (right - left + 1) ++
      disabledBackward workWidth endpointWidth left left := by
  let n := right - left + 1
  let u := workWidth - (right + 1)
  have hLn : left + n = right + 1 := by
    dsimp [n]
    omega
  have hsum : u + n + left = workWidth := by
    dsimp [n, u]
    omega
  have habove := selectedBackward_above
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) u workWidth (by omega) (by
      dsimp [u]
      omega)
  have hinside := selectedBackward_inside
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) n (right + 1)
    (by omega) (by omega) (by omega)
  have hbelow := selectedBackward_below
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) left left (by omega) (by omega)
  have hsplit₁ :
      selectedBackward left right workWidth endpointWidth workWidth workWidth =
        selectedBackward left right workWidth endpointWidth workWidth u ++
        selectedBackward left right workWidth endpointWidth
          (n + left) (n + left) := by
    have hs := selectedBackward_split left right workWidth endpointWidth
      0 u (n + left)
    simpa only [Nat.zero_add,
      show u + (n + left) = workWidth by omega,
      show u + n + left = workWidth by omega] using hs
  have hsplit₂ :
      selectedBackward left right workWidth endpointWidth (n + left) (n + left) =
        selectedBackward left right workWidth endpointWidth (right + 1) n ++
        selectedBackward left right workWidth endpointWidth left left := by
    have hs := selectedBackward_split left right workWidth endpointWidth
      0 n left
    simpa only [Nat.zero_add, hLn,
      show n + left = right + 1 by omega] using hs
  rw [selectedSecondScan_eq_backward, hsplit₁, hsplit₂,
    habove, hinside, hbelow]
  simp only [n, u, List.append_assoc]

theorem arithmeticLayout_width (width : Nat) :
    (arithmeticLayout width).width = 2 * width + 2 := by
  simp [arithmeticLayout, Layout.width]
  omega

theorem arithmetic_disjoint
    {left right workWidth endpointWidth : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    Wiring.Disjoint (arithmeticLayout (right - left + 1))
      (arithmeticWiring left workWidth endpointWidth) := by
  intro a b ha hb hne
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
    simp [arithmeticWiring] at ha
    omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by
    simp [arithmeticWiring] at hb
    omega
  rcases ha' with rfl | rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl | rfl <;>
    simp [arithmeticLayout, arithmeticWiring, Layout.size, targetOffset,
      sourceOffset, carryWire, signWire, outerWire] at * <;>
    omega

theorem place_arithmetic_target
    {left width workWidth endpointWidth k : Nat} (hk : k < width) :
    place (arithmeticLayout width)
        (arithmeticWiring left workWidth endpointWidth) k =
      targetOffset workWidth + left + k := by
  simp [arithmeticLayout, arithmeticWiring, place, hk]

theorem place_arithmetic_source
    {left width workWidth endpointWidth k : Nat} (hk : k < width) :
    place (arithmeticLayout width)
        (arithmeticWiring left workWidth endpointWidth) (width + k) =
      sourceOffset + left + k := by
  simp only [arithmeticLayout, arithmeticWiring, place]
  rw [if_neg (by omega), show width + k - width = k by omega,
    if_pos hk]

theorem place_arithmetic_carry
    (left width workWidth endpointWidth : Nat) :
    place (arithmeticLayout width)
        (arithmeticWiring left workWidth endpointWidth) (2 * width) =
      carryWire workWidth endpointWidth := by
  simp only [arithmeticLayout, arithmeticWiring, place]
  rw [if_neg (by omega), show 2 * width - width = width by omega,
    if_neg (by omega), Nat.sub_self, if_pos (by omega)]
  simp

theorem place_arithmetic_sign
    (left width workWidth endpointWidth : Nat) :
    place (arithmeticLayout width)
        (arithmeticWiring left workWidth endpointWidth) (2 * width + 1) =
      signWire workWidth endpointWidth := by
  simp only [arithmeticLayout, arithmeticWiring, place]
  rw [if_neg (by omega), show 2 * width + 1 - width = width + 1 by omega,
    if_neg (by omega), show width + 1 - width = 1 by omega,
    if_neg (by omega), Nat.sub_self, if_pos (by omega)]
  simp

theorem map_serial_maj
    {left width workWidth endpointWidth k : Nat} (hk : k < width) :
    (Adder.maj k (width + k) (2 * width)).map
        (RGate.map (place (arithmeticLayout width)
          (arithmeticWiring left workWidth endpointWidth))) =
      Adder.maj (targetOffset workWidth + (left + k))
        (sourceOffset + (left + k)) (carryWire workWidth endpointWidth) := by
  simp only [Adder.maj, List.map_cons, List.map_nil, RGate.map]
  rw [place_arithmetic_carry, place_arithmetic_source hk,
    place_arithmetic_target hk]
  simp only [Nat.add_assoc]

theorem map_serial_uma
    {left width workWidth endpointWidth k : Nat} (hk : k < width) :
    (Adder.uma (width + k) k (2 * width)).map
        (RGate.map (place (arithmeticLayout width)
          (arithmeticWiring left workWidth endpointWidth))) =
      Adder.uma (sourceOffset + (left + k))
        (targetOffset workWidth + (left + k))
        (carryWire workWidth endpointWidth) := by
  simp only [Adder.uma, List.map_cons, List.map_nil, RGate.map]
  rw [place_arithmetic_carry, place_arithmetic_source hk,
    place_arithmetic_target hk]
  simp only [Nat.add_assoc]

theorem adderUmaBackward_snoc (workWidth endpointWidth : Nat) : ∀ m top,
    m + 1 ≤ top →
    adderUmaBackward workWidth endpointWidth top (m + 1) =
      adderUmaBackward workWidth endpointWidth top m ++
      Adder.uma (sourceOffset + (top - (m + 1)))
        (targetOffset workWidth + (top - (m + 1)))
        (carryWire workWidth endpointWidth) := by
  intro m
  induction m with
  | zero =>
      intro top htop
      simp [adderUmaBackward]
      congr 4 <;> omega
  | succ m ih =>
      intro top htop
      change Adder.uma (sourceOffset + top - 1)
          (targetOffset workWidth + top - 1)
          (carryWire workWidth endpointWidth) ++
          adderUmaBackward workWidth endpointWidth (top - 1) (m + 1) =
        (Adder.uma (sourceOffset + top - 1)
            (targetOffset workWidth + top - 1)
            (carryWire workWidth endpointWidth) ++
          adderUmaBackward workWidth endpointWidth (top - 1) m) ++
        Adder.uma (sourceOffset + (top - (m + 1 + 1)))
          (targetOffset workWidth + (top - (m + 1 + 1)))
          (carryWire workWidth endpointWidth)
      rw [ih (top - 1) (by omega), List.append_assoc]
      simp only [show top - 1 - (m + 1) = top - (m + 1 + 1) by omega]

theorem map_serial_majChain
    {left width workWidth endpointWidth : Nat} : ∀ m st,
    st + m ≤ width →
    (Serial.majChain width st m).map
        (RGate.map (place (arithmeticLayout width)
          (arithmeticWiring left workWidth endpointWidth))) =
      adderMajForward workWidth endpointWidth (left + st) m := by
  intro m
  induction m with
  | zero => intro st _; rfl
  | succ m ih =>
      intro st hbound
      simp only [Serial.majChain, List.map_append, adderMajForward]
      rw [map_serial_maj (by omega), ih (st + 1) (by omega)]
      simp only [Nat.add_assoc]

theorem map_serial_umaChain
    {left width workWidth endpointWidth : Nat} : ∀ m st,
    st + m ≤ width →
    (Serial.umaChain width st m).map
        (RGate.map (place (arithmeticLayout width)
          (arithmeticWiring left workWidth endpointWidth))) =
      adderUmaBackward workWidth endpointWidth (left + st + m) m := by
  intro m
  induction m with
  | zero => intro st _; rfl
  | succ m ih =>
      intro st hbound
      simp only [Serial.umaChain, List.map_append]
      rw [ih (st + 1) (by omega), map_serial_uma (by omega),
        adderUmaBackward_snoc workWidth endpointWidth m
          (left + st + (m + 1)) (by omega)]
      simp only [
        show left + (st + 1) + m = left + st + (m + 1) by omega,
        show left + st + (m + 1) - (m + 1) = left + st by omega]

theorem idealGates_eq_adderGates
    {left right workWidth endpointWidth : Nat} (hLR : left ≤ right) :
    idealGates left right workWidth endpointWidth =
      adderMajForward workWidth endpointWidth left (right - left + 1) ++
      [.cx (carryWire workWidth endpointWidth)
        (signWire workWidth endpointWidth)] ++
      adderUmaBackward workWidth endpointWidth (right + 1)
        (right - left + 1) := by
  let width := right - left + 1
  have hwidth : 0 < width := by
    dsimp [width]
    omega
  have htop : left + width = right + 1 := by
    dsimp [width]
    omega
  simp only [idealGates, Serial.carryGates, List.map_append,
    List.map_cons, List.map_nil, RGate.map]
  rw [map_serial_majChain (left := left) (workWidth := workWidth)
      (endpointWidth := endpointWidth) width 0 (by omega),
    map_serial_umaChain (left := left) (workWidth := workWidth)
      (endpointWidth := endpointWidth) width 0 (by omega),
    place_arithmetic_carry,
    show Serial.signWire (right - left + 1) =
      2 * (right - left + 1) + 1 by rfl,
    place_arithmetic_sign]
  simp only [Nat.add_zero, htop, width]

structure Stable (left right workWidth endpointWidth I : Nat) : Prop where
  leftValue : readField I (leftOffset workWidth) endpointWidth = left
  rightValue : readField I (rightOffset workWidth endpointWidth) endpointWidth = right
  outerSet : I.testBit (outerWire workWidth endpointWidth) = true
  leftFlagClear : bitValue I (leftFlagWire workWidth endpointWidth) = 0
  rightFlagClear : bitValue I (rightFlagWire workWidth endpointWidth) = 0
  selectorScratchClear : readField I
    (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0
  cellScratchClear : I.testBit (cellScratchWire workWidth endpointWidth) = false

theorem Stable.writeAccumulator {left right workWidth endpointWidth I v : Nat}
    (h : Stable left right workWidth endpointWidth I) :
    Stable left right workWidth endpointWidth
      (writeField I (accumulatorWire workWidth endpointWidth) 1 v) := by
  constructor
  · rw [readField_writeField_of_disjoint (by
      simp [leftOffset, accumulatorWire, outerWire]
      omega), h.leftValue]
  · rw [readField_writeField_of_disjoint (by
      simp [rightOffset, accumulatorWire, outerWire]
      omega), h.rightValue]
  · rw [testBit_writeField_outside (by
      simp [outerWire, accumulatorWire]), h.outerSet]
  · rw [bitValue_write_ne (by
      simp [leftFlagWire, accumulatorWire]), h.leftFlagClear]
  · rw [bitValue_write_ne (by
      simp [rightFlagWire, accumulatorWire]), h.rightFlagClear]
  · rw [readField_writeField_of_disjoint (by
      simp [selectorScratchOffset, accumulatorWire, outerWire]),
    h.selectorScratchClear]
  · rw [testBit_writeField_outside (by
      simp [cellScratchWire, selectorScratchOffset, accumulatorWire, outerWire]
      omega), h.cellScratchClear]

theorem Stable.writeSign {left right workWidth endpointWidth I v : Nat}
    (h : Stable left right workWidth endpointWidth I) :
    Stable left right workWidth endpointWidth
      (writeField I (signWire workWidth endpointWidth) 1 v) := by
  constructor
  · rw [readField_writeField_of_disjoint (by
      simp [leftOffset, signWire, outerWire]
      omega), h.leftValue]
  · rw [readField_writeField_of_disjoint (by
      simp [rightOffset, signWire, outerWire]
      omega), h.rightValue]
  · rw [testBit_writeField_outside (by
      simp [outerWire, signWire]), h.outerSet]
  · rw [bitValue_write_ne (by
      simp [leftFlagWire, signWire, outerWire]), h.leftFlagClear]
  · rw [bitValue_write_ne (by
      simp [rightFlagWire, signWire, outerWire]), h.rightFlagClear]
  · rw [readField_writeField_of_disjoint (by
      simp [selectorScratchOffset, signWire, outerWire]), h.selectorScratchClear]
  · rw [testBit_writeField_outside (by
      simp [cellScratchWire, selectorScratchOffset, signWire, outerWire]
      omega), h.cellScratchClear]

theorem signGate_preserves_stable {left right workWidth endpointWidth I : Nat}
    (h : Stable left right workWidth endpointWidth I) :
    Stable left right workWidth endpointWidth
      (actGates [.cx (carryWire workWidth endpointWidth)
        (signWire workWidth endpointWidth)] I) := by
  simp only [actGates_cons, actGates_nil, act_cx_write]
  exact h.writeSign

theorem core_place_cases {q j workWidth endpointWidth : Nat} (hq : q < 3) :
    place coreLayout (coreWiring j workWidth endpointWidth) q =
        targetOffset workWidth + j ∨
      place coreLayout (coreWiring j workWidth endpointWidth) q =
        sourceOffset + j ∨
      place coreLayout (coreWiring j workWidth endpointWidth) q =
        carryWire workWidth endpointWidth := by
  have hq' : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hq' with rfl | rfl | rfl <;>
    simp [coreLayout, coreWiring, place]

theorem core_disjoint {j workWidth endpointWidth : Nat}
    (hj : j < workWidth) :
    Wiring.Disjoint coreLayout (coreWiring j workWidth endpointWidth) := by
  intro a b ha hb hne
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 := by
    simp [coreWiring] at ha
    omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by
    simp [coreWiring] at hb
    omega
  rcases ha' with rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl <;>
    simp [coreLayout, coreWiring, Layout.size, targetOffset, sourceOffset,
      carryWire, outerWire] at * <;>
    omega

theorem core_preserves_stable {gs : List RGate}
    {left right j workWidth endpointWidth I : Nat}
    (hj : j < workWidth)
    (hwf : ∀ g ∈ gs, g.wellFormed 3 = true)
    (h : Stable left right workWidth endpointWidth I) :
    Stable left right workWidth endpointWidth
      (actGates (coreGates gs j workWidth endpointWidth) I) := by
  let f := place coreLayout (coreWiring j workWidth endpointWidth)
  have hfield : ∀ off len,
      (∀ q, q < 3 → f q < off ∨ off + len ≤ f q) →
      readField (actGates (coreGates gs j workWidth endpointWidth) I) off len =
        readField I off len := by
    intro off len hout
    exact readField_actGates_map_of_outside hwf hout I
  have hbit : ∀ b, (∀ q, q < 3 → f q ≠ b) →
      (actGates (coreGates gs j workWidth endpointWidth) I).testBit b =
        I.testBit b := by
    intro b hout
    exact testBit_actGates_map_of_outside hwf hout I
  constructor
  · rw [hfield (leftOffset workWidth) endpointWidth (by
      intro q hq
      simp only [f]
      rcases core_place_cases (j := j) (workWidth := workWidth)
        (endpointWidth := endpointWidth) hq with he | he | he <;>
        rw [he] <;>
        simp [leftOffset, targetOffset, sourceOffset, carryWire, outerWire] <;>
        omega), h.leftValue]
  · rw [hfield (rightOffset workWidth endpointWidth) endpointWidth (by
      intro q hq
      simp only [f]
      rcases core_place_cases (j := j) (workWidth := workWidth)
        (endpointWidth := endpointWidth) hq with he | he | he <;>
        rw [he] <;>
        simp [rightOffset, targetOffset, sourceOffset, carryWire, outerWire] <;>
        omega), h.rightValue]
  · rw [hbit (outerWire workWidth endpointWidth) (by
      intro q hq
      simp only [f]
      rcases core_place_cases (j := j) (workWidth := workWidth)
        (endpointWidth := endpointWidth) hq with he | he | he <;>
        rw [he] <;>
        simp [targetOffset, sourceOffset, carryWire, outerWire] <;>
        omega), h.outerSet]
  · rw [← readField_one]
    rw [hfield (leftFlagWire workWidth endpointWidth) 1 (by
      intro q hq
      simp only [f]
      rcases core_place_cases (j := j) (workWidth := workWidth)
        (endpointWidth := endpointWidth) hq with he | he | he <;>
        rw [he] <;>
        simp [leftFlagWire, targetOffset, sourceOffset, carryWire, outerWire] <;>
        omega), readField_one, h.leftFlagClear]
  · rw [← readField_one]
    rw [hfield (rightFlagWire workWidth endpointWidth) 1 (by
      intro q hq
      simp only [f]
      rcases core_place_cases (j := j) (workWidth := workWidth)
        (endpointWidth := endpointWidth) hq with he | he | he <;>
        rw [he] <;>
        simp [rightFlagWire, targetOffset, sourceOffset, carryWire, outerWire] <;>
        omega), readField_one, h.rightFlagClear]
  · rw [hfield (selectorScratchOffset workWidth endpointWidth)
      endpointWidth (by
        intro q hq
        simp only [f]
        rcases core_place_cases (j := j) (workWidth := workWidth)
          (endpointWidth := endpointWidth) hq with he | he | he <;>
          rw [he] <;>
          simp [selectorScratchOffset, targetOffset, sourceOffset, carryWire,
            outerWire] <;>
          omega), h.selectorScratchClear]
  · rw [hbit (cellScratchWire workWidth endpointWidth) (by
      intro q hq
      simp only [f]
      rcases core_place_cases (j := j) (workWidth := workWidth)
        (endpointWidth := endpointWidth) hq with he | he | he <;>
        rw [he] <;>
        simp [cellScratchWire, selectorScratchOffset, targetOffset, sourceOffset,
          carryWire, outerWire] <;>
        omega), h.cellScratchClear]

theorem Stable.writeTargetInterval
    {left right workWidth endpointWidth I v : Nat}
    (h : Stable left right workWidth endpointWidth I)
    (hLR : left ≤ right) (hR : right < workWidth) :
    Stable left right workWidth endpointWidth
      (writeField I (targetOffset workWidth + left)
        (right - left + 1) v) := by
  constructor
  · rw [readField_writeField_of_disjoint (by
      left
      simp [leftOffset, targetOffset]
      omega), h.leftValue]
  · rw [readField_writeField_of_disjoint (by
      left
      simp [rightOffset, targetOffset]
      omega), h.rightValue]
  · rw [testBit_writeField_outside (by
      right
      simp [outerWire, targetOffset]
      omega), h.outerSet]
  · rw [bitValue_write_out (by
      right
      simp [leftFlagWire, outerWire, targetOffset]
      omega), h.leftFlagClear]
  · rw [bitValue_write_out (by
      right
      simp [rightFlagWire, outerWire, targetOffset]
      omega), h.rightFlagClear]
  · rw [readField_writeField_of_disjoint (by
      left
      simp [selectorScratchOffset, outerWire, targetOffset]
      omega), h.selectorScratchClear]
  · rw [testBit_writeField_outside (by
      right
      simp [cellScratchWire, selectorScratchOffset, outerWire, targetOffset]
      omega), h.cellScratchClear]

theorem coreGates_avoids_accumulator {gs : List RGate}
    {j workWidth endpointWidth : Nat}
    (hj : j < workWidth)
    (hwf : ∀ g ∈ gs, g.wellFormed 3 = true) :
    ∀ g ∈ coreGates gs j workWidth endpointWidth, ∀ q ∈ g.wires,
      q < accumulatorWire workWidth endpointWidth ∨
        accumulatorWire workWidth endpointWidth + 1 ≤ q := by
  apply placeGates_avoids
      (L := coreLayout) (W := coreWiring j workWidth endpointWidth)
  · simp [coreLayout, coreWiring]
  · exact hwf
  · intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by
      simp [coreLayout] at hk
      omega
    rcases hk' with rfl | rfl | rfl <;>
      simp [coreLayout, coreWiring, Layout.size, targetOffset, sourceOffset,
        carryWire, accumulatorWire, outerWire] <;>
      omega

theorem coreGates_bitValue_accumulator {gs : List RGate}
    {j workWidth endpointWidth I : Nat}
    (hj : j < workWidth)
    (hwf : ∀ g ∈ gs, g.wellFormed 3 = true) :
    bitValue (actGates (coreGates gs j workWidth endpointWidth) I)
        (accumulatorWire workWidth endpointWidth) =
      bitValue I (accumulatorWire workWidth endpointWidth) := by
  rw [← readField_one, readField_actGates_of_outside
    (coreGates_avoids_accumulator hj hwf) I, readField_one]

theorem coreGates_writeAccumulator {gs : List RGate}
    {j workWidth endpointWidth I v : Nat}
    (hj : j < workWidth)
    (hwf : ∀ g ∈ gs, g.wellFormed 3 = true) :
    actGates (coreGates gs j workWidth endpointWidth)
        (writeField I (accumulatorWire workWidth endpointWidth) 1 v) =
      writeField
        (actGates (coreGates gs j workWidth endpointWidth) I)
        (accumulatorWire workWidth endpointWidth) 1 v := by
  exact actGates_write_of_outside
    (coreGates_avoids_accumulator hj hwf) I

theorem disabledAt_eq_pair (j workWidth endpointWidth : Nat) :
    disabledAt j workWidth endpointWidth =
      [.cx (carryWire workWidth endpointWidth) (targetOffset workWidth + j),
       .cx (carryWire workWidth endpointWidth) (sourceOffset + j)] := by
  simp [disabledAt, CellPlaced.gates, Cell.disabledGates,
    CellPlaced.layout, CellPlaced.wiring, place, targetOffset, sourceOffset,
    carryWire, outerWire, RGate.map, Cell.carryWire, Cell.targetWire,
    Cell.sourceWire]

theorem disabledAt_preserves_carry
    {j workWidth endpointWidth I : Nat} (hj : j < workWidth) :
    bitValue (actGates (disabledAt j workWidth endpointWidth) I)
        (carryWire workWidth endpointWidth) =
      bitValue I (carryWire workWidth endpointWidth) := by
  rw [disabledAt_eq_pair]
  simp only [actGates_cons, actGates_nil, act_cx_write]
  rw [bitValue_write_ne (by
      simp [sourceOffset, carryWire, outerWire]
      omega),
    bitValue_write_ne (by
      simp [targetOffset, carryWire, outerWire]
      omega)]

theorem disabledAt_identity_of_carry_clear
    {j workWidth endpointWidth I : Nat}
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0) :
    actGates (disabledAt j workWidth endpointWidth) I = I := by
  have hc : I.testBit (carryWire workWidth endpointWidth) = false := by
    unfold bitValue at hcarry
    cases hb : I.testBit (carryWire workWidth endpointWidth) <;>
      simp_all
  rw [disabledAt_eq_pair]
  simp [actGates, RGate.act, hc]

theorem disabledAt_involutive
    {j workWidth endpointWidth I : Nat} (hj : j < workWidth) :
    actGates (disabledAt j workWidth endpointWidth)
        (actGates (disabledAt j workWidth endpointWidth) I) = I := by
  have hp := actGates_placed_congr
    (L := coreLayout) (W := coreWiring j workWidth endpointWidth)
    (gs := Cell.disabledGates ++ Cell.disabledGates) (hs := [])
    (core_disjoint hj) (by simp [coreLayout, coreWiring])
    (by decide) (by simp) I (by
      rw [actGates_append, Cell.disabledGates_act,
        Cell.disabledGates_act, Cell.disabledState_involutive,
        actGates_nil])
  simpa [disabledAt_eq_core, coreGates, List.map_append,
    actGates_append, actGates_nil] using hp

theorem baseMajAt_eq_adderMajAt
    {j workWidth endpointWidth I : Nat} (hj : j < workWidth) :
    actGates (baseMajAt j workWidth endpointWidth) I =
      actGates
        (Adder.maj (targetOffset workWidth + j) (sourceOffset + j)
          (carryWire workWidth endpointWidth)) I := by
  have hp := actGates_placed_congr
    (L := coreLayout) (W := coreWiring j workWidth endpointWidth)
    (gs := Cell.baseMajGates)
    (hs := Adder.maj Cell.targetWire Cell.sourceWire Cell.carryWire)
    (core_disjoint hj) (by simp [coreLayout, coreWiring])
    (by decide) (by decide) I (Cell.baseMaj_eq_adderMaj _)
  simpa [baseMajAt_eq_core, coreGates, Adder.maj, coreLayout, coreWiring,
    place, RGate.map, Cell.targetWire, Cell.sourceWire, Cell.carryWire]
    using hp

theorem baseUmaAt_eq_adderUmaAt
    {j workWidth endpointWidth I : Nat} (hj : j < workWidth) :
    actGates (baseUmaAt j workWidth endpointWidth) I =
      actGates
        (Adder.uma (sourceOffset + j) (targetOffset workWidth + j)
          (carryWire workWidth endpointWidth)) I := by
  have hp := actGates_placed_congr
    (L := coreLayout) (W := coreWiring j workWidth endpointWidth)
    (gs := Cell.baseUmaGates)
    (hs := Adder.uma Cell.sourceWire Cell.targetWire Cell.carryWire)
    (core_disjoint hj) (by simp [coreLayout, coreWiring])
    (by decide) (by decide) I (Cell.baseUma_eq_adderUma _)
  simpa [baseUmaAt_eq_core, coreGates, Adder.uma, coreLayout, coreWiring,
    place, RGate.map, Cell.targetWire, Cell.sourceWire, Cell.carryWire]
    using hp

theorem baseMajForward_eq_adderMajForward
    {workWidth endpointWidth I : Nat} : ∀ m j,
    j + m ≤ workWidth →
    actGates (baseMajForward workWidth endpointWidth j m) I =
      actGates (adderMajForward workWidth endpointWidth j m) I := by
  intro m
  induction m generalizing I with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [baseMajForward, adderMajForward, actGates_append]
      rw [baseMajAt_eq_adderMajAt (by omega),
        ih (j := j + 1) (by omega)]

theorem baseUmaBackward_eq_adderUmaBackward
    {workWidth endpointWidth I : Nat} : ∀ m top,
    m ≤ top → top ≤ workWidth →
    actGates (baseUmaBackward workWidth endpointWidth top m) I =
      actGates (adderUmaBackward workWidth endpointWidth top m) I := by
  intro m
  induction m generalizing I with
  | zero => intro top _ _; rfl
  | succ m ih =>
      intro top hmt htop
      simp only [baseUmaBackward, adderUmaBackward, actGates_append]
      have htopPos : 0 < top := by omega
      rw [baseUmaAt_eq_adderUmaAt (j := top - 1) (by omega)]
      change actGates (baseUmaBackward workWidth endpointWidth (top - 1) m)
          (actGates
            (Adder.uma (sourceOffset + (top - 1))
              (targetOffset workWidth + (top - 1))
              (carryWire workWidth endpointWidth)) I) = _
      rw [ih (top := top - 1) (by omega) (by omega)]
      congr 4 <;> omega

theorem activeGates_eq_ideal
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    actGates (activeGates left right workWidth endpointWidth) I =
      actGates (idealGates left right workWidth endpointWidth) I := by
  let width := right - left + 1
  have hwidth : left + width ≤ workWidth := by
    dsimp [width]
    omega
  have htop : width ≤ right + 1 := by
    dsimp [width]
    omega
  rw [idealGates_eq_adderGates hLR]
  simp only [activeGates, actGates_append]
  rw [baseMajForward_eq_adderMajForward
      (m := width) (j := left) hwidth]
  let middle := actGates
    [.cx (carryWire workWidth endpointWidth)
      (signWire workWidth endpointWidth)]
    (actGates (adderMajForward workWidth endpointWidth left width) I)
  change actGates
      (baseUmaBackward workWidth endpointWidth (right + 1) width) middle =
    actGates
      (adderUmaBackward workWidth endpointWidth (right + 1) width) middle
  exact baseUmaBackward_eq_adderUmaBackward
    (m := width) (top := right + 1) htop (by omega)

theorem idealGates_act
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    actGates (idealGates left right workWidth endpointWidth) I =
      writeField
        (writeField I (targetOffset workWidth + left) (right - left + 1)
          ((readField I (targetOffset workWidth + left) (right - left + 1) +
            readField I (sourceOffset + left) (right - left + 1) +
            bitValue I (carryWire workWidth endpointWidth)) %
              2 ^ (right - left + 1)))
        (signWire workWidth endpointWidth) 1
          ((bitValue I (signWire workWidth endpointWidth) +
            (readField I (targetOffset workWidth + left) (right - left + 1) +
              readField I (sourceOffset + left) (right - left + 1) +
              bitValue I (carryWire workWidth endpointWidth)) /
                2 ^ (right - left + 1)) % 2) := by
  let width := right - left + 1
  let L := arithmeticLayout width
  let W := arithmeticWiring left workWidth endpointWidth
  let gathered := gatherBits (place L W) L.width I
  have hwidth : 0 < width := by
    dsimp [width]
    omega
  have hTarget : readField gathered 0 width =
      readField I (targetOffset workWidth + left) width := by
    have hr := readField_gatherBits L W 0 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Layout.offset, Layout.size] using hr
  have hSource : readField gathered width width =
      readField I (sourceOffset + left) width := by
    have hr := readField_gatherBits L W 1 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Layout.offset, Layout.size] using hr
  have hCarry : bitValue gathered (2 * width) =
      bitValue I (carryWire workWidth endpointWidth) := by
    rw [← readField_one, ← readField_one]
    have hr := readField_gatherBits L W 2 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Layout.offset, Layout.size,
      show width + width = 2 * width by omega] using hr
  have hSign : bitValue gathered (Serial.signWire width) =
      bitValue I (signWire workWidth endpointWidth) := by
    rw [← readField_one, ← readField_one]
    have hr := readField_gatherBits L W 3 I (by simp [W, arithmeticWiring])
    simpa [gathered, L, W, arithmeticLayout, arithmeticWiring,
      Serial.signWire, Layout.offset, Layout.size,
      show width + (width + 1) = 2 * width + 1 by omega] using hr
  change actGates
      ((Serial.carryGates width).map (RGate.map (place L W))) I = _
  apply actGates_placed_write₂
      (L := L) (W := W) (k₁ := 0) (k₂ := 3)
      (v₁ := (readField I (targetOffset workWidth + left) width +
        readField I (sourceOffset + left) width +
        bitValue I (carryWire workWidth endpointWidth)) % 2 ^ width)
      (v₂ := (bitValue I (signWire workWidth endpointWidth) +
        (readField I (targetOffset workWidth + left) width +
          readField I (sourceOffset + left) width +
          bitValue I (carryWire workWidth endpointWidth)) / 2 ^ width) % 2)
      (arithmetic_disjoint hLR hR)
      (by simp [L, W, arithmeticLayout, arithmeticWiring])
      (by simp [L, arithmeticLayout])
      (by simp [L, arithmeticLayout])
      (by decide)
  · intro g hg
    rw [show Layout.width L = 2 * width + 2 by
      simp [L, arithmeticLayout_width]]
    exact RCircuit.wellFormed_mem
      (Serial.carryCircuit_wellFormed width) hg
  · have hlocal := Serial.carryGates_act
      (width := width) (i := gathered) hwidth
    rw [hlocal, hTarget, hSource, hCarry, hSign]
    simp [gathered, L, arithmeticLayout, Layout.write, Layout.offset,
      Layout.size, Serial.signWire,
      show width + (width + 1) = 2 * width + 1 by omega]

theorem idealGates_preserves_carry
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    bitValue (actGates (idealGates left right workWidth endpointWidth) I)
        (carryWire workWidth endpointWidth) =
      bitValue I (carryWire workWidth endpointWidth) := by
  rw [idealGates_act hLR hR]
  rw [bitValue_write_ne (by
      simp [carryWire, signWire, outerWire]),
    bitValue_write_out (by
      simp [targetOffset, carryWire, outerWire]
      omega)]

theorem activeGates_preserves_carry
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth) :
    bitValue (actGates (activeGates left right workWidth endpointWidth) I)
        (carryWire workWidth endpointWidth) =
      bitValue I (carryWire workWidth endpointWidth) := by
  rw [activeGates_eq_ideal hLR hR, idealGates_preserves_carry hLR hR]

theorem disabledForward_snoc (workWidth endpointWidth : Nat) : ∀ m j,
    disabledForward workWidth endpointWidth j (m + 1) =
      disabledForward workWidth endpointWidth j m ++
      disabledAt (j + m) workWidth endpointWidth := by
  intro m
  induction m with
  | zero => intro j; simp [disabledForward]
  | succ m ih =>
      intro j
      change disabledAt j workWidth endpointWidth ++
          disabledForward workWidth endpointWidth (j + 1) (m + 1) =
        (disabledAt j workWidth endpointWidth ++
          disabledForward workWidth endpointWidth (j + 1) m) ++
        disabledAt (j + (m + 1)) workWidth endpointWidth
      rw [ih (j + 1), List.append_assoc]
      simp only [show j + 1 + m = j + (m + 1) by omega]

theorem disabledForward_backward_cancel
    {j m workWidth endpointWidth I : Nat}
    (hbound : j + m ≤ workWidth) :
    actGates (disabledBackward workWidth endpointWidth (j + m) m)
        (actGates (disabledForward workWidth endpointWidth j m) I) = I := by
  induction m generalizing I with
  | zero => rfl
  | succ m ih =>
      rw [disabledForward_snoc, actGates_append]
      have htop : j + (m + 1) - 1 = j + m := by omega
      rw [show disabledBackward workWidth endpointWidth
          (j + (m + 1)) (m + 1) =
        disabledAt (j + m) workWidth endpointWidth ++
          disabledBackward workWidth endpointWidth (j + m) m by
        simp [disabledBackward, htop]]
      simp only [actGates_append]
      rw [disabledAt_involutive (by omega), ih (by omega)]

theorem disabledForward_identity_of_carry_clear
    {workWidth endpointWidth I : Nat} : ∀ m j,
    bitValue I (carryWire workWidth endpointWidth) = 0 →
    actGates (disabledForward workWidth endpointWidth j m) I = I := by
  intro m
  induction m generalizing I with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hcarry
      simp only [disabledForward, actGates_append]
      rw [disabledAt_identity_of_carry_clear hcarry]
      exact ih (j + 1) hcarry

theorem disabledBackward_identity_of_carry_clear
    {workWidth endpointWidth I : Nat} : ∀ m top,
    bitValue I (carryWire workWidth endpointWidth) = 0 →
    actGates (disabledBackward workWidth endpointWidth top m) I = I := by
  intro m
  induction m generalizing I with
  | zero => intro top _; rfl
  | succ m ih =>
      intro top hcarry
      simp only [disabledBackward, actGates_append]
      rw [disabledAt_identity_of_carry_clear hcarry]
      exact ih (top - 1) hcarry

theorem disabledAt_sign_comm
    {j workWidth endpointWidth I : Nat} (hj : j < workWidth) :
    actGates [.cx (carryWire workWidth endpointWidth)
        (signWire workWidth endpointWidth)]
        (actGates (disabledAt j workWidth endpointWidth) I) =
      actGates (disabledAt j workWidth endpointWidth)
        (actGates [.cx (carryWire workWidth endpointWidth)
          (signWire workWidth endpointWidth)] I) := by
  have hout : ∀ g ∈ disabledAt j workWidth endpointWidth,
      ∀ q ∈ g.wires,
      q < signWire workWidth endpointWidth ∨
        signWire workWidth endpointWidth + 1 ≤ q := by
    rw [disabledAt_eq_pair]
    intro g hg q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      simp [RGate.wires] at hq <;>
      rcases hq with rfl | rfl <;>
      simp [targetOffset, sourceOffset, carryWire, signWire, outerWire] <;>
      omega
  have hsign : bitValue
      (actGates (disabledAt j workWidth endpointWidth) I)
        (signWire workWidth endpointWidth) =
      bitValue I (signWire workWidth endpointWidth) := by
    rw [← readField_one,
      readField_actGates_of_outside hout I, readField_one]
  simp only [actGates_cons, actGates_nil, act_cx_write]
  rw [disabledAt_preserves_carry hj, hsign,
    actGates_write_of_outside hout]

theorem disabledBackward_sign_comm
    {m top workWidth endpointWidth I : Nat}
    (hmt : m ≤ top) (htop : top ≤ workWidth) :
    actGates [.cx (carryWire workWidth endpointWidth)
        (signWire workWidth endpointWidth)]
        (actGates (disabledBackward workWidth endpointWidth top m) I) =
      actGates (disabledBackward workWidth endpointWidth top m)
        (actGates [.cx (carryWire workWidth endpointWidth)
          (signWire workWidth endpointWidth)] I) := by
  induction m generalizing top I with
  | zero => rfl
  | succ m ih =>
      have htopPos : 0 < top := by omega
      simp only [disabledBackward, actGates_append]
      rw [ih (top := top - 1) (I := actGates
          (disabledAt (top - 1) workWidth endpointWidth) I)
          (by omega) (by omega),
        disabledAt_sign_comm (by omega)]

theorem disabled_sign_sandwich
    {j m workWidth endpointWidth I : Nat}
    (hbound : j + m ≤ workWidth) :
    actGates
        (disabledForward workWidth endpointWidth j m ++
          [.cx (carryWire workWidth endpointWidth)
            (signWire workWidth endpointWidth)] ++
          disabledBackward workWidth endpointWidth (j + m) m) I =
      actGates [.cx (carryWire workWidth endpointWidth)
        (signWire workWidth endpointWidth)] I := by
  simp only [actGates_append]
  rw [← disabledBackward_sign_comm (m := m) (top := j + m)
      (I := actGates (disabledForward workWidth endpointWidth j m) I)
      (by omega) hbound,
    disabledForward_backward_cancel hbound]

theorem selectedGates_eq_active_of_carry
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right) (hR : right < workWidth)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0)
    (hfinal : bitValue
      (actGates (activeGates left right workWidth endpointWidth) I)
        (carryWire workWidth endpointWidth) = 0) :
    actGates (selectedGates left right workWidth endpointWidth) I =
      actGates (activeGates left right workWidth endpointWidth) I := by
  let n := right - left + 1
  let u := workWidth - (right + 1)
  let lowForward := disabledForward workWidth endpointWidth 0 left
  let maj := baseMajForward workWidth endpointWidth left n
  let highForward := disabledForward workWidth endpointWidth (right + 1) u
  let sign : List RGate := [.cx (carryWire workWidth endpointWidth)
    (signWire workWidth endpointWidth)]
  let highBackward := disabledBackward workWidth endpointWidth workWidth u
  let uma := baseUmaBackward workWidth endpointWidth (right + 1) n
  let lowBackward := disabledBackward workWidth endpointWidth left left
  have hfirst := selectedFirstScan_decompose
    (endpointWidth := endpointWidth) hLR hR
  have hsecond := selectedSecondScan_decompose
    (endpointWidth := endpointWidth) hLR hR
  change selectedFirstScan left right workWidth endpointWidth 0 workWidth =
    lowForward ++ maj ++ highForward at hfirst
  change selectedSecondScan left right workWidth endpointWidth workWidth =
    highBackward ++ uma ++ lowBackward at hsecond
  have hlow := disabledForward_identity_of_carry_clear
    (workWidth := workWidth) (endpointWidth := endpointWidth)
    (I := I) left 0 hcarry
  change actGates lowForward I = I at hlow
  have hhigh := disabled_sign_sandwich
    (j := right + 1) (m := u) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (I := actGates maj I) (by
      dsimp [u]
      omega)
  have htop : right + 1 + u = workWidth := by
    dsimp [u]
    omega
  rw [htop] at hhigh
  change actGates (highForward ++ sign ++ highBackward)
    (actGates maj I) = actGates sign (actGates maj I) at hhigh
  simp only [actGates_append] at hhigh
  have hactive :
      actGates (activeGates left right workWidth endpointWidth) I =
        actGates uma (actGates sign (actGates maj I)) := by
    dsimp [activeGates, n, maj, sign, uma]
    simp only [actGates_append]
  have hlowBack := disabledBackward_identity_of_carry_clear
    (workWidth := workWidth) (endpointWidth := endpointWidth)
    (I := actGates uma (actGates sign (actGates maj I))) left left (by
      rw [← hactive]
      exact hfinal)
  change actGates lowBackward
    (actGates uma (actGates sign (actGates maj I))) =
      actGates uma (actGates sign (actGates maj I)) at hlowBack
  simp only [selectedGates, hfirst, hsecond, actGates_append]
  rw [hlow, hhigh, hlowBack]
  exact hactive.symm

def firstScan (workWidth endpointWidth : Nat) : Nat → Nat → List RGate
  | _, 0 => []
  | j, m + 1 =>
      leftToggle j workWidth endpointWidth ++
      majAt j workWidth endpointWidth ++
      rightToggle j workWidth endpointWidth ++
      firstScan workWidth endpointWidth (j + 1) m

def secondScan (workWidth endpointWidth : Nat) : Nat → List RGate
  | 0 => []
  | m + 1 =>
      rightToggle m workWidth endpointWidth ++
      umaAt m workWidth endpointWidth ++
      leftToggle m workWidth endpointWidth ++
      secondScan workWidth endpointWidth m

def gates (workWidth endpointWidth : Nat) : List RGate :=
  firstScan workWidth endpointWidth 0 workWidth ++
    [.cx (carryWire workWidth endpointWidth)
      (signWire workWidth endpointWidth)] ++
  secondScan workWidth endpointWidth workWidth

def circuit (workWidth endpointWidth : Nat) : RCircuit :=
  { width := (layout workWidth endpointWidth).width,
    gates := gates workWidth endpointWidth }

theorem layout_width (workWidth endpointWidth : Nat) :
    (layout workWidth endpointWidth).width =
      2 * workWidth + 3 * endpointWidth + 7 := by
  simp [layout, Layout.width]
  omega

theorem endpoint_disjoint {workWidth endpointWidth endpoint flag : Nat}
    (hendpoint : endpoint = leftOffset workWidth ∨
      endpoint = rightOffset workWidth endpointWidth)
    (hflag : flag = leftFlagWire workWidth endpointWidth ∨
      flag = rightFlagWire workWidth endpointWidth) :
    Wiring.Disjoint (Endpoint.layout endpointWidth)
      (endpointWiring workWidth endpointWidth endpoint flag) := by
  intro j k hj hk hne
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
    simp [endpointWiring] at hj
    omega
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    simp [endpointWiring] at hk
    omega
  rcases hendpoint with rfl | rfl <;>
    rcases hflag with rfl | rfl <;>
    rcases hj' with rfl | rfl | rfl | rfl | rfl <;>
    rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
    simp [Endpoint.layout, endpointWiring, Layout.size, leftOffset, rightOffset,
      outerWire, accumulatorWire, leftFlagWire, rightFlagWire,
      selectorScratchOffset] at * <;>
    omega

theorem cell_disjoint {j workWidth endpointWidth : Nat}
    (hj : j < workWidth) :
    Wiring.Disjoint CellPlaced.layout
      (cellWiring j workWidth endpointWidth) := by
  intro a b ha hb hne
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
    simp [cellWiring, CellPlaced.wiring] at ha
    omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by
    simp [cellWiring, CellPlaced.wiring] at hb
    omega
  rcases ha' with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl | rfl | rfl <;>
    simp [CellPlaced.layout, cellWiring, CellPlaced.wiring, Layout.size,
      targetOffset, sourceOffset, carryWire, accumulatorWire, cellScratchWire,
      selectorScratchOffset, outerWire] at * <;>
    omega

theorem majAt_reduces {j workWidth endpointWidth I : Nat}
    (hj : j < workWidth)
    (hscratch : I.testBit (cellScratchWire workWidth endpointWidth) = false) :
    actGates (majAt j workWidth endpointWidth) I =
      if I.testBit (accumulatorWire workWidth endpointWidth) then
        actGates (baseMajAt j workWidth endpointWidth) I
      else actGates (disabledAt j workWidth endpointWidth) I := by
  by_cases hcontrol : I.testBit
      (accumulatorWire workWidth endpointWidth) = true
  · rw [if_pos hcontrol]
    exact CellPlaced.maj_enabled (cell_disjoint hj) hcontrol hscratch
  · rw [if_neg hcontrol]
    exact CellPlaced.maj_control_clear (cell_disjoint hj)
      (Bool.eq_false_iff.mpr hcontrol) hscratch

theorem umaAt_reduces {j workWidth endpointWidth I : Nat}
    (hj : j < workWidth)
    (hscratch : I.testBit (cellScratchWire workWidth endpointWidth) = false) :
    actGates (umaAt j workWidth endpointWidth) I =
      if I.testBit (accumulatorWire workWidth endpointWidth) then
        actGates (baseUmaAt j workWidth endpointWidth) I
      else actGates (disabledAt j workWidth endpointWidth) I := by
  by_cases hcontrol : I.testBit
      (accumulatorWire workWidth endpointWidth) = true
  · rw [if_pos hcontrol]
    exact CellPlaced.uma_enabled (cell_disjoint hj) hcontrol hscratch
  · rw [if_neg hcontrol]
    exact CellPlaced.uma_control_clear (cell_disjoint hj)
      (Bool.eq_false_iff.mpr hcontrol) hscratch

theorem majAt_preserves_stable {left right j workWidth endpointWidth I : Nat}
    (hj : j < workWidth)
    (h : Stable left right workWidth endpointWidth I) :
    Stable left right workWidth endpointWidth
      (actGates (majAt j workWidth endpointWidth) I) := by
  rw [majAt_reduces hj h.cellScratchClear]
  by_cases hcontrol : I.testBit
      (accumulatorWire workWidth endpointWidth) = true
  · rw [if_pos hcontrol, baseMajAt_eq_core]
    exact core_preserves_stable hj
      (fun g hg => RCircuit.wellFormed_mem
        (by decide : Cell.baseMajCircuit.wellFormed = true) hg) h
  · rw [if_neg hcontrol, disabledAt_eq_core]
    exact core_preserves_stable hj (by decide) h

theorem umaAt_preserves_stable {left right j workWidth endpointWidth I : Nat}
    (hj : j < workWidth)
    (h : Stable left right workWidth endpointWidth I) :
    Stable left right workWidth endpointWidth
      (actGates (umaAt j workWidth endpointWidth) I) := by
  rw [umaAt_reduces hj h.cellScratchClear]
  by_cases hcontrol : I.testBit
      (accumulatorWire workWidth endpointWidth) = true
  · rw [if_pos hcontrol, baseUmaAt_eq_core]
    exact core_preserves_stable hj
      (fun g hg => RCircuit.wellFormed_mem
        (by decide : Cell.baseUmaCircuit.wellFormed = true) hg) h
  · rw [if_neg hcontrol, disabledAt_eq_core]
    exact core_preserves_stable hj (by decide) h

theorem selectedMajAt_preserves_stable
    {left right j workWidth endpointWidth I : Nat}
    (hj : j < workWidth)
    (h : Stable left right workWidth endpointWidth I) :
    Stable left right workWidth endpointWidth
      (actGates (selectedMajAt left right j workWidth endpointWidth) I) := by
  by_cases hselected : left ≤ j ∧ j ≤ right
  · rw [selectedMajAt, if_pos hselected, baseMajAt_eq_core]
    exact core_preserves_stable hj (by decide) h
  · rw [selectedMajAt, if_neg hselected, disabledAt_eq_core]
    exact core_preserves_stable hj (by decide) h

theorem selectedUmaAt_preserves_stable
    {left right j workWidth endpointWidth I : Nat}
    (hj : j < workWidth)
    (h : Stable left right workWidth endpointWidth I) :
    Stable left right workWidth endpointWidth
      (actGates (selectedUmaAt left right j workWidth endpointWidth) I) := by
  by_cases hselected : left ≤ j ∧ j ≤ right
  · rw [selectedUmaAt, if_pos hselected, baseUmaAt_eq_core]
    exact core_preserves_stable hj (by decide) h
  · rw [selectedUmaAt, if_neg hselected, disabledAt_eq_core]
    exact core_preserves_stable hj (by decide) h

theorem selectedMajAt_writeAccumulator
    {left right j workWidth endpointWidth I v : Nat}
    (hj : j < workWidth) :
    actGates (selectedMajAt left right j workWidth endpointWidth)
        (writeField I (accumulatorWire workWidth endpointWidth) 1 v) =
      writeField
        (actGates (selectedMajAt left right j workWidth endpointWidth) I)
        (accumulatorWire workWidth endpointWidth) 1 v := by
  by_cases hselected : left ≤ j ∧ j ≤ right
  · rw [selectedMajAt, if_pos hselected, baseMajAt_eq_core]
    exact coreGates_writeAccumulator hj (by decide)
  · rw [selectedMajAt, if_neg hselected, disabledAt_eq_core]
    exact coreGates_writeAccumulator hj (by decide)

theorem selectedUmaAt_writeAccumulator
    {left right j workWidth endpointWidth I v : Nat}
    (hj : j < workWidth) :
    actGates (selectedUmaAt left right j workWidth endpointWidth)
        (writeField I (accumulatorWire workWidth endpointWidth) 1 v) =
      writeField
        (actGates (selectedUmaAt left right j workWidth endpointWidth) I)
        (accumulatorWire workWidth endpointWidth) 1 v := by
  by_cases hselected : left ≤ j ∧ j ≤ right
  · rw [selectedUmaAt, if_pos hselected, baseUmaAt_eq_core]
    exact coreGates_writeAccumulator hj (by decide)
  · rw [selectedUmaAt, if_neg hselected, disabledAt_eq_core]
    exact coreGates_writeAccumulator hj (by decide)

theorem selectedFirstScan_preserves_stable
    {left right workWidth endpointWidth I : Nat}
    (h : Stable left right workWidth endpointWidth I) :
    ∀ m j, j + m ≤ workWidth →
    Stable left right workWidth endpointWidth
      (actGates
        (selectedFirstScan left right workWidth endpointWidth j m) I) := by
  intro m
  induction m generalizing I with
  | zero =>
      intro j _
      rw [selectedFirstScan, actGates_nil]
      exact h
  | succ m ih =>
      intro j hbound
      simp only [selectedFirstScan, actGates_append]
      exact ih
        (selectedMajAt_preserves_stable (by omega) h)
        (j + 1) (by omega)

theorem selectedSecondScan_preserves_stable
    {left right workWidth endpointWidth I : Nat}
    (h : Stable left right workWidth endpointWidth I) :
    ∀ m, m ≤ workWidth →
    Stable left right workWidth endpointWidth
      (actGates
        (selectedSecondScan left right workWidth endpointWidth m) I) := by
  intro m
  induction m generalizing I with
  | zero =>
      intro _
      rw [selectedSecondScan, actGates_nil]
      exact h
  | succ m ih =>
      intro hbound
      simp only [selectedSecondScan, actGates_append]
      exact ih
        (selectedUmaAt_preserves_stable (by omega) h)
        (by omega)

theorem selectedFirstScan_writeAccumulator
    {left right workWidth endpointWidth I v : Nat} :
    ∀ m j, j + m ≤ workWidth →
    actGates (selectedFirstScan left right workWidth endpointWidth j m)
        (writeField I (accumulatorWire workWidth endpointWidth) 1 v) =
      writeField
        (actGates
          (selectedFirstScan left right workWidth endpointWidth j m) I)
        (accumulatorWire workWidth endpointWidth) 1 v := by
  intro m
  induction m generalizing I with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [selectedFirstScan, actGates_append]
      rw [selectedMajAt_writeAccumulator (by omega),
        ih (j := j + 1) (by omega)]

theorem selectedSecondScan_writeAccumulator
    {left right workWidth endpointWidth I v : Nat} :
    ∀ m, m ≤ workWidth →
    actGates (selectedSecondScan left right workWidth endpointWidth m)
        (writeField I (accumulatorWire workWidth endpointWidth) 1 v) =
      writeField
        (actGates
          (selectedSecondScan left right workWidth endpointWidth m) I)
        (accumulatorWire workWidth endpointWidth) 1 v := by
  intro m
  induction m generalizing I with
  | zero => intro _; rfl
  | succ m ih =>
      intro hbound
      simp only [selectedSecondScan, actGates_append]
      rw [selectedUmaAt_writeAccumulator (by omega),
        ih (by omega)]

theorem endpointGates_wellFormed {value workWidth endpointWidth endpoint flag : Nat}
    (hendpoint : endpoint = leftOffset workWidth ∨
      endpoint = rightOffset workWidth endpointWidth)
    (hflag : flag = leftFlagWire workWidth endpointWidth ∨
      flag = rightFlagWire workWidth endpointWidth) :
    (endpointGates value workWidth endpointWidth endpoint flag).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  apply wellFormed_placeGates (endpoint_disjoint hendpoint hflag)
    (by simp [Endpoint.layout, endpointWiring])
  · intro j hj
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
      simp [Endpoint.layout] at hj
      omega
    rcases hendpoint with rfl | rfl <;>
      rcases hflag with rfl | rfl <;>
      rcases hj' with rfl | rfl | rfl | rfl | rfl <;>
      simp [endpointWiring, Endpoint.layout, Layout.size, layout_width,
        leftOffset, rightOffset, outerWire, accumulatorWire, leftFlagWire,
        rightFlagWire, selectorScratchOffset] <;>
      omega
  · intro g hg
    exact RCircuit.wellFormed_mem (Endpoint.circuit_wellFormed value endpointWidth) hg

theorem endpointGates_act {value workWidth endpointWidth endpoint flag I : Nat}
    (hendpoint : endpoint = leftOffset workWidth ∨
      endpoint = rightOffset workWidth endpointWidth)
    (hflagWire : flag = leftFlagWire workWidth endpointWidth ∨
      flag = rightFlagWire workWidth endpointWidth)
    (hflag : bitValue I flag = 0)
    (hscratch : readField I
      (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0) :
    actGates (endpointGates value workWidth endpointWidth endpoint flag) I =
      writeField I (accumulatorWire workWidth endpointWidth) 1
        ((bitValue I (accumulatorWire workWidth endpointWidth) +
          if I.testBit (outerWire workWidth endpointWidth) &&
              decide (readField I endpoint endpointWidth =
                value % 2 ^ endpointWidth) then 1 else 0) % 2) := by
  let L := Endpoint.layout endpointWidth
  let W := endpointWiring workWidth endpointWidth endpoint flag
  let gathered := gatherBits (place L W) L.width I
  have hEndpoint : readField gathered 0 endpointWidth =
      readField I endpoint endpointWidth := by
    have h := readField_gatherBits L W 0 I (by simp [W, endpointWiring])
    simpa [gathered, L, W, Endpoint.layout, endpointWiring,
      Layout.offset, Layout.size] using h
  have hOuter : bitValue gathered (Endpoint.outerWire endpointWidth) =
      bitValue I (outerWire workWidth endpointWidth) := by
    rw [← readField_one, ← readField_one]
    have h := readField_gatherBits L W 1 I (by simp [W, endpointWiring])
    simpa [gathered, L, W, Endpoint.layout, endpointWiring,
      Endpoint.outerWire, Layout.offset, Layout.size] using h
  have hAccumulator : bitValue gathered
      (Endpoint.accumulatorWire endpointWidth) =
      bitValue I (accumulatorWire workWidth endpointWidth) := by
    rw [← readField_one, ← readField_one]
    have h := readField_gatherBits L W 2 I (by simp [W, endpointWiring])
    simpa [gathered, L, W, Endpoint.layout, endpointWiring,
      Endpoint.accumulatorWire, Layout.offset, Layout.size] using h
  have hFlag : bitValue gathered (Endpoint.flagWire endpointWidth) = 0 := by
    have h := readField_gatherBits L W 3 I (by simp [W, endpointWiring])
    have h' : readField gathered (Endpoint.flagWire endpointWidth) 1 =
        readField I flag 1 := by
      simpa [gathered, L, W, endpointWiring, Endpoint.layout,
        Endpoint.flagWire, Layout.offset, Layout.size] using h
    rw [← readField_one, h', readField_one, hflag]
  have hScratch : readField gathered (Endpoint.scratchWire endpointWidth)
      endpointWidth = 0 := by
    have h := readField_gatherBits L W 4 I (by simp [W, endpointWiring])
    have h' : readField gathered (Endpoint.scratchWire endpointWidth)
        endpointWidth = readField I
          (selectorScratchOffset workWidth endpointWidth) endpointWidth := by
      simpa [gathered, L, W, endpointWiring, Endpoint.layout,
        Endpoint.scratchWire, Layout.offset, Layout.size] using h
    rw [h', hscratch]
  apply actGates_placed_write (endpoint_disjoint hendpoint hflagWire)
    (by simp [Endpoint.layout, endpointWiring]) (k := 2)
    (v := (bitValue I (accumulatorWire workWidth endpointWidth) +
      if I.testBit (outerWire workWidth endpointWidth) &&
          decide (readField I endpoint endpointWidth =
            value % 2 ^ endpointWidth) then 1 else 0) % 2)
  · simp [Endpoint.layout]
  · intro g hg
    exact RCircuit.wellFormed_mem
      (Endpoint.circuit_wellFormed value endpointWidth) hg
  · have hlocal := Endpoint.circuit_act (value := value) hFlag hScratch
    change actGates (Endpoint.circuit value endpointWidth).gates gathered = _ at hlocal
    rw [hlocal]
    change writeField gathered (Endpoint.accumulatorWire endpointWidth) 1
      ((bitValue gathered (Endpoint.accumulatorWire endpointWidth) +
        Endpoint.selected value endpointWidth gathered) % 2) = _
    rw [hAccumulator]
    unfold Endpoint.selected
    rw [hEndpoint]
    have hOuterTest : gathered.testBit (Endpoint.outerWire endpointWidth) =
        I.testBit (outerWire workWidth endpointWidth) := by
      cases hg : gathered.testBit (Endpoint.outerWire endpointWidth) <;>
        cases hi : I.testBit (outerWire workWidth endpointWidth) <;>
        simp [bitValue, hg, hi] at hOuter ⊢
    rw [hOuterTest]
    rfl

theorem endpointGates_eq_x_or_id
    {value workWidth endpointWidth endpoint flag I : Nat}
    (hendpoint : endpoint = leftOffset workWidth ∨
      endpoint = rightOffset workWidth endpointWidth)
    (hflagWire : flag = leftFlagWire workWidth endpointWidth ∨
      flag = rightFlagWire workWidth endpointWidth)
    (hflag : bitValue I flag = 0)
    (hscratch : readField I
      (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0) :
    actGates (endpointGates value workWidth endpointWidth endpoint flag) I =
      if I.testBit (outerWire workWidth endpointWidth) &&
          decide (readField I endpoint endpointWidth =
            value % 2 ^ endpointWidth) then
        RGate.act (.x (accumulatorWire workWidth endpointWidth)) I
      else I := by
  rw [endpointGates_act hendpoint hflagWire hflag hscratch]
  by_cases hselected : I.testBit (outerWire workWidth endpointWidth) &&
      decide (readField I endpoint endpointWidth =
        value % 2 ^ endpointWidth)
  · rw [if_pos hselected, if_pos hselected, act_x_write]
  · rw [if_neg hselected, if_neg hselected]
    simp only [Nat.add_zero]
    rw [Nat.mod_eq_of_lt
        (bitValue_lt I (accumulatorWire workWidth endpointWidth)),
      ← readField_one, writeField_read]

theorem leftToggle_preserves_stable
    {left right value workWidth endpointWidth I : Nat}
    (h : Stable left right workWidth endpointWidth I) :
    Stable left right workWidth endpointWidth
      (actGates (leftToggle value workWidth endpointWidth) I) := by
  have ha := endpointGates_act (value := value) (I := I)
    (Or.inl rfl) (Or.inl rfl) h.leftFlagClear h.selectorScratchClear
  change actGates (leftToggle value workWidth endpointWidth) I = _ at ha
  rw [ha]
  exact h.writeAccumulator

theorem rightToggle_preserves_stable
    {left right value workWidth endpointWidth I : Nat}
    (h : Stable left right workWidth endpointWidth I) :
    Stable left right workWidth endpointWidth
      (actGates (rightToggle value workWidth endpointWidth) I) := by
  have ha := endpointGates_act (value := value) (I := I)
    (Or.inr rfl) (Or.inr rfl) h.rightFlagClear h.selectorScratchClear
  change actGates (rightToggle value workWidth endpointWidth) I = _ at ha
  rw [ha]
  exact h.writeAccumulator

theorem fixedToggle_preserves_stable
    {left right endpoint j workWidth endpointWidth I : Nat}
    (h : Stable left right workWidth endpointWidth I) :
    Stable left right workWidth endpointWidth
      (actGates (fixedToggle endpoint j workWidth endpointWidth) I) := by
  by_cases heq : j = endpoint
  · simp only [fixedToggle, if_pos heq, actGates_cons, actGates_nil,
      act_x_write]
    exact h.writeAccumulator
  · simp only [fixedToggle, if_neg heq, actGates_nil]
    exact h

theorem fixedToggle_act {endpoint j workWidth endpointWidth I : Nat} :
    actGates (fixedToggle endpoint j workWidth endpointWidth) I =
      writeField I (accumulatorWire workWidth endpointWidth) 1
        ((bitValue I (accumulatorWire workWidth endpointWidth) +
          if j = endpoint then 1 else 0) % 2) := by
  by_cases heq : j = endpoint
  · simp only [fixedToggle, if_pos heq, actGates_cons, actGates_nil]
    exact act_x_write _ _
  · simp only [fixedToggle, if_neg heq, actGates_nil, Nat.add_zero]
    rw [Nat.mod_eq_of_lt
        (bitValue_lt I (accumulatorWire workWidth endpointWidth)),
      ← readField_one, writeField_read]

theorem scanAccumulator_left {left right j : Nat} (hLR : left ≤ right) :
    (scanAccumulator left right j + (if j = left then 1 else 0)) % 2 =
      if left ≤ j ∧ j ≤ right then 1 else 0 := by
  unfold scanAccumulator
  by_cases hbefore : left < j ∧ j ≤ right <;>
    by_cases htoggle : j = left <;>
    by_cases hactive : left ≤ j ∧ j ≤ right <;>
    simp [hbefore, htoggle, hactive] <;>
    omega

theorem scanAccumulator_right {left right j : Nat} (hLR : left ≤ right) :
    ((if left ≤ j ∧ j ≤ right then 1 else 0) +
        (if j = right then 1 else 0)) % 2 =
      scanAccumulator left right (j + 1) := by
  unfold scanAccumulator
  by_cases heq : j = right
  · subst j
    have hleft : left < right + 1 := by omega
    have hright : ¬right + 1 ≤ right := by omega
    simp [hLR, hleft, hright]
  · by_cases hjr : j < right
    · have hjle : j ≤ right := by omega
      have hnextRight : j + 1 ≤ right := by omega
      by_cases hlj : left ≤ j
      · have hnextLeft : left < j + 1 := by omega
        simp [heq, hjle, hlj, hnextLeft, hnextRight]
      · have hjl : j < left := by omega
        have hnextLeft : ¬left < j + 1 := by omega
        simp [heq, hjle, hlj, hnextLeft, hnextRight]
    · have hrj : right < j := by omega
      have hactive : ¬(left ≤ j ∧ j ≤ right) := by omega
      have hafter : ¬(left < j + 1 ∧ j + 1 ≤ right) := by omega
      simp [heq, hactive, hafter]

theorem scanAccumulator_zero (left right : Nat) :
    scanAccumulator left right 0 = 0 := by
  simp [scanAccumulator]

theorem scanAccumulator_width {left right workWidth : Nat}
    (hR : right < workWidth) :
    scanAccumulator left right workWidth = 0 := by
  simp [scanAccumulator]
  omega

theorem scanAccumulator_right_reverse {left right j : Nat}
    (hLR : left ≤ right) :
    (scanAccumulator left right (j + 1) +
        (if j = right then 1 else 0)) % 2 =
      if left ≤ j ∧ j ≤ right then 1 else 0 := by
  have h := scanAccumulator_right (left := left) (right := right)
    (j := j) hLR
  rw [← h]
  have hactive : (if left ≤ j ∧ j ≤ right then 1 else 0) < 2 := by
    by_cases ha : left ≤ j ∧ j ≤ right <;> simp [ha]
  have htoggle : (if j = right then 1 else 0) < 2 := by
    by_cases ht : j = right <;> simp [ht]
  omega

theorem scanAccumulator_left_reverse {left right j : Nat}
    (hLR : left ≤ right) :
    ((if left ≤ j ∧ j ≤ right then 1 else 0) +
        (if j = left then 1 else 0)) % 2 =
      scanAccumulator left right j := by
  have h := scanAccumulator_left (left := left) (right := right)
    (j := j) hLR
  rw [← h]
  have hbefore : scanAccumulator left right j < 2 := by
    unfold scanAccumulator
    by_cases hb : left < j ∧ j ≤ right <;> simp [hb]
  have htoggle : (if j = left then 1 else 0) < 2 := by
    by_cases ht : j = left <;> simp [ht]
  omega

theorem fixedFirstStep_act
    {left right j workWidth endpointWidth I : Nat}
    (hLR : left ≤ right)
    (hj : j < workWidth)
    (h : Stable left right workWidth endpointWidth I)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) =
      scanAccumulator left right j) :
    actGates
        (fixedToggle left j workWidth endpointWidth ++
          majAt j workWidth endpointWidth ++
          fixedToggle right j workWidth endpointWidth) I =
      writeField
        (actGates (selectedMajAt left right j workWidth endpointWidth) I)
        (accumulatorWire workWidth endpointWidth) 1
        (scanAccumulator left right (j + 1)) := by
  let active := if left ≤ j ∧ j ≤ right then 1 else 0
  let i₁ := actGates (fixedToggle left j workWidth endpointWidth) I
  have hi₁ : i₁ = writeField I
      (accumulatorWire workWidth endpointWidth) 1 active := by
    rw [show i₁ = actGates
      (fixedToggle left j workWidth endpointWidth) I from rfl,
      fixedToggle_act, hacc, scanAccumulator_left hLR]
  have hs₁ : Stable left right workWidth endpointWidth i₁ :=
    fixedToggle_preserves_stable h
  have hcell : actGates (majAt j workWidth endpointWidth) i₁ =
      actGates (selectedMajAt left right j workWidth endpointWidth) i₁ := by
    rw [majAt_reduces hj hs₁.cellScratchClear]
    by_cases hselected : left ≤ j ∧ j ≤ right
    · have htest : i₁.testBit
          (accumulatorWire workWidth endpointWidth) = true := by
        rw [hi₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp [active, hselected]
      rw [if_pos htest]
      simp [selectedMajAt, hselected]
    · have htest : i₁.testBit
          (accumulatorWire workWidth endpointWidth) = false := by
        rw [hi₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp [active, hselected]
      have hnot : ¬i₁.testBit
          (accumulatorWire workWidth endpointWidth) = true := by
        rw [htest]
        decide
      rw [if_neg hnot]
      simp [selectedMajAt, hselected]
  let i₂ := actGates (majAt j workWidth endpointWidth) i₁
  have hi₂ : i₂ = writeField
      (actGates (selectedMajAt left right j workWidth endpointWidth) I)
      (accumulatorWire workWidth endpointWidth) 1 active := by
    rw [show i₂ = actGates (majAt j workWidth endpointWidth) i₁ from rfl,
      hcell, hi₁, selectedMajAt_writeAccumulator hj]
  have hactive : active < 2 := by
    dsimp [active]
    by_cases hselected : left ≤ j ∧ j ≤ right <;>
      simp [hselected]
  simp only [actGates_append]
  change actGates (fixedToggle right j workWidth endpointWidth) i₂ = _
  rw [fixedToggle_act, hi₂, bitValue_write_self,
    Nat.mod_eq_of_lt hactive, scanAccumulator_right hLR,
    writeField_writeField]

theorem fixedFirstScan_act
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right)
    (h : Stable left right workWidth endpointWidth I) :
    ∀ m j, j + m ≤ workWidth →
    bitValue I (accumulatorWire workWidth endpointWidth) =
      scanAccumulator left right j →
    actGates (fixedFirstScan left right workWidth endpointWidth j m) I =
      writeField
        (actGates
          (selectedFirstScan left right workWidth endpointWidth j m) I)
        (accumulatorWire workWidth endpointWidth) 1
        (scanAccumulator left right (j + m)) := by
  intro m
  induction m generalizing I with
  | zero =>
      intro j _ hacc
      rw [fixedFirstScan, selectedFirstScan, actGates_nil, Nat.add_zero,
        ← hacc, ← readField_one, writeField_read]
  | succ m ih =>
      intro j hbound hacc
      let stepGates :=
        fixedToggle left j workWidth endpointWidth ++
          majAt j workWidth endpointWidth ++
          fixedToggle right j workWidth endpointWidth
      let stepState := actGates stepGates I
      have hstep : stepState = writeField
          (actGates
            (selectedMajAt left right j workWidth endpointWidth) I)
          (accumulatorWire workWidth endpointWidth) 1
          (scanAccumulator left right (j + 1)) := by
        exact fixedFirstStep_act hLR (by omega) h hacc
      have hsStep : Stable left right workWidth endpointWidth stepState := by
        dsimp [stepState, stepGates]
        simp only [actGates_append]
        exact fixedToggle_preserves_stable
          (majAt_preserves_stable (by omega)
            (fixedToggle_preserves_stable h))
      have hscan : scanAccumulator left right (j + 1) < 2 := by
        unfold scanAccumulator
        by_cases hs : left < j + 1 ∧ j + 1 ≤ right <;> simp [hs]
      have haccStep : bitValue stepState
          (accumulatorWire workWidth endpointWidth) =
          scanAccumulator left right (j + 1) := by
        rw [hstep, bitValue_write_self, Nat.mod_eq_of_lt hscan]
      rw [show fixedFirstScan left right workWidth endpointWidth j (m + 1) =
          stepGates ++
            fixedFirstScan left right workWidth endpointWidth (j + 1) m
        from rfl,
        actGates_append,
        ih hsStep (j + 1) (by omega) haccStep,
        hstep,
        selectedFirstScan_writeAccumulator (m := m) (j := j + 1)
          (by omega),
        show selectedFirstScan left right workWidth endpointWidth j (m + 1) =
          selectedMajAt left right j workWidth endpointWidth ++
            selectedFirstScan left right workWidth endpointWidth (j + 1) m
          from rfl,
        actGates_append,
        writeField_writeField]
      congr 2
      omega

theorem fixedSecondStep_act
    {left right j workWidth endpointWidth I : Nat}
    (hLR : left ≤ right)
    (hj : j < workWidth)
    (h : Stable left right workWidth endpointWidth I)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) =
      scanAccumulator left right (j + 1)) :
    actGates
        (fixedToggle right j workWidth endpointWidth ++
          umaAt j workWidth endpointWidth ++
          fixedToggle left j workWidth endpointWidth) I =
      writeField
        (actGates (selectedUmaAt left right j workWidth endpointWidth) I)
        (accumulatorWire workWidth endpointWidth) 1
        (scanAccumulator left right j) := by
  let active := if left ≤ j ∧ j ≤ right then 1 else 0
  let i₁ := actGates (fixedToggle right j workWidth endpointWidth) I
  have hi₁ : i₁ = writeField I
      (accumulatorWire workWidth endpointWidth) 1 active := by
    rw [show i₁ = actGates
      (fixedToggle right j workWidth endpointWidth) I from rfl,
      fixedToggle_act, hacc, scanAccumulator_right_reverse hLR]
  have hs₁ : Stable left right workWidth endpointWidth i₁ :=
    fixedToggle_preserves_stable h
  have hcell : actGates (umaAt j workWidth endpointWidth) i₁ =
      actGates (selectedUmaAt left right j workWidth endpointWidth) i₁ := by
    rw [umaAt_reduces hj hs₁.cellScratchClear]
    by_cases hselected : left ≤ j ∧ j ≤ right
    · have htest : i₁.testBit
          (accumulatorWire workWidth endpointWidth) = true := by
        rw [hi₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp [active, hselected]
      rw [if_pos htest]
      simp [selectedUmaAt, hselected]
    · have htest : i₁.testBit
          (accumulatorWire workWidth endpointWidth) = false := by
        rw [hi₁, testBit_writeField_inside (Nat.le_refl _) (by omega)]
        simp [active, hselected]
      have hnot : ¬i₁.testBit
          (accumulatorWire workWidth endpointWidth) = true := by
        rw [htest]
        decide
      rw [if_neg hnot]
      simp [selectedUmaAt, hselected]
  let i₂ := actGates (umaAt j workWidth endpointWidth) i₁
  have hi₂ : i₂ = writeField
      (actGates (selectedUmaAt left right j workWidth endpointWidth) I)
      (accumulatorWire workWidth endpointWidth) 1 active := by
    rw [show i₂ = actGates (umaAt j workWidth endpointWidth) i₁ from rfl,
      hcell, hi₁, selectedUmaAt_writeAccumulator hj]
  have hactive : active < 2 := by
    dsimp [active]
    by_cases hselected : left ≤ j ∧ j ≤ right <;>
      simp [hselected]
  simp only [actGates_append]
  change actGates (fixedToggle left j workWidth endpointWidth) i₂ = _
  rw [fixedToggle_act, hi₂, bitValue_write_self,
    Nat.mod_eq_of_lt hactive, scanAccumulator_left_reverse hLR,
    writeField_writeField]

theorem fixedSecondScan_act
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right)
    (h : Stable left right workWidth endpointWidth I) :
    ∀ m, m ≤ workWidth →
    bitValue I (accumulatorWire workWidth endpointWidth) =
      scanAccumulator left right m →
    actGates (fixedSecondScan left right workWidth endpointWidth m) I =
      writeField
        (actGates
          (selectedSecondScan left right workWidth endpointWidth m) I)
        (accumulatorWire workWidth endpointWidth) 1
        (scanAccumulator left right 0) := by
  intro m
  induction m generalizing I with
  | zero =>
      intro _ hacc
      rw [fixedSecondScan, selectedSecondScan, actGates_nil,
        ← hacc, ← readField_one, writeField_read]
  | succ m ih =>
      intro hbound hacc
      let stepGates :=
        fixedToggle right m workWidth endpointWidth ++
          umaAt m workWidth endpointWidth ++
          fixedToggle left m workWidth endpointWidth
      let stepState := actGates stepGates I
      have hstep : stepState = writeField
          (actGates
            (selectedUmaAt left right m workWidth endpointWidth) I)
          (accumulatorWire workWidth endpointWidth) 1
          (scanAccumulator left right m) := by
        exact fixedSecondStep_act hLR (by omega) h hacc
      have hsStep : Stable left right workWidth endpointWidth stepState := by
        dsimp [stepState, stepGates]
        simp only [actGates_append]
        exact fixedToggle_preserves_stable
          (umaAt_preserves_stable (by omega)
            (fixedToggle_preserves_stable h))
      have hscan : scanAccumulator left right m < 2 := by
        unfold scanAccumulator
        by_cases hs : left < m ∧ m ≤ right <;> simp [hs]
      have haccStep : bitValue stepState
          (accumulatorWire workWidth endpointWidth) =
          scanAccumulator left right m := by
        rw [hstep, bitValue_write_self, Nat.mod_eq_of_lt hscan]
      rw [show fixedSecondScan left right workWidth endpointWidth (m + 1) =
          stepGates ++
            fixedSecondScan left right workWidth endpointWidth m
        from rfl,
        actGates_append,
        ih hsStep (by omega) haccStep,
        hstep,
        selectedSecondScan_writeAccumulator (m := m) (by omega),
        show selectedSecondScan left right workWidth endpointWidth (m + 1) =
          selectedUmaAt left right m workWidth endpointWidth ++
            selectedSecondScan left right workWidth endpointWidth m
          from rfl,
        actGates_append,
        writeField_writeField]

theorem fixedGates_eq_selected
    {left right workWidth endpointWidth I : Nat}
    (hLR : left ≤ right)
    (hR : right < workWidth)
    (h : Stable left right workWidth endpointWidth I)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0) :
    actGates (fixedGates left right workWidth endpointWidth) I =
      actGates (selectedGates left right workWidth endpointWidth) I := by
  let firstSelected :=
    selectedFirstScan left right workWidth endpointWidth 0 workWidth
  have hIclear : writeField I
      (accumulatorWire workWidth endpointWidth) 1 0 = I := by
    rw [show 0 = bitValue I
      (accumulatorWire workWidth endpointWidth) from hacc.symm,
      ← readField_one, writeField_read]
  have hfirstWrite := selectedFirstScan_writeAccumulator
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (I := I) (v := 0)
    workWidth 0 (by omega)
  change actGates firstSelected
      (writeField I (accumulatorWire workWidth endpointWidth) 1 0) =
    writeField (actGates firstSelected I)
      (accumulatorWire workWidth endpointWidth) 1 0 at hfirstWrite
  rw [hIclear] at hfirstWrite
  have hfirst := fixedFirstScan_act hLR h workWidth 0 (by omega) (by
    rw [hacc, scanAccumulator_zero])
  simp only [Nat.zero_add] at hfirst
  change actGates
      (fixedFirstScan left right workWidth endpointWidth 0 workWidth) I =
    writeField (actGates firstSelected I)
      (accumulatorWire workWidth endpointWidth) 1
      (scanAccumulator left right workWidth) at hfirst
  rw [scanAccumulator_width hR, ← hfirstWrite] at hfirst
  let i₁ := actGates firstSelected I
  have hs₁ : Stable left right workWidth endpointWidth i₁ :=
    selectedFirstScan_preserves_stable h workWidth 0 (by omega)
  have hi₁acc : bitValue i₁
      (accumulatorWire workWidth endpointWidth) = 0 := by
    have hb := congrArg
      (fun J => bitValue J (accumulatorWire workWidth endpointWidth))
      hfirstWrite
    rw [bitValue_write_self] at hb
    simpa using hb
  let i₂ := actGates
    [.cx (carryWire workWidth endpointWidth)
      (signWire workWidth endpointWidth)] i₁
  have hs₂ : Stable left right workWidth endpointWidth i₂ :=
    signGate_preserves_stable hs₁
  have hi₂acc : bitValue i₂
      (accumulatorWire workWidth endpointWidth) = 0 := by
    rw [show i₂ = actGates
      [.cx (carryWire workWidth endpointWidth)
        (signWire workWidth endpointWidth)] i₁ from rfl,
      actGates_cons, actGates_nil, act_cx_write,
      bitValue_write_ne (by
        simp [signWire, accumulatorWire, outerWire])]
    exact hi₁acc
  let secondSelected :=
    selectedSecondScan left right workWidth endpointWidth workWidth
  have hi₂clear : writeField i₂
      (accumulatorWire workWidth endpointWidth) 1 0 = i₂ := by
    rw [show 0 = bitValue i₂
      (accumulatorWire workWidth endpointWidth) from hi₂acc.symm,
      ← readField_one, writeField_read]
  have hsecondWrite := selectedSecondScan_writeAccumulator
    (left := left) (right := right) (workWidth := workWidth)
    (endpointWidth := endpointWidth) (I := i₂) (v := 0)
    workWidth (by omega)
  change actGates secondSelected
      (writeField i₂ (accumulatorWire workWidth endpointWidth) 1 0) =
    writeField (actGates secondSelected i₂)
      (accumulatorWire workWidth endpointWidth) 1 0 at hsecondWrite
  rw [hi₂clear] at hsecondWrite
  have hsecond := fixedSecondScan_act hLR hs₂ workWidth (by omega) (by
    rw [hi₂acc, scanAccumulator_width hR])
  change actGates
      (fixedSecondScan left right workWidth endpointWidth workWidth) i₂ =
    writeField (actGates secondSelected i₂)
      (accumulatorWire workWidth endpointWidth) 1
      (scanAccumulator left right 0) at hsecond
  rw [scanAccumulator_zero, ← hsecondWrite] at hsecond
  simp only [fixedGates, selectedGates, actGates_append]
  rw [hfirst]
  change actGates
      (fixedSecondScan left right workWidth endpointWidth workWidth) i₂ = _
  exact hsecond

theorem leftToggle_eq_fixed
    {left right j workWidth endpointWidth I : Nat}
    (hj : j < 2 ^ endpointWidth)
    (h : Stable left right workWidth endpointWidth I) :
    actGates (leftToggle j workWidth endpointWidth) I =
      actGates (fixedToggle left j workWidth endpointWidth) I := by
  have ha := endpointGates_eq_x_or_id (value := j) (I := I)
    (Or.inl rfl) (Or.inl rfl) h.leftFlagClear h.selectorScratchClear
  change actGates (leftToggle j workWidth endpointWidth) I = _ at ha
  rw [ha]
  by_cases heq : j = left
  · subst left
    simp [fixedToggle, h.outerSet, h.leftValue, Nat.mod_eq_of_lt hj,
      actGates]
  · have hsym : left ≠ j := Ne.symm heq
    simp [fixedToggle, heq, hsym, h.outerSet, h.leftValue,
      Nat.mod_eq_of_lt hj, actGates]

theorem rightToggle_eq_fixed
    {left right j workWidth endpointWidth I : Nat}
    (hj : j < 2 ^ endpointWidth)
    (h : Stable left right workWidth endpointWidth I) :
    actGates (rightToggle j workWidth endpointWidth) I =
      actGates (fixedToggle right j workWidth endpointWidth) I := by
  have ha := endpointGates_eq_x_or_id (value := j) (I := I)
    (Or.inr rfl) (Or.inr rfl) h.rightFlagClear h.selectorScratchClear
  change actGates (rightToggle j workWidth endpointWidth) I = _ at ha
  rw [ha]
  by_cases heq : j = right
  · subst right
    simp [fixedToggle, h.outerSet, h.rightValue, Nat.mod_eq_of_lt hj,
      actGates]
  · have hsym : right ≠ j := Ne.symm heq
    simp [fixedToggle, heq, hsym, h.outerSet, h.rightValue,
      Nat.mod_eq_of_lt hj, actGates]

theorem firstScan_preserves_stable
    {left right workWidth endpointWidth I : Nat}
    (h : Stable left right workWidth endpointWidth I) :
    ∀ m j, j + m ≤ workWidth →
    Stable left right workWidth endpointWidth
      (actGates (firstScan workWidth endpointWidth j m) I) := by
  intro m
  induction m generalizing I with
  | zero =>
      intro j _
      rw [firstScan, actGates_nil]
      exact h
  | succ m ih =>
      intro j hbound
      simp only [firstScan, actGates_append]
      exact ih
        (rightToggle_preserves_stable
          (majAt_preserves_stable (by omega)
            (leftToggle_preserves_stable h)))
        (j + 1) (by omega)

theorem secondScan_preserves_stable
    {left right workWidth endpointWidth I : Nat}
    (h : Stable left right workWidth endpointWidth I) :
    ∀ m, m ≤ workWidth →
    Stable left right workWidth endpointWidth
      (actGates (secondScan workWidth endpointWidth m) I) := by
  intro m
  induction m generalizing I with
  | zero =>
      intro _
      rw [secondScan, actGates_nil]
      exact h
  | succ m ih =>
      intro hbound
      simp only [secondScan, actGates_append]
      exact ih
        (leftToggle_preserves_stable
          (umaAt_preserves_stable (by omega)
            (rightToggle_preserves_stable h)))
        (by omega)

theorem fixedFirstScan_preserves_stable
    {left right workWidth endpointWidth I : Nat}
    (h : Stable left right workWidth endpointWidth I) :
    ∀ m j, j + m ≤ workWidth →
    Stable left right workWidth endpointWidth
      (actGates (fixedFirstScan left right workWidth endpointWidth j m) I) := by
  intro m
  induction m generalizing I with
  | zero =>
      intro j _
      rw [fixedFirstScan, actGates_nil]
      exact h
  | succ m ih =>
      intro j hbound
      simp only [fixedFirstScan, actGates_append]
      exact ih
        (fixedToggle_preserves_stable
          (majAt_preserves_stable (by omega)
            (fixedToggle_preserves_stable h)))
        (j + 1) (by omega)

theorem fixedSecondScan_preserves_stable
    {left right workWidth endpointWidth I : Nat}
    (h : Stable left right workWidth endpointWidth I) :
    ∀ m, m ≤ workWidth →
    Stable left right workWidth endpointWidth
      (actGates (fixedSecondScan left right workWidth endpointWidth m) I) := by
  intro m
  induction m generalizing I with
  | zero =>
      intro _
      rw [fixedSecondScan, actGates_nil]
      exact h
  | succ m ih =>
      intro hbound
      simp only [fixedSecondScan, actGates_append]
      exact ih
        (fixedToggle_preserves_stable
          (umaAt_preserves_stable (by omega)
            (fixedToggle_preserves_stable h)))
        (by omega)

theorem firstScan_eq_fixed
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (h : Stable left right workWidth endpointWidth I) :
    ∀ m j, j + m ≤ workWidth →
    actGates (firstScan workWidth endpointWidth j m) I =
      actGates (fixedFirstScan left right workWidth endpointWidth j m) I := by
  intro m
  induction m generalizing I with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [firstScan, fixedFirstScan, actGates_append]
      have hleft := leftToggle_eq_fixed (j := j) (workWidth := workWidth)
        (endpointWidth := endpointWidth) (I := I) (by omega) h
      rw [hleft]
      let i₁ := actGates (fixedToggle left j workWidth endpointWidth) I
      have hs₁ : Stable left right workWidth endpointWidth i₁ :=
        fixedToggle_preserves_stable h
      let i₂ := actGates (majAt j workWidth endpointWidth) i₁
      have hs₂ : Stable left right workWidth endpointWidth i₂ :=
        majAt_preserves_stable (by omega) hs₁
      have hright := rightToggle_eq_fixed (j := j) (workWidth := workWidth)
        (endpointWidth := endpointWidth) (I := i₂) (by omega) hs₂
      change actGates (firstScan workWidth endpointWidth (j + 1) m)
          (actGates (rightToggle j workWidth endpointWidth) i₂) = _
      rw [hright]
      have hs₃ : Stable left right workWidth endpointWidth
          (actGates (fixedToggle right j workWidth endpointWidth) i₂) :=
        fixedToggle_preserves_stable hs₂
      exact ih hs₃ (j + 1) (by omega)

theorem secondScan_eq_fixed
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (h : Stable left right workWidth endpointWidth I) :
    ∀ m, m ≤ workWidth →
    actGates (secondScan workWidth endpointWidth m) I =
      actGates (fixedSecondScan left right workWidth endpointWidth m) I := by
  intro m
  induction m generalizing I with
  | zero => intro _; rfl
  | succ m ih =>
      intro hbound
      simp only [secondScan, fixedSecondScan, actGates_append]
      have hright := rightToggle_eq_fixed (j := m) (workWidth := workWidth)
        (endpointWidth := endpointWidth) (I := I) (by omega) h
      rw [hright]
      let i₁ := actGates (fixedToggle right m workWidth endpointWidth) I
      have hs₁ : Stable left right workWidth endpointWidth i₁ :=
        fixedToggle_preserves_stable h
      let i₂ := actGates (umaAt m workWidth endpointWidth) i₁
      have hs₂ : Stable left right workWidth endpointWidth i₂ :=
        umaAt_preserves_stable (by omega) hs₁
      have hleft := leftToggle_eq_fixed (j := m) (workWidth := workWidth)
        (endpointWidth := endpointWidth) (I := i₂) (by omega) hs₂
      change actGates (secondScan workWidth endpointWidth m)
          (actGates (leftToggle m workWidth endpointWidth) i₂) = _
      rw [hleft]
      have hs₃ : Stable left right workWidth endpointWidth
          (actGates (fixedToggle left m workWidth endpointWidth) i₂) :=
        fixedToggle_preserves_stable hs₂
      exact ih hs₃ (by omega)

theorem gates_eq_fixed {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (h : Stable left right workWidth endpointWidth I) :
    actGates (gates workWidth endpointWidth) I =
      actGates (fixedGates left right workWidth endpointWidth) I := by
  simp only [gates, fixedGates, actGates_append]
  have hfirst := firstScan_eq_fixed hwidth h workWidth 0 (by omega)
  rw [hfirst]
  let i₁ := actGates
    (fixedFirstScan left right workWidth endpointWidth 0 workWidth) I
  have hs₁ : Stable left right workWidth endpointWidth i₁ :=
    fixedFirstScan_preserves_stable h workWidth 0 (by omega)
  let i₂ := actGates
    [.cx (carryWire workWidth endpointWidth)
      (signWire workWidth endpointWidth)] i₁
  have hs₂ : Stable left right workWidth endpointWidth i₂ :=
    signGate_preserves_stable hs₁
  change actGates (secondScan workWidth endpointWidth workWidth) i₂ = _
  exact secondScan_eq_fixed hwidth hs₂ workWidth (by omega)

theorem gates_act
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (hLR : left ≤ right) (hR : right < workWidth)
    (h : Stable left right workWidth endpointWidth I)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0) :
    actGates (gates workWidth endpointWidth) I =
      writeField
        (writeField I (targetOffset workWidth + left) (right - left + 1)
          ((readField I (targetOffset workWidth + left) (right - left + 1) +
            readField I (sourceOffset + left) (right - left + 1)) %
              2 ^ (right - left + 1)))
        (signWire workWidth endpointWidth) 1
          ((bitValue I (signWire workWidth endpointWidth) +
            (readField I (targetOffset workWidth + left) (right - left + 1) +
              readField I (sourceOffset + left) (right - left + 1)) /
                2 ^ (right - left + 1)) % 2) := by
  have hactiveCarry : bitValue
      (actGates (activeGates left right workWidth endpointWidth) I)
        (carryWire workWidth endpointWidth) = 0 := by
    rw [activeGates_preserves_carry hLR hR, hcarry]
  rw [gates_eq_fixed hwidth h,
    fixedGates_eq_selected hLR hR h hacc,
    selectedGates_eq_active_of_carry hLR hR hcarry hactiveCarry,
    activeGates_eq_ideal hLR hR,
    idealGates_act hLR hR,
    hcarry]
  simp only [Nat.add_zero]

theorem majAt_wellFormed {j workWidth endpointWidth : Nat}
    (hj : j < workWidth) :
    (majAt j workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  apply wellFormed_placeGates (cell_disjoint hj)
    (by simp [CellPlaced.layout, cellWiring, CellPlaced.wiring])
  · intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
      simp [CellPlaced.layout] at hk
      omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
      simp [cellWiring, CellPlaced.wiring, CellPlaced.layout, Layout.size,
        layout_width, targetOffset, sourceOffset, carryWire, accumulatorWire,
        cellScratchWire, selectorScratchOffset, outerWire] <;>
      omega
  · exact CellPlaced.component_wellFormed CellPlaced.maj_wellFormed

theorem umaAt_wellFormed {j workWidth endpointWidth : Nat}
    (hj : j < workWidth) :
    (umaAt j workWidth endpointWidth).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  apply wellFormed_placeGates (cell_disjoint hj)
    (by simp [CellPlaced.layout, cellWiring, CellPlaced.wiring])
  · intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
      simp [CellPlaced.layout] at hk
      omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl <;>
      simp [cellWiring, CellPlaced.wiring, CellPlaced.layout, Layout.size,
        layout_width, targetOffset, sourceOffset, carryWire, accumulatorWire,
        cellScratchWire, selectorScratchOffset, outerWire] <;>
      omega
  · exact CellPlaced.component_wellFormed CellPlaced.uma_wellFormed

theorem firstScan_wellFormed (workWidth endpointWidth : Nat) :
    ∀ m j, j + m ≤ workWidth →
    (firstScan workWidth endpointWidth j m).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [firstScan, List.all_append, Bool.and_eq_true]
      exact ⟨⟨⟨endpointGates_wellFormed (Or.inl rfl) (Or.inl rfl),
        majAt_wellFormed (by omega)⟩,
        endpointGates_wellFormed (Or.inr rfl) (Or.inr rfl)⟩,
        ih (j + 1) (by omega)⟩

theorem secondScan_wellFormed (workWidth endpointWidth : Nat) :
    ∀ m, m ≤ workWidth →
    (secondScan workWidth endpointWidth m).all
      (RGate.wellFormed (layout workWidth endpointWidth).width) = true := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hbound
      simp only [secondScan, List.all_append, Bool.and_eq_true]
      exact ⟨⟨⟨endpointGates_wellFormed (Or.inr rfl) (Or.inr rfl),
        umaAt_wellFormed (by omega)⟩,
        endpointGates_wellFormed (Or.inl rfl) (Or.inl rfl)⟩,
        ih (by omega)⟩

theorem circuit_wellFormed (workWidth endpointWidth : Nat) :
    (circuit workWidth endpointWidth).wellFormed = true := by
  change (gates workWidth endpointWidth).all
    (RGate.wellFormed (layout workWidth endpointWidth).width) = true
  simp only [gates, List.all_append, Bool.and_eq_true]
  refine ⟨⟨firstScan_wellFormed workWidth endpointWidth workWidth 0 (by omega), ?_⟩,
    secondScan_wellFormed workWidth endpointWidth workWidth (by omega)⟩
  simp [RGate.wellFormed, layout_width, carryWire, signWire, outerWire]
  omega

theorem endpointGates_identity_of_outer_clear
    {value workWidth endpointWidth endpoint flag I : Nat}
    (hendpoint : endpoint = leftOffset workWidth ∨
      endpoint = rightOffset workWidth endpointWidth)
    (hflagWire : flag = leftFlagWire workWidth endpointWidth ∨
      flag = rightFlagWire workWidth endpointWidth)
    (houter : I.testBit (outerWire workWidth endpointWidth) = false)
    (hflag : bitValue I flag = 0)
    (hscratch : readField I
      (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0) :
    actGates (endpointGates value workWidth endpointWidth endpoint flag) I =
      I := by
  rw [endpointGates_eq_x_or_id hendpoint hflagWire hflag hscratch]
  simp [houter]

theorem leftToggle_identity_of_outer_clear
    {value workWidth endpointWidth I : Nat}
    (houter : I.testBit (outerWire workWidth endpointWidth) = false)
    (hflag : bitValue I (leftFlagWire workWidth endpointWidth) = 0)
    (hscratch : readField I
      (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0) :
    actGates (leftToggle value workWidth endpointWidth) I = I := by
  exact endpointGates_identity_of_outer_clear
    (Or.inl rfl) (Or.inl rfl) houter hflag hscratch

theorem rightToggle_identity_of_outer_clear
    {value workWidth endpointWidth I : Nat}
    (houter : I.testBit (outerWire workWidth endpointWidth) = false)
    (hflag : bitValue I (rightFlagWire workWidth endpointWidth) = 0)
    (hscratch : readField I
      (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0) :
    actGates (rightToggle value workWidth endpointWidth) I = I := by
  exact endpointGates_identity_of_outer_clear
    (Or.inr rfl) (Or.inr rfl) houter hflag hscratch

theorem majAt_identity_of_control_clear
    {j workWidth endpointWidth I : Nat}
    (hj : j < workWidth)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hscratch : I.testBit
      (cellScratchWire workWidth endpointWidth) = false) :
    actGates (majAt j workWidth endpointWidth) I = I := by
  have hacc' : I.testBit
      (accumulatorWire workWidth endpointWidth) = false := by
    unfold bitValue at hacc
    cases hbit : I.testBit (accumulatorWire workWidth endpointWidth) <;>
      simp_all
  rw [majAt_reduces hj hscratch,
    if_neg (by rw [hacc']; decide),
    disabledAt_identity_of_carry_clear hcarry]

theorem umaAt_identity_of_control_clear
    {j workWidth endpointWidth I : Nat}
    (hj : j < workWidth)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hscratch : I.testBit
      (cellScratchWire workWidth endpointWidth) = false) :
    actGates (umaAt j workWidth endpointWidth) I = I := by
  have hacc' : I.testBit
      (accumulatorWire workWidth endpointWidth) = false := by
    unfold bitValue at hacc
    cases hbit : I.testBit (accumulatorWire workWidth endpointWidth) <;>
      simp_all
  rw [umaAt_reduces hj hscratch,
    if_neg (by rw [hacc']; decide),
    disabledAt_identity_of_carry_clear hcarry]

theorem firstScan_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (outerWire workWidth endpointWidth) = false)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I (leftFlagWire workWidth endpointWidth) = 0)
    (hrightFlag : bitValue I (rightFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0)
    (hcell : I.testBit (cellScratchWire workWidth endpointWidth) = false) :
    ∀ m j, j + m ≤ workWidth →
    actGates (firstScan workWidth endpointWidth j m) I = I := by
  intro m
  induction m with
  | zero => intro j _; rfl
  | succ m ih =>
      intro j hbound
      simp only [firstScan, actGates_append]
      rw [leftToggle_identity_of_outer_clear houter hleftFlag hselector,
        majAt_identity_of_control_clear (by omega) hcarry hacc hcell,
        rightToggle_identity_of_outer_clear houter hrightFlag hselector,
        ih (j + 1) (by omega)]

theorem secondScan_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (outerWire workWidth endpointWidth) = false)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I (leftFlagWire workWidth endpointWidth) = 0)
    (hrightFlag : bitValue I (rightFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0)
    (hcell : I.testBit (cellScratchWire workWidth endpointWidth) = false) :
    ∀ m, m ≤ workWidth → actGates
      (secondScan workWidth endpointWidth m) I = I := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hbound
      simp only [secondScan, actGates_append]
      rw [rightToggle_identity_of_outer_clear houter hrightFlag hselector,
        umaAt_identity_of_control_clear (by omega) hcarry hacc hcell,
        leftToggle_identity_of_outer_clear houter hleftFlag hselector,
        ih (by omega)]

theorem gates_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (outerWire workWidth endpointWidth) = false)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I (leftFlagWire workWidth endpointWidth) = 0)
    (hrightFlag : bitValue I (rightFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0)
    (hcell : I.testBit (cellScratchWire workWidth endpointWidth) = false) :
    actGates (gates workWidth endpointWidth) I = I := by
  have hfirst := firstScan_identity_of_outer_clear houter hcarry hacc
    hleftFlag hrightFlag hselector hcell workWidth 0 (by omega)
  have hcarryTest : I.testBit (carryWire workWidth endpointWidth) = false := by
    unfold bitValue at hcarry
    cases hbit : I.testBit (carryWire workWidth endpointWidth) <;>
      simp_all
  have hsign : actGates
      [.cx (carryWire workWidth endpointWidth)
        (signWire workWidth endpointWidth)] I = I := by
    simp [actGates, RGate.act, hcarryTest]
  have hsecond := secondScan_identity_of_outer_clear houter hcarry hacc
    hleftFlag hrightFlag hselector hcell workWidth (by omega)
  simp only [gates, actGates_append]
  rw [hfirst, hsign, hsecond]

theorem gates_reverse_identity_of_outer_clear
    {workWidth endpointWidth I : Nat}
    (houter : I.testBit (outerWire workWidth endpointWidth) = false)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hleftFlag : bitValue I (leftFlagWire workWidth endpointWidth) = 0)
    (hrightFlag : bitValue I (rightFlagWire workWidth endpointWidth) = 0)
    (hselector : readField I
      (selectorScratchOffset workWidth endpointWidth) endpointWidth = 0)
    (hcell : I.testBit (cellScratchWire workWidth endpointWidth) = false) :
    actGates (gates workWidth endpointWidth).reverse I = I := by
  have hforward := gates_identity_of_outer_clear houter hcarry hacc
    hleftFlag hrightFlag hselector hcell
  have hinverse := actGates_reverse
    (w := (circuit workWidth endpointWidth).width)
    (circuit_wellFormed workWidth endpointWidth) I
  change actGates (gates workWidth endpointWidth).reverse
    (actGates (gates workWidth endpointWidth) I) = I at hinverse
  rw [hforward] at hinverse
  exact hinverse

theorem gates_reverse_act
    {left right workWidth endpointWidth I : Nat}
    (hwidth : workWidth ≤ 2 ^ endpointWidth)
    (hLR : left ≤ right) (hR : right < workWidth)
    (h : Stable left right workWidth endpointWidth I)
    (hacc : bitValue I (accumulatorWire workWidth endpointWidth) = 0)
    (hcarry : bitValue I (carryWire workWidth endpointWidth) = 0) :
    actGates (gates workWidth endpointWidth).reverse I =
      writeField
        (writeField I (targetOffset workWidth + left) (right - left + 1)
          (Adder.difference (right - left + 1)
            (readField I (sourceOffset + left) (right - left + 1))
            (readField I (targetOffset workWidth + left)
              (right - left + 1))))
        (signWire workWidth endpointWidth) 1
          ((bitValue I (signWire workWidth endpointWidth) +
            Adder.borrow
              (readField I (sourceOffset + left) (right - left + 1))
              (readField I (targetOffset workWidth + left)
                (right - left + 1))) % 2) := by
  let width := right - left + 1
  let target := targetOffset workWidth + left
  let source := sourceOffset + left
  let sign := signWire workWidth endpointWidth
  let a := readField I source width
  let b := readField I target width
  let s := bitValue I sign
  let x := Adder.difference width a b
  let br := Adder.borrow a b
  let j := writeField (writeField I target width x)
    sign 1 ((s + br) % 2)
  have hwidthPos : 0 < width := by
    dsimp [width]
    omega
  have hSourceTarget : source + width ≤ target := by
    dsimp [source, target, width]
    simp [sourceOffset, targetOffset]
    omega
  have ha : a < 2 ^ width := readField_lt I source width
  have hb : b < 2 ^ width := readField_lt I target width
  have hs : s < 2 := bitValue_lt I sign
  have hspec : (a + x) % 2 ^ width = b ∧
      (a + x) / 2 ^ width = Adder.borrow a b := by
    simpa [x, Adder.difference] using
      Adder.difference_add (a := a) (b := b)
        (Nat.two_pow_pos width) ha hb
  have hx : x < 2 ^ width :=
    Nat.mod_lt _ (Nat.two_pow_pos width)
  have hjTarget : readField j target width = x := by
    simp only [j]
    rw [readField_writeField_of_disjoint (by
        right
        simp [sign, target, signWire, targetOffset, outerWire]
        omega),
      readField_writeField_self hx]
  have hjSource : readField j source width = a := by
    simp only [j]
    rw [readField_writeField_of_disjoint (by
        right
        simp [sign, source, signWire, sourceOffset, outerWire]
        omega),
      readField_writeField_of_disjoint (by
        exact Or.inr hSourceTarget)]
  have hjCarry : bitValue j (carryWire workWidth endpointWidth) = 0 := by
    simp only [j]
    rw [bitValue_write_ne (by
        simp [sign, signWire, carryWire, outerWire]),
      bitValue_write_out (by
        right
        simp [target, targetOffset, carryWire, outerWire]
        omega),
      hcarry]
  have hjAccumulator : bitValue j
      (accumulatorWire workWidth endpointWidth) = 0 := by
    simp only [j]
    rw [bitValue_write_ne (by
        simp [sign, signWire, accumulatorWire, outerWire]),
      bitValue_write_out (by
        right
        simp [target, targetOffset, accumulatorWire, outerWire]
        omega),
      hacc]
  have hjSign : bitValue j sign = (s + br) % 2 := by
    simp only [j]
    rw [bitValue_write_self]
    omega
  have hjStable : Stable left right workWidth endpointWidth j := by
    exact (h.writeTargetInterval hLR hR).writeSign
  have hsign : (((s + br) % 2 + br) % 2) = s := by
    unfold br Adder.borrow
    by_cases hlt : b < a <;> simp [hlt] <;> omega
  have hrestore : writeField (writeField j target width b) sign 1 s = I := by
    simp only [j]
    rw [writeField_comm
        (i := writeField I target width x)
        (o₁ := sign) (n₁ := 1) (v := (s + br) % 2)
        (o₂ := target) (n₂ := width) (u := b)
        (Or.inr (by
          simp [sign, target, signWire, targetOffset, outerWire]
          omega)),
      writeField_writeField]
    change writeField
      (writeField (writeField I target width x) target width b)
      sign 1 s = I
    rw [writeField_writeField,
      show b = readField I target width from rfl,
      writeField_read]
    change writeField I sign 1 (bitValue I sign) = I
    rw [← readField_one, writeField_read]
  have hfwd := gates_act
    (I := j) hwidth hLR hR hjStable hjAccumulator hjCarry
  change actGates (gates workWidth endpointWidth) j = _ at hfwd
  rw [hjTarget, hjSource, show x + a = a + x by omega,
    hspec.1, hjSign, hspec.2, hsign] at hfwd
  change actGates (gates workWidth endpointWidth) j =
    writeField (writeField j target width b) sign 1 s at hfwd
  rw [hrestore] at hfwd
  have hinv := actGates_reverse
    (w := (circuit workWidth endpointWidth).width)
    (circuit_wellFormed workWidth endpointWidth) j
  change actGates (gates workWidth endpointWidth).reverse
    (actGates (gates workWidth endpointWidth) j) = j at hinv
  rw [hfwd] at hinv
  simpa [j, x, br, a, b, s, target, source, sign, width] using hinv

theorem endpointGates_length_le (value workWidth endpointWidth endpoint flag : Nat) :
    (endpointGates value workWidth endpointWidth endpoint flag).length ≤
      8 * endpointWidth + 3 := by
  simp only [endpointGates, List.length_map]
  exact Endpoint.gates_length_le value endpointWidth

theorem endpointGates_ccx_le (value workWidth endpointWidth endpoint flag : Nat) :
    (endpointGates value workWidth endpointWidth endpoint flag).countP
      RGate.isCcx ≤ 4 * endpointWidth + 1 := by
  rw [endpointGates, countP_map_gates (fun g => RGate.isCcx_map _ g)]
  exact Endpoint.gates_ccx_le value endpointWidth

theorem firstScan_length_le (workWidth endpointWidth : Nat) :
    ∀ m j, (firstScan workWidth endpointWidth j m).length ≤
      m * (16 * endpointWidth + 11) := by
  intro m
  induction m with
  | zero => intro j; simp [firstScan]
  | succ m ih =>
      intro j
      simp only [firstScan, List.length_append]
      have hl : (leftToggle j workWidth endpointWidth).length ≤
          8 * endpointWidth + 3 := by
        exact endpointGates_length_le j workWidth endpointWidth
          (leftOffset workWidth) (leftFlagWire workWidth endpointWidth)
      have hr : (rightToggle j workWidth endpointWidth).length ≤
          8 * endpointWidth + 3 := by
        exact endpointGates_length_le j workWidth endpointWidth
          (rightOffset workWidth endpointWidth) (rightFlagWire workWidth endpointWidth)
      have hm : (majAt j workWidth endpointWidth).length = 5 := by
        simp [majAt, CellPlaced.gates, Cell.maj_length]
      have hi := ih (j + 1)
      have hmul : (m + 1) * (16 * endpointWidth + 11) =
          m * (16 * endpointWidth + 11) + (16 * endpointWidth + 11) := by
        simp [Nat.add_mul]
      rw [hm, hmul]
      omega

theorem secondScan_length_le (workWidth endpointWidth : Nat) :
    ∀ m, (secondScan workWidth endpointWidth m).length ≤
      m * (16 * endpointWidth + 12) := by
  intro m
  induction m with
  | zero => simp [secondScan]
  | succ m ih =>
      simp only [secondScan, List.length_append]
      have hl : (leftToggle m workWidth endpointWidth).length ≤
          8 * endpointWidth + 3 := by
        exact endpointGates_length_le m workWidth endpointWidth
          (leftOffset workWidth) (leftFlagWire workWidth endpointWidth)
      have hr : (rightToggle m workWidth endpointWidth).length ≤
          8 * endpointWidth + 3 := by
        exact endpointGates_length_le m workWidth endpointWidth
          (rightOffset workWidth endpointWidth) (rightFlagWire workWidth endpointWidth)
      have hu : (umaAt m workWidth endpointWidth).length = 6 := by
        simp [umaAt, CellPlaced.gates, Cell.uma_length]
      have hmul : (m + 1) * (16 * endpointWidth + 12) =
          m * (16 * endpointWidth + 12) + (16 * endpointWidth + 12) := by
        simp [Nat.add_mul]
      rw [hu, hmul]
      omega

theorem gates_length_le (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).length ≤
      workWidth * (32 * endpointWidth + 23) + 1 := by
  simp only [gates, List.length_append, List.length_cons, List.length_nil]
  have h₁ := firstScan_length_le workWidth endpointWidth workWidth 0
  have h₂ := secondScan_length_le workWidth endpointWidth workWidth
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
    ∀ m j, (firstScan workWidth endpointWidth j m).countP RGate.isCcx ≤
      m * (8 * endpointWidth + 5) := by
  intro m
  induction m with
  | zero => intro j; simp [firstScan]
  | succ m ih =>
      intro j
      simp only [firstScan, List.countP_append]
      have hl : (leftToggle j workWidth endpointWidth).countP RGate.isCcx ≤
          4 * endpointWidth + 1 := by
        exact endpointGates_ccx_le j workWidth endpointWidth
          (leftOffset workWidth) (leftFlagWire workWidth endpointWidth)
      have hr : (rightToggle j workWidth endpointWidth).countP RGate.isCcx ≤
          4 * endpointWidth + 1 := by
        exact endpointGates_ccx_le j workWidth endpointWidth
          (rightOffset workWidth endpointWidth) (rightFlagWire workWidth endpointWidth)
      have hm : (majAt j workWidth endpointWidth).countP RGate.isCcx = 3 := by
        rw [majAt, CellPlaced.gates,
          countP_map_gates (fun g => RGate.isCcx_map _ g)]
        exact Cell.maj_ccx
      have hi := ih (j + 1)
      have hmul : (m + 1) * (8 * endpointWidth + 5) =
          m * (8 * endpointWidth + 5) + (8 * endpointWidth + 5) := by
        simp [Nat.add_mul]
      rw [hm, hmul]
      omega

theorem secondScan_ccx_le (workWidth endpointWidth : Nat) :
    ∀ m, (secondScan workWidth endpointWidth m).countP RGate.isCcx ≤
      m * (8 * endpointWidth + 6) := by
  intro m
  induction m with
  | zero => simp [secondScan]
  | succ m ih =>
      simp only [secondScan, List.countP_append]
      have hl : (leftToggle m workWidth endpointWidth).countP RGate.isCcx ≤
          4 * endpointWidth + 1 := by
        exact endpointGates_ccx_le m workWidth endpointWidth
          (leftOffset workWidth) (leftFlagWire workWidth endpointWidth)
      have hr : (rightToggle m workWidth endpointWidth).countP RGate.isCcx ≤
          4 * endpointWidth + 1 := by
        exact endpointGates_ccx_le m workWidth endpointWidth
          (rightOffset workWidth endpointWidth) (rightFlagWire workWidth endpointWidth)
      have hu : (umaAt m workWidth endpointWidth).countP RGate.isCcx = 4 := by
        rw [umaAt, CellPlaced.gates,
          countP_map_gates (fun g => RGate.isCcx_map _ g)]
        exact Cell.uma_ccx
      have hmul : (m + 1) * (8 * endpointWidth + 6) =
          m * (8 * endpointWidth + 6) + (8 * endpointWidth + 6) := by
        simp [Nat.add_mul]
      rw [hu, hmul]
      omega

theorem gates_ccx_le (workWidth endpointWidth : Nat) :
    (gates workWidth endpointWidth).countP RGate.isCcx ≤
      workWidth * (16 * endpointWidth + 11) := by
  simp only [gates, List.countP_append, List.countP_cons, List.countP_nil,
    RGate.isCcx, Bool.false_eq_true, if_false, Nat.add_zero]
  have h₁ := firstScan_ccx_le workWidth endpointWidth workWidth 0
  have h₂ := secondScan_ccx_le workWidth endpointWidth workWidth
  have hmul : workWidth * (16 * endpointWidth + 11) =
      workWidth * (8 * endpointWidth + 5) +
        workWidth * (8 * endpointWidth + 6) := by
    have hinner : 16 * endpointWidth + 11 =
        (8 * endpointWidth + 5) + (8 * endpointWidth + 6) := by
      omega
    rw [hinner, Nat.mul_add]
  rw [hmul]
  omega

end Interval
end Euclid
end VQ
