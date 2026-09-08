import VQ.Curve.PackedModularDoubling

namespace VQ.Curve.PackedClearTargetProduct

open Reversible Semantics
open VQ.Curve.PackedModularAddition
open VQ.Curve.PackedModularDoubling

def multiplierOffset : Nat := 0

def multiplicandOffset (wordWidth : Nat) : Nat := wordWidth

def targetOffset (wordWidth : Nat) : Nat := 2 * wordWidth

def auxiliaryOffset (wordWidth : Nat) : Nat := 3 * wordWidth

def width (wordWidth : Nat) : Nat := 3 * wordWidth + 6

def blockLayout (wordWidth : Nat) : Layout :=
  [wordWidth, 1, wordWidth, 1, 1, 1, 1, 1, 1]

def blockWiring (wordWidth controlBit : Nat) : Wiring :=
  [targetOffset wordWidth,
    auxiliaryOffset wordWidth,
    multiplicandOffset wordWidth,
    auxiliaryOffset wordWidth + 1,
    auxiliaryOffset wordWidth + 2,
    auxiliaryOffset wordWidth + 3,
    auxiliaryOffset wordWidth + 4,
    auxiliaryOffset wordWidth + 5,
    multiplierOffset + controlBit]

def blockMap (wordWidth controlBit : Nat) : Nat → Nat :=
  place (blockLayout wordWidth) (blockWiring wordWidth controlBit)

theorem blockLayout_width (wordWidth : Nat) :
    (blockLayout wordWidth).width =
      PackedModularAddition.width wordWidth := by
  simp [blockLayout, Layout.width, PackedModularAddition.width]
  omega

theorem blockWiring_disjoint {wordWidth controlBit : Nat}
    (hwidth : 0 < wordWidth) (hcontrol : controlBit < wordWidth) :
    Wiring.Disjoint (blockLayout wordWidth)
      (blockWiring wordWidth controlBit) := by
  intro j k hj hk hne
  simp [blockWiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp [blockLayout, blockWiring, Layout.size, multiplierOffset,
      multiplicandOffset, targetOffset, auxiliaryOffset] <;> omega

theorem blockMap_lt {wordWidth controlBit q : Nat}
    (hwidth : 0 < wordWidth) (hcontrol : controlBit < wordWidth)
    (hq : q < PackedModularAddition.width wordWidth) :
    blockMap wordWidth controlBit q < width wordWidth := by
  apply place_lt (L := blockLayout wordWidth)
    (W := blockWiring wordWidth controlBit)
  · simp [blockLayout, blockWiring]
  · intro j hj
    simp [blockLayout] at hj
    interval_cases j <;>
      simp [blockLayout, blockWiring, Layout.size, multiplierOffset,
        multiplicandOffset, targetOffset, auxiliaryOffset, width] <;> omega
  · simpa [blockMap, blockLayout_width] using hq

theorem blockMap_injective {wordWidth controlBit x y : Nat}
    (hwidth : 0 < wordWidth) (hcontrol : controlBit < wordWidth)
    (hx : x < PackedModularAddition.width wordWidth)
    (hy : y < PackedModularAddition.width wordWidth)
    (hxy : blockMap wordWidth controlBit x =
      blockMap wordWidth controlBit y) :
    x = y := by
  apply place_inj (L := blockLayout wordWidth)
    (W := blockWiring wordWidth controlBit)
      (by simp [blockLayout, blockWiring])
      (blockWiring_disjoint hwidth hcontrol)
  · simpa [blockMap, blockLayout_width] using hx
  · simpa [blockMap, blockLayout_width] using hy
  · exact hxy

def addOps (modulus wordWidth controlBit : Nat) : List Op :=
  Op.relabelAll (blockMap wordWidth controlBit)
    (PackedModularAddition.modularAddOps modulus wordWidth)

def doubleOps (modulus wordWidth controlBit : Nat) : List Op :=
  Op.relabelAll (blockMap wordWidth controlBit)
    (PackedModularDoubling.modularDoubleOps modulus wordWidth)

theorem addOps_wellFormed
    {level modulus wordWidth controlBit : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hcontrol : controlBit < wordWidth) :
    Program.opsWellFormed level (width wordWidth) 0 wordWidth
      (addOps modulus wordWidth controlBit) = true := by
  apply Program.opsWellFormed_relabel
  · exact fun q hq => blockMap_lt (by omega) hcontrol hq
  · exact fun x y hx hy hxy =>
      blockMap_injective (by omega) hcontrol hx hy hxy
  · exact PackedModularAddition.modularAddOps_wellFormed hl hwidth

theorem doubleOps_wellFormed
    {level modulus wordWidth controlBit : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth)
    (hcontrol : controlBit < wordWidth) :
    Program.opsWellFormed level (width wordWidth) 0 wordWidth
      (doubleOps modulus wordWidth controlBit) = true := by
  apply Program.opsWellFormed_relabel
  · exact fun q hq => blockMap_lt (by omega) hcontrol hq
  · exact fun x y hx hy hxy =>
      blockMap_injective (by omega) hcontrol hx hy hxy
  · exact PackedModularDoubling.modularDoubleOps_wellFormed hl hwidth

def productOpsAux (modulus wordWidth : Nat) : List Nat → List Op
  | [] => []
  | [controlBit] => addOps modulus wordWidth controlBit
  | controlBit :: nextBit :: rest =>
      productOpsAux modulus wordWidth (nextBit :: rest) ++
        doubleOps modulus wordWidth controlBit ++
        addOps modulus wordWidth controlBit

def productOps (modulus wordWidth : Nat) : List Op :=
  productOpsAux modulus wordWidth (List.range wordWidth)

theorem productOpsAux_wellFormed
    {level modulus wordWidth : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth) :
    ∀ controls,
      (∀ controlBit ∈ controls, controlBit < wordWidth) →
      Program.opsWellFormed level (width wordWidth) 0 wordWidth
        (productOpsAux modulus wordWidth controls) = true
  | [], _ => by rfl
  | [controlBit], hcontrols => by
      exact addOps_wellFormed hl hwidth
        (hcontrols controlBit (by simp))
  | controlBit :: nextBit :: rest, hcontrols => by
      rw [productOpsAux, Program.opsWellFormed_append,
        Program.opsWellFormed_append,
        productOpsAux_wellFormed hl hwidth (nextBit :: rest)
          (fun q hq => hcontrols q (List.mem_cons_of_mem controlBit hq)),
        doubleOps_wellFormed hl hwidth
          (hcontrols controlBit (by simp)),
        addOps_wellFormed hl hwidth
          (hcontrols controlBit (by simp))]
      rfl

theorem productOps_wellFormed
    {level modulus wordWidth : Nat}
    (hl : 3 ≤ level) (hwidth : 2 ≤ wordWidth) :
    Program.opsWellFormed level (width wordWidth) 0 wordWidth
      (productOps modulus wordWidth) = true := by
  apply productOpsAux_wellFormed hl hwidth
  intro controlBit hcontrol
  simpa using List.mem_range.mp hcontrol

end VQ.Curve.PackedClearTargetProduct
