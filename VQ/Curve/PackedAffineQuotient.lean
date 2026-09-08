import VQ.Curve.PackedAffineLayout
import VQ.Curve.PackedClearTargetProduct
import Mathlib.Tactic.IntervalCases

namespace VQ.Curve.PackedAffineQuotient

open Reversible Semantics

def multiplierOffset : Nat := Euclid.PackedStepLayout.workTwoOffset

def multiplicandOffset : Nat := PackedAffineLayout.inverseOffset

def targetOffset : Nat := Euclid.PackedStepLayout.workOneOffset

def localLayout : Layout := [256, 256, 256, 1, 1, 1, 1, 1, 1]

def wiring : Wiring :=
  [multiplierOffset, multiplicandOffset, targetOffset,
    Euclid.PackedStepLayout.workTwoOffset + 256,
    Euclid.PackedStepLayout.workTwoOffset + 257,
    Euclid.PackedStepLayout.workTwoOffset + 258,
    Euclid.PackedStepLayout.phaseOneWire,
    Euclid.PackedStepLayout.phaseTwoWire,
    Euclid.PackedStepLayout.signWire]

def embedding : Nat → Nat := place localLayout wiring

def ops : List Op :=
  Op.relabelAll embedding
    (PackedClearTargetProduct.productOps Curve.p 256)

def program : Program :=
  { width := PackedAffineLayout.width
    cbits := 256
    ops }

theorem localLayout_width : localLayout.width =
    PackedClearTargetProduct.width 256 := by
  decide

theorem wiring_disjoint : Wiring.Disjoint localLayout wiring := by
  intro j k hj hk hne
  simp [wiring] at hj hk
  interval_cases j <;> interval_cases k <;>
    simp_all [localLayout, wiring, Layout.size, multiplierOffset,
      multiplicandOffset, targetOffset,
      Euclid.PackedStepLayout.workOneOffset,
      Euclid.PackedStepLayout.workTwoOffset,
      Euclid.PackedStepLayout.phaseOneWire,
      Euclid.PackedStepLayout.phaseTwoWire,
      Euclid.PackedStepLayout.signWire,
      PackedAffineLayout.inverseOffset,
      Euclid.PackedTerminalEndpoint.outputOffset,
      Euclid.PackedStepLayout.width, Euclid.PackedStepLayout.layout,
      Euclid.PackedStepLayout.workWidth,
      Euclid.PackedStepLayout.lengthWidth,
      Euclid.PackedStepLayout.remainderLengthWidth,
      Euclid.PackedStepLayout.poolWidth, Layout.width]

theorem wiring_length : localLayout.length ≤ wiring.length := by
  decide

theorem wiring_bound : ∀ j, j < localLayout.length →
    wiring.getD j 0 + localLayout.size j ≤ PackedAffineLayout.width := by
  native_decide

theorem wiring_bound_core : ∀ j, j < localLayout.length →
    wiring.getD j 0 + localLayout.size j ≤
      PackedAffineLayout.auxiliaryOffset := by
  native_decide

theorem embedding_lt {q : Nat}
    (hq : q < PackedClearTargetProduct.width 256) :
    embedding q < PackedAffineLayout.width := by
  apply place_lt (L := localLayout) (W := wiring)
  · exact wiring_length
  · exact wiring_bound
  · simpa [embedding, localLayout_width] using hq

theorem embedding_lt_core {q : Nat}
    (hq : q < PackedClearTargetProduct.width 256) :
    embedding q < PackedAffineLayout.auxiliaryOffset := by
  apply place_lt (L := localLayout) (W := wiring)
  · exact wiring_length
  · exact wiring_bound_core
  · simpa [embedding, localLayout_width] using hq

theorem embedding_injective {x y : Nat}
    (hx : x < PackedClearTargetProduct.width 256)
    (hy : y < PackedClearTargetProduct.width 256)
    (hxy : embedding x = embedding y) :
    x = y := by
  apply place_inj (L := localLayout) (W := wiring)
      wiring_length wiring_disjoint
  · simpa [embedding, localLayout_width] using hx
  · simpa [embedding, localLayout_width] using hy
  · exact hxy

theorem ops_wellFormed {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level PackedAffineLayout.width 0 256 ops = true := by
  apply Program.opsWellFormed_relabel
  · exact fun _ hq => embedding_lt hq
  · exact fun _ _ hx hy hxy => embedding_injective hx hy hxy
  · exact PackedClearTargetProduct.productOps_wellFormed hl (by norm_num)

theorem ops_wellFormed_core {level : Nat} (hl : 3 ≤ level) :
    Program.opsWellFormed level PackedAffineLayout.auxiliaryOffset 0 256
      ops = true := by
  apply Program.opsWellFormed_relabel
  · exact fun _ hq => embedding_lt_core hq
  · exact fun _ _ hx hy hxy => embedding_injective hx hy hxy
  · exact PackedClearTargetProduct.productOps_wellFormed hl (by norm_num)

theorem program_wellFormed {level : Nat} (hl : 3 ≤ level) :
    program.wellFormed level = true := by
  simpa only [Program.wellFormed, program] using ops_wellFormed hl

end VQ.Curve.PackedAffineQuotient
