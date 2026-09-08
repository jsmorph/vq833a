import VQMathlib.Euclid.PackedRotationLowCounts
import VQMathlib.Euclid.PackedRotationHighCounts

namespace VQMathlib.Euclid.PackedRotationCounts

open VQ.Euclid VQ.Reversible

theorem rotationSwapCount :
    LuoSelectionPermutation.sourceRotationSwapCount 259 10 = 2580 := by
  have hcount : ∀ bit ∈ List.range 10,
      (LuoSelectionPermutation.selectionSwaps 259 (barrelAmount 259 bit)).length =
        258 := by
    intro bit hbit
    cases bit with
    | zero => exact firstRotation
    | succ bit =>
      rw [selectionSwaps_length]
      have hbit := List.mem_range.mp hbit
      rcases bit with (_ | _ | _ | _ | _ | _ | _ | _ | _ | bit)
      · exact rotationTwo
      · exact rotationFour
      · exact rotationEight
      · exact rotationSixteen
      · exact rotationThirtyTwo
      · exact rotationSixtyFour
      · exact rotationOneTwentyEight
      · exact rotationTwoFiftySix
      · exact rotationTwoFiftyThree
      · omega
  unfold LuoSelectionPermutation.sourceRotationSwapCount
  calc
    _ = ((List.range 10).map fun _ => 258).sum :=
      congrArg List.sum (List.map_congr_left hcount)
    _ = 2580 := by decide

end VQMathlib.Euclid.PackedRotationCounts
