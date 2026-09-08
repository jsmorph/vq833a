import VQMathlib.Euclid.PackedRotationCounts

namespace VQMathlib.Euclid.PackedRotationCounts

set_option maxRecDepth 4096

theorem rotationThirtyTwo : swapCount 259 32 = 258 := by decide +kernel
theorem rotationSixtyFour : swapCount 259 64 = 258 := by decide +kernel
theorem rotationOneTwentyEight : swapCount 259 128 = 258 := by decide +kernel
theorem rotationTwoFiftySix : swapCount 259 256 = 258 := by decide +kernel
theorem rotationTwoFiftyThree : swapCount 259 253 = 258 := by decide +kernel

end VQMathlib.Euclid.PackedRotationCounts
