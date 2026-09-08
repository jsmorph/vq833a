import VQMathlib.Euclid.PackedRotationCounts

namespace VQMathlib.Euclid.PackedRotationCounts

set_option maxRecDepth 4096

theorem rotationTwo : swapCount 259 2 = 258 := by decide +kernel
theorem rotationFour : swapCount 259 4 = 258 := by decide +kernel
theorem rotationEight : swapCount 259 8 = 258 := by decide +kernel
theorem rotationSixteen : swapCount 259 16 = 258 := by decide +kernel

end VQMathlib.Euclid.PackedRotationCounts
