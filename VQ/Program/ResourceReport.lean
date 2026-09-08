import VQ.Program.Depth

namespace VQ
namespace Program

/-- Resource fields computed from a program's syntax.  Range endpoints are
the minimum and maximum over branch arms. -/
structure ResourceReport where
  qubits : Nat
  inputBits : Nat
  localBits : Nat
  usedQubits : Nat
  usedInputBits : Nat
  usedLocalBits : Nat
  gates : Range
  clifford : Range
  cnot : Range
  toffoli : Range
  totalDepth : Range
  toffoliDepth : Range
  measurements : Range
  resets : Range
  measurementResets : Range
  measurementDepth : Range
  feedForwardDepth : Range
  classicalOps : Range
  classicalDepth : Range
  cczToTUpper : Nat
  deriving DecidableEq, Repr

/-- Compute a resource report from the program that the report describes.
The T-count field applies the seven-T exact decomposition to each CCZ at the
upper endpoint of the program's Toffoli range. -/
def resourceReport (p : Program) : ResourceReport :=
  { qubits := p.width
    inputBits := p.inputBits
    localBits := p.cbits
    usedQubits := p.usedWires
    usedInputBits := p.usedInputBits
    usedLocalBits := p.usedCbits
    gates := p.gateCount
    clifford := p.cliffordCount
    cnot := p.cnotCount
    toffoli := p.toffoliCount
    totalDepth := p.depthRange
    toffoliDepth := p.toffoliDepthRange
    measurements := p.measureCount
    resets := p.resetCount
    measurementResets := p.measureResetCount
    measurementDepth := p.measurementDepthRange
    feedForwardDepth := p.feedForwardDepthRange
    classicalOps := p.classicalOpCount
    classicalDepth := p.classicalDepthRange
    cczToTUpper := 7 * p.toffoliCount.hi }

theorem resourceReport_cczToTUpper (p : Program) :
    (resourceReport p).cczToTUpper = 7 * p.toffoliCount.hi := rfl

end Program
end VQ
