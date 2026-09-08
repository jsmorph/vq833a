import VQ.Euclid.InputPreparation
import VQ.Euclid.InverterTotalCaller

namespace VQ.Euclid.InputPreparation

theorem totalPreprocessorSpec
    {p n lengthWidth shiftWidth : Nat}
    (hn : 0 < n) (hp : 0 < p) (hpFit : p < 2 ^ n)
    (hwork : workWidth n < 2 ^ lengthWidth) :
    InverterTotalCaller.PreprocessorSpec
      (gates p n lengthWidth shiftWidth) p n lengthWidth shiftWidth := by
  exact ⟨preprocessorSpec hn hpFit hwork,
    gates_act_rawInput_zero hn hp hpFit hwork⟩

end VQ.Euclid.InputPreparation
