import VQMathlib.ECDLP.FourierRecovery.DirichletPeak

namespace VQ.Tests.ECDLPFourierRecovery

def productLabel (q d : Nat) (hq : 0 < q) (k : Fin q) : Fin q :=
  ⟨(d * k.val) % q, Nat.mod_lt _ hq⟩

def selectedPair (N q d : Nat) (hq : 0 < q) (hqN : q ≤ N)
    (k : Fin q) : Fin N × Fin N :=
  (peakIndex N q hq hqN k,
    peakIndex N q hq hqN (productLabel q d hq k))

theorem selectedPair_injective {N q d : Nat} (hq : 0 < q) (hqN : q ≤ N) :
    Function.Injective (selectedPair N q d hq hqN) := by
  intro a b hab
  apply peakIndex_injective hq hqN
  exact congrArg Prod.fst hab

theorem decode_selectedPair {N q d : Nat} (hq : 0 < q) (hqN : q ≤ N)
    (k : Fin q) :
    decode q N (selectedPair N q d hq hqN k).1.val = k.val ∧
      decode q N (selectedPair N q d hq hqN k).2.val =
        (d * k.val) % q := by
  constructor
  · exact decode_peak hq hqN
  · exact decode_peak hq hqN

theorem selectedPair_probability_product {N q d : Nat}
    (hq : 0 < q) (hqN : q ≤ N) (k : Fin q) :
    (2401 : Real) / 14641 ≤
      fourierPeakProbability N q
          (selectedPair N q d hq hqN k).1.val k.val *
        fourierPeakProbability N q
          (selectedPair N q d hq hqN k).2.val
          (productLabel q d hq k).val := by
  have hfirst := fortyNine_div_121_le_peakProbability
    (N := N) (q := q) (t := k.val) hq hqN
  have hsecond := fortyNine_div_121_le_peakProbability
    (N := N) (q := q) (t := (productLabel q d hq k).val) hq hqN
  change (49 : Real) / 121 ≤
      fourierPeakProbability N q
        (selectedPair N q d hq hqN k).1.val k.val at hfirst
  change (49 : Real) / 121 ≤
      fourierPeakProbability N q
        (selectedPair N q d hq hqN k).2.val
        (productLabel q d hq k).val at hsecond
  have hfirstNonneg : 0 ≤ fourierPeakProbability N q
      (selectedPair N q d hq hqN k).1.val k.val := by
    exact sq_nonneg _
  have hsecondNonneg : 0 ≤ fourierPeakProbability N q
      (selectedPair N q d hq hqN k).2.val
      (productLabel q d hq k).val := by
    exact sq_nonneg _
  nlinarith

def zeroLabel (q : Nat) (hq : 0 < q) : Fin q :=
  ⟨0, hq⟩

def nonzeroLabels (q : Nat) (hq : 0 < q) : Finset (Fin q) :=
  Finset.univ.erase (zeroLabel q hq)

theorem mem_nonzeroLabels_iff {q : Nat} (hq : 0 < q) (k : Fin q) :
    k ∈ nonzeroLabels q hq ↔ k.val ≠ 0 := by
  simp [nonzeroLabels, zeroLabel, Fin.ext_iff]

theorem card_nonzeroLabels {q : Nat} (hq : 0 < q) :
    (nonzeroLabels q hq).card = q - 1 := by
  simp [nonzeroLabels, zeroLabel]

/-- info: 'VQ.Tests.ECDLPFourierRecovery.selectedPair_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms selectedPair_injective

/-- info: 'VQ.Tests.ECDLPFourierRecovery.decode_selectedPair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decode_selectedPair

/-- info: 'VQ.Tests.ECDLPFourierRecovery.selectedPair_probability_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selectedPair_probability_product

end VQ.Tests.ECDLPFourierRecovery
