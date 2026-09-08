import VQBridge.Palomar833.Specification
import VQMathlib.ECDLP.FourierRecovery.SelectedSum
import VQMathlib.ECDLP.Recovery.Algebra

namespace Palomar833.Connection

open VQ.Tests.ECDLPFourierRecovery

theorem order_le_dimension : q ≤ N :=
  VQ.Tests.Secp256k1Order.q_lt_two_pow_256.le

theorem selected_iff (d : Nat) (o : Outcome) :
    selected d o ↔ o ∈ selectedObservables N q d q_prime.pos order_le_dimension := by
  rw [mem_selectedObservables_iff]
  constructor
  · rintro ⟨k, hk, hkq, hf, hs⟩
    refine ⟨⟨k, hkq⟩, Nat.ne_of_gt hk, ?_⟩
    apply Prod.ext
    · apply Fin.ext
      exact hf.symm
    · apply Fin.ext
      exact hs.symm
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.val, Nat.pos_of_ne_zero hk, k.isLt, rfl, rfl⟩

theorem decoder_eq (o : Outcome) :
    Palomar833.decode o = VQ.Tests.ECDLPRecovery.checkedNatural q
      (VQ.Tests.ECDLPFourierRecovery.decode q N o.1.val)
      (VQ.Tests.ECDLPFourierRecovery.decode q N o.2.val) := rfl

end Palomar833.Connection

namespace Palomar833

theorem selected_recovers
    {pointQ d : Nat} (hpoint : validPoint pointQ)
    (hdpos : 0 < d) (hd : d < q) (hQ : decodePoint pointQ = d • generator)
    {o : Outcome} (ho : selected d o) :
    decode o = some d ∧ publicAccepts pointQ d := by
  obtain ⟨hkq, hk, hv⟩ := VQ.Tests.ECDLPFourierRecovery.decode_mem_selectedObservables
    q_prime.pos Connection.order_le_dimension ((Connection.selected_iff d o).mp ho)
  have hvz :
      (VQ.Tests.ECDLPFourierRecovery.decode q N o.2.val : ZMod q) =
        (d : ZMod q) * (VQ.Tests.ECDLPFourierRecovery.decode q N o.1.val : ZMod q) := by
    rw [hv, ZMod.natCast_mod, Nat.cast_mul]
  constructor
  · rw [Connection.decoder_eq]
    exact VQ.Tests.ECDLPRecovery.checkedNatural_recovers q_prime hd hkq hk hvz
  · exact ⟨hd, hQ.symm⟩

theorem repeated_recovers
    {pointQ d : Nat} (hpoint : validPoint pointQ)
    (hdpos : 0 < d) (hd : d < q) (hQ : decodePoint pointQ = d • generator)
    {o : Fin 26 → Outcome} (ho : ∃ i, selected d (o i)) :
    ∃ i, decode (o i) = some d ∧ publicAccepts pointQ d := by
  obtain ⟨i, hi⟩ := ho
  exact ⟨i, selected_recovers hpoint hdpos hd hQ hi⟩

end Palomar833
