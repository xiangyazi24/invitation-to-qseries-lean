import QseriesFormalization.Chapter20

namespace QseriesFormalization.PartIV.Ch20

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- Small Lean-side decidable check of Ramanujan's mod-691 congruence using the
same `tauEtaPowCoeffZ` convolution engine as `Chapter20.lean`.

Index `i` checks `tau(i+1) = sigma11(i+1)` modulo 691. -/
theorem ch20_tau_sigma_mod691_first_ten_by_decide :
    ∀ i : Fin 10,
      ((tauEtaPowCoeffZ 24 i.1 : ZMod 691) = (sigma11 (i.1 + 1) : ZMod 691)) := by
  decide

end QseriesFormalization.PartIV.Ch20
