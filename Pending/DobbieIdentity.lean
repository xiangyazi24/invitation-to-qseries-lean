import QseriesFormalization.Pending.Chapter15_R_ODE
import QseriesFormalization.Pending.RamanujanQuinticJTP

namespace QseriesFormalization
namespace Pending
namespace DobbieIdentityRootCheck

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch15RODE

noncomputable def expand5Qpoch (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (qPochInfPS R)

theorem specialized_dobbie_identity (R : Type*) [CommRing R] :
    chan15LHSPS R * expand5Qpoch R = (qPochInfPS R) ^ 5 := by
  simpa [expand5Qpoch] using chan_theorem_11_7 R

end DobbieIdentityRootCheck
end Pending
end QseriesFormalization
