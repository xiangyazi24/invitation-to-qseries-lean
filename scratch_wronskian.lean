import QseriesFormalization.Pending.Chapter15_FormalDeriv
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal
import QseriesFormalization.Pending.Chapter16_MBI_Proof

namespace QseriesFormalization
namespace Pending
namespace ScratchWronskian

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch15FormalDeriv
open QseriesFormalization.Pending.JTPFormalPSPentagonal

example :
    (qPochInfPS ℚ) ^ 6 =
      pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
        5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
          pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ)) := by
  rw [QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two]
  ext n
  simp only [coeff_jacobiThetaPS, coeff_pentagonal014SeriesPS, coeff_pentagonal023SeriesPS,
    coeff_thetaOp, PowerSeries.coeff_mul]
  sorry

end ScratchWronskian
end Pending
end QseriesFormalization
