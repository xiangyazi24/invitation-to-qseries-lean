import QseriesFormalization.Pending.RR_AnalyticProof
import QseriesFormalization.Pending.RogersRamanujan_FormalPS

/-!
# Rogers-Ramanujan analytic-to-formal lift

This file contains the algebraic descent layer needed for the formal
Rogers-Ramanujan `G` identity.  The remaining analytic input is the Taylor
bridge identifying the formal series `rrGPS` with `q ↦ rrJInf 1 q`.
-/

namespace QseriesFormalization
namespace Pending
namespace RRLiftToFormalPS

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.RogersRamanujanFormalPS

/-- Naturality of the `023` pentagonal series under `ℚ → ℂ`. -/
theorem map_pentagonal023SeriesPS_rat_complex :
    PowerSeries.map (algebraMap ℚ ℂ) (pentagonal023SeriesPS ℚ) =
      pentagonal023SeriesPS ℂ := by
  ext n
  rw [PowerSeries.coeff_map, coeff_pentagonal023SeriesPS, coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : pentagonal023Exp k = n <;> simp [hk, negOnePowInt]

/--
Descent from the complexified formal identity to the rational formal identity.

This is the last algebraic step once the analytic-to-formal Taylor bridge has
proved the complexified coefficient identity.
-/
theorem rogers_ramanujan_G_formal_of_complexification
    (h_complex :
      PowerSeries.map (algebraMap ℚ ℂ) (rrGPS * qPochInfPS ℚ) =
        pentagonal023SeriesPS ℂ) :
    rrGPS * qPochInfPS ℚ = pentagonal023SeriesPS ℚ := by
  apply PowerSeries.map_injective (algebraMap ℚ ℂ) (Rat.cast_injective)
  rw [h_complex, map_pentagonal023SeriesPS_rat_complex]

/--
Same descent step, but with the complexified identity written after mapping
the two formal factors separately.  This is the shape produced by a Taylor
bridge for `rrGPS` together with `map_qPochInfPS`.
-/
theorem rogers_ramanujan_G_formal_of_complex_identity
    (h_complex :
      PowerSeries.map (algebraMap ℚ ℂ) rrGPS * qPochInfPS ℂ =
        pentagonal023SeriesPS ℂ) :
    rrGPS * qPochInfPS ℚ = pentagonal023SeriesPS ℚ := by
  apply rogers_ramanujan_G_formal_of_complexification
  rw [map_mul, map_qPochInfPS (algebraMap ℚ ℂ), h_complex]

end RRLiftToFormalPS
end Pending
end QseriesFormalization
