import QseriesFormalization.Chapter14_Thm116
import QseriesFormalization.Pending.Chapter13_RRCF_RForm

/-!
# Chan Equation 12.37 in formal power series

This file packages the product-core identity already implicit in the closed
Macdonald-Bailey / Ramanujan-quintic proof.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch13Eq1237

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch16MBIProof
open QseriesFormalization.Pending.JTPFormalPSPentagonal

/-- The expanded product-core identity follows from the closed
`E5DenominatorCoreRat * E(q^25) = E(q^5)^6` identity and the product bridge
proved in `Chapter14_Thm116`. -/
theorem mod5_product_core_atFive_of_E5_denominator_identity
    (hden :
      E5DenominatorCoreRat *
          PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) =
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6) :
    (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^6 *
        ramanujanMod5ProductCoreRat =
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
        (pentagonalProduct014AtFiveRat)^5 *
        (pentagonalProduct023AtFiveRat)^5 := by
  let E0 : ℚ⟦X⟧ := E5 ℚ 0
  let E1 : ℚ⟦X⟧ := E5 ℚ 1
  let E2 : ℚ⟦X⟧ := E5 ℚ 2
  let H : ℚ⟦X⟧ := pentagonalProduct014AtFiveRat
  let G : ℚ⟦X⟧ := pentagonalProduct023AtFiveRat
  let W : ℚ⟦X⟧ := PowerSeries.expand 25 (by decide) (qPochInfPS ℚ)
  let F : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
  have hE0 : E0 * H = W * G := by
    simpa [E0, H, W, G] using
      QseriesFormalization.PartIII.Ch14Thm116.E5_zero_product_bridge_expanded_rat
  have hE1 : E1 = -PowerSeries.X * W := by
    simpa [E1, W] using E5_one_eq_neg_X_mul_expand_twentyfive_qPochInfPS ℚ
  have hE2 : E2 * G = -PowerSeries.X^2 * W * H := by
    have hbridge :=
      E5_two_product_bridge_of_E5_zero_product_bridge
        QseriesFormalization.PartIII.Ch14Thm116.E5_zero_product_bridge_expanded_rat
    simpa [E2, G, W, H] using hbridge
  have hE0pow : E0^5 * H^5 = W^5 * G^5 := by
    rw [← mul_pow, hE0, mul_pow]
  have hE1pow : E1^5 = -PowerSeries.X^5 * W^5 := by
    rw [hE1]
    ring
  have hE2pow : E2^5 * G^5 = -PowerSeries.X^10 * W^5 * H^5 := by
    rw [← mul_pow, hE2]
    ring
  have hE0term :
      E0^5 * W * (H^5 * G^5) = W^6 * G^10 := by
    calc
      E0^5 * W * (H^5 * G^5) = (E0^5 * H^5) * W * G^5 := by ring
      _ = (W^5 * G^5) * W * G^5 := by rw [hE0pow]
      _ = W^6 * G^10 := by ring
  have hE1term :
      (11 : ℚ⟦X⟧) * E1^5 * W * (H^5 * G^5) =
        W^6 * (-(11 : ℚ⟦X⟧) * PowerSeries.X^5 * H^5 * G^5) := by
    rw [hE1pow]
    ring
  have hE2term :
      E2^5 * W * (H^5 * G^5) =
        W^6 * (-PowerSeries.X^10 * H^10) := by
    calc
      E2^5 * W * (H^5 * G^5) = (E2^5 * G^5) * W * H^5 := by ring
      _ = (-PowerSeries.X^10 * W^5 * H^5) * W * H^5 := by rw [hE2pow]
      _ = W^6 * (-PowerSeries.X^10 * H^10) := by ring
  have hcore :
      (E5DenominatorCoreRat * W) * (H^5 * G^5) =
        W^6 * ramanujanMod5ProductCoreRat := by
    calc
      (E5DenominatorCoreRat * W) * (H^5 * G^5)
          =
        E0^5 * W * (H^5 * G^5) +
          (11 : ℚ⟦X⟧) * E1^5 * W * (H^5 * G^5) +
          E2^5 * W * (H^5 * G^5) := by
            simp [E5DenominatorCoreRat, E0, E1, E2]
            ring
      _ =
        W^6 * G^10 +
          W^6 * (-(11 : ℚ⟦X⟧) * PowerSeries.X^5 * H^5 * G^5) +
          W^6 * (-PowerSeries.X^10 * H^10) := by
            rw [hE0term, hE1term, hE2term]
      _ =
        W^6 * (G^10 - (11 : ℚ⟦X⟧) * PowerSeries.X^5 * H^5 * G^5 -
          PowerSeries.X^10 * H^10) := by ring
      _ = W^6 * ramanujanMod5ProductCoreRat := by
            simp [ramanujanMod5ProductCoreRat, H, G]
  have hden' : E5DenominatorCoreRat * W = F^6 := by
    simpa [W, F] using hden
  change W^6 * ramanujanMod5ProductCoreRat = F^6 * H^5 * G^5
  calc
    W^6 * ramanujanMod5ProductCoreRat =
        (E5DenominatorCoreRat * W) * (H^5 * G^5) := hcore.symm
    _ = F^6 * (H^5 * G^5) := by rw [hden']
    _ = F^6 * H^5 * G^5 := by ring

/-- Uncompressed product-core bridge obtained by injectivity of `X ↦ X^5`. -/
theorem mod5_product_core_compressed_of_atFive
    (h :
      (PowerSeries.expand 25 (by decide) (qPochInfPS ℚ))^6 *
          ramanujanMod5ProductCoreRat =
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
          (pentagonalProduct014AtFiveRat)^5 *
          (pentagonalProduct023AtFiveRat)^5) :
    (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
        ramanujanMod5ProductCoreCompressedRat =
      (qPochInfPS ℚ)^6 *
        (pentagonalProduct014PS ℚ)^5 *
        (pentagonalProduct023PS ℚ)^5 := by
  apply expand_five_injective_rat
  rw [map_mul, map_pow, map_mul, map_mul, map_pow, map_pow, map_pow,
    expand_five_ramanujanMod5ProductCoreCompressedRat]
  rw [← PowerSeries.expand_mul (p := 5) (hp := by decide) (q := 5)
    (hq := by decide) (qPochInfPS ℚ)]
  simpa [pentagonalProduct014AtFiveRat, pentagonalProduct023AtFiveRat, mul_assoc]
    using h

/-- The theta-series product core used by Chan Eq. 12.37. -/
theorem chan_eq_12_37_product_core :
    (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
        ramanujanMod5ProductCoreThetaRat =
      (qPochInfPS ℚ)^6 *
        (pentagonal014SeriesPS ℚ)^5 *
        (pentagonal023SeriesPS ℚ)^5 := by
  have hAtFive :=
    mod5_product_core_atFive_of_E5_denominator_identity
      QseriesFormalization.Pending.RamanujanQuinticJTP.E5DenominatorCoreRat_mul_expand_twentyfive_qPochInfPS
  have hCompressed := mod5_product_core_compressed_of_atFive hAtFive
  simpa [ramanujanMod5ProductCoreCompressedRat_eq_theta,
    pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat,
    pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat] using hCompressed

/-- Chan Eq. 12.37, cleared of denominators, as an identity in `ℚ⟦X⟧`. -/
theorem chan_eq_12_37_cleared :
    (qPochInfPS ℚ)^6 *
        (pentagonal014SeriesPS ℚ)^5 *
        (pentagonal023SeriesPS ℚ)^5 =
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
        ((pentagonal023SeriesPS ℚ)^10 -
          (11 : ℚ⟦X⟧) * PowerSeries.X *
            (pentagonal014SeriesPS ℚ)^5 * (pentagonal023SeriesPS ℚ)^5 -
          PowerSeries.X^2 * (pentagonal014SeriesPS ℚ)^10) := by
  simpa [ramanujanMod5ProductCoreThetaRat] using chan_eq_12_37_product_core.symm

end Ch13Eq1237
end Pending
end QseriesFormalization
