import QseriesFormalization.Pending.Chapter10_TenthOrder
import QseriesFormalization.Pending.ASD_EtaProducts

/-!
# Ramanujan's `1ψ1`: formal JTP-limit interface for Chapter 10

This file records the no-gap formal-power-series interface currently available
from the proved Jacobi triple product infrastructure.  In the one-variable
formal setting of this repository, the directly usable `1ψ1` input for Ch10 is
the JTP limiting specialization

`(X, X^4, X^5; X^5)_∞ = ∑_{k∈ℤ} (-1)^k X^((5k²-3k)/2)`.

It is the specialization used by the pentagonal factor in Chan Eq. (10.15).
-/

namespace QseriesFormalization
namespace Pending
namespace Ramanujan1Psi1

open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.ASDEtaProducts

/-! ## Product-side utilities -/

/-- Expanding the formal Euler product `(X;X)_∞` gives `(X^s;X^s)_∞`. -/
theorem expand_qPochInfPS_eq_qPochAPPS
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (s : ℕ) (hs : s ≠ 0) :
    PowerSeries.expand s hs (qPochInfPS R) = qPochAPPS R s s := by
  rw [qPochInfPS_eq_tprod R]
  rw [(multipliable_one_sub_X_pow_succ R).map_tprod
    (PowerSeries.expand s hs) (continuous_expand R s hs)]
  unfold qPochAPPS
  apply tprod_congr
  intro n
  calc
    PowerSeries.expand s hs ((1 : R⟦X⟧) - PowerSeries.X ^ (n + 1))
        = (1 : R⟦X⟧) - PowerSeries.X ^ (s * (n + 1)) := by
          rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
    _ = apFactorPS R s s n := by
          rw [apFactorPS]
          congr 1
          ring

/-- Ch10's `(Q^d;Q^d)_∞` helper is the AP product `(X^d;X^d)_∞`. -/
theorem ch10_qPochInfAtPowerPS_eq_qPochAPPS (d : ℕ) (hd : d ≠ 0) :
    QseriesFormalization.Pending.Ch10TenthOrder.qPochInfAtPowerPS d hd =
      qPochAPPS ℚ d d := by
  unfold QseriesFormalization.Pending.Ch10TenthOrder.qPochInfAtPowerPS
  exact expand_qPochInfPS_eq_qPochAPPS ℚ d hd

/-! ## The formal `1ψ1`/JTP limiting specialization -/

/-- Product side `(X, X^4, X^5; X^5)_∞`. -/
noncomputable abbrev onePsiOneLimit014ProductPS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  pentagonalProduct014PS R

/-- Series side `∑ (-1)^k X^((5k²-3k)/2)`. -/
noncomputable abbrev onePsiOneLimit014SeriesPS
    (R : Type*) [CommRing R] : R⟦X⟧ :=
  pentagonal014SeriesPS R

/-- Product side `(X^2, X^3, X^5; X^5)_∞`. -/
noncomputable abbrev onePsiOneLimit023ProductPS
    (R : Type*) [CommRing R] [TopologicalSpace R] : R⟦X⟧ :=
  pentagonalProduct023PS R

/-- Series side `∑ (-1)^k X^((5k²-k)/2)`. -/
noncomputable abbrev onePsiOneLimit023SeriesPS
    (R : Type*) [CommRing R] : R⟦X⟧ :=
  pentagonal023SeriesPS R

/-- Complex formal form of the JTP-limit case of Ramanujan's `1ψ1`. -/
theorem ramanujan1Psi1_limit014_formal_complex :
    onePsiOneLimit014ProductPS ℂ = onePsiOneLimit014SeriesPS ℂ :=
  pentagonalProduct014PS_eq_pentagonal014SeriesPS_complex

/-- The companion mod-5 JTP-limit case. -/
theorem ramanujan1Psi1_limit023_formal_complex :
    onePsiOneLimit023ProductPS ℂ = onePsiOneLimit023SeriesPS ℂ :=
  pentagonalProduct023PS_eq_pentagonal023SeriesPS_complex

private theorem map_pentagonalTripleFactor014PS_int
    (R : Type*) [CommRing R] (n : ℕ) :
    PowerSeries.map (Int.castRingHom R) (pentagonalTripleFactor014PS ℤ n) =
      pentagonalTripleFactor014PS R n := by
  simp [pentagonalTripleFactor014PS, apFactorPS, PowerSeries.map_X]

private theorem map_pentagonalTripleFactor023PS_int
    (R : Type*) [CommRing R] (n : ℕ) :
    PowerSeries.map (Int.castRingHom R) (pentagonalTripleFactor023PS ℤ n) =
      pentagonalTripleFactor023PS R n := by
  simp [pentagonalTripleFactor023PS, apFactorPS, PowerSeries.map_X]

private theorem map_pentagonalProduct014PS_int
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    PowerSeries.map (Int.castRingHom R) (pentagonalProduct014PS ℤ) =
      pentagonalProduct014PS R := by
  ext k
  rw [PowerSeries.coeff_map, coeff_pentagonalProduct014PS_eq_coeff_partial ℤ k,
    coeff_pentagonalProduct014PS_eq_coeff_partial R k]
  rw [← PowerSeries.coeff_map]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro n _hn
  exact map_pentagonalTripleFactor014PS_int R n

private theorem map_pentagonalProduct023PS_int
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    PowerSeries.map (Int.castRingHom R) (pentagonalProduct023PS ℤ) =
      pentagonalProduct023PS R := by
  ext k
  rw [PowerSeries.coeff_map, coeff_pentagonalProduct023PS_eq_coeff_partial ℤ k,
    coeff_pentagonalProduct023PS_eq_coeff_partial R k]
  rw [← PowerSeries.coeff_map]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro n _hn
  exact map_pentagonalTripleFactor023PS_int R n

private theorem map_pentagonal014SeriesPS_int
    (R : Type*) [CommRing R] :
    PowerSeries.map (Int.castRingHom R) (pentagonal014SeriesPS ℤ) =
      pentagonal014SeriesPS R := by
  ext n
  rw [PowerSeries.coeff_map, coeff_pentagonal014SeriesPS, coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : pentagonal014Exp k = n <;> simp [hk, negOnePowInt]

private theorem map_pentagonal023SeriesPS_int
    (R : Type*) [CommRing R] :
    PowerSeries.map (Int.castRingHom R) (pentagonal023SeriesPS ℤ) =
      pentagonal023SeriesPS R := by
  ext n
  rw [PowerSeries.coeff_map, coeff_pentagonal023SeriesPS, coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : pentagonal023Exp k = n <;> simp [hk, negOnePowInt]

/-- Rational formal form of the Ch10-facing `1ψ1`/JTP limiting specialization. -/
theorem ramanujan1Psi1_limit014_formal_rat :
    onePsiOneLimit014ProductPS ℚ = onePsiOneLimit014SeriesPS ℚ := by
  calc
    onePsiOneLimit014ProductPS ℚ
        = PowerSeries.map (Int.castRingHom ℚ) (pentagonalProduct014PS ℤ) :=
          (map_pentagonalProduct014PS_int ℚ).symm
    _ = PowerSeries.map (Int.castRingHom ℚ) (pentagonal014SeriesPS ℤ) := by
          rw [pentagonalProduct014PS_eq_pentagonal014SeriesPS_int]
    _ = onePsiOneLimit014SeriesPS ℚ := map_pentagonal014SeriesPS_int ℚ

/-- Rational form of the companion mod-5 specialization. -/
theorem ramanujan1Psi1_limit023_formal_rat :
    onePsiOneLimit023ProductPS ℚ = onePsiOneLimit023SeriesPS ℚ := by
  calc
    onePsiOneLimit023ProductPS ℚ
        = PowerSeries.map (Int.castRingHom ℚ) (pentagonalProduct023PS ℤ) :=
          (map_pentagonalProduct023PS_int ℚ).symm
    _ = PowerSeries.map (Int.castRingHom ℚ) (pentagonal023SeriesPS ℤ) := by
          rw [pentagonalProduct023PS_eq_pentagonal023SeriesPS_int]
    _ = onePsiOneLimit023SeriesPS ℚ := map_pentagonal023SeriesPS_int ℚ

/-! ## Chapter 10 hooks -/

/-- Ch10's pentagonal factor is the `q ↦ Q^3` expansion of the `1ψ1` limit series. -/
theorem ch10_chan1015PentagonalPS_eq_expand_onePsiOneLimit014_series :
    QseriesFormalization.Pending.Ch10TenthOrder.chan1015PentagonalPS =
      PowerSeries.expand 3 (by decide : (3 : ℕ) ≠ 0)
        (onePsiOneLimit014SeriesPS ℚ) := rfl

/-- The same Ch10 factor may be written with the product side, by `1ψ1`/JTP. -/
theorem ch10_expand_onePsiOneLimit014_product_eq_chan1015PentagonalPS :
    PowerSeries.expand 3 (by decide : (3 : ℕ) ≠ 0)
        (onePsiOneLimit014ProductPS ℚ) =
      QseriesFormalization.Pending.Ch10TenthOrder.chan1015PentagonalPS := by
  rw [ramanujan1Psi1_limit014_formal_rat]
  exact ch10_chan1015PentagonalPS_eq_expand_onePsiOneLimit014_series.symm

/-- Coefficient form of the Ch10 pentagonal factor. -/
theorem coeff_ch10_chan1015PentagonalPS (n : ℕ) :
    (QseriesFormalization.Pending.Ch10TenthOrder.chan1015PentagonalPS).coeff n =
      if 3 ∣ n then pentagonal014Coeff ℚ (n / 3) else 0 := by
  rw [QseriesFormalization.Pending.Ch10TenthOrder.chan1015PentagonalPS,
    PowerSeries.coeff_expand]
  by_cases hdiv : 3 ∣ n <;> simp [hdiv]

/-- Ch10 RHS with the pentagonal factor rewritten through the product-side `1ψ1` limit. -/
theorem chan1015RHSPS_eq_onePsiOneLimit_product_form :
    QseriesFormalization.Pending.Ch10TenthOrder.chan1015RHSPS =
      -((QseriesFormalization.Pending.Ch10TenthOrder.qPochInfAtPowerPS 3
            (by decide : (3 : ℕ) ≠ 0)) ^ 5 *
        ((QseriesFormalization.Pending.Ch10TenthOrder.qPochInfAtPowerPS 6
            (by decide : (6 : ℕ) ≠ 0)) ^ 2)⁻¹ *
        PowerSeries.expand 3 (by decide : (3 : ℕ) ≠ 0)
          (onePsiOneLimit014ProductPS ℚ)) := by
  unfold QseriesFormalization.Pending.Ch10TenthOrder.chan1015RHSPS
  rw [ch10_expand_onePsiOneLimit014_product_eq_chan1015PentagonalPS]

/-- Ch10 RHS entirely in AP-product notation. -/
theorem chan1015RHSPS_eq_AP_product_form :
    QseriesFormalization.Pending.Ch10TenthOrder.chan1015RHSPS =
      -((qPochAPPS ℚ 3 3) ^ 5 * ((qPochAPPS ℚ 6 6) ^ 2)⁻¹ *
        PowerSeries.expand 3 (by decide : (3 : ℕ) ≠ 0)
          (onePsiOneLimit014ProductPS ℚ)) := by
  rw [chan1015RHSPS_eq_onePsiOneLimit_product_form]
  rw [ch10_qPochInfAtPowerPS_eq_qPochAPPS 3 (by decide : (3 : ℕ) ≠ 0),
    ch10_qPochInfAtPowerPS_eq_qPochAPPS 6 (by decide : (6 : ℕ) ≠ 0)]

end Ramanujan1Psi1
end Pending
end QseriesFormalization
