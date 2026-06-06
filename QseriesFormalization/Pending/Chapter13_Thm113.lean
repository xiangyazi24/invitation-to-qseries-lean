import QseriesFormalization.Pending.RamanujanQuinticJTP

/-!
# Chan Theorem 11.3, formal-power-series form

This file proves the cleared, fractional-power-free form of Chan's Theorem
11.3 after the substitution `q -> q^5`.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch13Thm113

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology

open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.RamanujanQuinticJTP

private theorem map_pentagonal014SeriesPS_rat_complex :
    PowerSeries.map (algebraMap ℚ ℂ) (pentagonal014SeriesPS ℚ) =
      pentagonal014SeriesPS ℂ := by
  ext n
  rw [PowerSeries.coeff_map, coeff_pentagonal014SeriesPS, coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : pentagonal014Exp k = n <;> simp [hk, negOnePowInt]

private theorem map_pentagonal023SeriesPS_rat_complex :
    PowerSeries.map (algebraMap ℚ ℂ) (pentagonal023SeriesPS ℚ) =
      pentagonal023SeriesPS ℂ := by
  ext n
  rw [PowerSeries.coeff_map, coeff_pentagonal023SeriesPS, coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hk : pentagonal023Exp k = n <;> simp [hk, negOnePowInt]

private theorem continuous_expand (R : Type*) [CommRing R] [TopologicalSpace R]
    (s : ℕ) (hs : s ≠ 0) :
    Continuous (PowerSeries.expand s hs : R⟦X⟧ → R⟦X⟧) := by
  rw [continuous_iff_continuousAt]
  intro φ
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp_rw [PowerSeries.coeff_expand s hs]
  by_cases hdiv : s ∣ n
  · simpa [hdiv] using
      (PowerSeries.WithPiTopology.continuous_coeff R (n / s)).tendsto φ
  · simpa [hdiv] using tendsto_const_nhds

private theorem hasProd_expand_five_qPochInfPS_complex :
    HasProd (fun n : ℕ => (1 : ℂ⟦X⟧) - PowerSeries.X ^ (5 * (n + 1)))
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)) := by
  have hbase : HasProd (fun n : ℕ => oneSubXPow ℂ n) (qPochInfPS ℂ) := by
    rw [qPochInfPS_eq_tprod ℂ]
    exact (multipliable_one_sub_X_pow_succ ℂ).hasProd
  have hmap := hbase.map (PowerSeries.expand 5 (by decide))
    (continuous_expand ℂ 5 (by decide))
  exact hmap.congr_fun fun n => by
    symm
    unfold oneSubXPow
    dsimp only [Function.comp_apply]
    rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]

private theorem prod_constQFactorPS_fifth
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    (∏ j : Fin 5, constQFactorPS (ζ ^ (j : ℕ)) n) =
      (1 : ℂ⟦X⟧) - PowerSeries.X ^ (5 * (n + 1)) := by
  calc
    (∏ j : Fin 5, constQFactorPS (ζ ^ (j : ℕ)) n)
        = ∏ j : Fin 5,
            (1 - PowerSeries.C (ζ ^ (j : ℕ)) * PowerSeries.X ^ (n + 1)) := rfl
    _ = (1 : ℂ⟦X⟧) - (PowerSeries.X ^ (n + 1)) ^ 5 := by
        exact prod_one_sub_primitive_fifth_powerSeries
          (R := ℂ) (μ := ζ) (Y := PowerSeries.X ^ (n + 1)) hζ
    _ = (1 : ℂ⟦X⟧) - PowerSeries.X ^ (5 * (n + 1)) := by
        rw [← pow_mul]
        congr 1
        ring

private theorem prod_constQPochInfPS_fifth_collapse_complex
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (∏ j : Fin 5, constQPochInfPS (ζ ^ (j : ℕ))) =
      PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) := by
  have hprod :
      HasProd
        (fun n : ℕ => ∏ j : Fin 5, constQFactorPS (ζ ^ (j : ℕ)) n)
        (∏ j : Fin 5, constQPochInfPS (ζ ^ (j : ℕ))) := by
    exact hasProd_prod (s := (Finset.univ : Finset (Fin 5)))
      (f := fun (j : Fin 5) (n : ℕ) => constQFactorPS (ζ ^ (j : ℕ)) n)
      (a := fun j : Fin 5 => constQPochInfPS (ζ ^ (j : ℕ)))
      (by
        intro j _hj
        exact hasProd_constQFactorPS (ζ ^ (j : ℕ)))
  have hprod' :
      HasProd (fun n : ℕ => (1 : ℂ⟦X⟧) - PowerSeries.X ^ (5 * (n + 1)))
        (∏ j : Fin 5, constQPochInfPS (ζ ^ (j : ℕ))) :=
    hprod.congr_fun fun n => (prod_constQFactorPS_fifth hζ n).symm
  exact hprod'.unique hasProd_expand_five_qPochInfPS_complex

private theorem zeta_inv_eq_pow_four {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    ζ⁻¹ = ζ ^ 4 := by
  exact inv_eq_of_mul_eq_one_right (by
    rw [← pow_succ', show 4 + 1 = 5 by norm_num, hζ.pow_eq_one])

private theorem zeta_sq_inv_eq_pow_three {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (ζ ^ 2)⁻¹ = ζ ^ 3 := by
  exact inv_eq_of_mul_eq_one_right (by
    rw [← pow_add, show 2 + 3 = 5 by norm_num, hζ.pow_eq_one])

private theorem section83JTPProductPS_pair_product_eq_qPochInfPS_mul_expand
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    section83JTPProductPS ζ * section83JTPProductPS (ζ ^ 2) =
      qPochInfPS ℂ * PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) := by
  have hζinv : ζ⁻¹ = ζ ^ 4 := zeta_inv_eq_pow_four hζ
  have hζ2inv : (ζ ^ 2)⁻¹ = ζ ^ 3 := zeta_sq_inv_eq_pow_three hζ
  have hcollapse := prod_constQPochInfPS_fifth_collapse_complex hζ
  have hcollapse' :
      constQPochInfPS 1 * constQPochInfPS ζ * constQPochInfPS (ζ ^ 2) *
          constQPochInfPS (ζ ^ 3) * constQPochInfPS (ζ ^ 4) =
        PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) := by
    simpa [Fin.prod_univ_five] using hcollapse
  unfold section83JTPProductPS
  rw [hζinv, hζ2inv]
  calc
    (constQPochInfPS 1 * constQPochInfPS ζ * constQPochInfPS (ζ ^ 4)) *
        (constQPochInfPS 1 * constQPochInfPS (ζ ^ 2) * constQPochInfPS (ζ ^ 3))
        =
      constQPochInfPS 1 *
        (constQPochInfPS 1 * constQPochInfPS ζ * constQPochInfPS (ζ ^ 2) *
          constQPochInfPS (ζ ^ 3) * constQPochInfPS (ζ ^ 4)) := by
        ring
    _ = qPochInfPS ℂ * PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) := by
        rw [← hcollapse', constQPochInfPS_one]

private theorem section83_rhs_pair_product_eq_chan113_left
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    section83_rhs_pair14 ζ * section83_rhs_pair23 ζ =
      (section83A ℂ)^2 - PowerSeries.X * section83A ℂ * section83B ℂ -
        PowerSeries.X^2 * (section83B ℂ)^2 := by
  let A : ℂ⟦X⟧ := section83A ℂ
  let B : ℂ⟦X⟧ := section83B ℂ
  let a : ℂ := quinticPeriodAlpha ζ
  let b : ℂ := quinticPeriodBeta ζ
  have hsum : a + b = -1 := by
    simpa [a, b] using quinticPeriod_sum (R := ℂ) hζ
  have hprod : a * b = -1 := by
    simpa [a, b] using quinticPeriod_mul (R := ℂ) hζ
  have hsumC :
      PowerSeries.C b + PowerSeries.C a = (-1 : ℂ⟦X⟧) := by
    rw [← map_add, add_comm, hsum]
    simp
  have hprodC :
      PowerSeries.C b * PowerSeries.C a = (-1 : ℂ⟦X⟧) := by
    rw [← map_mul, mul_comm, hprod]
    simp
  calc
    section83_rhs_pair14 ζ * section83_rhs_pair23 ζ
        =
      (A + PowerSeries.C b * PowerSeries.X * B) *
        (A + PowerSeries.C a * PowerSeries.X * B) := by
        rfl
    _ =
      A^2 + (PowerSeries.C b + PowerSeries.C a) * PowerSeries.X * A * B +
        (PowerSeries.C b * PowerSeries.C a) * PowerSeries.X^2 * B^2 := by
        ring
    _ = A^2 - PowerSeries.X * A * B - PowerSeries.X^2 * B^2 := by
        rw [hsumC, hprodC]
        ring

private theorem chan_theorem_11_3_complex_of_primitive
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℂ))^2 -
        PowerSeries.X *
          PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℂ) *
          PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℂ) -
        PowerSeries.X^2 *
          (PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℂ))^2 =
      qPochInfPS ℂ * PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) := by
  calc
    (PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℂ))^2 -
        PowerSeries.X *
          PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℂ) *
          PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℂ) -
        PowerSeries.X^2 *
          (PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℂ))^2
        =
      (section83A ℂ)^2 - PowerSeries.X * section83A ℂ * section83B ℂ -
        PowerSeries.X^2 * (section83B ℂ)^2 := by
        rfl
    _ = section83_rhs_pair14 ζ * section83_rhs_pair23 ζ :=
        (section83_rhs_pair_product_eq_chan113_left hζ).symm
    _ = section83JTPProductPS ζ * section83JTPProductPS (ζ ^ 2) := by
        rw [← section83JTPProductPS_eq_rhs_pair14 hζ,
          ← section83JTPProductPS_eq_rhs_pair23 hζ]
    _ = qPochInfPS ℂ * PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) :=
        section83JTPProductPS_pair_product_eq_qPochInfPS_mul_expand hζ

private theorem chan_theorem_11_3_complex :
    (PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℂ))^2 -
        PowerSeries.X *
          PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℂ) *
          PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℂ) -
        PowerSeries.X^2 *
          (PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℂ))^2 =
      qPochInfPS ℂ * PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)
  have hζ : IsPrimitiveRoot ζ 5 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp 5 (by norm_num : (5 : ℕ) ≠ 0)
  exact chan_theorem_11_3_complex_of_primitive hζ

/-- Chan Theorem 11.3 in cleared formal-power-series form, after `q -> q^5`. -/
theorem chan_theorem_11_3_formal_ps :
    (PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ))^2 -
        PowerSeries.X *
          PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ) *
          PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ) -
        PowerSeries.X^2 *
          (PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ))^2 =
      qPochInfPS ℚ * PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) := by
  apply PowerSeries.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  simpa [map_sub, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_expand,
    map_pentagonal023SeriesPS_rat_complex, map_pentagonal014SeriesPS_rat_complex,
    map_qPochInfPS (algebraMap ℚ ℂ)] using chan_theorem_11_3_complex

end Ch13Thm113
end Pending
end QseriesFormalization
