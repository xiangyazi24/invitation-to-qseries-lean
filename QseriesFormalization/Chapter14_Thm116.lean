import QseriesFormalization.Pending.RamanujanQuinticJTP
import QseriesFormalization.Pending.ASD_EtaProducts
import QseriesFormalization.Chapter11

/-!
# Chapter 14 — Chan Theorem 11.6 formal target

This file records the formal-power-series objects for the Lost Notebook
identity in Chan Theorem 11.6 and closes the reusable JTP-at-a-fifth-root
denominator collapse.  The remaining unproved bridge is isolated as a single
product identity involving the Rogers-Ramanujan `G,H` product factors below.
-/

namespace QseriesFormalization
namespace PartIII
namespace Ch14Thm116

open PowerSeries
open Filter
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.RamanujanQuinticJTP
open QseriesFormalization.Pending.Ch16MBIProof

noncomputable abbrev CPowerSeries := ℂ⟦X⟧

/-! ## The four product-side series in Theorem 11.6 -/

/-- Formal `f(-q^25) = (q^25;q^25)_∞`. -/
noncomputable def fMinusQ25PS : CPowerSeries :=
  PowerSeries.expand 25 (by decide) (qPochInfPS ℂ)

/-- Denominator of `G(q^5)`: `(q^5,q^20;q^25)_∞`. -/
noncomputable def rrGDenAtQ5PS : CPowerSeries :=
  qPochAPPS ℂ 5 25 * qPochAPPS ℂ 20 25

/-- Denominator of `H(q^5)`: `(q^10,q^15;q^25)_∞`. -/
noncomputable def rrHDenAtQ5PS : CPowerSeries :=
  qPochAPPS ℂ 10 25 * qPochAPPS ℂ 15 25

/-- Formal Rogers-Ramanujan product `G(q^5)`. -/
noncomputable def rrGAtQ5PS : CPowerSeries :=
  (rrGDenAtQ5PS)⁻¹

/-- Formal Rogers-Ramanujan product `H(q^5)`. -/
noncomputable def rrHAtQ5PS : CPowerSeries :=
  (rrHDenAtQ5PS)⁻¹

/-- `A(q^5) = f(-q^25) G(q^5)^2 / H(q^5)`. -/
noncomputable def chan116A : CPowerSeries :=
  fMinusQ25PS * rrGAtQ5PS ^ 2 * (rrHAtQ5PS)⁻¹

/-- `B(q^5) = f(-q^25) G(q^5)`. -/
noncomputable def chan116B : CPowerSeries :=
  fMinusQ25PS * rrGAtQ5PS

/-- `C(q^5) = f(-q^25) H(q^5)`. -/
noncomputable def chan116C : CPowerSeries :=
  fMinusQ25PS * rrHAtQ5PS

/-- `D(q^5) = f(-q^25) H(q^5)^2 / G(q^5)`. -/
noncomputable def chan116D : CPowerSeries :=
  fMinusQ25PS * rrHAtQ5PS ^ 2 * (rrGAtQ5PS)⁻¹

/-- The denominator `(ζq;q)_∞ (ζ⁻¹q;q)_∞` in formal-power-series form. -/
noncomputable def chan116DenomPS (ζ : ℂ) : CPowerSeries :=
  constQPochInfPS ζ * constQPochInfPS ζ⁻¹

/-- The formal left side `(q;q)_∞ / ((ζq;q)_∞(ζ⁻¹q;q)_∞)`. -/
noncomputable def chan116LHS (ζ : ℂ) : CPowerSeries :=
  qPochInfPS ℂ * (chan116DenomPS ζ)⁻¹

/-- The four-term right side in the statement of Chan Theorem 11.6. -/
noncomputable def chan116RHS (ζ : ℂ) : CPowerSeries :=
  chan116A
    - PowerSeries.C ((ζ + ζ⁻¹) ^ 2) * PowerSeries.X * chan116B
    + PowerSeries.C (ζ ^ 2 + (ζ⁻¹) ^ 2) * PowerSeries.X ^ 2 * chan116C
    - PowerSeries.C (ζ + ζ⁻¹) * PowerSeries.X ^ 3 * chan116D

/-- The same RHS, written with the Gaussian periods already used by the
quintic JTP formalization. -/
noncomputable def chan116RHS_period (ζ : ℂ) : CPowerSeries :=
  chan116A
    - PowerSeries.C ((quinticPeriodAlpha ζ) ^ 2) * PowerSeries.X * chan116B
    + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X ^ 2 * chan116C
    - PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X ^ 3 * chan116D

/-! ## Period normalizations for a primitive fifth root -/

private theorem zeta_ne_zero {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) : ζ ≠ 0 := by
  intro h
  have hpow : ζ ^ 5 = 1 := hζ.pow_eq_one
  rw [h] at hpow
  norm_num at hpow

theorem zeta_inv_eq_pow_four {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    ζ⁻¹ = ζ ^ 4 := by
  apply inv_eq_of_mul_eq_one_right
  calc
    ζ * ζ ^ 4 = ζ ^ 5 := by ring
    _ = 1 := hζ.pow_eq_one

theorem zeta_inv_sq_eq_pow_three {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (ζ⁻¹) ^ 2 = ζ ^ 3 := by
  rw [zeta_inv_eq_pow_four hζ]
  calc
    (ζ ^ 4) ^ 2 = ζ ^ (5 * 1 + 3) := by ring
    _ = ζ ^ 3 := quintic_zeta_pow_five_mul_add (R := ℂ) hζ 1 3

theorem zeta_add_inv_eq_quinticPeriodAlpha {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    ζ + ζ⁻¹ = quinticPeriodAlpha ζ := by
  rw [zeta_inv_eq_pow_four hζ]
  rfl

theorem zeta_sq_add_inv_sq_eq_quinticPeriodBeta {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) :
    ζ ^ 2 + (ζ⁻¹) ^ 2 = quinticPeriodBeta ζ := by
  rw [zeta_inv_sq_eq_pow_three hζ]
  rfl

theorem chan116RHS_eq_period {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    chan116RHS ζ = chan116RHS_period ζ := by
  unfold chan116RHS chan116RHS_period
  rw [zeta_add_inv_eq_quinticPeriodAlpha hζ,
    zeta_sq_add_inv_sq_eq_quinticPeriodBeta hζ]

/-! ## Product rewrites for the §8.3 factors -/

theorem fMinusQ25PS_eq_qPochAPPS_25_25 :
    fMinusQ25PS = qPochAPPS ℂ 25 25 := by
  unfold fMinusQ25PS
  rw [qPochInfPS_eq_tprod ℂ]
  rw [(multipliable_one_sub_X_pow_succ ℂ).map_tprod
    (PowerSeries.expand 25 (by decide))
    (QseriesFormalization.Pending.ASDEtaProducts.continuous_expand ℂ 25 (by decide))]
  unfold qPochAPPS
  apply tprod_congr
  intro n
  calc
    PowerSeries.expand 25 (by decide) ((1 : ℂ⟦X⟧) - PowerSeries.X ^ (n + 1))
        = (1 : ℂ⟦X⟧) - PowerSeries.X ^ (25 * (n + 1)) := by
          rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
    _ = apFactorPS ℂ 25 25 n := by
          rw [apFactorPS]
          congr 1
          ring_nf

theorem section83A_eq_rrHDenAtQ5PS_mul_fMinusQ25PS :
    section83A ℂ = rrHDenAtQ5PS * fMinusQ25PS := by
  calc
    section83A ℂ = QseriesFormalization.Pending.ASDEtaProducts.asd5FSeriesPS ℂ := rfl
    _ = QseriesFormalization.Pending.ASDEtaProducts.asd5FProductPS ℂ :=
        QseriesFormalization.Pending.ASDEtaProducts.asd5FProductPS_eq_asd5FSeriesPS_complex.symm
    _ = rrHDenAtQ5PS * fMinusQ25PS := by
        unfold QseriesFormalization.Pending.ASDEtaProducts.asd5FProductPS
          rrHDenAtQ5PS
        rw [fMinusQ25PS_eq_qPochAPPS_25_25]

theorem section83B_eq_rrGDenAtQ5PS_mul_fMinusQ25PS :
    section83B ℂ = rrGDenAtQ5PS * fMinusQ25PS := by
  calc
    section83B ℂ = QseriesFormalization.Pending.ASDEtaProducts.asd5GSeriesPS ℂ := rfl
    _ = QseriesFormalization.Pending.ASDEtaProducts.asd5GProductPS ℂ :=
        QseriesFormalization.Pending.ASDEtaProducts.asd5GProductPS_eq_asd5GSeriesPS_complex.symm
    _ = rrGDenAtQ5PS * fMinusQ25PS := by
        unfold QseriesFormalization.Pending.ASDEtaProducts.asd5GProductPS
          rrGDenAtQ5PS
        rw [fMinusQ25PS_eq_qPochAPPS_25_25]

theorem section83_rhs_pair14_eq_fMinusQ25PS_mul {ζ : ℂ} :
    section83_rhs_pair14 ζ =
      fMinusQ25PS *
        (rrHDenAtQ5PS +
          PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X * rrGDenAtQ5PS) := by
  unfold section83_rhs_pair14
  rw [section83A_eq_rrHDenAtQ5PS_mul_fMinusQ25PS,
    section83B_eq_rrGDenAtQ5PS_mul_fMinusQ25PS]
  ring

/-! ## The JTP denominator collapse reused by Theorem 11.6 -/

theorem section83JTPProductPS_eq_qPoch_mul_chan116DenomPS (ζ : ℂ) :
    section83JTPProductPS ζ = qPochInfPS ℂ * chan116DenomPS ζ := by
  unfold section83JTPProductPS chan116DenomPS
  rw [constQPochInfPS_one]
  ring

/-- The already-formalized JTP-at-`ζ` identity, rewritten as the product
denominator needed by Theorem 11.6. -/
theorem chan116_jtp_denominator_collapse {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    qPochInfPS ℂ * chan116DenomPS ζ = section83_rhs_pair14 ζ := by
  rw [← section83JTPProductPS_eq_qPoch_mul_chan116DenomPS ζ]
  exact section83JTPProductPS_eq_rhs_pair14 hζ

/-- The conjugate JTP-at-`ζ²` collapse.  This is the second period identity
available from the existing quintic JTP file. -/
theorem chan116_jtp_denominator_collapse_sq {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) :
    qPochInfPS ℂ * chan116DenomPS (ζ ^ 2) = section83_rhs_pair23 ζ := by
  rw [← section83JTPProductPS_eq_qPoch_mul_chan116DenomPS (ζ ^ 2)]
  exact section83JTPProductPS_eq_rhs_pair23 hζ

/-! ## Unit bookkeeping for the reciprocal side -/

@[simp] theorem coeff_zero_constQFactorPS (c : ℂ) (n : ℕ) :
    (constQFactorPS c n).coeff 0 = 1 := by
  simp [constQFactorPS]

private theorem coeff_zero_partial_constQFactorPS (c : ℂ) (N : ℕ) :
    (∏ n ∈ Finset.range N, constQFactorPS c n).coeff 0 = 1 := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.prod_range_succ]
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rw [ih, coeff_zero_constQFactorPS]
      ring

theorem coeff_zero_constQPochInfPS (c : ℂ) :
    (constQPochInfPS c).coeff 0 = 1 := by
  have hprod := (hasProd_constQFactorPS c).tendsto_prod_nat
  have hcoeff :
      Tendsto
        (fun N : ℕ => (∏ n ∈ Finset.range N, constQFactorPS c n).coeff 0)
        atTop (𝓝 ((constQPochInfPS c).coeff 0)) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℂ 0).tendsto _).comp hprod
  have hone :
      Tendsto
        (fun N : ℕ => (∏ n ∈ Finset.range N, constQFactorPS c n).coeff 0)
        atTop (𝓝 (1 : ℂ)) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    exact Filter.Eventually.of_forall fun N => (coeff_zero_partial_constQFactorPS c N).symm
  exact tendsto_nhds_unique hcoeff hone

theorem isUnit_constQPochInfPS (c : ℂ) : IsUnit (constQPochInfPS c) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [coeff_zero_constQPochInfPS]

theorem isUnit_chan116DenomPS (ζ : ℂ) : IsUnit (chan116DenomPS ζ) := by
  unfold chan116DenomPS
  exact (isUnit_constQPochInfPS ζ).mul (isUnit_constQPochInfPS ζ⁻¹)

/-- Multiplying the formal left side by the collapsed JTP denominator leaves
`(q;q)_∞²`.  This is the exact reciprocal algebra needed before the remaining
Rogers-Ramanujan product identity is supplied. -/
theorem chan116LHS_mul_section83_rhs_pair14 {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) :
    chan116LHS ζ * section83_rhs_pair14 ζ = (qPochInfPS ℂ) ^ 2 := by
  have hden_unit : IsUnit (chan116DenomPS ζ) := isUnit_chan116DenomPS ζ
  have hden_coeff_ne : PowerSeries.constantCoeff (chan116DenomPS ζ) ≠ 0 :=
    (PowerSeries.isUnit_iff_constantCoeff.mp hden_unit).ne_zero
  have hcollapse := chan116_jtp_denominator_collapse hζ
  unfold chan116LHS
  rw [← hcollapse]
  calc
    (qPochInfPS ℂ * (chan116DenomPS ζ)⁻¹) *
        (qPochInfPS ℂ * chan116DenomPS ζ)
        = (qPochInfPS ℂ) ^ 2 *
            ((chan116DenomPS ζ)⁻¹ * chan116DenomPS ζ) := by ring
    _ = (qPochInfPS ℂ) ^ 2 := by
        rw [PowerSeries.inv_mul_cancel (chan116DenomPS ζ) hden_coeff_ne]
        ring

/-- A precise reduction of Chan Theorem 11.6: once the remaining
Rogers-Ramanujan product multiplication identity is proved, the reciprocal
identity follows from the JTP denominator collapse above. -/
theorem chan116_of_rhs_mul_section83
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (hRR :
      chan116RHS ζ * section83_rhs_pair14 ζ = (qPochInfPS ℂ) ^ 2) :
    chan116LHS ζ = chan116RHS ζ := by
  have hleft := chan116LHS_mul_section83_rhs_pair14 hζ
  have hunit : IsUnit (section83_rhs_pair14 ζ) := by
    rw [← chan116_jtp_denominator_collapse hζ]
    exact (isUnit_qPochInfPS ℂ).mul (isUnit_chan116DenomPS ζ)
  apply hunit.mul_left_inj.mp
  rw [hleft, hRR]

/-! ## Closing the remaining product bridge -/

private theorem expand_five_qPochInfPS_eq_qPochAPPS_complex :
    PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) = qPochAPPS ℂ 5 5 := by
  rw [qPochInfPS_eq_tprod ℂ]
  rw [(multipliable_one_sub_X_pow_succ ℂ).map_tprod
    (PowerSeries.expand 5 (by decide))
    (QseriesFormalization.Pending.ASDEtaProducts.continuous_expand ℂ 5 (by decide))]
  unfold qPochAPPS
  apply tprod_congr
  intro n
  calc
    PowerSeries.expand 5 (by decide) ((1 : ℂ⟦X⟧) - PowerSeries.X ^ (n + 1))
        = (1 : ℂ⟦X⟧) - PowerSeries.X ^ (5 * (n + 1)) := by
          rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
    _ = apFactorPS ℂ 5 5 n := by
          rw [apFactorPS]
          congr 1
          ring

private theorem constQFactorPS_fifth_product {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (n : ℕ) :
    constQFactorPS 1 n * constQFactorPS ζ n * constQFactorPS (ζ ^ 2) n *
        constQFactorPS (ζ ^ 3) n * constQFactorPS (ζ ^ 4) n =
      apFactorPS ℂ 5 5 n := by
  have hfin :
      (∏ j : Fin 5, constQFactorPS (ζ ^ (j : ℕ)) n) =
        (1 : ℂ⟦X⟧) - PowerSeries.X ^ (5 * (n + 1)) := by
    calc
      (∏ j : Fin 5, constQFactorPS (ζ ^ (j : ℕ)) n)
          = ∏ j : Fin 5,
              ((1 : ℂ⟦X⟧) - PowerSeries.C (ζ ^ (j : ℕ)) *
                PowerSeries.X ^ (n + 1)) := by rfl
      _ = (1 : ℂ⟦X⟧) - (PowerSeries.X ^ (n + 1)) ^ 5 := by
            exact prod_one_sub_primitive_fifth_powerSeries
              (R := ℂ) (μ := ζ) (PowerSeries.X ^ (n + 1)) hζ
      _ = (1 : ℂ⟦X⟧) - PowerSeries.X ^ (5 * (n + 1)) := by
            rw [← pow_mul]
            congr 1
            ring
  have horder :
      constQFactorPS 1 n * constQFactorPS ζ n * constQFactorPS (ζ ^ 2) n *
          constQFactorPS (ζ ^ 3) n * constQFactorPS (ζ ^ 4) n =
        ∏ j : Fin 5, constQFactorPS (ζ ^ (j : ℕ)) n := by
    norm_num [Fin.prod_univ_five]
  rw [horder, hfin]
  rw [apFactorPS]
  congr 1
  ring

private theorem constQPochInfPS_fifth_product {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    constQPochInfPS 1 * constQPochInfPS ζ * constQPochInfPS (ζ ^ 2) *
        constQPochInfPS (ζ ^ 3) * constQPochInfPS (ζ ^ 4) =
      PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) := by
  have hprod : HasProd
      (fun n : ℕ =>
        constQFactorPS 1 n * constQFactorPS ζ n * constQFactorPS (ζ ^ 2) n *
          constQFactorPS (ζ ^ 3) n * constQFactorPS (ζ ^ 4) n)
      (constQPochInfPS 1 * constQPochInfPS ζ * constQPochInfPS (ζ ^ 2) *
        constQPochInfPS (ζ ^ 3) * constQPochInfPS (ζ ^ 4)) := by
    exact
      ((((hasProd_constQFactorPS 1).mul (hasProd_constQFactorPS ζ)).mul
        (hasProd_constQFactorPS (ζ ^ 2))).mul
        (hasProd_constQFactorPS (ζ ^ 3))).mul
        (hasProd_constQFactorPS (ζ ^ 4))
  have hap : HasProd
      (fun n : ℕ => apFactorPS ℂ 5 5 n)
      (constQPochInfPS 1 * constQPochInfPS ζ * constQPochInfPS (ζ ^ 2) *
        constQPochInfPS (ζ ^ 3) * constQPochInfPS (ζ ^ 4)) := by
    convert hprod using 1
    funext n
    exact (constQFactorPS_fifth_product hζ n).symm
  have hap' : HasProd
      (fun n : ℕ => apFactorPS ℂ 5 5 n)
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)) := by
    rw [expand_five_qPochInfPS_eq_qPochAPPS_complex]
    exact hasProd_qPochAPPS ℂ 5 5 (by norm_num)
  exact hap.unique hap'

private theorem zeta_sq_inv_eq_pow_three {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (ζ ^ 2)⁻¹ = ζ ^ 3 := by
  apply inv_eq_of_mul_eq_one_right
  calc
    ζ ^ 2 * ζ ^ 3 = ζ ^ 5 := by ring
    _ = 1 := hζ.pow_eq_one

theorem section83_rhs_pair14_mul_pair23 {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    section83_rhs_pair14 ζ * section83_rhs_pair23 ζ =
      qPochInfPS ℂ * PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) := by
  have hprod := constQPochInfPS_fifth_product hζ
  rw [constQPochInfPS_one] at hprod
  rw [← section83JTPProductPS_eq_rhs_pair14 hζ,
    ← section83JTPProductPS_eq_rhs_pair23 hζ]
  unfold section83JTPProductPS
  rw [zeta_inv_eq_pow_four hζ, zeta_sq_inv_eq_pow_three hζ]
  calc
    (constQPochInfPS 1 * constQPochInfPS ζ * constQPochInfPS (ζ ^ 4)) *
        (constQPochInfPS 1 * constQPochInfPS (ζ ^ 2) * constQPochInfPS (ζ ^ 3))
        = qPochInfPS ℂ *
          (qPochInfPS ℂ * constQPochInfPS ζ * constQPochInfPS (ζ ^ 2) *
            constQPochInfPS (ζ ^ 3) * constQPochInfPS (ζ ^ 4)) := by
          rw [constQPochInfPS_one]
          ring
    _ = qPochInfPS ℂ * PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) := by
          rw [hprod]

theorem section83_quadratic_product {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (section83A ℂ)^2 - PowerSeries.X * section83A ℂ * section83B ℂ -
        PowerSeries.X^2 * (section83B ℂ)^2 =
      qPochInfPS ℂ * PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) := by
  have hpair := section83_rhs_pair14_mul_pair23 hζ
  have hsum : quinticPeriodAlpha ζ + quinticPeriodBeta ζ = (-1 : ℂ) :=
    quinticPeriod_sum (R := ℂ) hζ
  have hmul : quinticPeriodAlpha ζ * quinticPeriodBeta ζ = (-1 : ℂ) :=
    quinticPeriod_mul (R := ℂ) hζ
  unfold section83_rhs_pair14 section83_rhs_pair23 at hpair
  have hβa : PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.C (quinticPeriodAlpha ζ) =
      (-1 : ℂ⟦X⟧) := by
    rw [← map_mul, mul_comm (quinticPeriodBeta ζ) (quinticPeriodAlpha ζ), hmul]
    simp
  have hβα : PowerSeries.C (quinticPeriodBeta ζ) + PowerSeries.C (quinticPeriodAlpha ζ) =
      (-1 : ℂ⟦X⟧) := by
    rw [← map_add, add_comm (quinticPeriodBeta ζ) (quinticPeriodAlpha ζ), hsum]
    simp
  rw [← hpair]
  symm
  calc
    (section83A ℂ + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X * section83B ℂ) *
          (section83A ℂ + PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X * section83B ℂ)
        = (section83A ℂ)^2 +
          (PowerSeries.C (quinticPeriodBeta ζ) + PowerSeries.C (quinticPeriodAlpha ζ)) *
            PowerSeries.X * section83A ℂ * section83B ℂ +
          (PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.C (quinticPeriodAlpha ζ)) *
            PowerSeries.X^2 * (section83B ℂ)^2 := by
          ring
    _ = (section83A ℂ)^2 - PowerSeries.X * section83A ℂ * section83B ℂ -
          PowerSeries.X^2 * (section83B ℂ)^2 := by
          rw [hβα, hβa]
          ring

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

private theorem pentagonal014Series_mul_pentagonal023Series_eq_qPochInfPS_mul_expand_five_qPochInfPS_complex :
    pentagonal014SeriesPS ℂ * pentagonal023SeriesPS ℂ =
      qPochInfPS ℂ * PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) := by
  have hmap := congrArg (PowerSeries.map (algebraMap ℚ ℂ))
    pentagonal014Series_mul_pentagonal023Series_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat
  rw [map_mul, map_mul, map_pentagonal014SeriesPS_rat_complex,
    map_pentagonal023SeriesPS_rat_complex, map_qPochInfPS (algebraMap ℚ ℂ),
    PowerSeries.map_expand, map_qPochInfPS (algebraMap ℚ ℂ)] at hmap
  exact hmap

private theorem section83B_mul_section83A_eq_expand_five_mul_expand_twentyfive_qPochInfPS :
    section83B ℂ * section83A ℂ =
      PowerSeries.expand 5 (by decide) (qPochInfPS ℂ) *
        PowerSeries.expand 25 (by decide) (qPochInfPS ℂ) := by
  have h := congrArg (PowerSeries.expand 5 (by decide))
    pentagonal014Series_mul_pentagonal023Series_eq_qPochInfPS_mul_expand_five_qPochInfPS_complex
  rw [map_mul, map_mul] at h
  rw [← PowerSeries.expand_mul (p := 5) (hp := by decide) (q := 5) (hq := by decide)
    (qPochInfPS ℂ)] at h
  simpa [section83A, section83B, mul_comm, mul_left_comm, mul_assoc] using h

private theorem map_E5_rat_complex (r : ℕ) :
    PowerSeries.map (algebraMap ℚ ℂ) (E5 ℚ r) = E5 ℂ r := by
  ext n
  rw [PowerSeries.coeff_map]
  unfold E5
  rw [coeff_section5, coeff_section5]
  by_cases hn : n % 5 = r
  · rw [if_pos hn, if_pos hn]
    rw [← PowerSeries.coeff_map]
    rw [map_qPochInfPS (algebraMap ℚ ℂ)]
  · rw [if_neg hn, if_neg hn]
    simp

private theorem E5_zero_mul_two_eq_neg_one_sq_complex :
    E5 ℂ 0 * E5 ℂ 2 = -(E5 ℂ 1)^2 := by
  have hmap := congrArg (PowerSeries.map (algebraMap ℚ ℂ))
    E5_zero_mul_two_eq_neg_one_sq_rat
  rw [map_mul, map_neg, map_pow, map_E5_rat_complex 0, map_E5_rat_complex 1,
    map_E5_rat_complex 2] at hmap
  exact hmap

private theorem coeff_zero_apFactorPS_complex {r m n : ℕ} (hr : 0 < r) :
    (apFactorPS ℂ r m n).coeff 0 = 1 := by
  rw [apFactorPS]
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  simp [show ¬0 = r + m * n by omega]

private theorem coeff_zero_partial_apFactorPS_complex {r m : ℕ} (hr : 0 < r) (N : ℕ) :
    (∏ n ∈ Finset.range N, apFactorPS ℂ r m n).coeff 0 = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ]
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rw [ih, coeff_zero_apFactorPS_complex (r := r) (m := m) (n := N) hr]
      ring

private theorem coeff_zero_qPochAPPS_complex {r m : ℕ} (hr : 0 < r) (hm : 0 < m) :
    (qPochAPPS ℂ r m).coeff 0 = 1 := by
  have hprod := (hasProd_qPochAPPS ℂ r m hm).tendsto_prod_nat
  have hcoeff :
      Tendsto
        (fun N : ℕ => (∏ n ∈ Finset.range N, apFactorPS ℂ r m n).coeff 0)
        atTop (𝓝 ((qPochAPPS ℂ r m).coeff 0)) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℂ 0).tendsto _).comp hprod
  have hone :
      Tendsto
        (fun N : ℕ => (∏ n ∈ Finset.range N, apFactorPS ℂ r m n).coeff 0)
        atTop (𝓝 (1 : ℂ)) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    exact Filter.Eventually.of_forall fun N =>
      (coeff_zero_partial_apFactorPS_complex (r := r) (m := m) hr N).symm
  exact tendsto_nhds_unique hcoeff hone

private theorem coeff_zero_section83A_complex : (section83A ℂ).coeff 0 = 1 := by
  rw [section83A_eq_rrHDenAtQ5PS_mul_fMinusQ25PS]
  unfold rrHDenAtQ5PS fMinusQ25PS
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  rw [map_mul]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply (qPochAPPS ℂ 10 25),
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply (qPochAPPS ℂ 15 25),
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply
      (PowerSeries.expand 25 (by decide) (qPochInfPS ℂ))]
  rw [coeff_zero_qPochAPPS_complex (r := 10) (m := 25) (by norm_num) (by norm_num),
    coeff_zero_qPochAPPS_complex (r := 15) (m := 25) (by norm_num) (by norm_num)]
  rw [PowerSeries.coeff_expand]
  simp [coeff_zero_qPochInfPS]

private theorem coeff_zero_E5_zero_complex : (E5 ℂ 0).coeff 0 = 1 := by
  rw [E5, coeff_section5]
  simp [coeff_zero_qPochInfPS]

private theorem isUnit_E5_zero_mul_section83A_add_X_sq_expand25_mul_section83B :
    IsUnit (E5 ℂ 0 * section83A ℂ +
      PowerSeries.X^2 * PowerSeries.expand 25 (by decide) (qPochInfPS ℂ) * section83B ℂ) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [map_add]
  have hx : (PowerSeries.X^2 * PowerSeries.expand 25 (by decide) (qPochInfPS ℂ) *
      section83B ℂ).coeff 0 = 0 := by
    rw [show PowerSeries.X^2 * PowerSeries.expand 25 (by decide) (qPochInfPS ℂ) *
        section83B ℂ =
      PowerSeries.X^2 * (PowerSeries.expand 25 (by decide) (qPochInfPS ℂ) *
        section83B ℂ) by ring]
    rw [PowerSeries.coeff_X_pow_mul']
    simp
  rw [hx]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply (E5 ℂ 0),
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply (section83A ℂ)]
  rw [coeff_zero_E5_zero_complex, coeff_zero_section83A_complex]
  norm_num

theorem E5_zero_mul_section83B_eq_expand_twentyfive_mul_section83A
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    E5 ℂ 0 * section83B ℂ =
      PowerSeries.expand 25 (by decide) (qPochInfPS ℂ) * section83A ℂ := by
  let E0 : ℂ⟦X⟧ := E5 ℂ 0
  let E1 : ℂ⟦X⟧ := E5 ℂ 1
  let E2 : ℂ⟦X⟧ := E5 ℂ 2
  let A : ℂ⟦X⟧ := section83A ℂ
  let B : ℂ⟦X⟧ := section83B ℂ
  let E : ℂ⟦X⟧ := qPochInfPS ℂ
  let F : ℂ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)
  let W : ℂ⟦X⟧ := PowerSeries.expand 25 (by decide) (qPochInfPS ℂ)
  have hAB : B * A = F * W := by
    simpa [A, B, F, W] using section83B_mul_section83A_eq_expand_five_mul_expand_twentyfive_qPochInfPS
  have hAB' : A * B = F * W := by
    simpa [mul_comm] using hAB
  have hquad : A^2 - PowerSeries.X * A * B - PowerSeries.X^2 * B^2 = E * F := by
    simpa [A, B, E, F] using section83_quadratic_product hζ
  have hE1 : E1 = -PowerSeries.X * W := by
    simpa [E1, W] using E5_one_eq_neg_X_mul_expand_twentyfive_qPochInfPS ℂ
  have hdissect : E = E0 - PowerSeries.X * W + E2 := by
    calc
      E = E0 + E1 + E2 := by
        simpa [E, E0, E1, E2] using qPochInfPS_five_dissection ℂ
      _ = E0 - PowerSeries.X * W + E2 := by rw [hE1]; ring
  have h02 : E0 * E2 = -PowerSeries.X^2 * W^2 := by
    calc
      E0 * E2 = -E1^2 := by
        simpa [E0, E1, E2] using E5_zero_mul_two_eq_neg_one_sq_complex
      _ = -PowerSeries.X^2 * W^2 := by rw [hE1]; ring
  have hquad0 : A^2 - PowerSeries.X^2 * B^2 = (E0 + E2) * F := by
    calc
      A^2 - PowerSeries.X^2 * B^2 =
          (A^2 - PowerSeries.X * A * B - PowerSeries.X^2 * B^2) +
            PowerSeries.X * (A * B) := by ring
      _ = E * F + PowerSeries.X * (F * W) := by rw [hquad, hAB']
      _ = (E0 + E2) * F := by rw [hdissect]; ring
  let Delta : ℂ⟦X⟧ := E0 * B - W * A
  let Xi : ℂ⟦X⟧ := E2 * A + PowerSeries.X^2 * W * B
  have hlin : A * Delta + B * Xi = 0 := by
    calc
      A * Delta + B * Xi = (E0 + E2) * (A * B) -
          W * (A^2 - PowerSeries.X^2 * B^2) := by
        simp [Delta, Xi]
        ring
      _ = (E0 + E2) * (F * W) -
          W * (A^2 - PowerSeries.X^2 * B^2) := by rw [hAB']
      _ = W * ((E0 + E2) * F - (A^2 - PowerSeries.X^2 * B^2)) := by ring
      _ = 0 := by rw [hquad0]; ring
  have hE0Xi : E0 * Xi = PowerSeries.X^2 * W * Delta := by
    calc
      E0 * Xi = E0 * E2 * A + PowerSeries.X^2 * W * E0 * B := by
        simp [Xi]
        ring
      _ = (-PowerSeries.X^2 * W^2) * A + PowerSeries.X^2 * W * E0 * B := by
        rw [h02]
      _ = PowerSeries.X^2 * W * Delta := by
        simp [Delta]
        ring
  have hDelta_zero_mul : (E0 * A + PowerSeries.X^2 * W * B) * Delta = 0 := by
    calc
      (E0 * A + PowerSeries.X^2 * W * B) * Delta =
          E0 * (A * Delta) + B * (PowerSeries.X^2 * W * Delta) := by ring
      _ = E0 * (A * Delta) + B * (E0 * Xi) := by rw [← hE0Xi]
      _ = E0 * (A * Delta + B * Xi) := by ring
      _ = 0 := by rw [hlin]; ring
  have hunit : IsUnit (E0 * A + PowerSeries.X^2 * W * B) := by
    simpa [E0, A, B, W] using isUnit_E5_zero_mul_section83A_add_X_sq_expand25_mul_section83B
  have hDelta : Delta = 0 := by
    apply hunit.mul_left_inj.mp
    simpa [mul_comm] using hDelta_zero_mul
  change E0 * B = W * A
  simpa [Delta] using sub_eq_zero.mp hDelta

private theorem map_pentagonalProduct014AtFiveRat_complex :
    PowerSeries.map (algebraMap ℚ ℂ) pentagonalProduct014AtFiveRat = section83B ℂ := by
  rw [pentagonalProduct014AtFiveRat, PowerSeries.map_expand]
  rw [pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat,
    map_pentagonal014SeriesPS_rat_complex]
  rfl

private theorem map_pentagonalProduct023AtFiveRat_complex :
    PowerSeries.map (algebraMap ℚ ℂ) pentagonalProduct023AtFiveRat = section83A ℂ := by
  rw [pentagonalProduct023AtFiveRat, PowerSeries.map_expand]
  rw [pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat,
    map_pentagonal023SeriesPS_rat_complex]
  rfl

theorem E5_zero_product_bridge_expanded_rat :
    E5 ℚ 0 * pentagonalProduct014AtFiveRat =
      PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
        pentagonalProduct023AtFiveRat := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)
  have hζ : IsPrimitiveRoot ζ 5 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp 5 (by norm_num : (5 : ℕ) ≠ 0)
  apply PowerSeries.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  rw [map_mul, map_mul, map_E5_rat_complex 0, map_pentagonalProduct014AtFiveRat_complex,
    PowerSeries.map_expand, map_qPochInfPS (algebraMap ℚ ℂ),
    map_pentagonalProduct023AtFiveRat_complex]
  exact E5_zero_mul_section83B_eq_expand_twentyfive_mul_section83A hζ

end Ch14Thm116
end PartIII

namespace Pending
namespace Ch16MBIProof

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal

private theorem expand_five_injective_rat_local {φ ψ : ℚ⟦X⟧}
    (h : PowerSeries.expand 5 (by decide) φ = PowerSeries.expand 5 (by decide) ψ) :
    φ = ψ := by
  ext n
  have hcoeff := congrArg (fun θ : ℚ⟦X⟧ => θ.coeff (5 * n)) h
  change (PowerSeries.expand 5 (by decide) φ).coeff (5 * n) =
    (PowerSeries.expand 5 (by decide) ψ).coeff (5 * n) at hcoeff
  rw [PowerSeries.coeff_expand, PowerSeries.coeff_expand] at hcoeff
  have hdvd : 5 ∣ 5 * n := dvd_mul_right 5 n
  rw [if_pos hdvd, if_pos hdvd] at hcoeff
  simpa [Nat.mul_div_right n (by decide : 0 < 5)] using hcoeff

theorem compressed_E5_zero_bridge :
    compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonalProduct014PS ℚ =
      PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) * pentagonalProduct023PS ℚ := by
  apply expand_five_injective_rat_local
  calc
    PowerSeries.expand 5 (by decide)
        (compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonalProduct014PS ℚ)
        = E5 ℚ 0 * pentagonalProduct014AtFiveRat := by
          rw [map_mul, E5_zero_eq_expand_compressedSection5_zero_qPochInfPS_rat,
            pentagonalProduct014AtFiveRat]
    _ = PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) *
          pentagonalProduct023AtFiveRat :=
          QseriesFormalization.PartIII.Ch14Thm116.E5_zero_product_bridge_expanded_rat
    _ = PowerSeries.expand 5 (by decide)
        (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) * pentagonalProduct023PS ℚ) := by
          rw [map_mul, pentagonalProduct023AtFiveRat]
          rw [← PowerSeries.expand_mul (p := 5) (hp := by decide) (q := 5)
            (hq := by decide) (qPochInfPS ℚ)]

end Ch16MBIProof
end Pending

namespace PartIII
namespace Ch14Thm116

open PowerSeries
open Filter
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.RamanujanQuinticJTP
open QseriesFormalization.Pending.Ch16MBIProof

private theorem coeff_zero_rrGDenAtQ5PS : rrGDenAtQ5PS.coeff 0 = 1 := by
  unfold rrGDenAtQ5PS
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply (qPochAPPS ℂ 5 25),
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply (qPochAPPS ℂ 20 25)]
  rw [coeff_zero_qPochAPPS_complex (r := 5) (m := 25) (by norm_num) (by norm_num),
    coeff_zero_qPochAPPS_complex (r := 20) (m := 25) (by norm_num) (by norm_num)]
  ring

private theorem coeff_zero_rrHDenAtQ5PS : rrHDenAtQ5PS.coeff 0 = 1 := by
  unfold rrHDenAtQ5PS
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply (qPochAPPS ℂ 10 25),
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply (qPochAPPS ℂ 15 25)]
  rw [coeff_zero_qPochAPPS_complex (r := 10) (m := 25) (by norm_num) (by norm_num),
    coeff_zero_qPochAPPS_complex (r := 15) (m := 25) (by norm_num) (by norm_num)]
  ring

private theorem coeff_zero_fMinusQ25PS : fMinusQ25PS.coeff 0 = 1 := by
  unfold fMinusQ25PS
  rw [PowerSeries.coeff_expand]
  simp [coeff_zero_qPochInfPS]

private theorem constantCoeff_ne_zero_of_coeff_zero_one {φ : ℂ⟦X⟧}
    (h : φ.coeff 0 = 1) :
    PowerSeries.constantCoeff φ ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  norm_num

private theorem ps_inv_inv_of_unit (φ : ℂ⟦X⟧)
    (h : PowerSeries.constantCoeff φ ≠ 0) :
    (φ⁻¹)⁻¹ = φ := by
  have hinv : PowerSeries.constantCoeff φ⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]
    exact inv_ne_zero h
  rw [PowerSeries.inv_eq_iff_mul_eq_one hinv]
  exact PowerSeries.mul_inv_cancel φ h

private theorem chan116A_mul_den_expanded
    (hU : PowerSeries.constantCoeff rrGDenAtQ5PS ≠ 0)
    (hV : PowerSeries.constantCoeff rrHDenAtQ5PS ≠ 0) :
    chan116A * (rrGDenAtQ5PS * rrGDenAtQ5PS *
        (rrHDenAtQ5PS * rrHDenAtQ5PS)) =
      fMinusQ25PS * (rrHDenAtQ5PS * rrHDenAtQ5PS * rrHDenAtQ5PS) := by
  unfold chan116A rrGAtQ5PS rrHAtQ5PS
  rw [ps_inv_inv_of_unit rrHDenAtQ5PS hV]
  calc
    (fMinusQ25PS * (rrGDenAtQ5PS⁻¹)^2 * rrHDenAtQ5PS) *
        (rrGDenAtQ5PS * rrGDenAtQ5PS * (rrHDenAtQ5PS * rrHDenAtQ5PS))
        = fMinusQ25PS * ((rrGDenAtQ5PS⁻¹ * rrGDenAtQ5PS) *
            (rrGDenAtQ5PS⁻¹ * rrGDenAtQ5PS)) *
            (rrHDenAtQ5PS * rrHDenAtQ5PS * rrHDenAtQ5PS) := by ring
    _ = fMinusQ25PS * (rrHDenAtQ5PS * rrHDenAtQ5PS * rrHDenAtQ5PS) := by
        rw [PowerSeries.inv_mul_cancel rrGDenAtQ5PS hU]
        ring

private theorem X_chan116B_mul_den_expanded
    (hU : PowerSeries.constantCoeff rrGDenAtQ5PS ≠ 0) :
    (PowerSeries.X * chan116B) * (rrGDenAtQ5PS * rrGDenAtQ5PS *
        (rrHDenAtQ5PS * rrHDenAtQ5PS)) =
      PowerSeries.X * fMinusQ25PS * rrGDenAtQ5PS *
        (rrHDenAtQ5PS * rrHDenAtQ5PS) := by
  unfold chan116B rrGAtQ5PS
  calc
    (PowerSeries.X * (fMinusQ25PS * rrGDenAtQ5PS⁻¹)) *
        (rrGDenAtQ5PS * rrGDenAtQ5PS * (rrHDenAtQ5PS * rrHDenAtQ5PS))
        = PowerSeries.X * fMinusQ25PS * (rrGDenAtQ5PS⁻¹ * rrGDenAtQ5PS) *
          rrGDenAtQ5PS * (rrHDenAtQ5PS * rrHDenAtQ5PS) := by ring
    _ = PowerSeries.X * fMinusQ25PS * rrGDenAtQ5PS *
          (rrHDenAtQ5PS * rrHDenAtQ5PS) := by
        rw [PowerSeries.inv_mul_cancel rrGDenAtQ5PS hU]
        ring

private theorem X_sq_chan116C_mul_den_expanded
    (hV : PowerSeries.constantCoeff rrHDenAtQ5PS ≠ 0) :
    (PowerSeries.X^2 * chan116C) * (rrGDenAtQ5PS * rrGDenAtQ5PS *
        (rrHDenAtQ5PS * rrHDenAtQ5PS)) =
      PowerSeries.X^2 * fMinusQ25PS * (rrGDenAtQ5PS * rrGDenAtQ5PS) *
        rrHDenAtQ5PS := by
  unfold chan116C rrHAtQ5PS
  calc
    (PowerSeries.X^2 * (fMinusQ25PS * rrHDenAtQ5PS⁻¹)) *
        (rrGDenAtQ5PS * rrGDenAtQ5PS * (rrHDenAtQ5PS * rrHDenAtQ5PS))
        = PowerSeries.X^2 * fMinusQ25PS * (rrGDenAtQ5PS * rrGDenAtQ5PS) *
          (rrHDenAtQ5PS⁻¹ * rrHDenAtQ5PS) * rrHDenAtQ5PS := by ring
    _ = PowerSeries.X^2 * fMinusQ25PS * (rrGDenAtQ5PS * rrGDenAtQ5PS) *
          rrHDenAtQ5PS := by
        rw [PowerSeries.inv_mul_cancel rrHDenAtQ5PS hV]
        ring

private theorem X_cu_chan116D_mul_den_expanded
    (hU : PowerSeries.constantCoeff rrGDenAtQ5PS ≠ 0)
    (hV : PowerSeries.constantCoeff rrHDenAtQ5PS ≠ 0) :
    (PowerSeries.X^3 * chan116D) * (rrGDenAtQ5PS * rrGDenAtQ5PS *
        (rrHDenAtQ5PS * rrHDenAtQ5PS)) =
      PowerSeries.X^3 * fMinusQ25PS *
        (rrGDenAtQ5PS * rrGDenAtQ5PS * rrGDenAtQ5PS) := by
  unfold chan116D rrGAtQ5PS rrHAtQ5PS
  rw [ps_inv_inv_of_unit rrGDenAtQ5PS hU]
  calc
    (PowerSeries.X^3 * (fMinusQ25PS * (rrHDenAtQ5PS⁻¹)^2 *
        rrGDenAtQ5PS)) *
        (rrGDenAtQ5PS * rrGDenAtQ5PS * (rrHDenAtQ5PS * rrHDenAtQ5PS))
        = PowerSeries.X^3 * fMinusQ25PS *
          (rrGDenAtQ5PS * rrGDenAtQ5PS * rrGDenAtQ5PS) *
          ((rrHDenAtQ5PS⁻¹ * rrHDenAtQ5PS) *
            (rrHDenAtQ5PS⁻¹ * rrHDenAtQ5PS)) := by ring
    _ = PowerSeries.X^3 * fMinusQ25PS *
          (rrGDenAtQ5PS * rrGDenAtQ5PS * rrGDenAtQ5PS) := by
        rw [PowerSeries.inv_mul_cancel rrHDenAtQ5PS hV]
        ring

private theorem chan116RHS_period_mul_den_expanded {ζ : ℂ} :
    chan116RHS_period ζ * (rrGDenAtQ5PS * rrGDenAtQ5PS *
        (rrHDenAtQ5PS * rrHDenAtQ5PS)) =
      fMinusQ25PS *
        (rrHDenAtQ5PS * rrHDenAtQ5PS * rrHDenAtQ5PS
          - PowerSeries.C ((quinticPeriodAlpha ζ)^2) * PowerSeries.X *
            rrGDenAtQ5PS * (rrHDenAtQ5PS * rrHDenAtQ5PS)
          + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X^2 *
            (rrGDenAtQ5PS * rrGDenAtQ5PS) * rrHDenAtQ5PS
          - PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X^3 *
            (rrGDenAtQ5PS * rrGDenAtQ5PS * rrGDenAtQ5PS)) := by
  have hU : PowerSeries.constantCoeff rrGDenAtQ5PS ≠ 0 :=
    constantCoeff_ne_zero_of_coeff_zero_one coeff_zero_rrGDenAtQ5PS
  have hV : PowerSeries.constantCoeff rrHDenAtQ5PS ≠ 0 :=
    constantCoeff_ne_zero_of_coeff_zero_one coeff_zero_rrHDenAtQ5PS
  unfold chan116RHS_period
  calc
    (chan116A
        - PowerSeries.C ((quinticPeriodAlpha ζ) ^ 2) * PowerSeries.X * chan116B
        + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X ^ 2 * chan116C
        - PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X ^ 3 * chan116D) *
        (rrGDenAtQ5PS * rrGDenAtQ5PS * (rrHDenAtQ5PS * rrHDenAtQ5PS))
        =
      chan116A * (rrGDenAtQ5PS * rrGDenAtQ5PS *
          (rrHDenAtQ5PS * rrHDenAtQ5PS))
        - PowerSeries.C ((quinticPeriodAlpha ζ) ^ 2) *
          ((PowerSeries.X * chan116B) *
            (rrGDenAtQ5PS * rrGDenAtQ5PS * (rrHDenAtQ5PS * rrHDenAtQ5PS)))
        + PowerSeries.C (quinticPeriodBeta ζ) *
          ((PowerSeries.X^2 * chan116C) *
            (rrGDenAtQ5PS * rrGDenAtQ5PS * (rrHDenAtQ5PS * rrHDenAtQ5PS)))
        - PowerSeries.C (quinticPeriodAlpha ζ) *
          ((PowerSeries.X^3 * chan116D) *
            (rrGDenAtQ5PS * rrGDenAtQ5PS * (rrHDenAtQ5PS * rrHDenAtQ5PS))) := by
          ring
    _ = fMinusQ25PS *
        (rrHDenAtQ5PS * rrHDenAtQ5PS * rrHDenAtQ5PS
          - PowerSeries.C ((quinticPeriodAlpha ζ)^2) * PowerSeries.X *
            rrGDenAtQ5PS * (rrHDenAtQ5PS * rrHDenAtQ5PS)
          + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X^2 *
            (rrGDenAtQ5PS * rrGDenAtQ5PS) * rrHDenAtQ5PS
          - PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X^3 *
            (rrGDenAtQ5PS * rrGDenAtQ5PS * rrGDenAtQ5PS)) := by
          rw [chan116A_mul_den_expanded hU hV, X_chan116B_mul_den_expanded hU,
            X_sq_chan116C_mul_den_expanded hV, X_cu_chan116D_mul_den_expanded hU hV]
          ring

private theorem chan116_period_polynomial_identity {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) (U V : ℂ⟦X⟧) :
    (V + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X * U) *
        (V * V * V
          - PowerSeries.C ((quinticPeriodAlpha ζ)^2) * PowerSeries.X * U * (V * V)
          + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X^2 * (U * U) * V
          - PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X^3 * (U * U * U)) =
      (V * V - PowerSeries.X * U * V - PowerSeries.X^2 * (U * U))^2 := by
  have hsum : quinticPeriodAlpha ζ + quinticPeriodBeta ζ = (-1 : ℂ) :=
    quinticPeriod_sum (R := ℂ) hζ
  have hα2 : (quinticPeriodAlpha ζ)^2 = -quinticPeriodAlpha ζ + 1 :=
    quinticPeriodAlpha_sq (R := ℂ) hζ
  have hα2C : PowerSeries.C ((quinticPeriodAlpha ζ)^2) =
      (-PowerSeries.C (quinticPeriodAlpha ζ) + 1 : ℂ⟦X⟧) := by
    rw [hα2]
    simp
  have hβ : quinticPeriodBeta ζ = -1 - quinticPeriodAlpha ζ := by
    linear_combination hsum
  have hβC : PowerSeries.C (quinticPeriodBeta ζ) =
      (-1 - PowerSeries.C (quinticPeriodAlpha ζ) : ℂ⟦X⟧) := by
    rw [hβ]
    simp
  have hαC_sq : (PowerSeries.C (quinticPeriodAlpha ζ) : ℂ⟦X⟧)^2 =
      -PowerSeries.C (quinticPeriodAlpha ζ) + 1 := by
    rw [← map_pow, hα2]
    simp
  rw [hα2C, hβC]
  ring_nf
  rw [hαC_sq]
  ring

private theorem E5_two_mul_section83A_eq_neg_X_sq_expand_twentyfive_mul_section83B
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    E5 ℂ 2 * section83A ℂ =
      -PowerSeries.X^2 * PowerSeries.expand 25 (by decide) (qPochInfPS ℂ) *
        section83B ℂ := by
  let E0 : ℂ⟦X⟧ := E5 ℂ 0
  let E1 : ℂ⟦X⟧ := E5 ℂ 1
  let E2 : ℂ⟦X⟧ := E5 ℂ 2
  let A : ℂ⟦X⟧ := section83A ℂ
  let B : ℂ⟦X⟧ := section83B ℂ
  let W : ℂ⟦X⟧ := PowerSeries.expand 25 (by decide) (qPochInfPS ℂ)
  have hE0 : E0 * B = W * A := by
    simpa [E0, A, B, W] using
      E5_zero_mul_section83B_eq_expand_twentyfive_mul_section83A hζ
  have hE1 : E1 = -PowerSeries.X * W := by
    simpa [E1, W] using E5_one_eq_neg_X_mul_expand_twentyfive_qPochInfPS ℂ
  have h02 : E0 * E2 = -PowerSeries.X^2 * W^2 := by
    calc
      E0 * E2 = -E1^2 := by
        simpa [E0, E1, E2] using E5_zero_mul_two_eq_neg_one_sq_complex
      _ = -PowerSeries.X^2 * W^2 := by rw [hE1]; ring
  have hW_unit : IsUnit W := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [PowerSeries.coeff_expand]
    simp [coeff_zero_qPochInfPS]
  have hmul :
      (E2 * A) * W = (-PowerSeries.X^2 * W * B) * W := by
    calc
      (E2 * A) * W = (W * A) * E2 := by ring
      _ = (E0 * B) * E2 := by rw [← hE0]
      _ = (E0 * E2) * B := by ring
      _ = (-PowerSeries.X^2 * W^2) * B := by rw [h02]
      _ = (-PowerSeries.X^2 * W * B) * W := by ring
  have hmul_left : W * (E2 * A) = W * (-PowerSeries.X^2 * W * B) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  change E2 * A = -PowerSeries.X^2 * W * B
  exact hW_unit.mul_right_inj.mp hmul_left

private theorem E_mul_rr_den_product_eq {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    qPochInfPS ℂ * rrGDenAtQ5PS * rrHDenAtQ5PS =
      fMinusQ25PS *
        (rrHDenAtQ5PS * rrHDenAtQ5PS
          - PowerSeries.X * rrGDenAtQ5PS * rrHDenAtQ5PS
          - PowerSeries.X^2 * (rrGDenAtQ5PS * rrGDenAtQ5PS)) := by
  let E0 : ℂ⟦X⟧ := E5 ℂ 0
  let E1 : ℂ⟦X⟧ := E5 ℂ 1
  let E2 : ℂ⟦X⟧ := E5 ℂ 2
  let U : ℂ⟦X⟧ := rrGDenAtQ5PS
  let V : ℂ⟦X⟧ := rrHDenAtQ5PS
  let W : ℂ⟦X⟧ := fMinusQ25PS
  have hWexp : W = PowerSeries.expand 25 (by decide) (qPochInfPS ℂ) := rfl
  have hA : section83A ℂ = V * W := by
    simpa [V, W] using section83A_eq_rrHDenAtQ5PS_mul_fMinusQ25PS
  have hB : section83B ℂ = U * W := by
    simpa [U, W] using section83B_eq_rrGDenAtQ5PS_mul_fMinusQ25PS
  have hW_unit : IsUnit W := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_fMinusQ25PS]
    norm_num
  have hE0raw : E0 * (U * W) =
      (PowerSeries.expand 25 (by decide) (qPochInfPS ℂ)) * (V * W) := by
    simpa [E0, U, V, W, hA, hB] using
      E5_zero_mul_section83B_eq_expand_twentyfive_mul_section83A hζ
  have hE0U : E0 * U = V * W := by
    have hmul : W * (E0 * U) = W * (V * W) := by
      simpa [hWexp, mul_comm, mul_left_comm, mul_assoc] using hE0raw
    exact hW_unit.mul_right_inj.mp hmul
  have hE2raw : E2 * (V * W) =
      -PowerSeries.X^2 * PowerSeries.expand 25 (by decide) (qPochInfPS ℂ) * (U * W) := by
    simpa [E2, U, V, W, hA, hB] using
      E5_two_mul_section83A_eq_neg_X_sq_expand_twentyfive_mul_section83B hζ
  have hE2V : E2 * V = -PowerSeries.X^2 * W * U := by
    have hmul : W * (E2 * V) = W * (-PowerSeries.X^2 * W * U) := by
      simpa [hWexp, mul_comm, mul_left_comm, mul_assoc] using hE2raw
    exact hW_unit.mul_right_inj.mp hmul
  have hE1 : E1 = -PowerSeries.X * W := by
    simpa [E1, W] using E5_one_eq_neg_X_mul_expand_twentyfive_qPochInfPS ℂ
  have hdissect : qPochInfPS ℂ = E0 - PowerSeries.X * W + E2 := by
    calc
      qPochInfPS ℂ = E0 + E1 + E2 := by
        simpa [E0, E1, E2] using qPochInfPS_five_dissection ℂ
      _ = E0 - PowerSeries.X * W + E2 := by rw [hE1]; ring
  calc
    qPochInfPS ℂ * U * V =
        (E0 - PowerSeries.X * W + E2) * U * V := by rw [hdissect]
    _ = (E0 * U) * V - PowerSeries.X * W * U * V + (E2 * V) * U := by
        ring
    _ = (V * W) * V - PowerSeries.X * W * U * V +
          (-PowerSeries.X^2 * W * U) * U := by
        rw [hE0U, hE2V]
    _ = W * (V * V - PowerSeries.X * U * V - PowerSeries.X^2 * (U * U)) := by
        ring

theorem chan116RHS_period_mul_section83_rhs_pair14
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    chan116RHS_period ζ * section83_rhs_pair14 ζ = (qPochInfPS ℂ)^2 := by
  let U : ℂ⟦X⟧ := rrGDenAtQ5PS
  let V : ℂ⟦X⟧ := rrHDenAtQ5PS
  let W : ℂ⟦X⟧ := fMinusQ25PS
  let D : ℂ⟦X⟧ := U * U * (V * V)
  let Q : ℂ⟦X⟧ := V * V - PowerSeries.X * U * V - PowerSeries.X^2 * (U * U)
  have hpair : section83_rhs_pair14 ζ = W * (V + PowerSeries.C (quinticPeriodBeta ζ) *
      PowerSeries.X * U) := by
    simpa [U, V, W] using section83_rhs_pair14_eq_fMinusQ25PS_mul (ζ := ζ)
  have hRden : chan116RHS_period ζ * D =
      W *
        (V * V * V
          - PowerSeries.C ((quinticPeriodAlpha ζ)^2) * PowerSeries.X * U * (V * V)
          + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X^2 * (U * U) * V
          - PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X^3 * (U * U * U)) := by
    simpa [U, V, W, D, mul_comm, mul_left_comm, mul_assoc] using
      chan116RHS_period_mul_den_expanded (ζ := ζ)
  have hpoly := chan116_period_polynomial_identity hζ U V
  have hEUV := E_mul_rr_den_product_eq hζ
  have hDunit : IsUnit D := by
    have hU : IsUnit U := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simpa [U] using
        constantCoeff_ne_zero_of_coeff_zero_one coeff_zero_rrGDenAtQ5PS
    have hV : IsUnit V := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simpa [V] using
        constantCoeff_ne_zero_of_coeff_zero_one coeff_zero_rrHDenAtQ5PS
    exact (hU.mul hU).mul (hV.mul hV)
  have hmulD :
      (chan116RHS_period ζ * section83_rhs_pair14 ζ) * D =
        ((qPochInfPS ℂ)^2) * D := by
    calc
      (chan116RHS_period ζ * section83_rhs_pair14 ζ) * D =
          (chan116RHS_period ζ * D) * section83_rhs_pair14 ζ := by ring
      _ = (W *
        (V * V * V
          - PowerSeries.C ((quinticPeriodAlpha ζ)^2) * PowerSeries.X * U * (V * V)
          + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X^2 * (U * U) * V
          - PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X^3 * (U * U * U))) *
            (W * (V + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X * U)) := by
          rw [hRden, hpair]
      _ = W^2 * ((V + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X * U) *
            (V * V * V
              - PowerSeries.C ((quinticPeriodAlpha ζ)^2) * PowerSeries.X * U * (V * V)
              + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X^2 * (U * U) * V
              - PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X^3 * (U * U * U))) := by
          ring
      _ = W^2 * Q^2 := by
          rw [hpoly]
      _ = (qPochInfPS ℂ * U * V)^2 := by
          rw [hEUV]
          simp [U, V, W, Q]
          ring
      _ = ((qPochInfPS ℂ)^2) * D := by
          simp [D, U, V]
          ring
  apply hDunit.mul_left_inj.mp
  simpa [D, mul_comm, mul_left_comm, mul_assoc] using hmulD

theorem chan116RHS_mul_section83_rhs_pair14
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    chan116RHS ζ * section83_rhs_pair14 ζ = (qPochInfPS ℂ)^2 := by
  rw [chan116RHS_eq_period hζ]
  exact chan116RHS_period_mul_section83_rhs_pair14 hζ

/-- Formal power-series statement of Chan's Theorem 11.6 at a primitive fifth root. -/
theorem chan116_theorem_11_6 {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    chan116LHS ζ = chan116RHS ζ := by
  exact chan116_of_rhs_mul_section83 hζ (chan116RHS_mul_section83_rhs_pair14 hζ)

end Ch14Thm116
end PartIII
end QseriesFormalization
