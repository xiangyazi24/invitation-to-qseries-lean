import QseriesFormalization.Pending.Chapter15_FormalDeriv
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal
import QseriesFormalization.Pending.Chapter16_MBI_Proof
import QseriesFormalization.Pending.Chapter13_RRCF_RForm
import QseriesFormalization.Pending.Chapter10_TenthOrder
import QseriesFormalization.Chapter19
import QseriesFormalization.Pending.JacobiCubeAnalyticToFormal

/-!
# Chapter 15 — independent Wronskian coefficient reduction

This file deliberately avoids importing `Chapter15_R_ODE` and any theorem
depending on `chan_theorem_11_7`.  The remaining open mathematical point is the
all-degree finite double-sum identity between the pentagonal Wronskian
coefficients and the Jacobi-cube Cauchy-square coefficients.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch15WronskianIndependent

open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch15FormalDeriv
open QseriesFormalization.Pending.Ch16MBIProof
open QseriesFormalization.Pending.Ch13RRCF
open QseriesFormalization.Pending.Ch10TenthOrder
open QseriesFormalization.Pending.JacobiCubeAnalyticToFormal
open QseriesFormalization.Pending.JTPFormalPSPentagonal

/-! ## Quintuple-product logarithmic-derivative route scaffolding -/

/-- Chapter-15 shorthand for the pentagonal `0,1,4` product/series. -/
noncomputable abbrev P014 : ℚ⟦X⟧ :=
  pentagonal014SeriesPS ℚ

/-- Chapter-15 shorthand for the pentagonal `0,2,3` product/series. -/
noncomputable abbrev P023 : ℚ⟦X⟧ :=
  pentagonal023SeriesPS ℚ

/-- Product-side shorthand for `(q,q^4,q^5;q^5)_∞`. -/
noncomputable abbrev P014_product : ℚ⟦X⟧ :=
  pentagonalProduct014PS ℚ

/-- Product-side shorthand for `(q^2,q^3,q^5;q^5)_∞`. -/
noncomputable abbrev P023_product : ℚ⟦X⟧ :=
  pentagonalProduct023PS ℚ

/-- Chapter-15 shorthand for `(X^5; X^5)_∞ = expand 5 (X; X)_∞`. -/
noncomputable abbrev expandFiveQpochRat : ℚ⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)

/-- The formal logarithmic theta derivative `Theta(f) / f`. -/
noncomputable abbrev thetaLog (f : ℚ⟦X⟧) : ℚ⟦X⟧ :=
  thetaDlog f

/-- The logarithmic factor predicted by the quintuple-product route. -/
noncomputable abbrev quintupleLogFactor : ℚ⟦X⟧ :=
  (1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * (thetaLog P014 - thetaLog P023)

/-- Chan's residue-class Lambert side, written through AP divisor-sigma
series and without importing `Chapter15_R_ODE`. -/
noncomputable abbrev apSigmaLambertFactor : ℚ⟦X⟧ :=
  1 + (5 : ℚ⟦X⟧) *
    ((apDivisorSigmaPS ℚ 2 5 + apDivisorSigmaPS ℚ 3 5) -
      (apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 4 5))

/-- The four residue classes not divisible by `5` in Euler's product. -/
noncomputable abbrev qPochNonFiveRat : ℚ⟦X⟧ :=
  qPochAPPS ℚ 1 5 * qPochAPPS ℚ 2 5 *
    qPochAPPS ℚ 3 5 * qPochAPPS ℚ 4 5

/-- The AP divisor-sigma series over the four nonzero residue classes mod `5`. -/
noncomputable abbrev apDivisorSigmaNonFive : ℚ⟦X⟧ :=
  apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 2 5 +
    apDivisorSigmaPS ℚ 3 5 + apDivisorSigmaPS ℚ 4 5

/-- Product-side form of `η(q)^5/η(q^5)`: after cancelling one
`(X^5;X^5)_∞` factor it is `(X;X)_∞^4` times the product over
exponents not divisible by `5`. -/
noncomputable abbrev etaQuotientProductSide : ℚ⟦X⟧ :=
  (qPochInfPS ℚ) ^ 4 * qPochNonFiveRat

/-- Fully split AP-product form of `η(q)^5/η(q^5)`.  This is
`∏_{5∤n}(1-X^n)^5 * ∏_{5|n}(1-X^n)^4`. -/
noncomputable abbrev etaQuotientProductSplit : ℚ⟦X⟧ :=
  (qPochAPPS ℚ 1 5) ^ 5 * (qPochAPPS ℚ 2 5) ^ 5 *
    (qPochAPPS ℚ 3 5) ^ 5 * (qPochAPPS ℚ 4 5) ^ 5 *
      (qPochAPPS ℚ 5 5) ^ 4

/-- The logarithmic theta driver obtained directly from
`η(q)^5/η(q^5) = (X;X)_∞^4 * ∏_{5∤n}(1-X^n)`. -/
noncomputable abbrev etaQuotientThetaDriver : ℚ⟦X⟧ :=
  -(5 : ℚ⟦X⟧) * apDivisorSigmaNonFive -
    (4 : ℚ⟦X⟧) * apDivisorSigmaPS ℚ 5 5

/-- The product-side and bilateral-series versions of `P014` agree over `ℚ`. -/
theorem P014_product_eq_P014 :
    P014_product = P014 := by
  simp [P014_product, P014, pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat]

/-- The product-side and bilateral-series versions of `P023` agree over `ℚ`. -/
theorem P023_product_eq_P023 :
    P023_product = P023 := by
  simp [P023_product, P023, pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat]

/-- The indexing equivalence splitting `ℕ` into the five residue classes. -/
private def finFiveSigmaNatEquivNatCh15 : (Sigma fun _ : Fin 5 => ℕ) ≃ ℕ where
  toFun p := 5 * p.2 + p.1.val
  invFun k := Sigma.mk ⟨k % 5, Nat.mod_lt k (by decide)⟩ (k / 5)
  left_inv := by
    rintro ⟨i, n⟩
    simp
    constructor
    · ext
      exact Nat.mod_eq_of_lt i.2
    · have hi : i.val < 5 := i.2
      omega
  right_inv := by
    intro k
    exact Nat.div_add_mod k 5

/-- Five-dissection of Euler's product into AP products. -/
theorem qPochInfPS_eq_five_residue_ap_products_rat :
    qPochInfPS ℚ =
      qPochAPPS ℚ 1 5 * qPochAPPS ℚ 2 5 * qPochAPPS ℚ 3 5 *
        qPochAPPS ℚ 4 5 * qPochAPPS ℚ 5 5 := by
  let f : ℕ → ℚ⟦X⟧ := fun k => (1 : ℚ⟦X⟧) - PowerSeries.X ^ (k + 1)
  let e : (Sigma fun _ : Fin 5 => ℕ) ≃ ℕ := finFiveSigmaNatEquivNatCh15
  have hf : HasProd f (qPochInfPS ℚ) := by
    rw [qPochInfPS_eq_tprod ℚ]
    exact (multipliable_one_sub_X_pow_succ ℚ).hasProd
  have hsig : HasProd (f ∘ e) (qPochInfPS ℚ) :=
    (Equiv.hasProd_iff e).mpr hf
  have hfiber : ∀ i : Fin 5,
      HasProd (fun n : ℕ => (f ∘ e) (Sigma.mk i n))
        (qPochAPPS ℚ (i.val + 1) 5) := by
    intro i
    convert hasProd_qPochAPPS ℚ (i.val + 1) 5 (by norm_num) using 1
    ext n
    simp [f, e, finFiveSigmaNatEquivNatCh15, apFactorPS]
    congr 1
    ring_nf
  have hfin : HasProd (fun i : Fin 5 => qPochAPPS ℚ (i.val + 1) 5)
      (qPochInfPS ℚ) := hsig.sigma hfiber
  have hfin' : HasProd (fun i : Fin 5 => qPochAPPS ℚ (i.val + 1) 5)
      (∏ i : Fin 5, qPochAPPS ℚ (i.val + 1) 5) := hasProd_fintype _
  have hprod : qPochInfPS ℚ = ∏ i : Fin 5, qPochAPPS ℚ (i.val + 1) 5 :=
    hfin.unique hfin'
  rw [hprod]
  norm_num [Fin.prod_univ_five]

/-- `expand 5` turns Euler's product into the `0 mod 5` AP factor. -/
theorem expandFiveQpochRat_eq_qPochAPPS_five :
    expandFiveQpochRat = qPochAPPS ℚ 5 5 := by
  simpa [expandFiveQpochRat] using
    expand_qPochInfPS_eq_qPochAPPS_self_rat 5 (by decide : (5 : ℕ) ≠ 0)

/-- Euler's product split into the non-`5` classes and the `0 mod 5`
class.  This is the formal version of
`(X;X)_∞ = ∏_{5∤n}(1-X^n) * (X^5;X^5)_∞`. -/
theorem qPochInfPS_eq_qPochNonFive_mul_expandFive :
    qPochInfPS ℚ = qPochNonFiveRat * expandFiveQpochRat := by
  rw [qPochInfPS_eq_five_residue_ap_products_rat,
    expandFiveQpochRat_eq_qPochAPPS_five]

/-- The two eta-quotient product presentations agree by the `5`-adic split of
Euler's product. -/
theorem etaQuotientProductSplit_eq_etaQuotientProductSide :
    etaQuotientProductSplit = etaQuotientProductSide := by
  unfold etaQuotientProductSplit etaQuotientProductSide qPochNonFiveRat
  rw [qPochInfPS_eq_five_residue_ap_products_rat]
  ring

/-- Direct product-side proof of the five-residue-class split. -/
theorem P014_product_mul_P023_product_eq_qPochInfPS_mul_expand_five_qPochInfPS_direct :
    P014_product * P023_product =
      qPochInfPS ℚ * expandFiveQpochRat := by
  rw [expandFiveQpochRat_eq_qPochAPPS_five,
    qPochInfPS_eq_five_residue_ap_products_rat]
  unfold P014_product P023_product pentagonalProduct014PS pentagonalProduct023PS
  ring

/-- Product-side version of the five-residue-class split. -/
theorem P014_product_mul_P023_product_eq_qPochInfPS_mul_expand_five_qPochInfPS :
    P014_product * P023_product =
      qPochInfPS ℚ * expandFiveQpochRat := by
  exact P014_product_mul_P023_product_eq_qPochInfPS_mul_expand_five_qPochInfPS_direct

/-- The product split needed for the quintuple-product logarithmic-derivative
route: the two pentagonal factors cover the five residue classes, with the
`0 mod 5` class appearing as `expand 5 qPochInfPS`. -/
theorem P014_mul_P023_eq_qPochInfPS_mul_expand_five_qPochInfPS :
    P014 * P023 =
      qPochInfPS ℚ * PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) := by
  simpa [P014, P023] using
    pentagonal014Series_mul_pentagonal023Series_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat

/-- `P014` has nonzero constant coefficient, so its formal inverse is genuine. -/
theorem constantCoeff_P014_ne_zero :
    PowerSeries.constantCoeff P014 ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [P014, coeff_zero_pentagonal014SeriesPS_rat]
  exact one_ne_zero

/-- `P023` has nonzero constant coefficient, so its formal inverse is genuine. -/
theorem constantCoeff_P023_ne_zero :
    PowerSeries.constantCoeff P023 ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [P023, coeff_zero_pentagonal023SeriesPS_rat]
  exact one_ne_zero

/-- `expand 5 (qPochInfPS ℚ)` has nonzero constant coefficient. -/
theorem constantCoeff_expandFiveQpochRat_ne_zero :
    PowerSeries.constantCoeff expandFiveQpochRat ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [expandFiveQpochRat, PowerSeries.coeff_expand]
  simp [coeff_zero_qPochInfPS]

/-- The expanded `q`-Pochhammer factor `(X^5; X^5)_∞` is a unit. -/
theorem isUnit_expandFiveQpochRat : IsUnit expandFiveQpochRat := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [expandFiveQpochRat, PowerSeries.coeff_expand]
  simp [coeff_zero_qPochInfPS]

/-- Direct multiplicative Euler-product form of the eta quotient:
`((X;X)_∞^4 * ∏_{5∤n}(1-X^n)) * (X^5;X^5)_∞ = (X;X)_∞^5`. -/
theorem etaQuotientProductSide_mul_expandFive_eq_qPoch_pow_five :
    etaQuotientProductSide * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5 := by
  unfold etaQuotientProductSide
  calc
    ((qPochInfPS ℚ) ^ 4 * qPochNonFiveRat) * expandFiveQpochRat
        = (qPochInfPS ℚ) ^ 4 * (qPochNonFiveRat * expandFiveQpochRat) := by
            ring
    _ = (qPochInfPS ℚ) ^ 4 * qPochInfPS ℚ := by
            rw [← qPochInfPS_eq_qPochNonFive_mul_expandFive]
    _ = (qPochInfPS ℚ) ^ 5 := by ring

/-- The fully split eta quotient clears the denominator to `(X;X)_∞^5`. -/
theorem etaQuotientProductSplit_mul_expandFive_eq_qPoch_pow_five :
    etaQuotientProductSplit * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5 := by
  rw [etaQuotientProductSplit_eq_etaQuotientProductSide,
    etaQuotientProductSide_mul_expandFive_eq_qPoch_pow_five]

/-- Divided form of the same direct Euler-product identity. -/
theorem etaQuotientProductSide_eq_qPoch_pow_five_mul_expandFive_inv :
    etaQuotientProductSide = (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹ := by
  apply isUnit_expandFiveQpochRat.mul_left_inj.mp
  calc
    etaQuotientProductSide * expandFiveQpochRat
        = (qPochInfPS ℚ) ^ 5 :=
            etaQuotientProductSide_mul_expandFive_eq_qPoch_pow_five
    _ = ((qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) *
          expandFiveQpochRat := by
            rw [mul_assoc,
              PowerSeries.inv_mul_cancel _ constantCoeff_expandFiveQpochRat_ne_zero]
            ring

@[simp] theorem constantCoeff_qPochNonFiveRat :
    PowerSeries.constantCoeff qPochNonFiveRat = 1 := by
  unfold qPochNonFiveRat
  simp [constantCoeff_qPochAPPS_rat 1 5 (by norm_num) (by norm_num),
    constantCoeff_qPochAPPS_rat 2 5 (by norm_num) (by norm_num),
    constantCoeff_qPochAPPS_rat 3 5 (by norm_num) (by norm_num),
    constantCoeff_qPochAPPS_rat 4 5 (by norm_num) (by norm_num)]

/-- The non-`5` product is a unit. -/
theorem constantCoeff_qPochNonFiveRat_ne_zero :
    PowerSeries.constantCoeff qPochNonFiveRat ≠ 0 := by
  rw [constantCoeff_qPochNonFiveRat]
  exact one_ne_zero

@[simp] theorem constantCoeff_etaQuotientProductSide :
    PowerSeries.constantCoeff etaQuotientProductSide = 1 := by
  unfold etaQuotientProductSide
  rw [map_mul, map_pow]
  unfold qPochNonFiveRat
  rw [map_mul, map_mul, map_mul]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply (qPochInfPS ℚ),
    coeff_zero_qPochInfPS]
  rw [constantCoeff_qPochAPPS_rat 1 5 (by norm_num) (by norm_num),
    constantCoeff_qPochAPPS_rat 2 5 (by norm_num) (by norm_num),
    constantCoeff_qPochAPPS_rat 3 5 (by norm_num) (by norm_num),
    constantCoeff_qPochAPPS_rat 4 5 (by norm_num) (by norm_num)]
  norm_num

theorem constantCoeff_etaQuotientProductSide_ne_zero :
    PowerSeries.constantCoeff etaQuotientProductSide ≠ 0 := by
  rw [constantCoeff_etaQuotientProductSide]
  exact one_ne_zero

/-- The pentagonal product `P014 * P023` is a unit. -/
theorem isUnit_P014_mul_P023 : IsUnit (P014 * P023) := by
  rw [P014_mul_P023_eq_qPochInfPS_mul_expand_five_qPochInfPS]
  exact (isUnit_qPochInfPS ℚ).mul isUnit_expandFiveQpochRat

/-- Multiplying the proposed quintuple-product logarithmic derivative by
`P014 * P023` gives the pentagonal Wronskian numerator. -/
theorem quintuple_log_derivative_lhs_mul_P014_P023 :
    ((1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * (thetaLog P014 - thetaLog P023)) *
        (P014 * P023) =
      P014 * P023 +
        (5 : ℚ⟦X⟧) * (P023 * thetaOp P014 - P014 * thetaOp P023) := by
  unfold thetaLog thetaDlog
  have hAinv : P014⁻¹ * P014 = 1 := by
    rw [mul_comm, PowerSeries.mul_inv_cancel P014 constantCoeff_P014_ne_zero]
  have hBinv : P023⁻¹ * P023 = 1 := by
    rw [mul_comm, PowerSeries.mul_inv_cancel P023 constantCoeff_P023_ne_zero]
  calc
    ((1 : ℚ⟦X⟧) +
        (5 : ℚ⟦X⟧) * (thetaOp P014 * P014⁻¹ - thetaOp P023 * P023⁻¹)) *
        (P014 * P023)
        = P014 * P023 + (5 : ℚ⟦X⟧) *
          ((thetaOp P014 * P014⁻¹) * (P014 * P023) -
            (thetaOp P023 * P023⁻¹) * (P014 * P023)) := by
            ring
    _ = P014 * P023 +
        (5 : ℚ⟦X⟧) * (P023 * thetaOp P014 - P014 * thetaOp P023) := by
      have hAterm :
          (thetaOp P014 * P014⁻¹) * (P014 * P023) =
            P023 * thetaOp P014 := by
        calc
          (thetaOp P014 * P014⁻¹) * (P014 * P023)
              = thetaOp P014 * (P014⁻¹ * P014) * P023 := by ring
          _ = thetaOp P014 * 1 * P023 := by rw [hAinv]
          _ = P023 * thetaOp P014 := by ring
      have hBterm :
          (thetaOp P023 * P023⁻¹) * (P014 * P023) =
            P014 * thetaOp P023 := by
        calc
          (thetaOp P023 * P023⁻¹) * (P014 * P023)
              = thetaOp P023 * (P023⁻¹ * P023) * P014 := by ring
          _ = thetaOp P023 * 1 * P014 := by rw [hBinv]
          _ = P014 * thetaOp P023 := by ring
      rw [hAterm, hBterm]

/-- Multiplying `(X; X)_∞^5 / (X^5; X^5)_∞` by `P014 * P023`
collapses to `(X; X)_∞^6`. -/
theorem quintuple_log_derivative_rhs_mul_P014_P023 :
    ((qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) * (P014 * P023) =
      (qPochInfPS ℚ) ^ 6 := by
  have hE5inv : expandFiveQpochRat⁻¹ * expandFiveQpochRat = 1 := by
    rw [mul_comm,
      PowerSeries.mul_inv_cancel expandFiveQpochRat constantCoeff_expandFiveQpochRat_ne_zero]
  rw [P014_mul_P023_eq_qPochInfPS_mul_expand_five_qPochInfPS]
  change ((qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) *
      (qPochInfPS ℚ * expandFiveQpochRat) = (qPochInfPS ℚ) ^ 6
  calc
    ((qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) *
        (qPochInfPS ℚ * expandFiveQpochRat)
        = (qPochInfPS ℚ) ^ 6 * (expandFiveQpochRat⁻¹ * expandFiveQpochRat) := by
            ring
    _ = (qPochInfPS ℚ) ^ 6 * 1 := by rw [hE5inv]
    _ = (qPochInfPS ℚ) ^ 6 := by ring

/-- The quintuple-product logarithmic-derivative identity implies the
pentagonal-level Wronskian identity. -/
theorem wronskian_of_quintupleProduct_log_derivative_identity
    (hlog :
      (1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * (thetaLog P014 - thetaLog P023) =
        (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) :
    P014 * P023 +
        (5 : ℚ⟦X⟧) * (P023 * thetaOp P014 - P014 * thetaOp P023) =
      (qPochInfPS ℚ) ^ 6 := by
  have hmul := congrArg (fun f : ℚ⟦X⟧ => f * (P014 * P023)) hlog
  change
    ((1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * (thetaLog P014 - thetaLog P023)) *
        (P014 * P023) =
      ((qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) * (P014 * P023) at hmul
  rw [quintuple_log_derivative_lhs_mul_P014_P023,
    quintuple_log_derivative_rhs_mul_P014_P023] at hmul
  exact hmul

/-- Conversely, after multiplying by the unit `P014 * P023`, the Wronskian
identity is algebraically equivalent to the quintuple-product logarithmic
derivative identity. -/
theorem quintupleProduct_log_derivative_identity_of_wronskian
    (hw :
      P014 * P023 +
          (5 : ℚ⟦X⟧) * (P023 * thetaOp P014 - P014 * thetaOp P023) =
        (qPochInfPS ℚ) ^ 6) :
    (1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * (thetaLog P014 - thetaLog P023) =
      (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹ := by
  apply isUnit_P014_mul_P023.mul_left_inj.mp
  rw [quintuple_log_derivative_lhs_mul_P014_P023,
    quintuple_log_derivative_rhs_mul_P014_P023]
  exact hw

/-- Constant coefficient of a mod-5 AP product is nonzero. -/
theorem constantCoeff_qPochAPPS_five_ne_zero (r : ℕ) (hr : 0 < r) :
    PowerSeries.constantCoeff (qPochAPPS ℚ r 5) ≠ 0 := by
  rw [constantCoeff_qPochAPPS_rat r 5 hr (by norm_num)]
  exact one_ne_zero

/-- Logarithmic theta derivative of a mod-5 AP product. -/
theorem thetaLog_qPochAPPS_five (r : ℕ) (hr : 0 < r) :
    thetaLog (qPochAPPS ℚ r 5) =
      -apDivisorSigmaPS ℚ r 5 := by
  unfold thetaLog thetaDlog
  rw [thetaOp_qPochAPPS_rat r 5 hr (by norm_num)]
  have hcancel :
      (qPochAPPS ℚ r 5)⁻¹ * qPochAPPS ℚ r 5 = 1 := by
    rw [mul_comm, PowerSeries.mul_inv_cancel _ (constantCoeff_qPochAPPS_five_ne_zero r hr)]
  calc
    (-(qPochAPPS ℚ r 5) * apDivisorSigmaPS ℚ r 5) *
        (qPochAPPS ℚ r 5)⁻¹
        = -(apDivisorSigmaPS ℚ r 5) *
            ((qPochAPPS ℚ r 5)⁻¹ * qPochAPPS ℚ r 5) := by ring
    _ = -apDivisorSigmaPS ℚ r 5 := by
        rw [hcancel]
        ring

/-- Logarithmic theta derivative of the `0,1,4` pentagonal factor. -/
theorem thetaLog_P014_eq_neg_apSigmas :
    thetaLog P014 =
      -(apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 4 5 + apDivisorSigmaPS ℚ 5 5) := by
  have h1 : PowerSeries.constantCoeff (qPochAPPS ℚ 1 5) ≠ 0 :=
    constantCoeff_qPochAPPS_five_ne_zero 1 (by norm_num)
  have h4 : PowerSeries.constantCoeff (qPochAPPS ℚ 4 5) ≠ 0 :=
    constantCoeff_qPochAPPS_five_ne_zero 4 (by norm_num)
  have h5 : PowerSeries.constantCoeff (qPochAPPS ℚ 5 5) ≠ 0 :=
    constantCoeff_qPochAPPS_five_ne_zero 5 (by norm_num)
  have h14 : PowerSeries.constantCoeff (qPochAPPS ℚ 1 5 * qPochAPPS ℚ 4 5) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero h1 h4
  rw [← P014_product_eq_P014]
  unfold P014_product pentagonalProduct014PS
  unfold thetaLog
  rw [thetaDlog_mul (qPochAPPS ℚ 1 5 * qPochAPPS ℚ 4 5) (qPochAPPS ℚ 5 5)
      h14 h5,
    thetaDlog_mul (qPochAPPS ℚ 1 5) (qPochAPPS ℚ 4 5) h1 h4]
  change
    thetaLog (qPochAPPS ℚ 1 5) + thetaLog (qPochAPPS ℚ 4 5) +
        thetaLog (qPochAPPS ℚ 5 5) =
      -(apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 4 5 + apDivisorSigmaPS ℚ 5 5)
  rw [thetaLog_qPochAPPS_five 1 (by norm_num),
    thetaLog_qPochAPPS_five 4 (by norm_num),
    thetaLog_qPochAPPS_five 5 (by norm_num)]
  ring

/-- Logarithmic theta derivative of the `0,2,3` pentagonal factor. -/
theorem thetaLog_P023_eq_neg_apSigmas :
    thetaLog P023 =
      -(apDivisorSigmaPS ℚ 2 5 + apDivisorSigmaPS ℚ 3 5 + apDivisorSigmaPS ℚ 5 5) := by
  have h2 : PowerSeries.constantCoeff (qPochAPPS ℚ 2 5) ≠ 0 :=
    constantCoeff_qPochAPPS_five_ne_zero 2 (by norm_num)
  have h3 : PowerSeries.constantCoeff (qPochAPPS ℚ 3 5) ≠ 0 :=
    constantCoeff_qPochAPPS_five_ne_zero 3 (by norm_num)
  have h5 : PowerSeries.constantCoeff (qPochAPPS ℚ 5 5) ≠ 0 :=
    constantCoeff_qPochAPPS_five_ne_zero 5 (by norm_num)
  have h23 : PowerSeries.constantCoeff (qPochAPPS ℚ 2 5 * qPochAPPS ℚ 3 5) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero h2 h3
  rw [← P023_product_eq_P023]
  unfold P023_product pentagonalProduct023PS
  unfold thetaLog
  rw [thetaDlog_mul (qPochAPPS ℚ 2 5 * qPochAPPS ℚ 3 5) (qPochAPPS ℚ 5 5)
      h23 h5,
    thetaDlog_mul (qPochAPPS ℚ 2 5) (qPochAPPS ℚ 3 5) h2 h3]
  change
    thetaLog (qPochAPPS ℚ 2 5) + thetaLog (qPochAPPS ℚ 3 5) +
        thetaLog (qPochAPPS ℚ 5 5) =
      -(apDivisorSigmaPS ℚ 2 5 + apDivisorSigmaPS ℚ 3 5 + apDivisorSigmaPS ℚ 5 5)
  rw [thetaLog_qPochAPPS_five 2 (by norm_num),
    thetaLog_qPochAPPS_five 3 (by norm_num),
    thetaLog_qPochAPPS_five 5 (by norm_num)]
  ring

/-- The quintuple-product logarithmic factor is exactly Chan's residue-class
Lambert-series side.  The common `(q^5;q^5)_∞` logarithmic derivative cancels. -/
theorem quintuple_log_factor_eq_one_plus_apSigmas :
    (1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * (thetaLog P014 - thetaLog P023) =
      1 + (5 : ℚ⟦X⟧) *
        ((apDivisorSigmaPS ℚ 2 5 + apDivisorSigmaPS ℚ 3 5) -
          (apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 4 5)) := by
  rw [thetaLog_P014_eq_neg_apSigmas, thetaLog_P023_eq_neg_apSigmas]
  ring

/-- Abbreviated form of the logarithmic-factor/AP-sigma identification. -/
theorem quintupleLogFactor_eq_apSigmaLambertFactor :
    quintupleLogFactor = apSigmaLambertFactor := by
  simpa [quintupleLogFactor, apSigmaLambertFactor] using
    quintuple_log_factor_eq_one_plus_apSigmas

/-- The remaining logarithmic-derivative target is equivalent to the
eta-quotient form of Chan's residue-class Lambert identity. -/
theorem quintuple_log_identity_iff_apSigma_eta_quotient :
    ((1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * (thetaLog P014 - thetaLog P023) =
        (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) ↔
      (1 + (5 : ℚ⟦X⟧) *
        ((apDivisorSigmaPS ℚ 2 5 + apDivisorSigmaPS ℚ 3 5) -
          (apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 4 5)) =
        (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) := by
  rw [quintuple_log_factor_eq_one_plus_apSigmas]

/-- In abbreviated form, the quintuple logarithmic target is equivalent to the
AP-sigma eta-quotient identity. -/
theorem quintupleLogFactor_eq_etaQuotient_iff_apSigmaLambertFactor :
    (quintupleLogFactor =
        (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) ↔
      (apSigmaLambertFactor =
        (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) := by
  rw [quintupleLogFactor_eq_apSigmaLambertFactor]

/-- Divided and multiplied forms of the AP-sigma eta-quotient identity are
equivalent because `(X^5;X^5)_∞` is a unit. -/
theorem apSigmaLambertFactor_eq_etaQuotient_iff_mul_expandFive :
    (apSigmaLambertFactor =
        (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) ↔
      (apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5) := by
  constructor
  · intro h
    rw [h, mul_assoc, PowerSeries.inv_mul_cancel _ constantCoeff_expandFiveQpochRat_ne_zero]
    ring_nf
  · intro h
    apply isUnit_expandFiveQpochRat.mul_left_inj.mp
    calc
      apSigmaLambertFactor * expandFiveQpochRat =
          (qPochInfPS ℚ) ^ 5 := h
      _ = (qPochInfPS ℚ) ^ 5 * 1 := by ring
      _ = (qPochInfPS ℚ) ^ 5 * (expandFiveQpochRat⁻¹ * expandFiveQpochRat) := by
          rw [PowerSeries.inv_mul_cancel _ constantCoeff_expandFiveQpochRat_ne_zero]
      _ = ((qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹) * expandFiveQpochRat := by
          ring

/-- Multiplicative form of the remaining quintuple-product logarithmic
derivative target.  This avoids inverses in the statement and is the natural
coefficientwise closure target. -/
theorem quintupleLogFactor_mul_expandFive_eq_qPoch_pow_five_iff_apSigma :
    (quintupleLogFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5) ↔
      (apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5) := by
  rw [quintupleLogFactor_eq_apSigmaLambertFactor]

/-- If the AP-sigma Lambert side satisfies the eta-quotient identity in
multiplicative form, the quintuple-product logarithmic derivative identity
follows. -/
theorem quintupleProduct_log_derivative_identity_of_apSigma_mul_expandFive
    (h :
      apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5) :
    quintupleLogFactor =
      (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹ := by
  rw [quintupleLogFactor_eq_apSigmaLambertFactor]
  exact apSigmaLambertFactor_eq_etaQuotient_iff_mul_expandFive.mpr h

/-- Coefficientwise form of the remaining AP-sigma eta-quotient target. -/
theorem coeff_apSigmaLambertFactor_mul_expandFive_target_iff :
    (apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5) ↔
      ∀ N : ℕ,
        (apSigmaLambertFactor * expandFiveQpochRat).coeff N =
          ((qPochInfPS ℚ) ^ 5).coeff N := by
  constructor
  · intro h N
    rw [h]
  · intro h
    ext N
    exact h N

/-! ### Executable coefficient model for the cleared logarithmic target -/

/-- Integer coefficient model for the AP divisor-sigma series agrees with the
formal rational power-series coefficient. -/
theorem coeff_apDivisorSigmaPS_rat_eq_coeffZ (r m n : ℕ) :
    (apDivisorSigmaPS ℚ r m).coeff n = (apDivisorSigmaCoeffZ r m n : ℚ) := by
  unfold apDivisorSigmaCoeffZ
  rw [coeff_apDivisorSigmaPS, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases h : r + m * k ∣ n ∧ 0 < n <;> simp [h]

/-- Integer coefficients of the AP-sigma Lambert factor
`1 + 5*((Σ₂+Σ₃)-(Σ₁+Σ₄))`. -/
def apSigmaLambertCoeffZ (n : ℕ) : ℤ :=
  if n = 0 then 1
  else 5 *
    ((apDivisorSigmaCoeffZ 2 5 n + apDivisorSigmaCoeffZ 3 5 n) -
      (apDivisorSigmaCoeffZ 1 5 n + apDivisorSigmaCoeffZ 4 5 n))

/-- The AP-sigma Lambert factor has the advertised executable integer
coefficient model. -/
theorem coeff_apSigmaLambertFactor (n : ℕ) :
    apSigmaLambertFactor.coeff n = (apSigmaLambertCoeffZ n : ℚ) := by
  by_cases hn : n = 0
  · subst n
    simp [apSigmaLambertFactor, apSigmaLambertCoeffZ]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    unfold apSigmaLambertFactor apSigmaLambertCoeffZ
    rw [if_neg hn]
    change
      (1 + PowerSeries.C (5 : ℚ) *
        ((apDivisorSigmaPS ℚ 2 5 + apDivisorSigmaPS ℚ 3 5) -
          (apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 4 5))).coeff n =
        ((5 *
          ((apDivisorSigmaCoeffZ 2 5 n + apDivisorSigmaCoeffZ 3 5 n) -
            (apDivisorSigmaCoeffZ 1 5 n + apDivisorSigmaCoeffZ 4 5 n)) : ℤ) : ℚ)
    rw [map_add, PowerSeries.coeff_one, if_neg hn, PowerSeries.coeff_C_mul]
    rw [map_sub, map_add, map_add]
    rw [coeff_apDivisorSigmaPS_rat_eq_coeffZ,
      coeff_apDivisorSigmaPS_rat_eq_coeffZ,
      coeff_apDivisorSigmaPS_rat_eq_coeffZ,
      coeff_apDivisorSigmaPS_rat_eq_coeffZ]
    push_cast
    ring

/-- Integer coefficient model for powers of Euler's product, using Euler's
pentagonal-sign coefficients and ordinary Cauchy convolution. -/
def qPochPowPentagonalCoeffIndependent : ℕ → ℕ → ℤ
  | 0 => fun n => if n = 0 then 1 else 0
  | e + 1 => fun n =>
      ∑ k ∈ Finset.range (n + 1),
        qPochPowPentagonalCoeffIndependent e k *
          QseriesFormalization.PartI.Ch05.pentagonalSign (n - k)

/-- Coefficients of `(q;q)_∞^e` are computed by
`qPochPowPentagonalCoeffIndependent`. -/
theorem coeff_qPochInfPS_pow_pentagonal_independent (e n : ℕ) :
    ((qPochInfPS ℚ) ^ e).coeff n =
      (qPochPowPentagonalCoeffIndependent e n : ℚ) := by
  induction e generalizing n with
  | zero =>
      by_cases h : n = 0
      · simp [qPochPowPentagonalCoeffIndependent, PowerSeries.coeff_one, h]
      · simp [qPochPowPentagonalCoeffIndependent, PowerSeries.coeff_one, h]
  | succ e ih =>
      rw [pow_succ, PowerSeries.coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [qPochPowPentagonalCoeffIndependent]
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [ih k, coeff_qPochInfPS_eq_pentagonalSign]
      simp

/-- Integer coefficients of `(X^5;X^5)_∞ = expand 5 (X;X)_∞`. -/
def expandFiveQpochCoeffZ (n : ℕ) : ℤ :=
  if 5 ∣ n then QseriesFormalization.PartI.Ch05.pentagonalSign (n / 5) else 0

/-- Coefficients of `expandFiveQpochRat` in executable integer form. -/
theorem coeff_expandFiveQpochRat (n : ℕ) :
    expandFiveQpochRat.coeff n = (expandFiveQpochCoeffZ n : ℚ) := by
  unfold expandFiveQpochRat expandFiveQpochCoeffZ
  rw [PowerSeries.coeff_expand]
  by_cases h : 5 ∣ n
  · simp [h, coeff_qPochInfPS_eq_pentagonalSign]
  · simp [h]

/-- Executable convolution coefficient for the cleared AP-sigma target. -/
def apSigmaLambertMulExpandFiveCoeffZ (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    apSigmaLambertCoeffZ k * expandFiveQpochCoeffZ (n - k)

/-- Direct integer coefficient gap for the multiplicative eta identity
`apSigmaLambertFactor * (q^5;q^5)_∞ = (q;q)_∞^5`.  This is the coefficientwise
route that uses Euler's pentagonal coefficients for both Euler products. -/
def apSigmaEtaProductCoeffGapZ (n : ℕ) : ℤ :=
  apSigmaLambertMulExpandFiveCoeffZ n -
    qPochPowPentagonalCoeffIndependent 5 n

/-- The formal power-series gap in the cleared AP-sigma eta identity. -/
noncomputable abbrev apSigmaEtaProductGap : ℚ⟦X⟧ :=
  apSigmaLambertFactor * expandFiveQpochRat - (qPochInfPS ℚ) ^ 5

/-- Coefficients of
`apSigmaLambertFactor * expandFiveQpochRat` in executable integer form. -/
theorem coeff_apSigmaLambertFactor_mul_expandFive (n : ℕ) :
    (apSigmaLambertFactor * expandFiveQpochRat).coeff n =
      (apSigmaLambertMulExpandFiveCoeffZ n : ℚ) := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold apSigmaLambertMulExpandFiveCoeffZ
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [coeff_apSigmaLambertFactor, coeff_expandFiveQpochRat]
  simp

/-- Coefficients of the direct eta-product gap in executable integer form. -/
theorem coeff_apSigmaEtaProductGap (n : ℕ) :
    (apSigmaLambertFactor * expandFiveQpochRat - (qPochInfPS ℚ) ^ 5).coeff n =
      (apSigmaEtaProductCoeffGapZ n : ℚ) := by
  rw [map_sub, coeff_apSigmaLambertFactor_mul_expandFive,
    coeff_qPochInfPS_pow_pentagonal_independent]
  unfold apSigmaEtaProductCoeffGapZ
  norm_num

/-- Abbreviated coefficient bridge for the cleared AP-sigma eta-product gap. -/
theorem coeff_apSigmaEtaProductGap_abbrev (n : ℕ) :
    apSigmaEtaProductGap.coeff n = (apSigmaEtaProductCoeffGapZ n : ℚ) := by
  simpa [apSigmaEtaProductGap] using coeff_apSigmaEtaProductGap n

/-- The direct coefficient gap is equivalent to the multiplicative eta identity. -/
theorem apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_iff_direct_gap_zero :
    apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5 ↔
      ∀ n : ℕ, apSigmaEtaProductCoeffGapZ n = 0 := by
  constructor
  · intro h n
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
    have hdiff :
        apSigmaLambertFactor * expandFiveQpochRat - (qPochInfPS ℚ) ^ 5 = 0 := by
      rw [h]
      ring
    have hc := congrArg (fun f : ℚ⟦X⟧ => f.coeff n) hdiff
    change
      (apSigmaLambertFactor * expandFiveQpochRat - (qPochInfPS ℚ) ^ 5).coeff n =
        (0 : ℚ⟦X⟧).coeff n at hc
    rw [coeff_apSigmaEtaProductGap] at hc
    simpa using hc
  · intro hgap
    apply sub_eq_zero.mp
    ext n
    rw [coeff_apSigmaEtaProductGap, hgap n]
    simp

/-- The direct product-side target is equivalently the coefficient gap for
`apSigmaLambertFactor * (X^5;X^5)_∞ = (X;X)_∞^5`.  This avoids any recurrence
language: the remaining identity is exactly
`apSigmaLambertFactor = etaQuotientProductSide`. -/
theorem apSigmaLambertFactor_eq_etaQuotientProductSide_iff_direct_gap_zero :
    apSigmaLambertFactor = etaQuotientProductSide ↔
      ∀ n : ℕ, apSigmaEtaProductCoeffGapZ n = 0 := by
  constructor
  · intro h
    exact apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_iff_direct_gap_zero.mp
      (by rw [h]; exact etaQuotientProductSide_mul_expandFive_eq_qPoch_pow_five)
  · intro hgap
    apply isUnit_expandFiveQpochRat.mul_left_inj.mp
    calc
      apSigmaLambertFactor * expandFiveQpochRat
          = (qPochInfPS ℚ) ^ 5 :=
              apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_iff_direct_gap_zero.mpr hgap
      _ = etaQuotientProductSide * expandFiveQpochRat := by
              rw [etaQuotientProductSide_mul_expandFive_eq_qPoch_pow_five]

/-! ### Direct coefficient model for the eta-quotient side -/

/-- Coefficients of the inverse of a rational power series whose integer
coefficient model has constant coefficient `1`. -/
theorem coeff_inv_eq_unitInvCoeffAuxZ
    (f : ℚ⟦X⟧) (a : ℕ → ℤ)
    (hf : ∀ n : ℕ, f.coeff n = (a n : ℚ)) (ha0 : a 0 = 1) :
    ∀ n : ℕ, f⁻¹.coeff n = (unitInvCoeffAuxZ a n : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      have hcc : PowerSeries.constantCoeff f = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf 0, ha0]
        norm_num
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.constantCoeff_inv, hcc]
      norm_num [unitInvCoeffAuxZ]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hcc : PowerSeries.constantCoeff f = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf 0, ha0]
        norm_num
      rw [PowerSeries.coeff_inv (m + 1) f]
      simp only [Nat.succ_ne_zero, if_false, hcc, inv_one]
      have hsum :
          (∑ x ∈ Finset.antidiagonal (m + 1),
            if x.2 < m + 1 then f.coeff x.1 * (f⁻¹).coeff x.2 else 0) =
            ∑ i : Fin (m + 1),
              f.coeff (i.1 + 1) * (f⁻¹).coeff (m - i.1) := by
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        rw [Finset.sum_range_succ']
        have hzero :
            (if m + 1 - 0 < m + 1 then
              f.coeff 0 * (f⁻¹).coeff (m + 1 - 0) else 0) = 0 := by
          simp
        rw [hzero, add_zero]
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt : x < m + 1 := by
          simpa [Finset.mem_range] using hx
        have hnot : ¬ m < x := by omega
        have hsub : m + 1 - (x + 1) = m - x := by omega
        rw [hsub]
        simp [hnot]
      rw [hsum]
      rw [show (-1 : ℚ) *
          (∑ i : Fin (m + 1), f.coeff (i.1 + 1) * (f⁻¹).coeff (m - i.1)) =
            -∑ i : Fin (m + 1),
              f.coeff (i.1 + 1) * (f⁻¹).coeff (m - i.1) by ring]
      rw [show unitInvCoeffAuxZ a (m + 1) =
          -∑ i : Fin (m + 1),
            a (i.1 + 1) * unitInvCoeffAuxZ a (m - i.1) by
            simp [unitInvCoeffAuxZ]]
      change
        -∑ i : Fin (m + 1),
          f.coeff (i.1 + 1) * (f⁻¹).coeff (m - i.1) =
        ((-∑ i : Fin (m + 1),
          a (i.1 + 1) * unitInvCoeffAuxZ a (m - i.1) : ℤ) : ℚ)
      rw [Int.cast_neg, Int.cast_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      have hlt : m - i.1 < m + 1 := by omega
      rw [hf (i.1 + 1), ih (m - i.1) hlt]
      push_cast
      rfl

/-- Integer coefficients of the inverse of `(X^5; X^5)_∞`. -/
def expandFiveQpochInvCoeffZ (n : ℕ) : ℤ :=
  unitInvCoeffAuxZ expandFiveQpochCoeffZ n

/-- Coefficients of `expandFiveQpochRat⁻¹` in executable integer form. -/
theorem coeff_expandFiveQpochRat_inv (n : ℕ) :
    (expandFiveQpochRat⁻¹).coeff n = (expandFiveQpochInvCoeffZ n : ℚ) := by
  unfold expandFiveQpochInvCoeffZ
  apply coeff_inv_eq_unitInvCoeffAuxZ
  · exact coeff_expandFiveQpochRat
  · native_decide

/-- Direct integer coefficient model for
`etaQuotientProductSide = (X;X)_∞^5 * (X^5;X^5)_∞⁻¹`. -/
def etaQuotientProductSideCoeffZ (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    qPochPowPentagonalCoeffIndependent 5 k *
      expandFiveQpochInvCoeffZ (n - k)

/-- The product-side eta quotient has the direct executable coefficient model
obtained by expanding `(X;X)_∞^5` and the inverse of `(X^5;X^5)_∞`. -/
theorem coeff_etaQuotientProductSide_direct (n : ℕ) :
    etaQuotientProductSide.coeff n =
      (etaQuotientProductSideCoeffZ n : ℚ) := by
  rw [etaQuotientProductSide_eq_qPoch_pow_five_mul_expandFive_inv]
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold etaQuotientProductSideCoeffZ
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [coeff_qPochInfPS_pow_pentagonal_independent,
    coeff_expandFiveQpochRat_inv]
  norm_num

/-- Direct coefficient gap for
`apSigmaLambertFactor = etaQuotientProductSide`, without multiplying by
`(X^5;X^5)_∞`. -/
def apSigmaEtaQuotientCoeffGapZ (n : ℕ) : ℤ :=
  apSigmaLambertCoeffZ n - etaQuotientProductSideCoeffZ n

/-- Direct coefficient form of the quotient-side AP-sigma gap. -/
theorem coeff_apSigmaLambertFactor_sub_etaQuotientProductSide (n : ℕ) :
    (apSigmaLambertFactor - etaQuotientProductSide).coeff n =
      (apSigmaEtaQuotientCoeffGapZ n : ℚ) := by
  rw [map_sub, coeff_apSigmaLambertFactor,
    coeff_etaQuotientProductSide_direct]
  unfold apSigmaEtaQuotientCoeffGapZ
  norm_num

/-- The AP-sigma eta quotient is equivalent to the direct coefficient gap,
with no theta-log or recurrence hypothesis. -/
theorem apSigmaLambertFactor_eq_etaQuotientProductSide_iff_direct_coeff_gap_zero :
    apSigmaLambertFactor = etaQuotientProductSide ↔
      ∀ n : ℕ, apSigmaEtaQuotientCoeffGapZ n = 0 := by
  constructor
  · intro h n
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
    have hdiff :
        apSigmaLambertFactor - etaQuotientProductSide = 0 := by
      rw [h]
      ring
    have hc := congrArg (fun f : ℚ⟦X⟧ => f.coeff n) hdiff
    change
      (apSigmaLambertFactor - etaQuotientProductSide).coeff n =
        (0 : ℚ⟦X⟧).coeff n at hc
    rw [coeff_apSigmaLambertFactor_sub_etaQuotientProductSide] at hc
    simpa using hc
  · intro hgap
    apply sub_eq_zero.mp
    ext n
    change
      (apSigmaLambertFactor - etaQuotientProductSide).coeff n =
        (0 : ℚ⟦X⟧).coeff n
    rw [coeff_apSigmaLambertFactor_sub_etaQuotientProductSide, hgap n]
    simp

/-- The quotient-side direct coefficient gap and the cleared product
coefficient gap are equivalent all-degree arithmetic targets. -/
theorem apSigmaEtaQuotientCoeffGapZ_zero_iff_productCoeffGapZ_zero :
    (∀ n : ℕ, apSigmaEtaQuotientCoeffGapZ n = 0) ↔
      ∀ n : ℕ, apSigmaEtaProductCoeffGapZ n = 0 := by
  constructor
  · intro hq
    exact apSigmaLambertFactor_eq_etaQuotientProductSide_iff_direct_gap_zero.mp
      (apSigmaLambertFactor_eq_etaQuotientProductSide_iff_direct_coeff_gap_zero.mpr hq)
  · intro hp
    exact apSigmaLambertFactor_eq_etaQuotientProductSide_iff_direct_coeff_gap_zero.mp
      (apSigmaLambertFactor_eq_etaQuotientProductSide_iff_direct_gap_zero.mpr hp)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- Direct quotient-side coefficient gap, verified through degree `10`. -/
theorem apSigmaEtaQuotientCoeffGapZ_eq_zero_le_ten :
    ∀ n : ℕ, n ≤ 10 → apSigmaEtaQuotientCoeffGapZ n = 0 := by
  intro n hn
  interval_cases n <;> native_decide

/-- Direct coefficient equality
`apSigmaLambertFactor.coeff n = etaQuotientProductSide.coeff n`, verified
through degree `10` using the quotient-side coefficient model. -/
theorem coeff_apSigmaLambertFactor_eq_etaQuotientProductSide_le_ten :
    ∀ n : ℕ, n ≤ 10 →
      apSigmaLambertFactor.coeff n = etaQuotientProductSide.coeff n := by
  intro n hn
  rw [coeff_apSigmaLambertFactor, coeff_etaQuotientProductSide_direct]
  have hgap := apSigmaEtaQuotientCoeffGapZ_eq_zero_le_ten n hn
  unfold apSigmaEtaQuotientCoeffGapZ at hgap
  exact_mod_cast sub_eq_zero.mp hgap

/-! ### Prime-power local Eisenstein structure -/

/-- The quadratic character modulo `5`, extended by `0` on multiples of `5`. -/
def chiFiveZ (n : ℕ) : ℤ :=
  if n % 5 = 1 ∨ n % 5 = 4 then 1
  else if n % 5 = 2 ∨ n % 5 = 3 then -1
  else 0

theorem chiFiveZ_mul (m n : ℕ) :
    chiFiveZ (m * n) = chiFiveZ m * chiFiveZ n := by
  have hm_lt : m % 5 < 5 := Nat.mod_lt m (by decide)
  have hn_lt : n % 5 < 5 := Nat.mod_lt n (by decide)
  interval_cases hm : m % 5 <;> interval_cases hn : n % 5 <;>
    simp [chiFiveZ, hm, hn, Nat.mul_mod]

/-- The `χ₅` divisor-sigma series in the AP basis already used by the file:
`Σ_{n≥1}(Σ_{d|n} χ₅(d)d) X^n`. -/
noncomputable abbrev chiFiveAPDivisorSigmaPS : ℚ⟦X⟧ :=
  (apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 4 5) -
    (apDivisorSigmaPS ℚ 2 5 + apDivisorSigmaPS ℚ 3 5)

/-- The current Lambert-side target is the character-twisted identity
`1 - 5*Σχ₅(d)d`, not the untwisted `5∤d` divisor sum. -/
theorem apSigmaLambertFactor_eq_one_sub_five_chiFiveAPDivisorSigmaPS :
    apSigmaLambertFactor =
      1 - (5 : ℚ⟦X⟧) * chiFiveAPDivisorSigmaPS := by
  unfold apSigmaLambertFactor chiFiveAPDivisorSigmaPS
  ring

/-- Exact remaining input supplied by the Jacobi-Weierstrass fifth-root
specialization.  The root-of-unity coefficient table gives the `χ₅` signs;
the eta quotient side is already `etaQuotientProductSide`. -/
abbrev JacobiWeierstrassFifthRootLambertIdentity : Prop :=
  etaQuotientProductSide =
    1 - (5 : ℚ⟦X⟧) * chiFiveAPDivisorSigmaPS

theorem apSigmaLambertFactor_eq_etaQuotientProductSide_of_jacobiWeierstrass
    (hjw : JacobiWeierstrassFifthRootLambertIdentity) :
    apSigmaLambertFactor = etaQuotientProductSide := by
  rw [apSigmaLambertFactor_eq_one_sub_five_chiFiveAPDivisorSigmaPS, hjw]

/-- Geometric partial sums, the local factor coefficients for a weight-2
Eisenstein series with Satake parameter `a`. -/
def geometricPartialSumZ (a : ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1), a ^ i

theorem geometricPartialSumZ_succ (a : ℤ) (k : ℕ) :
    geometricPartialSumZ a (k + 1) =
      geometricPartialSumZ a k + a ^ (k + 1) := by
  unfold geometricPartialSumZ
  rw [Finset.sum_range_succ]

/-- Local Hecke recursion for the Euler factor
`1 / ((1-X) * (1-a*X))`. -/
theorem geometricPartialSumZ_succ_succ (a : ℤ) (k : ℕ) :
    geometricPartialSumZ a (k + 2) =
      (1 + a) * geometricPartialSumZ a (k + 1) -
        a * geometricPartialSumZ a k := by
  have h1 := geometricPartialSumZ_succ a (k + 1)
  have h0 := geometricPartialSumZ_succ a k
  rw [show k + 2 = k + 1 + 1 by omega]
  rw [h1, h0]
  have hp : a ^ (k + 1 + 1) = a * a ^ (k + 1) := by
    rw [pow_succ]
    ring
  rw [hp]
  ring

/-- Prime-power local coefficients for the level-5 Eisenstein divisor sum
`Σ_{d|n} χ₅(d)d`. -/
def chan15LocalEulerCoeffZ (p k : ℕ) : ℤ :=
  geometricPartialSumZ (chiFiveZ p * (p : ℤ)) k

/-- Correct prime-power recursion for the level-5 character.  For primes
`p ≡ 1,4 (mod 5)` this specializes to the usual `(p+1, -p)` recursion; for
`p ≡ 2,3 (mod 5)` the signs are different. -/
theorem chan15LocalEulerCoeffZ_succ_succ (p k : ℕ) :
    chan15LocalEulerCoeffZ p (k + 2) =
      (1 + chiFiveZ p * (p : ℤ)) * chan15LocalEulerCoeffZ p (k + 1) -
        (chiFiveZ p * (p : ℤ)) * chan15LocalEulerCoeffZ p k := by
  simpa [chan15LocalEulerCoeffZ] using
    geometricPartialSumZ_succ_succ (chiFiveZ p * (p : ℤ)) k

/-- The uncharactered base value `p+1` is not the coefficient model used here:
already at `p=2`, Chan's signed mod-5 divisor sum has coefficient `5`. -/
theorem apSigmaLambertCoeffZ_two_ne_uncharactered_prime_base :
    apSigmaLambertCoeffZ 2 ≠ ((2 : ℤ) + 1) := by
  native_decide

/-- The quotient-side executable coefficient agrees with the same obstruction
at `p=2`; the missing identity cannot be closed by the trivial-character
`p+1` local data. -/
theorem etaQuotientProductSideCoeffZ_two_ne_uncharactered_prime_base :
    etaQuotientProductSideCoeffZ 2 ≠ ((2 : ℤ) + 1) := by
  native_decide

/-- Concrete sample of the corrected character-twisted recursion at `p=2`. -/
theorem apSigmaLambertCoeffZ_two_square_character_rec :
    apSigmaLambertCoeffZ (2 ^ 2) =
      (1 + chiFiveZ 2 * (2 : ℤ)) * apSigmaLambertCoeffZ 2 -
        (chiFiveZ 2 * (2 : ℤ)) * apSigmaLambertCoeffZ 1 := by
  native_decide

/-- The raw AP-sigma coefficients are not multiplicative: the coefficient of
`q` is `-5`, not `1`, so the usual prime-power reduction cannot be applied to
`apSigmaLambertCoeffZ` as stated. -/
theorem apSigmaLambertCoeffZ_raw_not_multiplicative :
    apSigmaLambertCoeffZ (2 * 3) ≠
      apSigmaLambertCoeffZ 2 * apSigmaLambertCoeffZ 3 := by
  native_decide

/-- The raw eta-quotient coefficient model has the same obstruction.  The
prime-power Euler-factor route must first normalize the nonconstant
coefficients by the `q`-coefficient. -/
theorem etaQuotientProductSideCoeffZ_raw_not_multiplicative :
    etaQuotientProductSideCoeffZ (2 * 3) ≠
      etaQuotientProductSideCoeffZ 2 * etaQuotientProductSideCoeffZ 3 := by
  native_decide

/-- The normalized level-5 Eisenstein divisor coefficient
`Σ_{d|n} χ₅(d)d`, written directly from the residue-class divisor sums.  This
is the sequence to which a prime-power multiplicativity argument can apply. -/
def chan15NormalizedDivisorCoeffZ (n : ℕ) : ℤ :=
  if n = 0 then 1
  else
    (apDivisorSigmaCoeffZ 1 5 n + apDivisorSigmaCoeffZ 4 5 n) -
      (apDivisorSigmaCoeffZ 2 5 n + apDivisorSigmaCoeffZ 3 5 n)

/-- Coefficients of the AP-basis `χ₅` divisor-sigma series.  Its constant
coefficient is `0`; the normalized arithmetic function has value `1` at
`n = 0` only for multiplicativity bookkeeping. -/
theorem coeff_chiFiveAPDivisorSigmaPS (n : ℕ) :
    chiFiveAPDivisorSigmaPS.coeff n =
      ((if n = 0 then 0 else chan15NormalizedDivisorCoeffZ n : ℤ) : ℚ) := by
  unfold chiFiveAPDivisorSigmaPS
  rw [map_sub, map_add, map_add]
  rw [coeff_apDivisorSigmaPS_rat_eq_coeffZ,
    coeff_apDivisorSigmaPS_rat_eq_coeffZ,
    coeff_apDivisorSigmaPS_rat_eq_coeffZ,
    coeff_apDivisorSigmaPS_rat_eq_coeffZ]
  by_cases hn : n = 0
  · subst n
    norm_num [chan15NormalizedDivisorCoeffZ, apDivisorSigmaCoeffZ]
  · simp [hn, chan15NormalizedDivisorCoeffZ]

/-- Unsigned divisor sum over the residue classes coprime to `5`.  This is
not the coefficient model used by Chan's quintuple-product Lambert factor. -/
def chan15NonFiveDivisorCoeffZ (n : ℕ) : ℤ :=
  if n = 0 then 1
  else
    apDivisorSigmaCoeffZ 1 5 n + apDivisorSigmaCoeffZ 2 5 n +
      apDivisorSigmaCoeffZ 3 5 n + apDivisorSigmaCoeffZ 4 5 n

/-- `apSigmaLambertCoeffZ` is `-5` times the normalized divisor coefficient in
positive degree. -/
theorem apSigmaLambertCoeffZ_eq_neg_five_mul_normalized
    {n : ℕ} (hn : n ≠ 0) :
    apSigmaLambertCoeffZ n = -5 * chan15NormalizedDivisorCoeffZ n := by
  unfold apSigmaLambertCoeffZ chan15NormalizedDivisorCoeffZ
  rw [if_neg hn, if_neg hn]
  ring

/-- At `n = 2`, the signed `χ₅` divisor coefficient is `1 - 2 = -1`. -/
theorem chan15NormalizedDivisorCoeffZ_two :
    chan15NormalizedDivisorCoeffZ 2 = -1 := by
  native_decide

/-- At `n = 2`, the unsigned non-`5` divisor coefficient is `1 + 2 = 3`. -/
theorem chan15NonFiveDivisorCoeffZ_two :
    chan15NonFiveDivisorCoeffZ 2 = 3 := by
  native_decide

/-- The AP-sigma Lambert coefficient uses the signed `χ₅` value:
`-5 * (1 - 2) = 5`. -/
theorem apSigmaLambertCoeffZ_two :
    apSigmaLambertCoeffZ 2 = 5 := by
  native_decide

/-- The eta-quotient product-side direct coefficient has the same signed
`χ₅` value at `q²`. -/
theorem etaQuotientProductSideCoeffZ_two :
    etaQuotientProductSideCoeffZ 2 = 5 := by
  native_decide

/-- The logarithmic quintuple factor has coefficient `5` at `q²`; this is the
signed `χ₅` coefficient, not the unsigned coprime-divisor sum. -/
theorem coeff_quintupleLogFactor_two :
    quintupleLogFactor.coeff 2 = 5 := by
  rw [quintupleLogFactor_eq_apSigmaLambertFactor, coeff_apSigmaLambertFactor]
  exact_mod_cast apSigmaLambertCoeffZ_two

/-- The unsigned coprime-divisor interpretation would give `5 * 3 = 15`, so it
does not match the actual `q²` coefficient. -/
theorem apSigmaLambertCoeffZ_two_ne_five_mul_nonFive :
    apSigmaLambertCoeffZ 2 ≠ 5 * chan15NonFiveDivisorCoeffZ 2 := by
  native_decide

/-- The normalized divisor coefficients are multiplicative on a checked
small coprime window.  This records the corrected local-Euler-factor target
without using the false raw-coefficient multiplicativity. -/
theorem chan15NormalizedDivisorCoeffZ_mul_coprime_le_ten :
    ∀ m n : ℕ, m ≤ 10 → n ≤ 10 → Nat.Coprime m n →
      chan15NormalizedDivisorCoeffZ (m * n) =
        chan15NormalizedDivisorCoeffZ m * chan15NormalizedDivisorCoeffZ n := by
  intro m n hm hn hcop
  interval_cases m <;> interval_cases n <;>
    first
    | native_decide
    | exfalso
      norm_num [Nat.Coprime] at hcop

/-- The product-side direct coefficient model matches the normalized divisor
coefficients through degree `10`, after dividing the nonconstant coefficients
by the common factor `-5`. -/
theorem etaQuotientProductSideCoeffZ_eq_neg_five_mul_normalized_le_ten :
    ∀ n : ℕ, n ≤ 10 → n ≠ 0 →
      etaQuotientProductSideCoeffZ n =
        -5 * chan15NormalizedDivisorCoeffZ n := by
  intro n hn hpos
  have hgap := apSigmaEtaQuotientCoeffGapZ_eq_zero_le_ten n hn
  unfold apSigmaEtaQuotientCoeffGapZ at hgap
  have hlam := apSigmaLambertCoeffZ_eq_neg_five_mul_normalized (n := n) hpos
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- The cleared AP-sigma eta-quotient target, checked by native computation
through degree `10`. -/
theorem apSigmaLambert_mul_expandFive_coeffZ_eq_qPoch_pow_five_le_ten :
    ∀ n : ℕ, n ≤ 10 →
      apSigmaLambertMulExpandFiveCoeffZ n =
        qPochPowPentagonalCoeffIndependent 5 n := by
  native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- Direct eta-product coefficient gap, verified through degree `30` using the
integer Euler-product coefficient model. -/
theorem apSigmaEtaProductCoeffGapZ_eq_zero_le_thirty :
    ∀ n : ℕ, n ≤ 30 → apSigmaEtaProductCoeffGapZ n = 0 := by
  intro n hn
  interval_cases n <;> native_decide

/-- The two coefficients needed by the expected weight-2, level-5 Sturm bound. -/
theorem apSigmaEtaProductCoeffGapZ_eq_zero_le_one :
    ∀ n : ℕ, n ≤ 1 → apSigmaEtaProductCoeffGapZ n = 0 := by
  intro n hn
  exact apSigmaEtaProductCoeffGapZ_eq_zero_le_thirty n (by omega)

/-- Coefficient form of the same two-term certificate. -/
theorem coeff_apSigmaEtaProductGap_eq_zero_le_one :
    ∀ n : ℕ, n ≤ 1 → apSigmaEtaProductGap.coeff n = 0 := by
  intro n hn
  rw [coeff_apSigmaEtaProductGap_abbrev,
    apSigmaEtaProductCoeffGapZ_eq_zero_le_one n hn]
  norm_num

/-- Exact formal shape of the missing Sturm-bound input for this eta quotient.

For a genuine modular-form proof, this is the specialized statement obtained
from the weight-2, level-5 Sturm bound: if the first two coefficients of the
cleared gap vanish, then the whole gap vanishes. -/
abbrev APSigmaEtaProductGapSturmBoundOne : Prop :=
  (∀ n : ℕ, n ≤ 1 → apSigmaEtaProductGap.coeff n = 0) →
    apSigmaEtaProductGap = 0

/-- Once the specialized Sturm-bound statement is available, the AP-sigma
eta quotient follows from the already-checked first two coefficients. -/
theorem apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_of_sturm_bound_one
    (hsturm : APSigmaEtaProductGapSturmBoundOne) :
    apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5 := by
  exact sub_eq_zero.mp (by
    simpa [apSigmaEtaProductGap] using
      hsturm coeff_apSigmaEtaProductGap_eq_zero_le_one)

/-- The cleared AP-sigma eta-quotient target, checked directly through degree
`30` by the Euler-product coefficient model. -/
theorem apSigmaLambert_mul_expandFive_coeffZ_eq_qPoch_pow_five_le_thirty :
    ∀ n : ℕ, n ≤ 30 →
      apSigmaLambertMulExpandFiveCoeffZ n =
        qPochPowPentagonalCoeffIndependent 5 n := by
  intro n hn
  exact sub_eq_zero.mp (apSigmaEtaProductCoeffGapZ_eq_zero_le_thirty n hn)

/-- Low-degree coefficient verification of the cleared quintuple-product
logarithmic-derivative target. -/
theorem coeff_apSigmaLambertFactor_mul_expandFive_eq_qPoch_pow_five_le_ten :
    ∀ n : ℕ, n ≤ 10 →
      (apSigmaLambertFactor * expandFiveQpochRat).coeff n =
        ((qPochInfPS ℚ) ^ 5).coeff n := by
  intro n hn
  rw [coeff_apSigmaLambertFactor_mul_expandFive,
    coeff_qPochInfPS_pow_pentagonal_independent]
  exact_mod_cast apSigmaLambert_mul_expandFive_coeffZ_eq_qPoch_pow_five_le_ten n hn

/-- Direct coefficient verification of the multiplicative eta identity through
degree `30`. -/
theorem coeff_apSigmaLambertFactor_mul_expandFive_eq_qPoch_pow_five_le_thirty :
    ∀ n : ℕ, n ≤ 30 →
      (apSigmaLambertFactor * expandFiveQpochRat).coeff n =
        ((qPochInfPS ℚ) ^ 5).coeff n := by
  intro n hn
  rw [coeff_apSigmaLambertFactor_mul_expandFive,
    coeff_qPochInfPS_pow_pentagonal_independent]
  exact_mod_cast apSigmaLambert_mul_expandFive_coeffZ_eq_qPoch_pow_five_le_thirty n hn

theorem coeff_quintupleLogFactor_mul_expandFive_eq_qPoch_pow_five_le_ten :
    ∀ n : ℕ, n ≤ 10 →
      (quintupleLogFactor * expandFiveQpochRat).coeff n =
        ((qPochInfPS ℚ) ^ 5).coeff n := by
  intro n hn
  rw [quintupleLogFactor_eq_apSigmaLambertFactor]
  exact coeff_apSigmaLambertFactor_mul_expandFive_eq_qPoch_pow_five_le_ten n hn

theorem coeff_quintupleLogFactor_mul_expandFive_eq_qPoch_pow_five_le_thirty :
    ∀ n : ℕ, n ≤ 30 →
      (quintupleLogFactor * expandFiveQpochRat).coeff n =
        ((qPochInfPS ℚ) ^ 5).coeff n := by
  intro n hn
  rw [quintupleLogFactor_eq_apSigmaLambertFactor]
  exact coeff_apSigmaLambertFactor_mul_expandFive_eq_qPoch_pow_five_le_thirty n hn

/-! ### Theta-log recurrence form of the eta-quotient gap -/

/-- Sum of the five AP divisor-sigma series.  This is the mod-5 residue split
of the ordinary `sigma_1` Lambert series, stated without importing Chapter 20. -/
noncomputable abbrev apDivisorSigmaAllFive : ℚ⟦X⟧ :=
  apDivisorSigmaNonFive + apDivisorSigmaPS ℚ 5 5

/-- The theta-log driver for `(q;q)_∞^5`, written with the mod-5 AP split. -/
noncomputable abbrev qPochPowFiveThetaDriver : ℚ⟦X⟧ :=
  (5 : ℚ⟦X⟧) * (-apDivisorSigmaAllFive)

/-- If `A * (q^5;q^5)_∞ = (q;q)_∞^5`, then the Lambert factor `A` must have
this theta-log driver before multiplication by the fifth AP product. -/
noncomputable abbrev apSigmaLambertThetaDriver : ℚ⟦X⟧ :=
  qPochPowFiveThetaDriver + apDivisorSigmaPS ℚ 5 5

/-- Integer coefficient model for the theta-log driver
`-5*Σ_all + Σ_5`. -/
def apSigmaLambertThetaDriverCoeffZ (n : ℕ) : ℤ :=
  -(5 : ℤ) *
      (apDivisorSigmaCoeffZ 1 5 n + apDivisorSigmaCoeffZ 2 5 n +
        apDivisorSigmaCoeffZ 3 5 n + apDivisorSigmaCoeffZ 4 5 n +
          apDivisorSigmaCoeffZ 5 5 n) +
    apDivisorSigmaCoeffZ 5 5 n

/-- Coefficients of `apSigmaLambertThetaDriver` in executable integer form. -/
theorem coeff_apSigmaLambertThetaDriver (n : ℕ) :
    apSigmaLambertThetaDriver.coeff n =
      (apSigmaLambertThetaDriverCoeffZ n : ℚ) := by
  unfold apSigmaLambertThetaDriver qPochPowFiveThetaDriver
    apDivisorSigmaAllFive apSigmaLambertThetaDriverCoeffZ
  change
    ((PowerSeries.C (5 : ℚ) *
        (-(apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 2 5 +
          apDivisorSigmaPS ℚ 3 5 + apDivisorSigmaPS ℚ 4 5 +
            apDivisorSigmaPS ℚ 5 5)) +
      apDivisorSigmaPS ℚ 5 5).coeff n) =
      ((-(5 : ℤ) *
          (apDivisorSigmaCoeffZ 1 5 n + apDivisorSigmaCoeffZ 2 5 n +
            apDivisorSigmaCoeffZ 3 5 n + apDivisorSigmaCoeffZ 4 5 n +
              apDivisorSigmaCoeffZ 5 5 n) +
        apDivisorSigmaCoeffZ 5 5 n : ℤ) : ℚ)
  rw [map_add, PowerSeries.coeff_C_mul, map_neg, map_add, map_add, map_add, map_add]
  rw [coeff_apDivisorSigmaPS_rat_eq_coeffZ,
    coeff_apDivisorSigmaPS_rat_eq_coeffZ,
    coeff_apDivisorSigmaPS_rat_eq_coeffZ,
    coeff_apDivisorSigmaPS_rat_eq_coeffZ,
    coeff_apDivisorSigmaPS_rat_eq_coeffZ]
  push_cast
  ring_nf

/-- Integer residual for the coefficient equation
`thetaOp apSigmaLambertFactor = apSigmaLambertThetaDriver * apSigmaLambertFactor`. -/
def apSigmaLambertThetaResidualZ (n : ℕ) : ℤ :=
  (n : ℤ) * apSigmaLambertCoeffZ n -
    ∑ ij ∈ Finset.antidiagonal n,
      apSigmaLambertThetaDriverCoeffZ ij.1 * apSigmaLambertCoeffZ ij.2

/-- Coefficient bridge for the AP-sigma Lambert theta-log residual. -/
theorem coeff_apSigmaLambertThetaResidual (n : ℕ) :
    (thetaOp apSigmaLambertFactor -
        apSigmaLambertThetaDriver * apSigmaLambertFactor).coeff n =
      (apSigmaLambertThetaResidualZ n : ℚ) := by
  rw [map_sub, coeff_thetaOp, PowerSeries.coeff_mul]
  unfold apSigmaLambertThetaResidualZ
  rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  rw [coeff_apSigmaLambertFactor]
  have hsum :
      (∑ ij ∈ Finset.antidiagonal n,
        apSigmaLambertThetaDriver.coeff ij.1 *
          apSigmaLambertFactor.coeff ij.2) =
        ((∑ ij ∈ Finset.antidiagonal n,
          apSigmaLambertThetaDriverCoeffZ ij.1 *
            apSigmaLambertCoeffZ ij.2 : ℤ) : ℚ) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro ij _hij
    rw [coeff_apSigmaLambertThetaDriver, coeff_apSigmaLambertFactor]
    simp
  rw [hsum]
  rw [Int.cast_sum]
  ring

/-- The all-coefficient residual is exactly the missing theta-log recurrence. -/
theorem apSigmaLambertFactor_satisfies_thetaLog_of_residual_zero
    (hres : ∀ n : ℕ, apSigmaLambertThetaResidualZ n = 0) :
    SatisfiesThetaLogRecurrence apSigmaLambertThetaDriver apSigmaLambertFactor := by
  unfold SatisfiesThetaLogRecurrence
  ext n
  have h := coeff_apSigmaLambertThetaResidual n
  rw [hres n] at h
  rw [Int.cast_zero] at h
  exact sub_eq_zero.mp h

/-- Conversely, a theta-log recurrence gives vanishing of every explicit
integer residual coefficient. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_of_satisfies_thetaLog
    (hA :
      SatisfiesThetaLogRecurrence apSigmaLambertThetaDriver apSigmaLambertFactor)
    (n : ℕ) :
    apSigmaLambertThetaResidualZ n = 0 := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
  have hdiff :
      thetaOp apSigmaLambertFactor -
          apSigmaLambertThetaDriver * apSigmaLambertFactor = 0 := by
    unfold SatisfiesThetaLogRecurrence at hA
    rw [hA]
    ring_nf
  have hc := congrArg (fun f : ℚ⟦X⟧ => f.coeff n) hdiff
  change
    (thetaOp apSigmaLambertFactor -
        apSigmaLambertThetaDriver * apSigmaLambertFactor).coeff n =
      (0 : ℚ⟦X⟧).coeff n at hc
  rw [coeff_apSigmaLambertThetaResidual] at hc
  simpa using hc

/-- The explicit integer residual is equivalent to the formal theta-log
recurrence. -/
theorem apSigmaLambertFactor_satisfies_thetaLog_iff_residual_zero :
    SatisfiesThetaLogRecurrence apSigmaLambertThetaDriver apSigmaLambertFactor ↔
      ∀ n : ℕ, apSigmaLambertThetaResidualZ n = 0 := by
  constructor
  · intro h n
    exact apSigmaLambertThetaResidualZ_eq_zero_of_satisfies_thetaLog h n
  · intro h
    exact apSigmaLambertFactor_satisfies_thetaLog_of_residual_zero h

/-- A single zero residual is exactly the coefficient equation of the
AP-sigma Lambert theta-log recurrence in that degree. -/
theorem apSigmaLambertFactor_thetaLog_coeff_eq_of_residual_zero
    {n : ℕ} (hres : apSigmaLambertThetaResidualZ n = 0) :
    (thetaOp apSigmaLambertFactor).coeff n =
      (apSigmaLambertThetaDriver * apSigmaLambertFactor).coeff n := by
  have h := coeff_apSigmaLambertThetaResidual n
  rw [hres, Int.cast_zero] at h
  exact sub_eq_zero.mp h

/-- Coefficient form of the recurrence through a finite range.  This is the
native-decision front end for the explicit residual certificate. -/
theorem apSigmaLambertFactor_thetaLog_coeff_eq_le_of_residual_zero
    {B : ℕ} (hres : ∀ n : ℕ, n ≤ B → apSigmaLambertThetaResidualZ n = 0) :
    ∀ n : ℕ, n ≤ B →
      (thetaOp apSigmaLambertFactor).coeff n =
        (apSigmaLambertThetaDriver * apSigmaLambertFactor).coeff n := by
  intro n hn
  exact apSigmaLambertFactor_thetaLog_coeff_eq_of_residual_zero (hres n hn)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- Bounded certificate for the explicit integer recurrence residual.  This is
kept below the degree where native evaluation becomes memory-heavy. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_le_thirty :
    ∀ n : ℕ, n ≤ 30 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hn
  interval_cases n <;> native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- The same explicit recurrence residual certificate through degree `50`. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_le_fifty :
    ∀ n : ℕ, n ≤ 50 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hn
  interval_cases n <;> native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
/-- The explicit recurrence residual certificate through degree `60`. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_le_sixty :
    ∀ n : ℕ, n ≤ 60 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hn
  interval_cases n <;> native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
/-- The explicit recurrence residual certificate through degree `100`. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_le_hundred :
    ∀ n : ℕ, n ≤ 100 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hn
  interval_cases n <;> native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
/-- The explicit recurrence residual certificate through degree `150`. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_le_onehundredfifty :
    ∀ n : ℕ, n ≤ 150 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hn
  interval_cases n <;> native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 15000000 in
/-- The explicit recurrence residual certificate through degree `200`. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_le_twohundred :
    ∀ n : ℕ, n ≤ 200 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hn
  interval_cases n <;> native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- The explicit recurrence residual certificate on degrees `201..250`.
Kept as a separate chunk so native evaluation does not need to compile one
large monolithic decision tree. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_201_250 :
    ∀ n : ℕ, 201 ≤ n → n ≤ 250 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hlo hhi
  interval_cases n <;> native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- The explicit recurrence residual certificate on degrees `251..300`. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_251_300 :
    ∀ n : ℕ, 251 ≤ n → n ≤ 300 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hlo hhi
  interval_cases n <;> native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- The explicit recurrence residual certificate on degrees `301..350`. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_301_350 :
    ∀ n : ℕ, 301 ≤ n → n ≤ 350 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hlo hhi
  interval_cases n <;> native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- The explicit recurrence residual certificate on degrees `351..400`. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_351_400 :
    ∀ n : ℕ, 351 ≤ n → n ≤ 400 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hlo hhi
  interval_cases n <;> native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- The explicit recurrence residual certificate on degrees `401..450`. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_401_450 :
    ∀ n : ℕ, 401 ≤ n → n ≤ 450 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hlo hhi
  interval_cases n <;> native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- The explicit recurrence residual certificate on degrees `451..500`. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_451_500 :
    ∀ n : ℕ, 451 ≤ n → n ≤ 500 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hlo hhi
  interval_cases n <;> native_decide

/-- The explicit AP-sigma theta residual certificate through degree `500`,
assembled from small native-decision chunks. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_le_fivehundred :
    ∀ n : ℕ, n ≤ 500 → apSigmaLambertThetaResidualZ n = 0 := by
  intro n hn
  by_cases h200 : n ≤ 200
  · exact apSigmaLambertThetaResidualZ_eq_zero_le_twohundred n h200
  · have h201 : 201 ≤ n := by omega
    by_cases h250 : n ≤ 250
    · exact apSigmaLambertThetaResidualZ_eq_zero_201_250 n h201 h250
    · have h251 : 251 ≤ n := by omega
      by_cases h300 : n ≤ 300
      · exact apSigmaLambertThetaResidualZ_eq_zero_251_300 n h251 h300
      · have h301 : 301 ≤ n := by omega
        by_cases h350 : n ≤ 350
        · exact apSigmaLambertThetaResidualZ_eq_zero_301_350 n h301 h350
        · have h351 : 351 ≤ n := by omega
          by_cases h400 : n ≤ 400
          · exact apSigmaLambertThetaResidualZ_eq_zero_351_400 n h351 h400
          · have h401 : 401 ≤ n := by omega
            by_cases h450 : n ≤ 450
            · exact apSigmaLambertThetaResidualZ_eq_zero_401_450 n h401 h450
            · have h451 : 451 ≤ n := by omega
              exact apSigmaLambertThetaResidualZ_eq_zero_451_500 n h451 hn

/-- A finite homogeneous recurrence plus enough zero initial values forces an
integer sequence to vanish identically.  The coefficient function is allowed to
depend on the target index `n`; the only structural requirement is that the
right side uses the previous `d` values. -/
theorem intSeq_eq_zero_of_finite_homogeneous_recurrence
    (u : ℕ → ℤ) (d : ℕ) (c : ℕ → ℕ → ℤ)
    (hinit : ∀ n : ℕ, n < d → u n = 0)
    (hrec : ∀ n : ℕ, d ≤ n →
      u n = ∑ i ∈ Finset.range d, c n i * u (n - 1 - i)) :
    ∀ n : ℕ, u n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < d
      · exact hinit n hn
      · have hdn : d ≤ n := Nat.le_of_not_gt hn
        rw [hrec n hdn]
        apply Finset.sum_eq_zero
        intro i hi
        have hid : i < d := Finset.mem_range.mp hi
        have hlt : n - 1 - i < n := by
          by_cases hd0 : d = 0
          · subst d
            simp at hi
          · have hpos : 0 < n := by omega
            omega
        rw [ih (n - 1 - i) hlt, mul_zero]

/-- Conditional closure of the AP-sigma residual by the proposed finite
recurrence route.  Thus any homogeneous recurrence of order at most `201`,
together with the existing `≤ 200` native certificate, proves the all-degree
theta-log recurrence residual. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_of_finite_homogeneous_recurrence
    {d : ℕ} (hd : d ≤ 201) (c : ℕ → ℕ → ℤ)
    (hrec : ∀ n : ℕ, d ≤ n →
      apSigmaLambertThetaResidualZ n =
        ∑ i ∈ Finset.range d, c n i * apSigmaLambertThetaResidualZ (n - 1 - i)) :
    ∀ n : ℕ, apSigmaLambertThetaResidualZ n = 0 := by
  apply intSeq_eq_zero_of_finite_homogeneous_recurrence
    apSigmaLambertThetaResidualZ d c
  · intro n hn
    exact apSigmaLambertThetaResidualZ_eq_zero_le_twohundred n (by omega)
  · exact hrec

/-- The AP-sigma Lambert factor satisfies the theta-log coefficient equation
through degree `200`. -/
theorem apSigmaLambertFactor_thetaLog_coeff_eq_le_twohundred :
    ∀ n : ℕ, n ≤ 200 →
      (thetaOp apSigmaLambertFactor).coeff n =
        (apSigmaLambertThetaDriver * apSigmaLambertFactor).coeff n :=
  apSigmaLambertFactor_thetaLog_coeff_eq_le_of_residual_zero
    apSigmaLambertThetaResidualZ_eq_zero_le_twohundred

/-- The AP-sigma Lambert factor satisfies the theta-log coefficient equation
through degree `150`. -/
theorem apSigmaLambertFactor_thetaLog_coeff_eq_le_onehundredfifty :
    ∀ n : ℕ, n ≤ 150 →
      (thetaOp apSigmaLambertFactor).coeff n =
        (apSigmaLambertThetaDriver * apSigmaLambertFactor).coeff n := by
  intro n hn
  exact apSigmaLambertFactor_thetaLog_coeff_eq_le_twohundred n (by omega)

/-- The AP-sigma Lambert factor satisfies the theta-log coefficient equation
through degree `100`. -/
theorem apSigmaLambertFactor_thetaLog_coeff_eq_le_hundred :
    ∀ n : ℕ, n ≤ 100 →
      (thetaOp apSigmaLambertFactor).coeff n =
        (apSigmaLambertThetaDriver * apSigmaLambertFactor).coeff n := by
  intro n hn
  exact apSigmaLambertFactor_thetaLog_coeff_eq_le_onehundredfifty n (by omega)

@[simp] theorem coeff_zero_apDivisorSigmaAllFive :
    apDivisorSigmaAllFive.coeff 0 = 0 := by
  simp [apDivisorSigmaAllFive]

@[simp] theorem coeff_zero_qPochPowFiveThetaDriver :
    qPochPowFiveThetaDriver.coeff 0 = 0 := by
  simp [qPochPowFiveThetaDriver]

theorem qPochInfPS_satisfies_allFive_thetaLog :
    SatisfiesThetaLogRecurrence (-apDivisorSigmaAllFive) (qPochInfPS ℚ) := by
  have h1 := qPochAPPS_satisfies_apSigmaThetaLog 1 5 (by norm_num) (by norm_num)
  have h2 := qPochAPPS_satisfies_apSigmaThetaLog 2 5 (by norm_num) (by norm_num)
  have h3 := qPochAPPS_satisfies_apSigmaThetaLog 3 5 (by norm_num) (by norm_num)
  have h4 := qPochAPPS_satisfies_apSigmaThetaLog 4 5 (by norm_num) (by norm_num)
  have h5 := qPochAPPS_satisfies_apSigmaThetaLog 5 5 (by norm_num) (by norm_num)
  have h12 := satisfiesThetaLogRecurrence_mul h1 h2
  have h123 := satisfiesThetaLogRecurrence_mul h12 h3
  have h1234 := satisfiesThetaLogRecurrence_mul h123 h4
  have h12345 := satisfiesThetaLogRecurrence_mul h1234 h5
  rw [qPochInfPS_eq_five_residue_ap_products_rat]
  convert h12345 using 1
  ring

theorem qPochPowFive_satisfies_thetaLog :
    SatisfiesThetaLogRecurrence qPochPowFiveThetaDriver ((qPochInfPS ℚ) ^ 5) := by
  have h := satisfiesThetaLogRecurrence_pow
    (n := 5) qPochInfPS_satisfies_allFive_thetaLog
  simpa [qPochPowFiveThetaDriver] using h

theorem expandFiveQpochRat_satisfies_thetaLog :
    SatisfiesThetaLogRecurrence (-(apDivisorSigmaPS ℚ 5 5)) expandFiveQpochRat := by
  rw [expandFiveQpochRat_eq_qPochAPPS_five]
  exact qPochAPPS_satisfies_apSigmaThetaLog 5 5 (by norm_num) (by norm_num)

/-- The product over the four nonzero residue classes mod `5` has logarithmic
theta derivative `-(Σ₁+Σ₂+Σ₃+Σ₄)`. -/
theorem qPochNonFiveRat_satisfies_thetaLog :
    SatisfiesThetaLogRecurrence (-apDivisorSigmaNonFive) qPochNonFiveRat := by
  have h1 := qPochAPPS_satisfies_apSigmaThetaLog 1 5 (by norm_num) (by norm_num)
  have h2 := qPochAPPS_satisfies_apSigmaThetaLog 2 5 (by norm_num) (by norm_num)
  have h3 := qPochAPPS_satisfies_apSigmaThetaLog 3 5 (by norm_num) (by norm_num)
  have h4 := qPochAPPS_satisfies_apSigmaThetaLog 4 5 (by norm_num) (by norm_num)
  have h12 := satisfiesThetaLogRecurrence_mul h1 h2
  have h123 := satisfiesThetaLogRecurrence_mul h12 h3
  have h1234 := satisfiesThetaLogRecurrence_mul h123 h4
  unfold qPochNonFiveRat
  convert h1234 using 1
  unfold apDivisorSigmaNonFive
  ring

/-- Formalized direct log-differentiation of
`(X;X)_∞^4 * ∏_{5∤n}(1-X^n)`: its theta-log driver is
`-5` times the non-`5` AP divisor-sigma series and `-4` times the `5`-class
series. -/
theorem etaQuotientProductSide_satisfies_thetaLog :
    SatisfiesThetaLogRecurrence etaQuotientThetaDriver etaQuotientProductSide := by
  have hE4 := satisfiesThetaLogRecurrence_pow
    (n := 4) qPochInfPS_satisfies_allFive_thetaLog
  have hmul := satisfiesThetaLogRecurrence_mul hE4 qPochNonFiveRat_satisfies_thetaLog
  unfold etaQuotientProductSide
  convert hmul using 1
  unfold etaQuotientThetaDriver apDivisorSigmaAllFive apDivisorSigmaNonFive
  ring

/-- Explicit logarithmic derivative form of the direct Euler-product
calculation:

`Theta(η(q)^5/η(q^5))/(η(q)^5/η(q^5))
 = -5*Σ_{5∤d} d q^d/(1-q^d) - 4*Σ_{5|d} d q^d/(1-q^d)`.
-/
theorem thetaDlog_etaQuotientProductSide :
    thetaDlog etaQuotientProductSide = etaQuotientThetaDriver := by
  exact thetaDlog_eq_of_satisfiesThetaLogRecurrence
    constantCoeff_etaQuotientProductSide_ne_zero
    etaQuotientProductSide_satisfies_thetaLog

/-- The direct product-side theta-log driver agrees with the driver forced by
the cleared AP-sigma eta identity. -/
theorem etaQuotientThetaDriver_eq_apSigmaLambertThetaDriver :
    etaQuotientThetaDriver = apSigmaLambertThetaDriver := by
  unfold etaQuotientThetaDriver apSigmaLambertThetaDriver qPochPowFiveThetaDriver
    apDivisorSigmaAllFive apDivisorSigmaNonFive
  ring

/-- The divided eta quotient `(X;X)_∞^5/(X^5;X^5)_∞` satisfies the same
theta-log equation as the target AP-sigma Lambert factor. -/
theorem etaQuotientProductSide_satisfies_apSigmaLambertThetaLog :
    SatisfiesThetaLogRecurrence apSigmaLambertThetaDriver etaQuotientProductSide := by
  rw [← etaQuotientThetaDriver_eq_apSigmaLambertThetaDriver]
  exact etaQuotientProductSide_satisfies_thetaLog

/-- The fully split AP-product eta quotient satisfies the same theta-log
equation. -/
theorem etaQuotientProductSplit_satisfies_apSigmaLambertThetaLog :
    SatisfiesThetaLogRecurrence apSigmaLambertThetaDriver etaQuotientProductSplit := by
  rw [etaQuotientProductSplit_eq_etaQuotientProductSide]
  exact etaQuotientProductSide_satisfies_apSigmaLambertThetaLog

@[simp] theorem coeff_zero_etaQuotientProductSide :
    etaQuotientProductSide.coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_etaQuotientProductSide]

@[simp] theorem coeff_zero_etaQuotientProductSplit :
    etaQuotientProductSplit.coeff 0 = 1 := by
  rw [etaQuotientProductSplit_eq_etaQuotientProductSide]
  exact coeff_zero_etaQuotientProductSide

/-- Over `ℚ`, `thetaOp` plus the constant coefficient determines a formal
power series. -/
theorem eq_of_coeff_zero_eq_of_thetaOp_eq_rat
    {f g : ℚ⟦X⟧}
    (h0 : f.coeff 0 = g.coeff 0)
    (hθ : thetaOp f = thetaOp g) :
    f = g := by
  ext n
  cases n with
  | zero => exact h0
  | succ n =>
      have hcoeff := congr_arg (PowerSeries.coeff (n + 1)) hθ
      simp only [coeff_thetaOp] at hcoeff
      have hne : ((n + 1 : ℕ) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (by omega)
      exact mul_right_cancel₀ hne hcoeff

/-- For the AP-sigma eta quotient target, equality is equivalent to equality
after applying `thetaOp`, because both constant coefficients are `1`. -/
theorem apSigmaLambertFactor_eq_etaQuotientProductSide_iff_thetaOp_eq :
    apSigmaLambertFactor = etaQuotientProductSide ↔
      thetaOp apSigmaLambertFactor = thetaOp etaQuotientProductSide := by
  constructor
  · intro h
    rw [h]
  · intro hθ
    exact eq_of_coeff_zero_eq_of_thetaOp_eq_rat (by simp) hθ

/-- If the AP-sigma Lambert factor satisfies the same theta-log recurrence as
the split eta quotient, recurrence uniqueness identifies the two series. -/
theorem apSigmaLambertFactor_eq_etaQuotientProductSide_of_satisfies_thetaLog
    (hA :
      SatisfiesThetaLogRecurrence apSigmaLambertThetaDriver apSigmaLambertFactor) :
    apSigmaLambertFactor = etaQuotientProductSide := by
  apply eq_of_same_thetaLogRecurrence (A := apSigmaLambertThetaDriver)
  · simp [apSigmaLambertThetaDriver, qPochPowFiveThetaDriver]
  · exact hA
  · exact etaQuotientProductSide_satisfies_apSigmaLambertThetaLog
  · simp

/-- Residual closure directly identifies Chan's AP-sigma Lambert side with the
elementary split product `η(q)^5/η(q^5)`. -/
theorem apSigmaLambertFactor_eq_etaQuotientProductSide_of_residual_zero
    (hres : ∀ n : ℕ, apSigmaLambertThetaResidualZ n = 0) :
    apSigmaLambertFactor = etaQuotientProductSide := by
  exact apSigmaLambertFactor_eq_etaQuotientProductSide_of_satisfies_thetaLog
    (apSigmaLambertFactor_satisfies_thetaLog_of_residual_zero hres)

/-- The elementary product-splitting route is equivalent to the same explicit
all-degree AP-sigma theta-log residual. -/
theorem apSigmaLambertFactor_eq_etaQuotientProductSide_iff_residual_zero :
    apSigmaLambertFactor = etaQuotientProductSide ↔
      ∀ n : ℕ, apSigmaLambertThetaResidualZ n = 0 := by
  constructor
  · intro h n
    exact apSigmaLambertThetaResidualZ_eq_zero_of_satisfies_thetaLog
      (by
        rw [h]
        exact etaQuotientProductSide_satisfies_apSigmaLambertThetaLog) n
  · intro hres
    exact apSigmaLambertFactor_eq_etaQuotientProductSide_of_residual_zero hres

/-- Thus the proposed thetaOp-image check is not a weaker target: it is
equivalent to the existing all-degree AP-sigma residual. -/
theorem thetaOp_apSigmaLambertFactor_eq_thetaOp_etaQuotientProductSide_iff_residual_zero :
    thetaOp apSigmaLambertFactor = thetaOp etaQuotientProductSide ↔
      ∀ n : ℕ, apSigmaLambertThetaResidualZ n = 0 := by
  rw [← apSigmaLambertFactor_eq_etaQuotientProductSide_iff_thetaOp_eq]
  exact apSigmaLambertFactor_eq_etaQuotientProductSide_iff_residual_zero

/-- Equivalently, the AP-sigma factor equals the fully split product iff the
explicit residual vanishes in every degree. -/
theorem apSigmaLambertFactor_eq_etaQuotientProductSplit_iff_residual_zero :
    apSigmaLambertFactor = etaQuotientProductSplit ↔
      ∀ n : ℕ, apSigmaLambertThetaResidualZ n = 0 := by
  rw [etaQuotientProductSplit_eq_etaQuotientProductSide]
  exact apSigmaLambertFactor_eq_etaQuotientProductSide_iff_residual_zero

theorem apSigmaLambert_mul_expandFive_satisfies_thetaLog_of_factor
    (hA :
      SatisfiesThetaLogRecurrence apSigmaLambertThetaDriver apSigmaLambertFactor) :
    SatisfiesThetaLogRecurrence qPochPowFiveThetaDriver
      (apSigmaLambertFactor * expandFiveQpochRat) := by
  have hmul := satisfiesThetaLogRecurrence_mul hA expandFiveQpochRat_satisfies_thetaLog
  convert hmul using 1
  ring

@[simp] theorem coeff_zero_apSigmaLambertFactor :
    apSigmaLambertFactor.coeff 0 = 1 := by
  rw [coeff_apSigmaLambertFactor]
  norm_num [apSigmaLambertCoeffZ]

@[simp] theorem coeff_zero_apSigmaLambertFactor_mul_expandFive :
    (apSigmaLambertFactor * expandFiveQpochRat).coeff 0 = 1 := by
  rw [coeff_apSigmaLambertFactor_mul_expandFive]
  native_decide

@[simp] theorem coeff_zero_qPochPowFive :
    ((qPochInfPS ℚ) ^ 5).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [coeff_zero_qPochInfPS]
  norm_num

/-- Recurrence-uniqueness closure for the remaining eta-quotient identity.
The only arithmetic input still missing is the all-degree theta-log recurrence
for the AP-sigma Lambert factor itself. -/
theorem apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_of_factor_thetaLog
    (hA :
      SatisfiesThetaLogRecurrence apSigmaLambertThetaDriver apSigmaLambertFactor) :
    apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5 := by
  apply eq_of_same_thetaLogRecurrence (A := qPochPowFiveThetaDriver)
  · simp
  · exact apSigmaLambert_mul_expandFive_satisfies_thetaLog_of_factor hA
  · exact qPochPowFive_satisfies_thetaLog
  · simp

/-- Residual form of the eta-quotient closure: proving the explicit integer
recurrence residual in every degree gives
`apSigmaLambertFactor * (q^5;q^5)_∞ = (q;q)_∞^5`. -/
theorem apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_of_residual_zero
    (hres : ∀ n : ℕ, apSigmaLambertThetaResidualZ n = 0) :
    apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5 := by
  exact apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_of_factor_thetaLog
    (apSigmaLambertFactor_satisfies_thetaLog_of_residual_zero hres)

/-- Conversely, the multiplicative eta identity forces the theta-log
recurrence for the AP-sigma Lambert factor.  This is the cancellation form of
the direct-product route: once
`apSigmaLambertFactor * (q^5;q^5)_∞ = (q;q)_∞^5` is proved, the missing
recurrence follows without coefficient computation. -/
theorem apSigmaLambertFactor_satisfies_thetaLog_of_mul_expandFive_eq_qPoch_pow_five
    (h :
      apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5) :
    SatisfiesThetaLogRecurrence apSigmaLambertThetaDriver apSigmaLambertFactor := by
  unfold SatisfiesThetaLogRecurrence
  apply isUnit_expandFiveQpochRat.mul_left_inj.mp
  have hprod :
      thetaOp (apSigmaLambertFactor * expandFiveQpochRat) =
        qPochPowFiveThetaDriver * (apSigmaLambertFactor * expandFiveQpochRat) := by
    rw [h]
    exact qPochPowFive_satisfies_thetaLog
  have hE :
      thetaOp expandFiveQpochRat =
        -(apDivisorSigmaPS ℚ 5 5) * expandFiveQpochRat := by
    exact expandFiveQpochRat_satisfies_thetaLog
  calc
    thetaOp apSigmaLambertFactor * expandFiveQpochRat
        = thetaOp (apSigmaLambertFactor * expandFiveQpochRat) -
            apSigmaLambertFactor * thetaOp expandFiveQpochRat := by
            rw [thetaOp_mul]
            ring
    _ = qPochPowFiveThetaDriver *
            (apSigmaLambertFactor * expandFiveQpochRat) -
          apSigmaLambertFactor *
            (-(apDivisorSigmaPS ℚ 5 5) * expandFiveQpochRat) := by
            rw [hprod, hE]
    _ = (apSigmaLambertThetaDriver * apSigmaLambertFactor) *
          expandFiveQpochRat := by
            unfold apSigmaLambertThetaDriver
            ring

/-- The recurrence gap and the multiplicative eta-quotient gap are equivalent.
This lets later work choose either a formal ODE proof of the AP-sigma Lambert
factor or a direct Euler-product/Jacobi-product proof of the eta identity. -/
theorem apSigmaLambertFactor_satisfies_thetaLog_iff_mul_expandFive_eq_qPoch_pow_five :
    SatisfiesThetaLogRecurrence apSigmaLambertThetaDriver apSigmaLambertFactor ↔
      apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5 := by
  constructor
  · exact apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_of_factor_thetaLog
  · exact apSigmaLambertFactor_satisfies_thetaLog_of_mul_expandFive_eq_qPoch_pow_five

/-- The explicit theta-log residual gap and the direct eta-product coefficient
gap are equivalent.  This records that the remaining arithmetic problem can be
attacked either through the first-order theta-log recurrence or directly
through coefficients of
`apSigmaLambertFactor * (X^5;X^5)_∞ = (X;X)_∞^5`. -/
theorem apSigmaLambertThetaResidualZ_zero_iff_direct_gap_zero :
    (∀ n : ℕ, apSigmaLambertThetaResidualZ n = 0) ↔
      ∀ n : ℕ, apSigmaEtaProductCoeffGapZ n = 0 := by
  constructor
  · intro hres
    exact
      apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_iff_direct_gap_zero.mp
        (apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_of_residual_zero hres)
  · intro hgap n
    exact apSigmaLambertThetaResidualZ_eq_zero_of_satisfies_thetaLog
      (apSigmaLambertFactor_satisfies_thetaLog_of_mul_expandFive_eq_qPoch_pow_five
        (apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_iff_direct_gap_zero.mpr hgap)) n

/-- Generic finite-certificate closure for an eventually linear backward
recurrence over integer sequences.  Once every term above `B` is a fixed
linear combination of earlier terms, zeros through `B` force all terms to be
zero. -/
theorem int_sequence_eq_zero_of_eventual_linear_recurrence
    (u c : ℕ → ℤ) (d B : ℕ)
    (hbase : ∀ n : ℕ, n ≤ B → u n = 0)
    (hrec : ∀ n : ℕ, B < n →
      u n = ∑ i ∈ Finset.range d, c i * u (n - (i + 1))) :
    ∀ n : ℕ, u n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnB : n ≤ B
      · exact hbase n hnB
      · have hBn : B < n := Nat.lt_of_not_ge hnB
        rw [hrec n hBn]
        apply Finset.sum_eq_zero
        intro i hi
        have hlt : n - (i + 1) < n := by
          have hnpos : 0 < n := by omega
          omega
        rw [ih (n - (i + 1)) hlt, mul_zero]

/-- Residual-specific version of the finite-certificate route: the existing
native certificate through degree `200` will imply the all-degree residual
once an explicit finite backward recurrence is proved for degrees above `200`. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_of_linear_recurrence_after_twohundred
    (c : ℕ → ℤ) (d : ℕ)
    (hrec : ∀ n : ℕ, 200 < n →
      apSigmaLambertThetaResidualZ n =
        ∑ i ∈ Finset.range d, c i * apSigmaLambertThetaResidualZ (n - (i + 1))) :
    ∀ n : ℕ, apSigmaLambertThetaResidualZ n = 0 := by
  exact int_sequence_eq_zero_of_eventual_linear_recurrence
    apSigmaLambertThetaResidualZ c d 200
    apSigmaLambertThetaResidualZ_eq_zero_le_twohundred hrec

/-- Diagnostic for the finite-recurrence route: with the existing certificate
through degree `200`, the first nontrivial recurrence step already has to prove
the degree-`201` residual.  Thus a guessed recurrence cannot add information
unless its `n = 201` instance is proved by genuine arithmetic. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_201_of_linear_recurrence_after_twohundred
    (c : ℕ → ℤ) (d : ℕ)
    (hrec : ∀ n : ℕ, 200 < n →
      apSigmaLambertThetaResidualZ n =
        ∑ i ∈ Finset.range d, c i * apSigmaLambertThetaResidualZ (n - (i + 1))) :
    apSigmaLambertThetaResidualZ 201 = 0 := by
  rw [hrec 201 (by norm_num)]
  apply Finset.sum_eq_zero
  intro i _hi
  have hle : 201 - (i + 1) ≤ 200 := by omega
  rw [apSigmaLambertThetaResidualZ_eq_zero_le_twohundred (201 - (i + 1)) hle,
    mul_zero]

/-- Rational/P-recursive analogue of the degree-`201` diagnostic: a recurrence
valid only above the checked range contributes new information exactly through
its first unchecked instance. -/
theorem apSigmaLambertThetaResidualZ_eq_zero_201_of_rational_recurrence_after_twohundred
    (c : ℕ → ℕ → ℚ) (d : ℕ) (_hd : d < 200)
    (hrec : ∀ n : ℕ, 200 < n →
      (apSigmaLambertThetaResidualZ n : ℚ) =
        ∑ i ∈ Finset.range d, c n i *
          (apSigmaLambertThetaResidualZ (n - (i + 1)) : ℚ)) :
    apSigmaLambertThetaResidualZ 201 = 0 := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
  rw [hrec 201 (by norm_num)]
  apply Finset.sum_eq_zero
  intro i _hi
  have hle : 201 - (i + 1) ≤ 200 := by omega
  rw [apSigmaLambertThetaResidualZ_eq_zero_le_twohundred (201 - (i + 1)) hle]
  simp

/-! ## Gaussian-integer scaffolding for the 5-string proof -/

abbrev GaussianInt := ℤ × ℤ

/-- Multiplication in `ℤ[i]`, represented as pairs. -/
def gaussMul (z w : GaussianInt) : GaussianInt :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- Complex conjugation in `ℤ[i]`. -/
def gaussConj (z : GaussianInt) : GaussianInt :=
  (z.1, -z.2)

/-- Norm squared `a^2 + b^2` on `ℤ[i]`. -/
def gaussNormSq (z : GaussianInt) : ℤ :=
  z.1 ^ 2 + z.2 ^ 2

def pi5 : GaussianInt := (1, 2)

def piBar5 : GaussianInt := (1, -2)

def gaussOne : GaussianInt := (1, 0)

def gaussPow (z : GaussianInt) : ℕ → GaussianInt
| 0 => gaussOne
| n + 1 => gaussMul z (gaussPow z n)

/-- The point `π^j * πbar^(t-j) * g` in the 5-string. -/
def fiveStringPoint (g : GaussianInt) (t j : ℕ) : GaussianInt :=
  gaussMul (gaussMul (gaussPow pi5 j) (gaussPow piBar5 (t - j))) g

/-- The scalar recurrence from the 5-string blueprint. -/
def fiveStringC : ℕ → ℤ
| 0 => 1
| 1 => -6
| n + 2 => -6 * fiveStringC (n + 1) - 25 * fiveStringC n

/-- Multiplication by the four units `1,i,-1,-i`. -/
def gaussUnitRotate (i : Fin 4) (z : GaussianInt) : GaussianInt :=
  match i.1 with
  | 0 => z
  | 1 => (-z.2, z.1)
  | 2 => (-z.1, -z.2)
  | _ => (z.2, -z.1)

/-- `(-1)^(a+1)`, expressed by parity. -/
def gaussEps (a : ℤ) : ℤ :=
  if a % 2 = 0 then -1 else 1

/-- Jacobi-side representation weight. -/
def gaussH (z : GaussianInt) : ℤ :=
  gaussEps z.1 * (z.1 ^ 2 - z.2 ^ 2)

/-- Parity sign for an integer quotient. -/
def paritySign (n : ℤ) : ℤ :=
  if n % 2 = 0 then 1 else -1

/-- Wronskian-side weight attached to one rotated `(R,S)` pair.  The condition
`x ≡ 2 (mod 5)` is the congruence `x = 10m - 3` from the blueprint, with
`x = R - 2S`, `y = 2R + S`. -/
def wronskianRSWeight (R S : ℤ) : ℤ :=
  let x := R - 2 * S
  let y := 2 * R + S
  if x % 5 = 2 then
    paritySign ((x + y + 4) / 10) * ((x ^ 2 - y ^ 2) / 8)
  else
    0

/-- Wronskian-side representation weight, summing over the four unit rotations
of `(R,S) = (A-B,A+B)`. -/
def gaussK (z : GaussianInt) : ℤ :=
  ∑ i : Fin 4,
    let RS := gaussUnitRotate i (z.1 - z.2, z.1 + z.2)
    wronskianRSWeight RS.1 RS.2

def unitConjOrbitH (z : GaussianInt) : ℤ :=
  (∑ i : Fin 4, gaussH (gaussUnitRotate i z)) +
    ∑ i : Fin 4, gaussH (gaussUnitRotate i (gaussConj z))

def unitConjOrbitK (z : GaussianInt) : ℤ :=
  (∑ i : Fin 4, gaussK (gaussUnitRotate i z)) +
    ∑ i : Fin 4, gaussK (gaussUnitRotate i (gaussConj z))

theorem gaussNormSq_mul (z w : GaussianInt) :
    gaussNormSq (gaussMul z w) = gaussNormSq z * gaussNormSq w := by
  unfold gaussNormSq gaussMul
  ring

theorem gaussMul_assoc (z w u : GaussianInt) :
    gaussMul (gaussMul z w) u = gaussMul z (gaussMul w u) := by
  rcases z with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  rcases u with ⟨e, f⟩
  ext
  · simp [gaussMul]
    ring
  · simp [gaussMul]
    ring

@[simp] theorem gaussNormSq_pi5 : gaussNormSq pi5 = 5 := by
  norm_num [gaussNormSq, pi5]

@[simp] theorem gaussNormSq_piBar5 : gaussNormSq piBar5 = 5 := by
  norm_num [gaussNormSq, piBar5]

@[simp] theorem gaussMul_pi5_piBar5 : gaussMul pi5 piBar5 = (5, 0) := by
  norm_num [gaussMul, pi5, piBar5]

@[simp] theorem gaussMul_one_left (z : GaussianInt) :
    gaussMul gaussOne z = z := by
  cases z
  simp [gaussMul, gaussOne]

@[simp] theorem gaussMul_one_right (z : GaussianInt) :
    gaussMul z gaussOne = z := by
  cases z
  simp [gaussMul, gaussOne]

@[simp] theorem fiveStringC_zero : fiveStringC 0 = 1 := rfl

@[simp] theorem fiveStringC_one : fiveStringC 1 = -6 := rfl

@[simp] theorem fiveStringPoint_t0 (g : GaussianInt) :
    fiveStringPoint g 0 0 = g := by
  simp [fiveStringPoint, gaussPow]

/-- The Jacobi-side part of the `t=0` string identity. -/
theorem fiveString_t0_H_identity (g : GaussianInt) :
    gaussH g + gaussH (gaussConj g) =
      2 * gaussEps g.1 * (g.1 ^ 2 - g.2 ^ 2) := by
  simp [gaussH, gaussConj]
  ring

@[simp] theorem gaussEps_neg (a : ℤ) : gaussEps (-a) = gaussEps a := by
  unfold gaussEps
  by_cases h : a % 2 = 0
  · have hneg : (-a) % 2 = 0 := by omega
    simp [h, hneg]
  · have hneg : (-a) % 2 ≠ 0 := by omega
    simp [h]

/-- Closed form for the Jacobi weight over the four unit rotations. -/
theorem unitOrbitH_closed (a b : ℤ) :
    (∑ i : Fin 4, gaussH (gaussUnitRotate i (a,b))) =
      2 * (gaussEps a - gaussEps b) * (a ^ 2 - b ^ 2) := by
  rw [Fin.sum_univ_four]
  simp [gaussH, gaussUnitRotate]
  ring

/-- If the two coordinates have opposite `gaussEps`, the four unit rotations
contribute the expected single-coordinate form. -/
theorem unitOrbitH_closed_of_eps_opposite {a b : ℤ}
    (hba : gaussEps b = -gaussEps a) :
    (∑ i : Fin 4, gaussH (gaussUnitRotate i (a,b))) =
      4 * gaussEps a * (a ^ 2 - b ^ 2) := by
  rw [unitOrbitH_closed, hba]
  ring

/-- Closed form for the Jacobi weight over unit rotations and conjugation. -/
theorem unitConjOrbitH_closed (a b : ℤ) :
    unitConjOrbitH (a,b) =
      4 * (gaussEps a - gaussEps b) * (a ^ 2 - b ^ 2) := by
  simp [unitConjOrbitH]
  rw [unitOrbitH_closed]
  rw [Fin.sum_univ_four]
  simp [gaussH, gaussUnitRotate, gaussConj]
  ring

/-- Conjugation doubles the four-unit orbit contribution. -/
theorem unitConjOrbitH_closed_of_eps_opposite {a b : ℤ}
    (hba : gaussEps b = -gaussEps a) :
    unitConjOrbitH (a,b) = 8 * gaussEps a * (a ^ 2 - b ^ 2) := by
  rw [unitConjOrbitH_closed, hba]
  ring

/-- Local simplification of a selected Wronskian `(R,S)` term. -/
theorem wronskianRSWeight_of_selector {R S : ℤ}
    (h : (R - 2 * S) % 5 = 2) :
    wronskianRSWeight R S =
      paritySign (((R - 2 * S) + (2 * R + S) + 4) / 10) *
        ((((R - 2 * S) ^ 2) - ((2 * R + S) ^ 2)) / 8) := by
  simp [wronskianRSWeight, h]

/-- Local simplification of an unselected Wronskian `(R,S)` term. -/
theorem wronskianRSWeight_of_not_selector {R S : ℤ}
    (h : (R - 2 * S) % 5 ≠ 2) :
    wronskianRSWeight R S = 0 := by
  simp [wronskianRSWeight, h]

/-- The four Wronskian rotations of `(R,S)=(a-b,a+b)` in explicit form. -/
theorem gaussK_explicit (a b : ℤ) :
    gaussK (a,b) =
      wronskianRSWeight (a - b) (a + b) +
      wronskianRSWeight (-(a + b)) (a - b) +
      wronskianRSWeight (-(a - b)) (-(a + b)) +
      wronskianRSWeight (a + b) (-(a - b)) := by
  unfold gaussK
  rw [Fin.sum_univ_four]
  simp [gaussUnitRotate]

theorem wronskianRSWeight_rot0_of_selector {a b : ℤ}
    (h : (-a - 3 * b) % 5 = 2) :
    wronskianRSWeight (a - b) (a + b) =
      paritySign ((2 * a - 4 * b + 4) / 10) *
        (((-a - 3 * b) ^ 2 - (3 * a - b) ^ 2) / 8) := by
  rw [wronskianRSWeight_of_selector]
  · ring_nf
  · have hx : ((a - b) - 2 * (a + b)) % 5 = (-a - 3 * b) % 5 := by omega
    rw [hx]
    exact h

theorem wronskianRSWeight_rot0_of_not_selector {a b : ℤ}
    (h : (-a - 3 * b) % 5 ≠ 2) :
    wronskianRSWeight (a - b) (a + b) = 0 := by
  apply wronskianRSWeight_of_not_selector
  have hx : ((a - b) - 2 * (a + b)) % 5 = (-a - 3 * b) % 5 := by omega
  rw [hx]
  exact h

theorem wronskianRSWeight_rot1_of_selector {a b : ℤ}
    (h : (-3 * a + b) % 5 = 2) :
    wronskianRSWeight (-(a + b)) (a - b) =
      paritySign ((-4 * a - 2 * b + 4) / 10) *
        (((-3 * a + b) ^ 2 - (-a - 3 * b) ^ 2) / 8) := by
  rw [wronskianRSWeight_of_selector]
  · ring_nf
  · have hx : ((-(a + b)) - 2 * (a - b)) % 5 = (-3 * a + b) % 5 := by omega
    rw [hx]
    exact h

theorem wronskianRSWeight_rot1_of_not_selector {a b : ℤ}
    (h : (-3 * a + b) % 5 ≠ 2) :
    wronskianRSWeight (-(a + b)) (a - b) = 0 := by
  apply wronskianRSWeight_of_not_selector
  have hx : ((-(a + b)) - 2 * (a - b)) % 5 = (-3 * a + b) % 5 := by omega
  rw [hx]
  exact h

theorem wronskianRSWeight_rot2_of_selector {a b : ℤ}
    (h : (a + 3 * b) % 5 = 2) :
    wronskianRSWeight (-(a - b)) (-(a + b)) =
      paritySign ((-2 * a + 4 * b + 4) / 10) *
        (((a + 3 * b) ^ 2 - (-3 * a + b) ^ 2) / 8) := by
  rw [wronskianRSWeight_of_selector]
  · ring_nf
  · have hx : ((-(a - b)) - 2 * (-(a + b))) % 5 = (a + 3 * b) % 5 := by omega
    rw [hx]
    exact h

theorem wronskianRSWeight_rot2_of_not_selector {a b : ℤ}
    (h : (a + 3 * b) % 5 ≠ 2) :
    wronskianRSWeight (-(a - b)) (-(a + b)) = 0 := by
  apply wronskianRSWeight_of_not_selector
  have hx : ((-(a - b)) - 2 * (-(a + b))) % 5 = (a + 3 * b) % 5 := by omega
  rw [hx]
  exact h

theorem wronskianRSWeight_rot3_of_selector {a b : ℤ}
    (h : (3 * a - b) % 5 = 2) :
    wronskianRSWeight (a + b) (-(a - b)) =
      paritySign ((4 * a + 2 * b + 4) / 10) *
        (((3 * a - b) ^ 2 - (a + 3 * b) ^ 2) / 8) := by
  rw [wronskianRSWeight_of_selector]
  · ring_nf
  · have hx : ((a + b) - 2 * (-(a - b))) % 5 = (3 * a - b) % 5 := by omega
    rw [hx]
    exact h

theorem wronskianRSWeight_rot3_of_not_selector {a b : ℤ}
    (h : (3 * a - b) % 5 ≠ 2) :
    wronskianRSWeight (a + b) (-(a - b)) = 0 := by
  apply wronskianRSWeight_of_not_selector
  have hx : ((a + b) - 2 * (-(a - b))) % 5 = (3 * a - b) % 5 := by omega
  rw [hx]
  exact h

/-- The mod-5 selectors for the four rotations in `gaussK (a,b)`. -/
def wronskianSelectorCount (a b : ℤ) : ℕ :=
  (if (-a - 3 * b) % 5 = 2 then 1 else 0) +
  (if (-3 * a + b) % 5 = 2 then 1 else 0) +
  (if (a + 3 * b) % 5 = 2 then 1 else 0) +
  (if (3 * a - b) % 5 = 2 then 1 else 0)

/-- The mod-5 selector table: if `a²+b²` is not divisible by `5`, exactly one
of the four rotations in `gaussK (a,b)` is selected. -/
theorem wronskianSelectorCount_residue_check :
    ∀ a b : Fin 5,
      (((a : ℤ) ^ 2 + (b : ℤ) ^ 2) % 5 ≠ 0) →
      wronskianSelectorCount (a : ℤ) (b : ℤ) = 1 := by
  native_decide

/-- Finite residue sanity check for the `t=0` unit-plus-conjugate orbit
identity.  This is not the all-integer orbit theorem; it verifies the complete
mod-20 sign/congruence table used by the intended proof. -/
theorem fiveString_t0_residue_orbit_check :
    ∀ a b : Fin 20,
      (gaussNormSq ((a : ℤ), (b : ℤ)) % 2 = 1 ∧
        gaussNormSq ((a : ℤ), (b : ℤ)) % 5 ≠ 0) →
      unitConjOrbitH ((a : ℤ), (b : ℤ)) =
        unitConjOrbitK ((a : ℤ), (b : ℤ)) := by
  native_decide

theorem gaussEps_opposite_of_norm_odd {a b : ℤ}
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1) :
    gaussEps b = -gaussEps a := by
  let qa := a / 2
  let qb := b / 2
  let ra := a % 2
  let rb := b % 2
  have hra_nonneg : 0 ≤ ra := by
    exact Int.emod_nonneg a (by norm_num : (2 : ℤ) ≠ 0)
  have hra_lt : ra < 2 := by
    exact Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 2)
  have hrb_nonneg : 0 ≤ rb := by
    exact Int.emod_nonneg b (by norm_num : (2 : ℤ) ≠ 0)
  have hrb_lt : rb < 2 := by
    exact Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 2)
  have ha : a = 2 * qa + ra := by
    calc
      a = 2 * (a / 2) + a % 2 := by rw [Int.mul_ediv_add_emod]
      _ = 2 * qa + ra := by rfl
  have hb : b = 2 * qb + rb := by
    calc
      b = 2 * (b / 2) + b % 2 := by rw [Int.mul_ediv_add_emod]
      _ = 2 * qb + rb := by rfl
  rw [ha, hb] at hodd ⊢
  interval_cases ra <;> interval_cases rb <;> simp [gaussEps] at hodd ⊢
  all_goals try ring_nf at hodd
  all_goals omega

def wronskianCore (a b : ℤ) : ℤ :=
  (((-a - 3 * b) ^ 2 - (3 * a - b) ^ 2) / 8)

theorem wronskianCore_num_dvd_eight_of_norm_odd {a b : ℤ}
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1) :
    8 ∣ ((-a - 3 * b) ^ 2 - (3 * a - b) ^ 2) := by
  let qa := a / 2
  let qb := b / 2
  let ra := a % 2
  let rb := b % 2
  have hra_nonneg : 0 ≤ ra := by
    exact Int.emod_nonneg a (by norm_num : (2 : ℤ) ≠ 0)
  have hra_lt : ra < 2 := by
    exact Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 2)
  have hrb_nonneg : 0 ≤ rb := by
    exact Int.emod_nonneg b (by norm_num : (2 : ℤ) ≠ 0)
  have hrb_lt : rb < 2 := by
    exact Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 2)
  have ha : a = 2 * qa + ra := by
    calc
      a = 2 * (a / 2) + a % 2 := by rw [Int.mul_ediv_add_emod]
      _ = 2 * qa + ra := by rfl
  have hb : b = 2 * qb + rb := by
    calc
      b = 2 * (b / 2) + b % 2 := by rw [Int.mul_ediv_add_emod]
      _ = 2 * qb + rb := by rfl
  rw [ha, hb] at hodd ⊢
  interval_cases ra <;> interval_cases rb
  · ring_nf at hodd
    omega
  · use -4 * qa ^ 2 + 6 * qa * qb + 3 * qa + 4 * qb ^ 2 + 4 * qb + 1
    ring_nf
  · use -4 * qa ^ 2 - 4 * qa - 1 + 6 * qa * qb + 3 * qb + 4 * qb ^ 2
    ring_nf
  · ring_nf at hodd
    omega

theorem wronskianCore_row1 {a b : ℤ}
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1) :
    (((-3 * a + b) ^ 2 - (-a - 3 * b) ^ 2) / 8) =
      -wronskianCore a b := by
  have hdiv : 8 ∣ ((-a - 3 * b) ^ 2 - (3 * a - b) ^ 2) :=
    wronskianCore_num_dvd_eight_of_norm_odd (a := a) (b := b) hodd
  unfold wronskianCore
  rw [show ((-3 * a + b) ^ 2 - (-a - 3 * b) ^ 2) =
      -((-a - 3 * b) ^ 2 - (3 * a - b) ^ 2) by ring]
  exact Int.neg_ediv_of_dvd hdiv

theorem wronskianCore_row2 (a b : ℤ) :
    (((a + 3 * b) ^ 2 - (-3 * a + b) ^ 2) / 8) =
      wronskianCore a b := by
  unfold wronskianCore
  ring_nf

theorem wronskianCore_row3 {a b : ℤ}
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1) :
    (((3 * a - b) ^ 2 - (a + 3 * b) ^ 2) / 8) =
      -wronskianCore a b := by
  have hdiv : 8 ∣ ((-a - 3 * b) ^ 2 - (3 * a - b) ^ 2) :=
    wronskianCore_num_dvd_eight_of_norm_odd (a := a) (b := b) hodd
  unfold wronskianCore
  rw [show ((3 * a - b) ^ 2 - (a + 3 * b) ^ 2) =
      -((-a - 3 * b) ^ 2 - (3 * a - b) ^ 2) by ring]
  exact Int.neg_ediv_of_dvd hdiv

theorem paritySign_rot0_of_selector {a b : ℤ}
    (h : (-a - 3 * b) % 5 = 2) :
    paritySign ((2 * a - 4 * b + 4) / 10) = -gaussEps a := by
  unfold gaussEps paritySign
  by_cases ha : a % 2 = 0
  · simp [ha]
    omega
  · simp [ha]
    omega

theorem paritySign_rot1_of_selector {a b : ℤ}
    (h : (-3 * a + b) % 5 = 2)
    (hopp : gaussEps b = -gaussEps a) :
    paritySign ((-4 * a - 2 * b + 4) / 10) = gaussEps a := by
  unfold gaussEps at hopp ⊢
  unfold paritySign
  by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0
  · simp [ha, hb] at hopp
  · simp [ha]
    omega
  · simp [ha]
    omega
  · simp [ha, hb] at hopp

theorem paritySign_rot2_of_selector {a b : ℤ}
    (h : (a + 3 * b) % 5 = 2) :
    paritySign ((-2 * a + 4 * b + 4) / 10) = -gaussEps a := by
  unfold gaussEps paritySign
  by_cases ha : a % 2 = 0
  · simp [ha]
    omega
  · simp [ha]
    omega

theorem paritySign_rot3_of_selector {a b : ℤ}
    (h : (3 * a - b) % 5 = 2)
    (hopp : gaussEps b = -gaussEps a) :
    paritySign ((4 * a + 2 * b + 4) / 10) = gaussEps a := by
  unfold gaussEps at hopp ⊢
  unfold paritySign
  by_cases ha : a % 2 = 0 <;> by_cases hb : b % 2 = 0
  · simp [ha, hb] at hopp
  · simp [ha]
    omega
  · simp [ha]
    omega
  · simp [ha, hb] at hopp

theorem gaussK_of_rot0_selector {a b : ℤ}
    (h0 : (-a - 3 * b) % 5 = 2) :
    gaussK (a,b) =
      paritySign ((2 * a - 4 * b + 4) / 10) *
        (((-a - 3 * b) ^ 2 - (3 * a - b) ^ 2) / 8) := by
  rw [gaussK_explicit]
  rw [wronskianRSWeight_rot0_of_selector h0]
  rw [wronskianRSWeight_rot1_of_not_selector]
  · rw [wronskianRSWeight_rot2_of_not_selector]
    · rw [wronskianRSWeight_rot3_of_not_selector]
      · ring
      · omega
    · omega
  · omega

theorem gaussK_of_rot1_selector {a b : ℤ}
    (h1 : (-3 * a + b) % 5 = 2) :
    gaussK (a,b) =
      paritySign ((-4 * a - 2 * b + 4) / 10) *
        (((-3 * a + b) ^ 2 - (-a - 3 * b) ^ 2) / 8) := by
  rw [gaussK_explicit]
  rw [wronskianRSWeight_rot0_of_not_selector]
  · rw [wronskianRSWeight_rot1_of_selector h1]
    rw [wronskianRSWeight_rot2_of_not_selector]
    · rw [wronskianRSWeight_rot3_of_not_selector]
      · ring
      · omega
    · omega
  · omega

theorem gaussK_of_rot2_selector {a b : ℤ}
    (h2 : (a + 3 * b) % 5 = 2) :
    gaussK (a,b) =
      paritySign ((-2 * a + 4 * b + 4) / 10) *
        (((a + 3 * b) ^ 2 - (-3 * a + b) ^ 2) / 8) := by
  rw [gaussK_explicit]
  rw [wronskianRSWeight_rot0_of_not_selector]
  · rw [wronskianRSWeight_rot1_of_not_selector]
    · rw [wronskianRSWeight_rot2_of_selector h2]
      rw [wronskianRSWeight_rot3_of_not_selector]
      · ring
      · omega
    · omega
  · omega

theorem gaussK_of_rot3_selector {a b : ℤ}
    (h3 : (3 * a - b) % 5 = 2) :
    gaussK (a,b) =
      paritySign ((4 * a + 2 * b + 4) / 10) *
        (((3 * a - b) ^ 2 - (a + 3 * b) ^ 2) / 8) := by
  rw [gaussK_explicit]
  rw [wronskianRSWeight_rot0_of_not_selector]
  · rw [wronskianRSWeight_rot1_of_not_selector]
    · rw [wronskianRSWeight_rot2_of_not_selector]
      · rw [wronskianRSWeight_rot3_of_selector h3]
        ring
      · omega
    · omega
  · omega

theorem gaussK_eq_zero_of_no_selector {a b : ℤ}
    (h0 : (-a - 3 * b) % 5 ≠ 2)
    (h1 : (-3 * a + b) % 5 ≠ 2)
    (h2 : (a + 3 * b) % 5 ≠ 2)
    (h3 : (3 * a - b) % 5 ≠ 2) :
    gaussK (a,b) = 0 := by
  rw [gaussK_explicit]
  rw [wronskianRSWeight_rot0_of_not_selector h0]
  rw [wronskianRSWeight_rot1_of_not_selector]
  · rw [wronskianRSWeight_rot2_of_not_selector]
    · rw [wronskianRSWeight_rot3_of_not_selector]
      · ring
      · exact h3
    · exact h2
  · exact h1

theorem wronskianSelector_exists_zmod5 :
    ∀ x y : ZMod 5,
      x ^ 2 + y ^ 2 ≠ 0 →
      -x - 3 * y = 2 ∨ -3 * x + y = 2 ∨
        x + 3 * y = 2 ∨ 3 * x - y = 2 := by
  native_decide

theorem wronskianSelector_exists_int (a b : ℤ)
    (h5 : (a ^ 2 + b ^ 2) % 5 ≠ 0) :
    (-a - 3 * b) % 5 = 2 ∨ (-3 * a + b) % 5 = 2 ∨
      (a + 3 * b) % 5 = 2 ∨ (3 * a - b) % 5 = 2 := by
  let ra := a % 5
  let rb := b % 5
  have hra_nonneg : 0 ≤ ra := Int.emod_nonneg a (by norm_num : (5 : ℤ) ≠ 0)
  have hra_lt : ra < 5 := Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 5)
  have hrb_nonneg : 0 ≤ rb := Int.emod_nonneg b (by norm_num : (5 : ℤ) ≠ 0)
  have hrb_lt : rb < 5 := Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 5)
  have ha : a = 5 * (a / 5) + ra := by
    calc
      a = 5 * (a / 5) + a % 5 := by rw [Int.mul_ediv_add_emod]
      _ = 5 * (a / 5) + ra := by rfl
  have hb : b = 5 * (b / 5) + rb := by
    calc
      b = 5 * (b / 5) + b % 5 := by rw [Int.mul_ediv_add_emod]
      _ = 5 * (b / 5) + rb := by rfl
  rw [ha, hb] at h5 ⊢
  interval_cases ra <;> interval_cases rb <;> simp at h5 ⊢
  all_goals try ring_nf at h5 ⊢
  all_goals omega

theorem pi5Selector_exists_zmod5 :
    ∀ x y : ZMod 5,
      x ^ 2 + y ^ 2 ≠ 0 →
      (-(x - 2 * y) - 3 * (2 * x + y) = 2) ∨
        (-3 * (x - 2 * y) + (2 * x + y) = 2) ∨
        ((x - 2 * y) + 3 * (2 * x + y) = 2) ∨
        (3 * (x - 2 * y) - (2 * x + y) = 2) := by
  native_decide

theorem pi5Selector_exists_int (a b : ℤ)
    (h5 : (a ^ 2 + b ^ 2) % 5 ≠ 0) :
    (-(a - 2 * b) - 3 * (2 * a + b)) % 5 = 2 ∨
      (-3 * (a - 2 * b) + (2 * a + b)) % 5 = 2 ∨
      ((a - 2 * b) + 3 * (2 * a + b)) % 5 = 2 ∨
      (3 * (a - 2 * b) - (2 * a + b)) % 5 = 2 := by
  let ra := a % 5
  let rb := b % 5
  have hra_nonneg : 0 ≤ ra := Int.emod_nonneg a (by norm_num : (5 : ℤ) ≠ 0)
  have hra_lt : ra < 5 := Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 5)
  have hrb_nonneg : 0 ≤ rb := Int.emod_nonneg b (by norm_num : (5 : ℤ) ≠ 0)
  have hrb_lt : rb < 5 := Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 5)
  have ha : a = 5 * (a / 5) + ra := by
    calc
      a = 5 * (a / 5) + a % 5 := by rw [Int.mul_ediv_add_emod]
      _ = 5 * (a / 5) + ra := by rfl
  have hb : b = 5 * (b / 5) + rb := by
    calc
      b = 5 * (b / 5) + b % 5 := by rw [Int.mul_ediv_add_emod]
      _ = 5 * (b / 5) + rb := by rfl
  rw [ha, hb] at h5 ⊢
  interval_cases ra <;> interval_cases rb <;> simp at h5 ⊢
  all_goals try ring_nf at h5 ⊢
  all_goals omega

theorem gaussK_t0_core (a b : ℤ)
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1)
    (h5 : (a ^ 2 + b ^ 2) % 5 ≠ 0) :
    gaussK (a,b) = -gaussEps a * wronskianCore a b := by
  have hopp : gaussEps b = -gaussEps a := gaussEps_opposite_of_norm_odd hodd
  rcases wronskianSelector_exists_int a b h5 with h0 | h1 | h2 | h3
  · rw [gaussK_of_rot0_selector h0, paritySign_rot0_of_selector h0]
    unfold wronskianCore
    ring
  · rw [gaussK_of_rot1_selector h1, paritySign_rot1_of_selector h1 hopp,
      wronskianCore_row1 hodd]
    ring
  · rw [gaussK_of_rot2_selector h2, paritySign_rot2_of_selector h2,
      wronskianCore_row2]
  · rw [gaussK_of_rot3_selector h3, paritySign_rot3_of_selector h3 hopp,
      wronskianCore_row3 hodd]
    ring

theorem gaussK_eq_neg_eps_mul_core_of_selector {a b : ℤ}
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1)
    (hsel : (-a - 3 * b) % 5 = 2 ∨ (-3 * a + b) % 5 = 2 ∨
      (a + 3 * b) % 5 = 2 ∨ (3 * a - b) % 5 = 2) :
    gaussK (a,b) = -gaussEps a * wronskianCore a b := by
  have hopp : gaussEps b = -gaussEps a := gaussEps_opposite_of_norm_odd hodd
  rcases hsel with h0 | h1 | h2 | h3
  · rw [gaussK_of_rot0_selector h0, paritySign_rot0_of_selector h0]
    unfold wronskianCore
    ring
  · rw [gaussK_of_rot1_selector h1, paritySign_rot1_of_selector h1 hopp,
      wronskianCore_row1 hodd]
    ring
  · rw [gaussK_of_rot2_selector h2, paritySign_rot2_of_selector h2,
      wronskianCore_row2]
  · rw [gaussK_of_rot3_selector h3, paritySign_rot3_of_selector h3 hopp,
      wronskianCore_row3 hodd]
    ring

theorem wronskianCore_add_conj_of_norm_odd {a b : ℤ}
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1) :
    wronskianCore a b + wronskianCore a (-b) =
      -2 * (a ^ 2 - b ^ 2) := by
  let N : ℤ := ((-a - 3 * b) ^ 2 - (3 * a - b) ^ 2)
  let M : ℤ := ((-a - 3 * (-b)) ^ 2 - (3 * a - (-b)) ^ 2)
  have hNdiv : 8 ∣ N := by
    simpa [N] using wronskianCore_num_dvd_eight_of_norm_odd
      (a := a) (b := b) hodd
  have hodd_neg : (a ^ 2 + (-b) ^ 2) % 2 = 1 := by
    simpa using hodd
  have hMdiv : 8 ∣ M := by
    simpa [M] using wronskianCore_num_dvd_eight_of_norm_odd
      (a := a) (b := -b) hodd_neg
  unfold wronskianCore
  apply mul_left_cancel₀ (show (8 : ℤ) ≠ 0 by norm_num)
  rw [mul_add]
  rw [show 8 * (N / 8) = N by
    simpa [mul_comm] using Int.ediv_mul_cancel hNdiv]
  rw [show 8 * (M / 8) = M by
    simpa [mul_comm] using Int.ediv_mul_cancel hMdiv]
  simp [N, M]
  ring

theorem wronskianCore_pi5_conj_pair_of_norm_odd {a b : ℤ}
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1) :
    wronskianCore (a - 2 * b) (2 * a + b) +
        wronskianCore (a + 2 * b) (2 * a - b) =
      12 * (a ^ 2 - b ^ 2) := by
  let N : ℤ :=
    (-(a - 2 * b) - 3 * (2 * a + b)) ^ 2 -
      (3 * (a - 2 * b) - (2 * a + b)) ^ 2
  let M : ℤ :=
    (-(a + 2 * b) - 3 * (2 * a - b)) ^ 2 -
      (3 * (a + 2 * b) - (2 * a - b)) ^ 2
  have hodd_pi : ((a - 2 * b) ^ 2 + (2 * a + b) ^ 2) % 2 = 1 := by
    rw [show (a - 2 * b) ^ 2 + (2 * a + b) ^ 2 =
      5 * (a ^ 2 + b ^ 2) by ring]
    omega
  have hodd_pic : ((a + 2 * b) ^ 2 + (2 * a - b) ^ 2) % 2 = 1 := by
    rw [show (a + 2 * b) ^ 2 + (2 * a - b) ^ 2 =
      5 * (a ^ 2 + b ^ 2) by ring]
    omega
  have hNdiv : 8 ∣ N := by
    simpa [N] using wronskianCore_num_dvd_eight_of_norm_odd
      (a := a - 2 * b) (b := 2 * a + b) hodd_pi
  have hMdiv : 8 ∣ M := by
    simpa [M] using wronskianCore_num_dvd_eight_of_norm_odd
      (a := a + 2 * b) (b := 2 * a - b) hodd_pic
  unfold wronskianCore
  apply mul_left_cancel₀ (show (8 : ℤ) ≠ 0 by norm_num)
  rw [mul_add]
  rw [show 8 * (N / 8) = N by
    simpa [mul_comm] using Int.ediv_mul_cancel hNdiv]
  rw [show 8 * (M / 8) = M by
    simpa [mul_comm] using Int.ediv_mul_cancel hMdiv]
  simp [N, M]
  ring

theorem gaussK_conj_pair_t0_identity (a b : ℤ)
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1)
    (h5 : (a ^ 2 + b ^ 2) % 5 ≠ 0) :
    gaussK (a,b) + gaussK (a,-b) =
      (gaussEps a - gaussEps b) * (a ^ 2 - b ^ 2) := by
  have hopp : gaussEps b = -gaussEps a := gaussEps_opposite_of_norm_odd hodd
  have hodd_neg : (a ^ 2 + (-b) ^ 2) % 2 = 1 := by
    simpa using hodd
  have h5_neg : (a ^ 2 + (-b) ^ 2) % 5 ≠ 0 := by
    simpa using h5
  rw [gaussK_t0_core a b hodd h5,
    gaussK_t0_core a (-b) hodd_neg h5_neg]
  rw [show -gaussEps a * wronskianCore a b +
      -gaussEps a * wronskianCore a (-b) =
      -gaussEps a * (wronskianCore a b + wronskianCore a (-b)) by ring]
  rw [wronskianCore_add_conj_of_norm_odd hodd, hopp]
  ring

@[simp] theorem gaussK_rotate90 (a b : ℤ) :
    gaussK (-b,a) = gaussK (a,b) := by
  simp [gaussK_explicit]
  ring_nf

@[simp] theorem gaussK_rotate180 (a b : ℤ) :
    gaussK (-a,-b) = gaussK (a,b) := by
  simp [gaussK_explicit]
  ring_nf

@[simp] theorem gaussK_rotate270 (a b : ℤ) :
    gaussK (b,-a) = gaussK (a,b) := by
  simp [gaussK_explicit]
  ring_nf

theorem unitConjOrbitK_closed (a b : ℤ) :
    unitConjOrbitK (a,b) = 4 * (gaussK (a,b) + gaussK (a,-b)) := by
  unfold unitConjOrbitK
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  simp [gaussConj, gaussUnitRotate]
  ring

theorem fiveString_t0_unitConjOrbit_identity (a b : ℤ)
    (hodd : gaussNormSq (a,b) % 2 = 1)
    (h5 : gaussNormSq (a,b) % 5 ≠ 0) :
    unitConjOrbitK (a,b) = unitConjOrbitH (a,b) := by
  have hodd' : (a ^ 2 + b ^ 2) % 2 = 1 := by
    simpa [gaussNormSq] using hodd
  have h5' : (a ^ 2 + b ^ 2) % 5 ≠ 0 := by
    simpa [gaussNormSq] using h5
  rw [unitConjOrbitK_closed, unitConjOrbitH_closed,
    gaussK_conj_pair_t0_identity a b hodd' h5']
  ring

theorem gaussK_of_five_dvd_coords (a b : ℤ) :
    gaussK (5 * a, 5 * b) = 0 := by
  rw [gaussK_explicit]
  rw [wronskianRSWeight_rot0_of_not_selector]
  · rw [wronskianRSWeight_rot1_of_not_selector]
    · rw [wronskianRSWeight_rot2_of_not_selector]
      · rw [wronskianRSWeight_rot3_of_not_selector]
        · ring
        · omega
      · omega
    · omega
  · omega

theorem unitConjOrbitK_of_five_dvd_coords (a b : ℤ) :
    unitConjOrbitK (5 * a, 5 * b) = 0 := by
  rw [unitConjOrbitK_closed]
  simp [gaussK_of_five_dvd_coords]

@[simp] theorem gaussMul_five_left (z : GaussianInt) :
    gaussMul (5,0) z = (5 * z.1, 5 * z.2) := by
  cases z
  simp [gaussMul]

@[simp] theorem gaussMul_pi5_left (a b : ℤ) :
    gaussMul pi5 (a,b) = (a - 2 * b, 2 * a + b) := by
  unfold gaussMul pi5
  ext
  · ring
  · ring

@[simp] theorem gaussMul_piBar5_left (a b : ℤ) :
    gaussMul piBar5 (a,b) = (a + 2 * b, -2 * a + b) := by
  unfold gaussMul piBar5
  ext
  · ring
  · ring

theorem gaussK_piBar5_mul (a b : ℤ) :
    gaussK (gaussMul piBar5 (a,b)) = 0 := by
  rw [gaussMul_piBar5_left]
  rw [gaussK_explicit]
  rw [wronskianRSWeight_rot0_of_not_selector]
  · rw [wronskianRSWeight_rot1_of_not_selector]
    · rw [wronskianRSWeight_rot2_of_not_selector]
      · rw [wronskianRSWeight_rot3_of_not_selector]
        · ring
        · omega
      · omega
    · omega
  · omega

@[simp] theorem gaussEps_add_two_mul (a b : ℤ) :
    gaussEps (a + 2 * b) = gaussEps a := by
  unfold gaussEps
  by_cases h : a % 2 = 0
  · have h' : (a + 2 * b) % 2 = 0 := by omega
    simp [h, h']
  · have h' : (a + 2 * b) % 2 ≠ 0 := by omega
    simp [h]

@[simp] theorem gaussEps_sub_two_mul (a b : ℤ) :
    gaussEps (a - 2 * b) = gaussEps a := by
  unfold gaussEps
  by_cases h : a % 2 = 0
  · have h' : (a - 2 * b) % 2 = 0 := by omega
    simp [h, h']
  · have h' : (a - 2 * b) % 2 ≠ 0 := by omega
    simp [h]

theorem gaussEps_eq_of_mod_two {a b : ℤ} (h : a % 2 = b % 2) :
    gaussEps a = gaussEps b := by
  unfold gaussEps
  rw [h]

@[simp] theorem gaussEps_neg_add_mul_two (a b : ℤ) :
    gaussEps (-a + b * 2) = gaussEps a := by
  apply gaussEps_eq_of_mod_two
  omega

@[simp] theorem gaussEps_neg_sub_mul_two (a b : ℤ) :
    gaussEps (-a - b * 2) = gaussEps a := by
  apply gaussEps_eq_of_mod_two
  omega

@[simp] theorem gaussEps_mul_two_sub (a b : ℤ) :
    gaussEps (a * 2 - b) = gaussEps b := by
  apply gaussEps_eq_of_mod_two
  omega

@[simp] theorem gaussEps_neg_mul_two_add (a b : ℤ) :
    gaussEps (-(a * 2) + b) = gaussEps b := by
  apply gaussEps_eq_of_mod_two
  omega

@[simp] theorem gaussEps_neg_mul_two_sub (a b : ℤ) :
    gaussEps (-(a * 2) - b) = gaussEps b := by
  apply gaussEps_eq_of_mod_two
  omega

theorem gaussH_pi5_add_piBar5 (a b : ℤ) :
    gaussH (gaussMul pi5 (a,b)) + gaussH (gaussMul piBar5 (a,b)) =
      -6 * gaussH (a,b) := by
  rw [gaussMul_pi5_left, gaussMul_piBar5_left]
  unfold gaussH
  simp
  ring

theorem unitConjOrbitH_pi5_add_piBar5 (z : GaussianInt) :
    unitConjOrbitH (gaussMul pi5 z) + unitConjOrbitH (gaussMul piBar5 z) =
      -6 * unitConjOrbitH z := by
  rcases z with ⟨a, b⟩
  unfold unitConjOrbitH
  repeat rw [Fin.sum_univ_four]
  simp [gaussUnitRotate, gaussConj, gaussMul, pi5, piBar5, gaussH]
  ring_nf
  simp
  ring

theorem gaussMul_comm (z w : GaussianInt) :
    gaussMul z w = gaussMul w z := by
  rcases z with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  ext
  · simp [gaussMul]
    ring
  · simp [gaussMul]
    ring

theorem gaussEps_five_mul (a : ℤ) :
    gaussEps (5 * a) = gaussEps a := by
  apply gaussEps_eq_of_mod_two
  omega

theorem gaussH_five_mul (z : GaussianInt) :
    gaussH (gaussMul (5,0) z) = 25 * gaussH z := by
  rcases z with ⟨a, b⟩
  simp [gaussMul, gaussH, gaussEps_five_mul]
  ring

def fiveStringHSum (g : GaussianInt) (t : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (t + 1), gaussH (fiveStringPoint g t j)

@[simp] theorem fiveStringHSum_zero (g : GaussianInt) :
    fiveStringHSum g 0 = gaussH g := by
  simp [fiveStringHSum, fiveStringPoint, gaussPow]

theorem fiveStringHSum_one (g : GaussianInt) :
    fiveStringHSum g 1 = -6 * gaussH g := by
  rcases g with ⟨a, b⟩
  unfold fiveStringHSum
  norm_num
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp [fiveStringPoint, gaussPow]
  unfold gaussH
  simp
  ring

theorem fiveStringPoint_succ_succ (g : GaussianInt) (t j : ℕ) :
    fiveStringPoint g (t + 1) (j + 1) =
      gaussMul pi5 (fiveStringPoint g t j) := by
  simp [fiveStringPoint, gaussPow, gaussMul_assoc]

theorem fiveStringPoint_succ_same_of_le (g : GaussianInt) {t j : ℕ} (hj : j ≤ t) :
    fiveStringPoint g (t + 1) j =
      gaussMul piBar5 (fiveStringPoint g t j) := by
  have hsub : t + 1 - j = (t - j) + 1 := by omega
  unfold fiveStringPoint
  rw [hsub]
  simp only [gaussPow]
  rcases gaussPow pi5 j with ⟨a, b⟩
  rcases gaussPow piBar5 (t - j) with ⟨c, d⟩
  rcases g with ⟨e, f⟩
  ext
  · simp [gaussMul, piBar5]
    ring_nf
  · simp [gaussMul, piBar5]
    ring_nf

theorem sum_range_shift_add_eq_full_add_interior (f : ℕ → ℤ) (t : ℕ) :
    (∑ j ∈ Finset.range (t + 2), f (j + 1)) +
        (∑ j ∈ Finset.range (t + 2), f j) =
      (∑ j ∈ Finset.range (t + 3), f j) +
        ∑ j ∈ Finset.range (t + 1), f (j + 1) := by
  induction t with
  | zero =>
      simp [Finset.sum_range_succ]
      ring
  | succ t ih =>
      simp [Finset.sum_range_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at ih ⊢
      omega

theorem fiveStringPoint_interior_factor_five_t
    (g : GaussianInt) {t j : ℕ} (hj : j ≤ t) :
    fiveStringPoint g (t + 2) (j + 1) =
      gaussMul (5,0) (fiveStringPoint g t j) := by
  have hsub : t + 2 - (j + 1) = (t - j) + 1 := by omega
  unfold fiveStringPoint
  rw [hsub]
  simp only [gaussPow]
  rcases gaussPow pi5 j with ⟨a, b⟩
  rcases gaussPow piBar5 (t - j) with ⟨c, d⟩
  rcases g with ⟨e, f⟩
  ext
  · simp [gaussMul, pi5, piBar5]
    ring_nf
  · simp [gaussMul, pi5, piBar5]
    ring_nf

theorem fiveStringHSum_recurrence (g : GaussianInt) (t : ℕ) :
    fiveStringHSum g (t + 2) =
      -6 * fiveStringHSum g (t + 1) - 25 * fiveStringHSum g t := by
  let f : ℕ → ℤ := fun j => gaussH (fiveStringPoint g (t + 2) j)
  have hpair :
      (∑ j ∈ Finset.range (t + 2), (f (j + 1) + f j)) =
        -6 * fiveStringHSum g (t + 1) := by
    calc
      (∑ j ∈ Finset.range (t + 2), (f (j + 1) + f j))
          = ∑ j ∈ Finset.range (t + 2),
              -6 * gaussH (fiveStringPoint g (t + 1) j) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjle : j ≤ t + 1 := by
                simp at hj
                omega
              unfold f
              rw [fiveStringPoint_succ_succ g (t + 1) j]
              rw [fiveStringPoint_succ_same_of_le g (t := t + 1) (j := j) hjle]
              rcases fiveStringPoint g (t + 1) j with ⟨a, b⟩
              exact gaussH_pi5_add_piBar5 a b
      _ = -6 * fiveStringHSum g (t + 1) := by
              rw [← Finset.mul_sum]
              simp [fiveStringHSum]
  have hinterior :
      (∑ j ∈ Finset.range (t + 1), f (j + 1)) =
        25 * fiveStringHSum g t := by
    calc
      (∑ j ∈ Finset.range (t + 1), f (j + 1))
          = ∑ j ∈ Finset.range (t + 1),
              25 * gaussH (fiveStringPoint g t j) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjle : j ≤ t := by
                simp at hj
                omega
              unfold f
              rw [fiveStringPoint_interior_factor_five_t g hjle]
              exact gaussH_five_mul (fiveStringPoint g t j)
      _ = 25 * fiveStringHSum g t := by
              rw [← Finset.mul_sum]
              simp [fiveStringHSum]
  have hdouble :
      (∑ j ∈ Finset.range (t + 2), (f (j + 1) + f j)) =
        fiveStringHSum g (t + 2) + 25 * fiveStringHSum g t := by
    rw [Finset.sum_add_distrib]
    rw [sum_range_shift_add_eq_full_add_interior f t]
    rw [hinterior]
    simp [fiveStringHSum, f]
  have hmain :
      fiveStringHSum g (t + 2) + 25 * fiveStringHSum g t =
        -6 * fiveStringHSum g (t + 1) := by
    rw [← hdouble, hpair]
  omega

theorem fiveStringHSum_eq_fiveStringC_mul (g : GaussianInt) (t : ℕ) :
    fiveStringHSum g t = fiveStringC t * gaussH g := by
  refine Nat.twoStepInduction
    (P := fun t => fiveStringHSum g t = fiveStringC t * gaussH g)
    ?h0 ?h1 ?hstep t
  · simp
  · change fiveStringHSum g 1 = fiveStringC 1 * gaussH g
    rw [fiveStringHSum_one, fiveStringC_one]
  · intro n hn hn1
    change fiveStringHSum g (n + 2) = fiveStringC (n + 2) * gaussH g
    rw [fiveStringHSum_recurrence, fiveStringC, hn, hn1]
    ring

def gaussA (z : GaussianInt) : ℤ :=
  z.1 ^ 2 - z.2 ^ 2

def gaussB (z : GaussianInt) : ℤ :=
  z.1 * z.2

theorem gaussA_pi5_add_piBar5 (a b : ℤ) :
    gaussA (gaussMul pi5 (a,b)) + gaussA (gaussMul piBar5 (a,b)) =
      -6 * gaussA (a,b) := by
  rw [gaussMul_pi5_left, gaussMul_piBar5_left]
  unfold gaussA
  ring

theorem gaussA_five_mul (z : GaussianInt) :
    gaussA (gaussMul (5,0) z) = 25 * gaussA z := by
  rcases z with ⟨a, b⟩
  simp [gaussMul, gaussA]
  ring

def fiveStringASum (g : GaussianInt) (t : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (t + 1), gaussA (fiveStringPoint g t j)

@[simp] theorem fiveStringASum_zero (g : GaussianInt) :
    fiveStringASum g 0 = gaussA g := by
  simp [fiveStringASum, fiveStringPoint, gaussPow]

theorem fiveStringASum_one (g : GaussianInt) :
    fiveStringASum g 1 = -6 * gaussA g := by
  rcases g with ⟨a, b⟩
  unfold fiveStringASum
  norm_num
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp [fiveStringPoint, gaussPow]
  unfold gaussA
  ring

theorem fiveStringASum_recurrence (g : GaussianInt) (t : ℕ) :
    fiveStringASum g (t + 2) =
      -6 * fiveStringASum g (t + 1) - 25 * fiveStringASum g t := by
  let f : ℕ → ℤ := fun j => gaussA (fiveStringPoint g (t + 2) j)
  have hpair :
      (∑ j ∈ Finset.range (t + 2), (f (j + 1) + f j)) =
        -6 * fiveStringASum g (t + 1) := by
    calc
      (∑ j ∈ Finset.range (t + 2), (f (j + 1) + f j))
          = ∑ j ∈ Finset.range (t + 2),
              -6 * gaussA (fiveStringPoint g (t + 1) j) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjle : j ≤ t + 1 := by
                simp at hj
                omega
              unfold f
              rw [fiveStringPoint_succ_succ g (t + 1) j]
              rw [fiveStringPoint_succ_same_of_le g (t := t + 1) (j := j) hjle]
              rcases fiveStringPoint g (t + 1) j with ⟨a, b⟩
              exact gaussA_pi5_add_piBar5 a b
      _ = -6 * fiveStringASum g (t + 1) := by
              rw [← Finset.mul_sum]
              simp [fiveStringASum]
  have hinterior :
      (∑ j ∈ Finset.range (t + 1), f (j + 1)) =
        25 * fiveStringASum g t := by
    calc
      (∑ j ∈ Finset.range (t + 1), f (j + 1))
          = ∑ j ∈ Finset.range (t + 1),
              25 * gaussA (fiveStringPoint g t j) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjle : j ≤ t := by
                simp at hj
                omega
              unfold f
              rw [fiveStringPoint_interior_factor_five_t g hjle]
              exact gaussA_five_mul (fiveStringPoint g t j)
      _ = 25 * fiveStringASum g t := by
              rw [← Finset.mul_sum]
              simp [fiveStringASum]
  have hdouble :
      (∑ j ∈ Finset.range (t + 2), (f (j + 1) + f j)) =
        fiveStringASum g (t + 2) + 25 * fiveStringASum g t := by
    rw [Finset.sum_add_distrib]
    rw [sum_range_shift_add_eq_full_add_interior f t]
    rw [hinterior]
    simp [fiveStringASum, f]
  have hmain :
      fiveStringASum g (t + 2) + 25 * fiveStringASum g t =
        -6 * fiveStringASum g (t + 1) := by
    rw [← hdouble, hpair]
  omega

theorem fiveStringASum_eq_fiveStringC_mul (g : GaussianInt) (t : ℕ) :
    fiveStringASum g t = fiveStringC t * gaussA g := by
  refine Nat.twoStepInduction
    (P := fun t => fiveStringASum g t = fiveStringC t * gaussA g)
    ?h0 ?h1 ?hstep t
  · simp
  · change fiveStringASum g 1 = fiveStringC 1 * gaussA g
    rw [fiveStringASum_one, fiveStringC_one]
  · intro n hn hn1
    change fiveStringASum g (n + 2) = fiveStringC (n + 2) * gaussA g
    rw [fiveStringASum_recurrence, fiveStringC, hn, hn1]
    ring

theorem gaussK_pi5_conj_pair_recurrence_residue_check :
    ∀ a b : Fin 20,
      ((((a : ℤ) ^ 2 + (b : ℤ) ^ 2) % 2 = 1) →
        ((((a : ℤ) ^ 2 + (b : ℤ) ^ 2) % 5 ≠ 0) →
          gaussK (gaussMul pi5 ((a : ℤ), (b : ℤ))) +
              gaussK (gaussMul pi5 ((a : ℤ), -(b : ℤ))) =
            -6 * (gaussK ((a : ℤ), (b : ℤ)) +
              gaussK ((a : ℤ), -(b : ℤ))))) := by
  native_decide

theorem gaussK_pi5_mul_eq_neg_eps_mul_core (a b : ℤ)
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1)
    (h5 : (a ^ 2 + b ^ 2) % 5 ≠ 0) :
    gaussK (gaussMul pi5 (a,b)) =
      -gaussEps a * wronskianCore (a - 2 * b) (2 * a + b) := by
  have hodd_pi : ((a - 2 * b) ^ 2 + (2 * a + b) ^ 2) % 2 = 1 := by
    rw [show (a - 2 * b) ^ 2 + (2 * a + b) ^ 2 =
      5 * (a ^ 2 + b ^ 2) by ring]
    omega
  have hsel := pi5Selector_exists_int a b h5
  have hcore := gaussK_eq_neg_eps_mul_core_of_selector
    (a := a - 2 * b) (b := 2 * a + b) hodd_pi hsel
  simpa using hcore

theorem gaussK_pi5_conj_pair_recurrence (a b : ℤ)
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1)
    (h5 : (a ^ 2 + b ^ 2) % 5 ≠ 0) :
    gaussK (gaussMul pi5 (a,b)) + gaussK (gaussMul pi5 (a,-b)) =
      -6 * (gaussK (a,b) + gaussK (a,-b)) := by
  have hodd_neg : (a ^ 2 + (-b) ^ 2) % 2 = 1 := by
    simpa using hodd
  have h5_neg : (a ^ 2 + (-b) ^ 2) % 5 ≠ 0 := by
    simpa using h5
  have hopp : gaussEps b = -gaussEps a := gaussEps_opposite_of_norm_odd hodd
  rw [gaussK_pi5_mul_eq_neg_eps_mul_core a b hodd h5,
    gaussK_pi5_mul_eq_neg_eps_mul_core a (-b) hodd_neg h5_neg,
    gaussK_conj_pair_t0_identity a b hodd h5]
  rw [show a - 2 * -b = a + 2 * b by ring]
  rw [show 2 * a + -b = 2 * a - b by ring]
  rw [show -gaussEps a * wronskianCore (a - 2 * b) (2 * a + b) +
      -gaussEps a * wronskianCore (a + 2 * b) (2 * a - b) =
      -gaussEps a * (wronskianCore (a - 2 * b) (2 * a + b) +
        wronskianCore (a + 2 * b) (2 * a - b)) by ring]
  rw [wronskianCore_pi5_conj_pair_of_norm_odd hodd, hopp]
  ring

theorem unitConjOrbitK_pi5_add_piBar5 (z : GaussianInt)
    (hodd : gaussNormSq z % 2 = 1)
    (h5 : gaussNormSq z % 5 ≠ 0) :
    unitConjOrbitK (gaussMul pi5 z) + unitConjOrbitK (gaussMul piBar5 z) =
      -6 * unitConjOrbitK z := by
  rcases z with ⟨a, b⟩
  have hodd' : (a ^ 2 + b ^ 2) % 2 = 1 := by
    simpa [gaussNormSq] using hodd
  have h5' : (a ^ 2 + b ^ 2) % 5 ≠ 0 := by
    simpa [gaussNormSq] using h5
  have hrec := gaussK_pi5_conj_pair_recurrence a b hodd' h5'
  have hzero_left : gaussK (a - 2 * b, -2 * a - b) = 0 := by
    simpa [gaussMul_piBar5_left] using gaussK_piBar5_mul a (-b)
  have hzero_right : gaussK (a + 2 * b, -2 * a + b) = 0 := by
    simpa [gaussMul_piBar5_left] using gaussK_piBar5_mul a b
  calc
    unitConjOrbitK (gaussMul pi5 (a,b)) + unitConjOrbitK (gaussMul piBar5 (a,b))
        = 4 * (gaussK (a - 2 * b, 2 * a + b) +
            gaussK (a + 2 * b, 2 * a - b)) := by
            rw [gaussMul_pi5_left, gaussMul_piBar5_left]
            rw [unitConjOrbitK_closed, unitConjOrbitK_closed]
            rw [show -(2 * a + b) = -2 * a - b by ring]
            rw [show -(-2 * a + b) = 2 * a - b by ring]
            rw [hzero_left, hzero_right]
            ring
    _ = 4 * (-6 * (gaussK (a,b) + gaussK (a,-b))) := by
            rw [show gaussK (a - 2 * b, 2 * a + b) +
                    gaussK (a + 2 * b, 2 * a - b) =
                  gaussK (gaussMul pi5 (a,b)) + gaussK (gaussMul pi5 (a,-b)) by
                simp [gaussMul_pi5_left]
                ring]
            rw [hrec]
    _ = -6 * unitConjOrbitK (a,b) := by
            rw [unitConjOrbitK_closed]
            ring

theorem fiveStringPoint_left_endpoint_succ (g : GaussianInt) (t : ℕ) :
    fiveStringPoint g (t + 1) 0 = gaussMul piBar5 (fiveStringPoint g t 0) := by
  simp [fiveStringPoint, gaussPow, gaussMul_assoc]

theorem fiveStringPoint_left_endpoint_succ_gaussK_zero (g : GaussianInt) (t : ℕ) :
    gaussK (fiveStringPoint g (t + 1) 0) = 0 := by
  rw [fiveStringPoint_left_endpoint_succ]
  rcases fiveStringPoint g t 0 with ⟨a, b⟩
  exact gaussK_piBar5_mul a b

set_option maxHeartbeats 4000000 in
theorem fiveStringPoint_interior_factor_five (g : GaussianInt) (j k : ℕ) :
    fiveStringPoint g (j + k + 2) (j + 1) =
      gaussMul (5,0)
        (gaussMul (gaussMul (gaussPow pi5 j) (gaussPow piBar5 k)) g) := by
  have hsub : j + k + 2 - (j + 1) = k + 1 := by omega
  ext <;> simp [fiveStringPoint, gaussPow, hsub, gaussMul, pi5, piBar5] <;> ring

theorem fiveStringPoint_interior_unitConjOrbitK_zero (g : GaussianInt) (j k : ℕ) :
    unitConjOrbitK (fiveStringPoint g (j + k + 2) (j + 1)) = 0 := by
  rw [fiveStringPoint_interior_factor_five]
  simp [unitConjOrbitK_of_five_dvd_coords]

def piEndpointPart (z : GaussianInt) : ℤ :=
  2 * gaussA z - 3 * gaussB z

def piBarEndpointPart (z : GaussianInt) : ℤ :=
  2 * gaussA z + 3 * gaussB z

def fiveStringEndpointScalar (g : GaussianInt) (t : ℕ) : ℤ :=
  piBarEndpointPart (fiveStringPoint g t 0) +
    piEndpointPart (fiveStringPoint g t t)

theorem piEndpointPart_pi5_pi5 (z : GaussianInt) :
    piEndpointPart (gaussMul pi5 (gaussMul pi5 z)) =
      -6 * piEndpointPart (gaussMul pi5 z) - 25 * piEndpointPart z := by
  rcases z with ⟨a, b⟩
  simp [piEndpointPart, gaussA, gaussB, gaussMul, pi5]
  ring

theorem piBarEndpointPart_piBar5_piBar5 (z : GaussianInt) :
    piBarEndpointPart (gaussMul piBar5 (gaussMul piBar5 z)) =
      -6 * piBarEndpointPart (gaussMul piBar5 z) -
        25 * piBarEndpointPart z := by
  rcases z with ⟨a, b⟩
  simp [piBarEndpointPart, gaussA, gaussB, gaussMul, piBar5]
  ring

theorem fiveStringPoint_right_endpoint_succ (g : GaussianInt) (t : ℕ) :
    fiveStringPoint g (t + 1) (t + 1) =
      gaussMul pi5 (fiveStringPoint g t t) := by
  exact fiveStringPoint_succ_succ g t t

theorem fiveStringPoint_left_endpoint_add_two (g : GaussianInt) (t : ℕ) :
    fiveStringPoint g (t + 2) 0 =
      gaussMul piBar5 (gaussMul piBar5 (fiveStringPoint g t 0)) := by
  rw [show t + 2 = t + 1 + 1 by omega]
  rw [fiveStringPoint_left_endpoint_succ]
  rw [fiveStringPoint_left_endpoint_succ]

theorem fiveStringPoint_right_endpoint_add_two (g : GaussianInt) (t : ℕ) :
    fiveStringPoint g (t + 2) (t + 2) =
      gaussMul pi5 (gaussMul pi5 (fiveStringPoint g t t)) := by
  rw [show t + 2 = t + 1 + 1 by omega]
  rw [fiveStringPoint_right_endpoint_succ]
  rw [fiveStringPoint_right_endpoint_succ]

theorem fiveStringEndpointScalar_zero (g : GaussianInt) :
    fiveStringEndpointScalar g 0 = 4 * gaussA g := by
  simp [fiveStringEndpointScalar, piEndpointPart, piBarEndpointPart]
  ring

theorem fiveStringEndpointScalar_one (g : GaussianInt) :
    fiveStringEndpointScalar g 1 = -24 * gaussA g := by
  rcases g with ⟨a, b⟩
  simp [fiveStringEndpointScalar, piEndpointPart, piBarEndpointPart,
    fiveStringPoint, gaussPow, gaussOne, gaussA, gaussB, gaussMul, pi5, piBar5]
  ring_nf

theorem fiveStringEndpointScalar_recurrence (g : GaussianInt) (t : ℕ) :
    fiveStringEndpointScalar g (t + 2) =
      -6 * fiveStringEndpointScalar g (t + 1) -
        25 * fiveStringEndpointScalar g t := by
  unfold fiveStringEndpointScalar
  rw [fiveStringPoint_left_endpoint_add_two,
    fiveStringPoint_right_endpoint_add_two]
  rw [piBarEndpointPart_piBar5_piBar5, piEndpointPart_pi5_pi5]
  rw [fiveStringPoint_left_endpoint_succ, fiveStringPoint_right_endpoint_succ]
  ring

theorem fiveStringEndpointScalar_eq_four_fiveStringC_mul
    (g : GaussianInt) (t : ℕ) :
    fiveStringEndpointScalar g t = 4 * fiveStringC t * gaussA g := by
  refine Nat.twoStepInduction
    (P := fun t => fiveStringEndpointScalar g t = 4 * fiveStringC t * gaussA g)
    ?h0 ?h1 ?hstep t
  · change fiveStringEndpointScalar g 0 = 4 * fiveStringC 0 * gaussA g
    rw [fiveStringEndpointScalar_zero, fiveStringC_zero]
    ring
  · change fiveStringEndpointScalar g 1 = 4 * fiveStringC 1 * gaussA g
    rw [fiveStringEndpointScalar_one, fiveStringC_one]
    ring
  · intro n hn hn1
    change fiveStringEndpointScalar g (n + 2) =
      4 * fiveStringC (n + 2) * gaussA g
    rw [fiveStringEndpointScalar_recurrence, fiveStringC, hn, hn1]
    ring

/-- Scalar identity for the Gaussian 5-string in the `π = 1 + 2i`
coordinates used in this file.  It is the cleared-denominator form of the
endpoint identity in the Dobbie 5-string proof. -/
theorem string_scalar_identity (g : GaussianInt) (t : ℕ) :
    fiveStringEndpointScalar g t = 4 * fiveStringASum g t := by
  rw [fiveStringEndpointScalar_eq_four_fiveStringC_mul,
    fiveStringASum_eq_fiveStringC_mul]
  ring

/-! ## Explicit coefficient reindexing maps -/

theorem paritySign_eq_negOnePowInt (n : ℤ) :
    paritySign n = negOnePowInt ℤ n := by
  cases n with
  | ofNat a =>
      simp [paritySign, negOnePowInt]
      rw [neg_one_pow_eq_ite]
      by_cases h : Even a
      · have hn : (a : ℤ) % 2 = 0 := by
          have := Nat.even_iff.mp h
          exact_mod_cast this
        simp [h, hn]
      · have hn : (a : ℤ) % 2 ≠ 0 := by
          intro hc
          have hcNat : a % 2 = 0 := by exact_mod_cast hc
          exact h (Nat.even_iff.mpr hcNat)
        have hmod : (a : ℤ) % 2 = 1 := by omega
        simp [h, hmod]
  | negSucc a =>
      simp [paritySign, negOnePowInt]
      rw [neg_one_pow_eq_ite]
      by_cases h : Even (a + 1)
      · have hn : ((a : ℤ) + 1) % 2 = 0 := by
          have hnNat : (a + 1) % 2 = 0 := Nat.even_iff.mp h
          exact_mod_cast hnNat
        simp [h, hn]
      · have hn : ((a : ℤ) + 1) % 2 ≠ 0 := by
          intro hc
          have hcNat : (a + 1) % 2 = 0 := by exact_mod_cast hc
          exact h (Nat.even_iff.mpr hcNat)
        have hmod : ((a : ℤ) + 1) % 2 = 1 := by omega
        simp [h, hmod]

theorem negOnePowInt_add (k l : ℤ) :
    negOnePowInt ℤ (k + l) = negOnePowInt ℤ k * negOnePowInt ℤ l := by
  rw [show negOnePowInt ℤ (k + l) = ((k + l).negOnePow : ℤˣ) by
    cases k + l <;> simp [negOnePowInt, Int.negOnePow]]
  rw [Int.negOnePow_add]
  rw [show negOnePowInt ℤ k = (k.negOnePow : ℤˣ) by
    cases k <;> simp [negOnePowInt, Int.negOnePow]]
  rw [show negOnePowInt ℤ l = (l.negOnePow : ℤˣ) by
    cases l <;> simp [negOnePowInt, Int.negOnePow]]
  norm_num

theorem negOnePowInt_natCast (r : ℕ) :
    negOnePowInt ℤ (r : ℤ) = (-1 : ℤ) ^ r := by
  simp [negOnePowInt]

def triangularIndex (r : ℕ) : ℕ :=
  r * (r + 1) / 2

def jacobiToGauss (r s : ℕ) : GaussianInt :=
  ((r : ℤ) + (s : ℤ) + 1, (r : ℤ) - (s : ℤ))

theorem jacobiToGauss_R_eq (r s : ℕ) :
    (jacobiToGauss r s).1 - (jacobiToGauss r s).2 = 2 * (s : ℤ) + 1 := by
  unfold jacobiToGauss
  ring

theorem jacobiToGauss_S_eq (r s : ℕ) :
    (jacobiToGauss r s).1 + (jacobiToGauss r s).2 = 2 * (r : ℤ) + 1 := by
  unfold jacobiToGauss
  ring

theorem jacobiToGauss_swap (r s : ℕ) :
    jacobiToGauss s r = gaussConj (jacobiToGauss r s) := by
  unfold jacobiToGauss gaussConj
  ext <;> ring

theorem triangularIndex_injective : Function.Injective triangularIndex := by
  intro a b h
  exact triangular_strictMono.injective (by simpa [triangularIndex] using h)

theorem jacobiTripleSign_eq_sum_range_of_le {n N : ℕ} (hn : n ≤ N) :
    jacobiTripleSign n =
      ∑ r ∈ Finset.range (N + 1),
        if triangularIndex r = n then (-1 : ℤ) ^ r * (2 * (r : ℤ) + 1) else 0 := by
  by_cases htri : ∃ r ≤ n, n = triangularIndex r
  · obtain ⟨r, hrle, hr⟩ := htri
    rw [hr]
    have hrmem : r ∈ Finset.range (N + 1) := by
      simp
      omega
    rw [show jacobiTripleSign (triangularIndex r) =
        (-1 : ℤ) ^ r * (2 * (r : ℤ) + 1) by
      simpa [triangularIndex] using jacobiTripleSign_triangular r]
    symm
    trans (if triangularIndex r = triangularIndex r then
        (-1 : ℤ) ^ r * (2 * (r : ℤ) + 1) else 0)
    · apply Finset.sum_eq_single r
      · intro b _hb hbr
        by_cases hbtri : triangularIndex b = triangularIndex r
        · have hbr_eq : b = r := triangularIndex_injective hbtri
          exact False.elim (hbr hbr_eq)
        · simp [hbtri]
      · intro hrnot
        exact False.elim (hrnot hrmem)
    · simp
  · push_neg at htri
    rw [jacobiTripleSign_of_not_triangular]
    · symm
      apply Finset.sum_eq_zero
      intro r _hrmem
      by_cases hrn : triangularIndex r = n
      · have hrle : r ≤ n := by
          rw [← hrn]
          simpa [triangularIndex] using k_le_triangular r
        exact False.elim (htri r hrle hrn.symm)
      · simp [hrn]
    · intro k hk hkn
      exact htri k hk (by simpa [triangularIndex] using hkn)

theorem jacobiTripleSign_rat_eq_sum_range_of_le {n N : ℕ} (hn : n ≤ N) :
    ((jacobiTripleSign n : ℤ) : ℚ) =
      ∑ r ∈ Finset.range (N + 1),
        if triangularIndex r = n then
          (((-1 : ℤ) ^ r * (2 * (r : ℤ) + 1) : ℤ) : ℚ)
        else 0 := by
  rw [jacobiTripleSign_eq_sum_range_of_le (n := n) (N := N) hn]
  norm_cast

theorem gaussEps_jacobiToGauss (r s : ℕ) :
    gaussEps (jacobiToGauss r s).1 = (-1 : ℤ) ^ r * (-1 : ℤ) ^ s := by
  have heps :
      gaussEps ((r : ℤ) + (s : ℤ) + 1) =
        paritySign ((r : ℤ) + (s : ℤ)) := by
    unfold gaussEps paritySign
    by_cases h : ((r : ℤ) + (s : ℤ)) % 2 = 0
    · have hA : ((r : ℤ) + (s : ℤ) + 1) % 2 ≠ 0 := by omega
      simp [h, hA]
    · have hA : ((r : ℤ) + (s : ℤ) + 1) % 2 = 0 := by omega
      simp [h, hA]
  rw [jacobiToGauss, heps, paritySign_eq_negOnePowInt,
    negOnePowInt_add, negOnePowInt_natCast, negOnePowInt_natCast]

theorem jacobiToGauss_H (r s : ℕ) :
    gaussH (jacobiToGauss r s) =
      jacobiTripleSign (triangularIndex r) * jacobiTripleSign (triangularIndex s) := by
  unfold triangularIndex
  rw [jacobiTripleSign_triangular, jacobiTripleSign_triangular]
  rw [show gaussH (jacobiToGauss r s) =
      gaussEps (jacobiToGauss r s).1 *
        ((jacobiToGauss r s).1 ^ 2 - (jacobiToGauss r s).2 ^ 2) by rfl]
  rw [gaussEps_jacobiToGauss]
  unfold jacobiToGauss
  ring_nf

theorem two_mul_int_triangularIndex (r : ℕ) :
    2 * (triangularIndex r : ℤ) = (r : ℤ) * ((r : ℤ) + 1) := by
  unfold triangularIndex
  exact_mod_cast two_mul_triangular r

theorem jacobiToGauss_norm (r s : ℕ) :
    gaussNormSq (jacobiToGauss r s) =
      4 * ((triangularIndex r : ℤ) + (triangularIndex s : ℤ)) + 1 := by
  have hT_r := two_mul_int_triangularIndex r
  have hT_s := two_mul_int_triangularIndex s
  apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
  calc
    2 * gaussNormSq (jacobiToGauss r s)
        = 4 * ((r : ℤ) * ((r : ℤ) + 1) + (s : ℤ) * ((s : ℤ) + 1)) + 2 := by
          unfold gaussNormSq jacobiToGauss
          ring
    _ = 2 * (4 * ((triangularIndex r : ℤ) + (triangularIndex s : ℤ)) + 1) := by
          rw [← hT_r, ← hT_s]
          ring

def pentagonalToGauss (k l : ℤ) : GaussianInt :=
  (-k + 3 * l, -3 * k - l + 1)

def pentagonalX (m : ℤ) : ℤ :=
  10 * m - 3

def pentagonalY (n : ℤ) : ℤ :=
  10 * n - 1

@[simp] theorem pentagonalX_mod_five (m : ℤ) : pentagonalX m % 5 = 2 := by
  unfold pentagonalX
  omega

@[simp] theorem pentagonalY_mod_five (n : ℤ) : pentagonalY n % 5 = 4 := by
  unfold pentagonalY
  omega

theorem pentagonalToGauss_selector (k l : ℤ) :
    (-(pentagonalToGauss k l).1 - 3 * (pentagonalToGauss k l).2) = 10 * k - 3 ∧
      (3 * (pentagonalToGauss k l).1 - (pentagonalToGauss k l).2) = 10 * l - 1 := by
  unfold pentagonalToGauss
  constructor <;> ring

theorem pentagonalToGauss_R_eq (m n : ℤ) :
    (pentagonalToGauss m n).1 - (pentagonalToGauss m n).2 =
      (pentagonalX m + 2 * pentagonalY n) / 5 := by
  unfold pentagonalToGauss pentagonalX pentagonalY
  rw [show 10 * m - 3 + 2 * (10 * n - 1) =
      5 * (2 * m + 4 * n - 1) by ring]
  rw [Int.mul_ediv_cancel_left]
  · ring
  · norm_num

theorem pentagonalToGauss_S_eq (m n : ℤ) :
    (pentagonalToGauss m n).1 + (pentagonalToGauss m n).2 =
      (-2 * pentagonalX m + pentagonalY n) / 5 := by
  unfold pentagonalToGauss pentagonalX pentagonalY
  rw [show -2 * (10 * m - 3) + (10 * n - 1) =
      5 * (-4 * m + 2 * n + 1) by ring]
  rw [Int.mul_ediv_cancel_left]
  · ring
  · norm_num

theorem pentagonalToGauss_rot0_selector (m n : ℤ) :
    (-(pentagonalToGauss m n).1 - 3 * (pentagonalToGauss m n).2) % 5 = 2 := by
  have h := (pentagonalToGauss_selector m n).1
  rw [h]
  omega

theorem pentagonalToGauss_wronskianRSWeight (k l : ℤ) :
    wronskianRSWeight
        ((pentagonalToGauss k l).1 - (pentagonalToGauss k l).2)
        ((pentagonalToGauss k l).1 + (pentagonalToGauss k l).2) =
      paritySign (k + l) * (((10 * k - 3) ^ 2 - (10 * l - 1) ^ 2) / 8) := by
  rw [wronskianRSWeight_rot0_of_selector]
  · unfold pentagonalToGauss
    have hq :
        (2 * (-k + 3 * l) - 4 * (-3 * k - l + 1) + 4) / 10 = k + l := by
      rw [show 2 * (-k + 3 * l) - 4 * (-3 * k - l + 1) + 4 =
          10 * (k + l) by ring]
      exact Int.mul_ediv_cancel_left (k + l) (by norm_num : (10 : ℤ) ≠ 0)
    rw [hq]
    congr 1
    ring_nf
  · unfold pentagonalToGauss
    omega

theorem two_dvd_pentagonal014_num (k : ℤ) :
    (2 : ℤ) ∣ k * (5 * k - 3) := by
  by_cases hk : k % 2 = 0
  · exact dvd_mul_of_dvd_left ((Int.dvd_iff_emod_eq_zero).mpr hk) (5 * k - 3)
  · have hfac : (5 * k - 3) % 2 = 0 := by omega
    exact dvd_mul_of_dvd_right ((Int.dvd_iff_emod_eq_zero).mpr hfac) k

theorem two_dvd_pentagonal023_num (k : ℤ) :
    (2 : ℤ) ∣ k * (5 * k - 1) := by
  by_cases hk : k % 2 = 0
  · exact dvd_mul_of_dvd_left ((Int.dvd_iff_emod_eq_zero).mpr hk) (5 * k - 1)
  · have hfac : (5 * k - 1) % 2 = 0 := by omega
    exact dvd_mul_of_dvd_right ((Int.dvd_iff_emod_eq_zero).mpr hfac) k

theorem two_mul_int_pentagonal014Exp (k : ℤ) :
    2 * (pentagonal014Exp k : ℤ) = k * (5 * k - 3) := by
  rw [int_coe_pentagonal014Exp]
  simpa [mul_comm] using Int.ediv_mul_cancel (two_dvd_pentagonal014_num k)

theorem two_mul_int_pentagonal023Exp (k : ℤ) :
    2 * (pentagonal023Exp k : ℤ) = k * (5 * k - 1) := by
  rw [int_coe_pentagonal023Exp]
  simpa [mul_comm] using Int.ediv_mul_cancel (two_dvd_pentagonal023_num k)

theorem pentagonalToGauss_norm (k l : ℤ) :
    gaussNormSq (pentagonalToGauss k l) =
      4 * ((pentagonal014Exp k : ℤ) + (pentagonal023Exp l : ℤ)) + 1 := by
  have h14 := two_mul_int_pentagonal014Exp k
  have h23 := two_mul_int_pentagonal023Exp l
  apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
  calc
    2 * gaussNormSq (pentagonalToGauss k l)
        = 4 * (k * (5 * k - 3) + l * (5 * l - 1)) + 2 := by
          unfold gaussNormSq pentagonalToGauss
          ring
    _ = 2 * (4 * ((pentagonal014Exp k : ℤ) + (pentagonal023Exp l : ℤ)) + 1) := by
          rw [← h14, ← h23]
          ring

theorem pentagonalToGauss_RS_sq_sum (m n : ℤ) :
    ((pentagonalToGauss m n).1 - (pentagonalToGauss m n).2) ^ 2 +
      ((pentagonalToGauss m n).1 + (pentagonalToGauss m n).2) ^ 2 =
        8 * ((pentagonal014Exp m : ℤ) + (pentagonal023Exp n : ℤ)) + 2 := by
  have hnorm := pentagonalToGauss_norm m n
  rw [show ((pentagonalToGauss m n).1 - (pentagonalToGauss m n).2) ^ 2 +
      ((pentagonalToGauss m n).1 + (pentagonalToGauss m n).2) ^ 2 =
        2 * gaussNormSq (pentagonalToGauss m n) by
    unfold gaussNormSq
    ring]
  rw [hnorm]
  ring

theorem jacobiToGauss_RS_sq_sum (r s : ℕ) :
    ((jacobiToGauss r s).1 - (jacobiToGauss r s).2) ^ 2 +
      ((jacobiToGauss r s).1 + (jacobiToGauss r s).2) ^ 2 =
        8 * ((triangularIndex r : ℤ) + (triangularIndex s : ℤ)) + 2 := by
  have hnorm := jacobiToGauss_norm r s
  rw [show ((jacobiToGauss r s).1 - (jacobiToGauss r s).2) ^ 2 +
      ((jacobiToGauss r s).1 + (jacobiToGauss r s).2) ^ 2 =
        2 * gaussNormSq (jacobiToGauss r s) by
    unfold gaussNormSq
    ring]
  rw [hnorm]
  ring

theorem pentagonalWeight_ediv_eq (k l : ℤ) :
    (((10 * k - 3) ^ 2 - (10 * l - 1) ^ 2) / 8) =
      1 + 5 * ((pentagonal014Exp k : ℤ) - (pentagonal023Exp l : ℤ)) := by
  let q : ℤ := 1 + 5 * ((pentagonal014Exp k : ℤ) - (pentagonal023Exp l : ℤ))
  have h14 := two_mul_int_pentagonal014Exp k
  have h23 := two_mul_int_pentagonal023Exp l
  have hnum : (10 * k - 3) ^ 2 - (10 * l - 1) ^ 2 = 8 * q := by
    calc
      (10 * k - 3) ^ 2 - (10 * l - 1) ^ 2
          = 20 * (k * (5 * k - 3) - l * (5 * l - 1)) + 8 := by ring
      _ = 20 * (2 * (pentagonal014Exp k : ℤ) -
            2 * (pentagonal023Exp l : ℤ)) + 8 := by rw [← h14, ← h23]
      _ = 8 * q := by
            simp [q]
            ring
  rw [hnum]
  exact Int.mul_ediv_cancel_left q (by norm_num : (8 : ℤ) ≠ 0)

theorem pentagonalToGauss_wronskianCoeffWeight (k l : ℤ) :
    wronskianRSWeight
        ((pentagonalToGauss k l).1 - (pentagonalToGauss k l).2)
        ((pentagonalToGauss k l).1 + (pentagonalToGauss k l).2) =
      negOnePowInt ℤ k * negOnePowInt ℤ l *
        (1 + 5 * ((pentagonal014Exp k : ℤ) - (pentagonal023Exp l : ℤ))) := by
  rw [pentagonalToGauss_wronskianRSWeight, pentagonalWeight_ediv_eq,
    paritySign_eq_negOnePowInt, negOnePowInt_add]

theorem gaussK_pentagonalToGauss_eq_row0 (m n : ℤ) :
    gaussK (pentagonalToGauss m n) =
      wronskianRSWeight
        ((pentagonalToGauss m n).1 - (pentagonalToGauss m n).2)
        ((pentagonalToGauss m n).1 + (pentagonalToGauss m n).2) := by
  rw [gaussK_explicit]
  have h0 := pentagonalToGauss_rot0_selector m n
  rw [wronskianRSWeight_rot0_of_selector h0]
  rw [wronskianRSWeight_rot1_of_not_selector]
  · rw [wronskianRSWeight_rot2_of_not_selector]
    · rw [wronskianRSWeight_rot3_of_not_selector]
      · ring
      · unfold pentagonalToGauss
        omega
    · unfold pentagonalToGauss
      omega
  · unfold pentagonalToGauss
    omega

theorem pentagonalToGauss_norm_of_exp_sum {N : ℕ} {m n : ℤ}
    (h : pentagonal014Exp m + pentagonal023Exp n = N) :
    gaussNormSq (pentagonalToGauss m n) = 4 * (N : ℤ) + 1 := by
  rw [pentagonalToGauss_norm]
  exact_mod_cast congrArg (fun t : ℕ => 4 * t + 1) h

theorem jacobiToGauss_norm_of_tri_sum {N r s : ℕ}
    (h : triangularIndex r + triangularIndex s = N) :
    gaussNormSq (jacobiToGauss r s) = 4 * (N : ℤ) + 1 := by
  rw [jacobiToGauss_norm]
  exact_mod_cast congrArg (fun t : ℕ => 4 * t + 1) h

theorem norm_odd_of_four_mul_add_one (N : ℕ) :
    (4 * (N : ℤ) + 1) % 2 = 1 := by
  omega

theorem pentagonalToGauss_norm_odd_of_exp_sum {N : ℕ} {m n : ℤ}
    (h : pentagonal014Exp m + pentagonal023Exp n = N) :
    gaussNormSq (pentagonalToGauss m n) % 2 = 1 := by
  rw [pentagonalToGauss_norm_of_exp_sum h]
  exact norm_odd_of_four_mul_add_one N

theorem jacobiToGauss_norm_odd_of_tri_sum {N r s : ℕ}
    (h : triangularIndex r + triangularIndex s = N) :
    gaussNormSq (jacobiToGauss r s) % 2 = 1 := by
  rw [jacobiToGauss_norm_of_tri_sum h]
  exact norm_odd_of_four_mul_add_one N

theorem pentagonalToGauss_norm_mod_five_of_exp_sum {N : ℕ} {m n : ℤ}
    (h : pentagonal014Exp m + pentagonal023Exp n = N) :
    gaussNormSq (pentagonalToGauss m n) % 5 = (4 * (N : ℤ) + 1) % 5 := by
  rw [pentagonalToGauss_norm_of_exp_sum h]

theorem jacobiToGauss_norm_mod_five_of_tri_sum {N r s : ℕ}
    (h : triangularIndex r + triangularIndex s = N) :
    gaussNormSq (jacobiToGauss r s) % 5 = (4 * (N : ℤ) + 1) % 5 := by
  rw [jacobiToGauss_norm_of_tri_sum h]

theorem unitConjOrbitH_eq_eight_gaussH_of_norm_odd {a b : ℤ}
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1) :
    unitConjOrbitH (a,b) = 8 * gaussH (a,b) := by
  have hopp : gaussEps b = -gaussEps a := gaussEps_opposite_of_norm_odd hodd
  rw [unitConjOrbitH_closed_of_eps_opposite hopp]
  unfold gaussH
  ring

theorem unitConjOrbitK_eq_eight_gaussH_of_t0 {a b : ℤ}
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1)
    (h5 : (a ^ 2 + b ^ 2) % 5 ≠ 0) :
    unitConjOrbitK (a,b) = 8 * gaussH (a,b) := by
  rw [fiveString_t0_unitConjOrbit_identity]
  · exact unitConjOrbitH_eq_eight_gaussH_of_norm_odd hodd
  · simpa [gaussNormSq] using hodd
  · simpa [gaussNormSq] using h5

theorem gaussK_pair_eq_gaussH_pair_sum_t0 {a b : ℤ}
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1)
    (h5 : (a ^ 2 + b ^ 2) % 5 ≠ 0) :
    gaussK (a,b) + gaussK (a,-b) = gaussH (a,b) + gaussH (a,-b) := by
  have hopp : gaussEps b = -gaussEps a := gaussEps_opposite_of_norm_odd hodd
  rw [gaussK_conj_pair_t0_identity a b hodd h5]
  simp [gaussH, hopp]
  ring

def rsSignSumK (R S : ℤ) : ℤ :=
  wronskianRSWeight R S + wronskianRSWeight (-R) S +
    wronskianRSWeight R (-S) + wronskianRSWeight (-R) (-S)

def rsSwapOrbitK (R S : ℤ) : ℤ :=
  if R = S then rsSignSumK R S else rsSignSumK R S + rsSignSumK S R

def rsJacobiWeight (R S : ℤ) : ℤ :=
  paritySign ((R + S - 2) / 2) * (R * S)

def rsSwapOrbitH (R S : ℤ) : ℤ :=
  if R = S then rsJacobiWeight R S else rsJacobiWeight R S + rsJacobiWeight S R

/-- Residue-table form of the `t=0` sign/swap orbit bridge in `(R,S)`
coordinates.  The remaining work is to lift this table from residues to the
full finite reindexing over absolute odd `R,S`. -/
theorem rsSwapOrbit_t0_residue_check :
    ∀ R S : Fin 20,
      ((R : ℤ) % 2 = 1) → ((S : ℤ) % 2 = 1) →
      ((((R : ℤ) ^ 2 + (S : ℤ) ^ 2) / 2) % 5 ≠ 0) →
      rsSwapOrbitK (R : ℤ) (S : ℤ) = rsSwapOrbitH (R : ℤ) (S : ℤ) := by
  native_decide

theorem gaussK_pair_eq_rsSwapOrbitK_of_ne {a b : ℤ} (hb : b ≠ 0) :
    gaussK (a,b) + gaussK (a,-b) = rsSwapOrbitK (a - b) (a + b) := by
  have hne : a - b ≠ a + b := by omega
  simp [rsSwapOrbitK, rsSignSumK, hne, gaussK_explicit]
  ring_nf

theorem gaussK_pair_eq_two_rsSwapOrbitK_of_eq {a b : ℤ} (hb : b = 0) :
    gaussK (a,b) + gaussK (a,-b) = 2 * rsSwapOrbitK (a - b) (a + b) := by
  subst hb
  simp [rsSwapOrbitK, rsSignSumK, gaussK_explicit]
  ring_nf

theorem rsJacobiWeight_jacobiToGauss (r s : ℕ) :
    rsJacobiWeight ((jacobiToGauss r s).1 - (jacobiToGauss r s).2)
      ((jacobiToGauss r s).1 + (jacobiToGauss r s).2) =
    gaussH (jacobiToGauss r s) := by
  unfold rsJacobiWeight
  rw [jacobiToGauss_R_eq, jacobiToGauss_S_eq]
  have hq : (2 * (s : ℤ) + 1 + (2 * (r : ℤ) + 1) - 2) / 2 =
      (r : ℤ) + (s : ℤ) := by
    rw [show 2 * (s : ℤ) + 1 + (2 * (r : ℤ) + 1) - 2 =
        2 * ((r : ℤ) + (s : ℤ)) by ring]
    exact Int.mul_ediv_cancel_left ((r : ℤ) + (s : ℤ)) (by norm_num : (2 : ℤ) ≠ 0)
  rw [hq, paritySign_eq_negOnePowInt, negOnePowInt_add,
    negOnePowInt_natCast, negOnePowInt_natCast]
  unfold gaussH
  rw [gaussEps_jacobiToGauss]
  unfold jacobiToGauss
  ring_nf

theorem rsJacobiWeight_jacobiToGauss_swap (r s : ℕ) :
    rsJacobiWeight ((jacobiToGauss r s).1 + (jacobiToGauss r s).2)
      ((jacobiToGauss r s).1 - (jacobiToGauss r s).2) =
    gaussH (gaussConj (jacobiToGauss r s)) := by
  rw [← jacobiToGauss_swap]
  simpa [jacobiToGauss, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
    rsJacobiWeight_jacobiToGauss s r

theorem pentagonal014Coeff_eq_sum_Icc_of_le {n N : ℕ} (hn : n ≤ N) :
    pentagonal014Coeff ℚ n =
      ∑ k ∈ Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ),
        if pentagonal014Exp k = n then negOnePowInt ℚ k else 0 := by
  unfold pentagonal014Coeff
  have hsub : Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) ⊆
      Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    constructor <;> omega
  apply Finset.sum_subset hsub
  intro k _hkBig hkSmall
  by_cases h : pentagonal014Exp k = n
  · exact False.elim (hkSmall (pentagonal014Exp_mem_Icc_of_eq h))
  · simp [h]

theorem pentagonal023Coeff_eq_sum_Icc_of_le {n N : ℕ} (hn : n ≤ N) :
    pentagonal023Coeff ℚ n =
      ∑ k ∈ Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ),
        if pentagonal023Exp k = n then negOnePowInt ℚ k else 0 := by
  unfold pentagonal023Coeff
  have hsub : Finset.Icc (-(n + 1 : ℤ)) (n + 1 : ℤ) ⊆
      Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    constructor <;> omega
  apply Finset.sum_subset hsub
  intro k _hkBig hkSmall
  by_cases h : pentagonal023Exp k = n
  · exact False.elim (hkSmall (pentagonal023Exp_mem_Icc_of_eq h))
  · simp [h]

theorem antidiagonal_indicator_pair (N i j : ℕ) (c : ℚ) :
    (∑ ij ∈ Finset.antidiagonal N,
        if j = ij.2 then if i = ij.1 then c else 0 else 0) =
      if i + j = N then c else 0 := by
  by_cases hsum : i + j = N
  · rw [if_pos hsum]
    trans (if j = (i, j).2 then if i = (i, j).1 then c else 0 else 0)
    · apply Finset.sum_eq_single (i, j)
      · intro x _hx hne
        by_cases hj : j = x.2
        · by_cases hi : i = x.1
          · exfalso
            apply hne
            ext <;> omega
          · simp [hj, hi]
        · simp [hj]
      · intro hnot
        exfalso
        apply hnot
        simp [Finset.mem_antidiagonal, hsum]
    · simp
  · rw [if_neg hsum]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hj : j = x.2
    · by_cases hi : i = x.1
      · exfalso
        have hxsum : x.1 + x.2 = N := by
          simpa [Finset.mem_antidiagonal] using hx
        omega
      · simp [hj, hi]
    · simp [hj]

theorem antidiagonal_indicator_pair_rightWeight (N i j : ℕ) (c : ℚ) :
    (∑ ij ∈ Finset.antidiagonal N,
        (if j = ij.2 then if i = ij.1 then c else 0 else 0) * (ij.2 : ℚ)) =
      if i + j = N then c * (j : ℚ) else 0 := by
  by_cases hsum : i + j = N
  · rw [if_pos hsum]
    trans ((if j = (i, j).2 then if i = (i, j).1 then c else 0 else 0) *
        ((i, j).2 : ℚ))
    · apply Finset.sum_eq_single (i, j)
      · intro x _hx hne
        by_cases hj : j = x.2
        · by_cases hi : i = x.1
          · exfalso
            apply hne
            ext <;> omega
          · simp [hj, hi]
        · simp [hj]
      · intro hnot
        exfalso
        apply hnot
        simp [Finset.mem_antidiagonal, hsum]
    · simp
  · rw [if_neg hsum]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hj : j = x.2
    · by_cases hi : i = x.1
      · exfalso
        have hxsum : x.1 + x.2 = N := by
          simpa [Finset.mem_antidiagonal] using hx
        omega
      · simp [hj, hi]
    · simp [hj]

theorem antidiagonal_indicator_product (N : ℕ) (A B : Finset ℤ)
    (e1 e2 : ℤ → ℕ) (f g : ℤ → ℚ) :
    (∑ ij ∈ Finset.antidiagonal N,
      (∑ a ∈ A, if e1 a = ij.1 then f a else 0) *
        (∑ b ∈ B, if e2 b = ij.2 then g b else 0)) =
      ∑ a ∈ A, ∑ b ∈ B,
        if e1 a + e2 b = N then f a * g b else 0 := by
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  have hprod : ∀ x : ℕ × ℕ,
      (if e1 a = x.1 then f a else 0) * (if e2 b = x.2 then g b else 0) =
        if e2 b = x.2 then if e1 a = x.1 then f a * g b else 0 else 0 := by
    intro x
    by_cases hi : e1 a = x.1 <;> by_cases hj : e2 b = x.2 <;> simp [hi, hj]
  simp_rw [hprod]
  exact antidiagonal_indicator_pair N (e1 a) (e2 b) (f a * g b)

theorem antidiagonal_indicator_product_rightWeight (N : ℕ) (A B : Finset ℤ)
    (e1 e2 : ℤ → ℕ) (f g : ℤ → ℚ) :
    (∑ ij ∈ Finset.antidiagonal N,
      (∑ a ∈ A, if e1 a = ij.1 then f a else 0) *
        (∑ b ∈ B, if e2 b = ij.2 then g b else 0) * (ij.2 : ℚ)) =
      ∑ a ∈ A, ∑ b ∈ B,
        if e1 a + e2 b = N then f a * g b * (e2 b : ℚ) else 0 := by
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  have hprod : ∀ x : ℕ × ℕ,
      (if e1 a = x.1 then f a else 0) * (if e2 b = x.2 then g b else 0) =
        if e2 b = x.2 then if e1 a = x.1 then f a * g b else 0 else 0 := by
    intro x
    by_cases hi : e1 a = x.1 <;> by_cases hj : e2 b = x.2 <;> simp [hi, hj]
  simp_rw [hprod]
  exact antidiagonal_indicator_pair_rightWeight N (e1 a) (e2 b) (f a * g b)

theorem antidiagonal_indicator_product_nat (N : ℕ) (A B : Finset ℕ)
    (e1 e2 : ℕ → ℕ) (f g : ℕ → ℚ) :
    (∑ ij ∈ Finset.antidiagonal N,
      (∑ a ∈ A, if e1 a = ij.1 then f a else 0) *
        (∑ b ∈ B, if e2 b = ij.2 then g b else 0)) =
      ∑ a ∈ A, ∑ b ∈ B,
        if e1 a + e2 b = N then f a * g b else 0 := by
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  have hprod : ∀ x : ℕ × ℕ,
      (if e1 a = x.1 then f a else 0) * (if e2 b = x.2 then g b else 0) =
        if e2 b = x.2 then if e1 a = x.1 then f a * g b else 0 else 0 := by
    intro x
    by_cases hi : e1 a = x.1 <;> by_cases hj : e2 b = x.2 <;> simp [hi, hj]
  simp_rw [hprod]
  exact antidiagonal_indicator_pair N (e1 a) (e2 b) (f a * g b)

/-! ## Coefficientwise Wronskian reduction to Jacobi cube -/

/-- Raw Cauchy-product coefficient of
`P14*P23 + 5*(P23*theta(P14) - P14*theta(P23))`. -/
def pentagonalWronskianCoeff (N : ℕ) : ℚ :=
  (∑ ij ∈ Finset.antidiagonal N,
    pentagonal014Coeff ℚ ij.1 * pentagonal023Coeff ℚ ij.2) +
  5 *
    ((∑ ij ∈ Finset.antidiagonal N,
        pentagonal023Coeff ℚ ij.1 * pentagonal014Coeff ℚ ij.2 * (ij.2 : ℚ)) -
      (∑ ij ∈ Finset.antidiagonal N,
        pentagonal014Coeff ℚ ij.1 * pentagonal023Coeff ℚ ij.2 * (ij.2 : ℚ)))

/-- The Wronskian numerator has already been multiplied by `P014 * P023`; its
`N = 2` coefficient is therefore `9`, not the bare Lambert-factor coefficient
`5`. -/
theorem pentagonalWronskianCoeff_two :
    pentagonalWronskianCoeff 2 = 9 := by
  native_decide

/-- Cauchy-product coefficient of `(jacobiThetaPS ℚ)^2`. -/
def jacobiThetaSquareCoeff (N : ℕ) : ℚ :=
  ∑ ij ∈ Finset.antidiagonal N,
    ((jacobiTripleSign ij.1 : ℤ) : ℚ) * ((jacobiTripleSign ij.2 : ℤ) : ℚ)

def jacobiSignAt (r : ℕ) : ℚ :=
  (((-1 : ℤ) ^ r * (2 * (r : ℤ) + 1) : ℤ) : ℚ)

theorem jacobiSignAt_eq_jacobiTripleSign (r : ℕ) :
    jacobiSignAt r = ((jacobiTripleSign (triangularIndex r) : ℤ) : ℚ) := by
  unfold jacobiSignAt triangularIndex
  rw [jacobiTripleSign_triangular]

theorem jacobiExpandedWeight_eq_gaussH (r s : ℕ) :
    jacobiSignAt r * jacobiSignAt s = ((gaussH (jacobiToGauss r s) : ℤ) : ℚ) := by
  rw [jacobiSignAt_eq_jacobiTripleSign, jacobiSignAt_eq_jacobiTripleSign]
  rw [jacobiToGauss_H]
  norm_cast

def jacobiThetaSquareCoeffExpanded (N : ℕ) : ℚ :=
  ∑ r ∈ Finset.range (N + 1),
    ∑ s ∈ Finset.range (N + 1),
      if triangularIndex r + triangularIndex s = N then
        jacobiSignAt r * jacobiSignAt s
      else 0

theorem jacobiThetaSquareCoeff_eq_expanded (N : ℕ) :
    jacobiThetaSquareCoeff N = jacobiThetaSquareCoeffExpanded N := by
  let R : Finset ℕ := Finset.range (N + 1)
  have hrew : ∀ ij ∈ Finset.antidiagonal N,
      ((jacobiTripleSign ij.1 : ℤ) : ℚ) =
        ∑ r ∈ R, if triangularIndex r = ij.1 then jacobiSignAt r else 0 := by
    intro ij hij
    have hsum : ij.1 + ij.2 = N := by simpa [Finset.mem_antidiagonal] using hij
    have hle : ij.1 ≤ N := by omega
    simpa [R, jacobiSignAt] using
      jacobiTripleSign_rat_eq_sum_range_of_le (n := ij.1) (N := N) hle
  have hrew2 : ∀ ij ∈ Finset.antidiagonal N,
      ((jacobiTripleSign ij.2 : ℤ) : ℚ) =
        ∑ s ∈ R, if triangularIndex s = ij.2 then jacobiSignAt s else 0 := by
    intro ij hij
    have hsum : ij.1 + ij.2 = N := by simpa [Finset.mem_antidiagonal] using hij
    have hle : ij.2 ≤ N := by omega
    simpa [R, jacobiSignAt] using
      jacobiTripleSign_rat_eq_sum_range_of_le (n := ij.2) (N := N) hle
  unfold jacobiThetaSquareCoeff jacobiThetaSquareCoeffExpanded
  calc
    (∑ ij ∈ Finset.antidiagonal N,
      ((jacobiTripleSign ij.1 : ℤ) : ℚ) * ((jacobiTripleSign ij.2 : ℤ) : ℚ))
        = ∑ ij ∈ Finset.antidiagonal N,
            (∑ r ∈ R, if triangularIndex r = ij.1 then jacobiSignAt r else 0) *
              (∑ s ∈ R, if triangularIndex s = ij.2 then jacobiSignAt s else 0) := by
            apply Finset.sum_congr rfl
            intro ij hij
            rw [hrew ij hij, hrew2 ij hij]
    _ = ∑ r ∈ R, ∑ s ∈ R,
          if triangularIndex r + triangularIndex s = N then
            jacobiSignAt r * jacobiSignAt s
          else 0 := by
          exact antidiagonal_indicator_product_nat N R R triangularIndex triangularIndex
            jacobiSignAt jacobiSignAt
    _ = ∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
          if triangularIndex r + triangularIndex s = N then
            jacobiSignAt r * jacobiSignAt s
          else 0 := by
          simp [R]

def pentagonalCoeffPairWeight (k l : ℤ) : ℚ :=
  negOnePowInt ℚ k * negOnePowInt ℚ l *
    (1 + 5 * ((pentagonal014Exp k : ℚ) - (pentagonal023Exp l : ℚ)))

theorem intCast_negOnePowInt_rat (k : ℤ) :
    ((negOnePowInt ℤ k : ℤ) : ℚ) = negOnePowInt ℚ k := by
  simp [negOnePowInt]

theorem pentagonalCoeffPairWeight_eq_wronskianRSWeight (k l : ℤ) :
    pentagonalCoeffPairWeight k l =
      ((wronskianRSWeight
        ((pentagonalToGauss k l).1 - (pentagonalToGauss k l).2)
        ((pentagonalToGauss k l).1 + (pentagonalToGauss k l).2) : ℤ) : ℚ) := by
  rw [pentagonalToGauss_wronskianCoeffWeight]
  unfold pentagonalCoeffPairWeight
  norm_cast
  simp [intCast_negOnePowInt_rat]

theorem pentagonalCoeffPairWeight_eq_gaussK (k l : ℤ) :
    pentagonalCoeffPairWeight k l =
      ((gaussK (pentagonalToGauss k l) : ℤ) : ℚ) := by
  rw [gaussK_pentagonalToGauss_eq_row0, pentagonalCoeffPairWeight_eq_wronskianRSWeight]

def pentagonalWronskianCoeffExpanded (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ),
    ∑ l ∈ Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ),
      if pentagonal014Exp k + pentagonal023Exp l = N then
        pentagonalCoeffPairWeight k l
      else 0

def pentagonalShellPairs (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ)).product
      (Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ)) |>.filter
    (fun kl => pentagonal014Exp kl.1 + pentagonal023Exp kl.2 = N)

def normShellBox (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(2 * (N : ℤ) + 1)) (2 * (N : ℤ) + 1)

/-- Full norm-shell Jacobi weight, normalized by the four sign symmetries.
The expected final orbit proof shows both expanded coefficient sums equal this
intermediate quantity. -/
def fullNormShellHQuarterSum (N : ℕ) : ℚ :=
  (∑ A ∈ normShellBox N,
    ∑ B ∈ normShellBox N,
      if A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1 then ((gaussH (A,B) : ℤ) : ℚ) else 0) / 4

def jacobiShellPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1)).product (Finset.range (N + 1)) |>.filter
    (fun rs => triangularIndex rs.1 + triangularIndex rs.2 = N)

def fullNormShell (N : ℕ) : Finset GaussianInt :=
  (normShellBox N).product (normShellBox N) |>.filter
    (fun z => z.1 ^ 2 + z.2 ^ 2 = 4 * (N : ℤ) + 1)

def pentagonalSectorPred (z : GaussianInt) : Prop :=
  (-z.1 - 3 * z.2) % 5 = 2 ∧ (3 * z.1 - z.2) % 5 = 4

instance : DecidablePred pentagonalSectorPred := by
  intro z
  unfold pentagonalSectorPred
  infer_instance

def pentagonalSector (N : ℕ) : Finset GaussianInt :=
  (fullNormShell N).filter pentagonalSectorPred

def fullNormShellKSum (N : ℕ) : ℚ :=
  ∑ z ∈ fullNormShell N, ((gaussK z : ℤ) : ℚ)

/-! ### Wide norm shells for 5-recurrence bookkeeping -/

def normShellBoxByNorm (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(M : ℤ)) (M : ℤ)

def normShellByNorm (M : ℕ) : Finset GaussianInt :=
  (normShellBoxByNorm M).product (normShellBoxByNorm M) |>.filter
    (fun z => z.1 ^ 2 + z.2 ^ 2 = (M : ℤ))

def normShellHSumByNorm (M : ℕ) : ℚ :=
  ∑ z ∈ normShellByNorm M, ((gaussH z : ℤ) : ℚ)

def normShellKSumByNorm (M : ℕ) : ℚ :=
  ∑ z ∈ normShellByNorm M, ((gaussK z : ℤ) : ℚ)

def piDividesExact (z : GaussianInt) : Prop :=
  (z.1 + 2 * z.2) % 5 = 0 ∧ (-2 * z.1 + z.2) % 5 = 0

def piBarDividesExact (z : GaussianInt) : Prop :=
  (z.1 - 2 * z.2) % 5 = 0 ∧ (2 * z.1 + z.2) % 5 = 0

instance : DecidablePred piDividesExact := by
  intro z
  unfold piDividesExact
  infer_instance

instance : DecidablePred piBarDividesExact := by
  intro z
  unfold piBarDividesExact
  infer_instance

def gaussPiDiv (z : GaussianInt) : GaussianInt :=
  ((z.1 + 2 * z.2) / 5, (-2 * z.1 + z.2) / 5)

def gaussPiBarDiv (z : GaussianInt) : GaussianInt :=
  ((z.1 - 2 * z.2) / 5, (2 * z.1 + z.2) / 5)

def gaussFiveDiv (z : GaussianInt) : GaussianInt :=
  (z.1 / 5, z.2 / 5)

@[simp] theorem piDividesExact_gaussMul_pi5 (z : GaussianInt) :
    piDividesExact (gaussMul pi5 z) := by
  rcases z with ⟨a, b⟩
  simp [piDividesExact, gaussMul, pi5]
  constructor <;> omega

@[simp] theorem piBarDividesExact_gaussMul_piBar5 (z : GaussianInt) :
    piBarDividesExact (gaussMul piBar5 z) := by
  rcases z with ⟨a, b⟩
  simp [piBarDividesExact, gaussMul, piBar5]
  constructor <;> omega

@[simp] theorem gaussPiDiv_gaussMul_pi5 (z : GaussianInt) :
    gaussPiDiv (gaussMul pi5 z) = z := by
  rcases z with ⟨a, b⟩
  ext
  · simp [gaussPiDiv, gaussMul, pi5]
    rw [show a - 2 * b + 2 * (b + 2 * a) = 5 * a by ring]
    exact Int.mul_ediv_cancel_left a (by norm_num : (5 : ℤ) ≠ 0)
  · simp [gaussPiDiv, gaussMul, pi5]
    rw [show -(2 * (a - 2 * b)) + (b + 2 * a) = 5 * b by ring]
    exact Int.mul_ediv_cancel_left b (by norm_num : (5 : ℤ) ≠ 0)

@[simp] theorem gaussPiBarDiv_gaussMul_piBar5 (z : GaussianInt) :
    gaussPiBarDiv (gaussMul piBar5 z) = z := by
  rcases z with ⟨a, b⟩
  ext
  · simp [gaussPiBarDiv, gaussMul, piBar5]
    rw [show a + 2 * b - 2 * (b + -(2 * a)) = 5 * a by ring]
    exact Int.mul_ediv_cancel_left a (by norm_num : (5 : ℤ) ≠ 0)
  · simp [gaussPiBarDiv, gaussMul, piBar5]
    rw [show 2 * (a + 2 * b) + (b + -(2 * a)) = 5 * b by ring]
    exact Int.mul_ediv_cancel_left b (by norm_num : (5 : ℤ) ≠ 0)

theorem gaussMul_pi5_gaussPiDiv_of_piDividesExact {z : GaussianInt}
    (hz : piDividesExact z) :
    gaussMul pi5 (gaussPiDiv z) = z := by
  rcases z with ⟨a, b⟩
  rcases hz with ⟨h1, h2⟩
  have h1dvd : (5 : ℤ) ∣ a + 2 * b := (Int.dvd_iff_emod_eq_zero).mpr h1
  have h2dvd : (5 : ℤ) ∣ -2 * a + b := (Int.dvd_iff_emod_eq_zero).mpr h2
  have h1mul : 5 * ((a + 2 * b) / 5) = a + 2 * b := by
    simpa [mul_comm] using Int.ediv_mul_cancel h1dvd
  have h2mul : 5 * ((-2 * a + b) / 5) = -2 * a + b := by
    simpa [mul_comm] using Int.ediv_mul_cancel h2dvd
  have h2mul' : 5 * (((-(2 * a) + b) / 5)) = -(2 * a) + b := by
    have harg : -(2 * a) + b = -2 * a + b := by ring
    rw [harg]
    exact h2mul
  ext
  · simp [gaussPiDiv, gaussMul, pi5]
    apply mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num)
    calc
      5 * ((a + 2 * b) / 5 - 2 * ((-(2 * a) + b) / 5))
          = 5 * ((a + 2 * b) / 5) -
              2 * (5 * ((-(2 * a) + b) / 5)) := by ring
      _ = (a + 2 * b) - 2 * (-(2 * a) + b) := by rw [h1mul, h2mul']
      _ = 5 * a := by ring
  · simp [gaussPiDiv, gaussMul, pi5]
    apply mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num)
    calc
      5 * ((-(2 * a) + b) / 5 + 2 * ((a + 2 * b) / 5))
          = 5 * ((-(2 * a) + b) / 5) +
              2 * (5 * ((a + 2 * b) / 5)) := by ring
      _ = (-(2 * a) + b) + 2 * (a + 2 * b) := by rw [h2mul', h1mul]
      _ = 5 * b := by ring

theorem gaussMul_piBar5_gaussPiBarDiv_of_piBarDividesExact {z : GaussianInt}
    (hz : piBarDividesExact z) :
    gaussMul piBar5 (gaussPiBarDiv z) = z := by
  rcases z with ⟨a, b⟩
  rcases hz with ⟨h1, h2⟩
  have h1dvd : (5 : ℤ) ∣ a - 2 * b := (Int.dvd_iff_emod_eq_zero).mpr h1
  have h2dvd : (5 : ℤ) ∣ 2 * a + b := (Int.dvd_iff_emod_eq_zero).mpr h2
  have h1mul : 5 * ((a - 2 * b) / 5) = a - 2 * b := by
    simpa [mul_comm] using Int.ediv_mul_cancel h1dvd
  have h2mul : 5 * ((2 * a + b) / 5) = 2 * a + b := by
    simpa [mul_comm] using Int.ediv_mul_cancel h2dvd
  ext
  · simp [gaussPiBarDiv, gaussMul, piBar5]
    apply mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num)
    nlinarith
  · simp [gaussPiBarDiv, gaussMul, piBar5]
    apply mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num)
    nlinarith

@[simp] theorem gaussFiveDiv_gaussMul_five (z : GaussianInt) :
    gaussFiveDiv (gaussMul (5,0) z) = z := by
  rcases z with ⟨a, b⟩
  ext <;> simp [gaussFiveDiv, gaussMul]

theorem gaussMul_five_gaussFiveDiv_of_five_dvd_coords {z : GaussianInt}
    (ha : z.1 % 5 = 0) (hb : z.2 % 5 = 0) :
    gaussMul (5,0) (gaussFiveDiv z) = z := by
  rcases z with ⟨a, b⟩
  have hadvd : (5 : ℤ) ∣ a := (Int.dvd_iff_emod_eq_zero).mpr ha
  have hbdvd : (5 : ℤ) ∣ b := (Int.dvd_iff_emod_eq_zero).mpr hb
  have hamul : 5 * (a / 5) = a := by
    simpa [mul_comm] using Int.ediv_mul_cancel hadvd
  have hbmul : 5 * (b / 5) = b := by
    simpa [mul_comm] using Int.ediv_mul_cancel hbdvd
  ext <;> simp [gaussFiveDiv, gaussMul, hamul, hbmul]

theorem pi_or_piBarDividesExact_zmod5 :
    ∀ x y : ZMod 5,
      x ^ 2 + y ^ 2 = 0 →
        (x + 2 * y = 0 ∧ -2 * x + y = 0) ∨
          (x - 2 * y = 0 ∧ 2 * x + y = 0) := by
  decide

theorem pi_or_piBarDividesExact_of_norm_mod_five_zero (z : GaussianInt)
    (h5 : gaussNormSq z % 5 = 0) :
    piDividesExact z ∨ piBarDividesExact z := by
  rcases z with ⟨a, b⟩
  have hz : (a : ZMod 5) ^ 2 + (b : ZMod 5) ^ 2 = 0 := by
    have hcast : (((a ^ 2 + b ^ 2 : ℤ) : ZMod 5) = 0) := by
      have hdvd : (5 : ℤ) ∣ a ^ 2 + b ^ 2 := by
        exact (Int.dvd_iff_emod_eq_zero).mpr (by simpa [gaussNormSq] using h5)
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + b ^ 2) 5).mpr hdvd
    simpa [Int.cast_pow] using hcast
  rcases pi_or_piBarDividesExact_zmod5 (a : ZMod 5) (b : ZMod 5) hz with hpi | hpibar
  · left
    constructor
    · have hm : (((a + 2 * b : ℤ) : ZMod 5) = (0 : ZMod 5)) := by
        simpa using hpi.1
      have hmod := (ZMod.intCast_eq_intCast_iff (a + 2 * b) 0 5).mp hm
      simpa using Int.ModEq.eq hmod
    · have hm : (((-2 * a + b : ℤ) : ZMod 5) = (0 : ZMod 5)) := by
        simpa using hpi.2
      have hmod := (ZMod.intCast_eq_intCast_iff (-2 * a + b) 0 5).mp hm
      simpa using Int.ModEq.eq hmod
  · right
    constructor
    · have hm : (((a - 2 * b : ℤ) : ZMod 5) = (0 : ZMod 5)) := by
        simpa using hpibar.1
      have hmod := (ZMod.intCast_eq_intCast_iff (a - 2 * b) 0 5).mp hm
      simpa using Int.ModEq.eq hmod
    · have hm : (((2 * a + b : ℤ) : ZMod 5) = (0 : ZMod 5)) := by
        simpa using hpibar.2
      have hmod := (ZMod.intCast_eq_intCast_iff (2 * a + b) 0 5).mp hm
      simpa using Int.ModEq.eq hmod

theorem five_dvd_coords_of_pi_and_piBarDividesExact {z : GaussianInt}
    (hpi : piDividesExact z) (hpibar : piBarDividesExact z) :
    z.1 % 5 = 0 ∧ z.2 % 5 = 0 := by
  rcases z with ⟨a, b⟩
  rcases hpi with ⟨hpi1, hpi2⟩
  rcases hpibar with ⟨hbar1, hbar2⟩
  constructor <;> omega

theorem pi_and_piBarDividesExact_of_five_dvd_coords {z : GaussianInt}
    (ha : z.1 % 5 = 0) (hb : z.2 % 5 = 0) :
    piDividesExact z ∧ piBarDividesExact z := by
  rcases z with ⟨a, b⟩
  constructor <;> constructor <;> omega

theorem mem_normShellBoxByNorm_of_norm_eq {M : ℕ} {A B : ℤ}
    (h : A ^ 2 + B ^ 2 = (M : ℤ)) :
    A ∈ normShellBoxByNorm M ∧ B ∈ normShellBoxByNorm M := by
  have hA_sq : A ^ 2 ≤ (M : ℤ) := by
    have hB : 0 ≤ B ^ 2 := sq_nonneg B
    nlinarith
  have hB_sq : B ^ 2 ≤ (M : ℤ) := by
    have hA : 0 ≤ A ^ 2 := sq_nonneg A
    nlinarith
  constructor
  · simp [normShellBoxByNorm]
    constructor
    · by_contra hlt
      push_neg at hlt
      nlinarith
    · by_contra hgt
      push_neg at hgt
      nlinarith
  · simp [normShellBoxByNorm]
    constructor
    · by_contra hlt
      push_neg at hlt
      nlinarith
    · by_contra hgt
      push_neg at hgt
      nlinarith

theorem normShellHSumByNorm_pi_reindex (M : ℕ) :
    (∑ z ∈ normShellByNorm M,
        ((gaussH (gaussMul pi5 z) : ℤ) : ℚ)) =
      ∑ w ∈ (normShellByNorm (5 * M)).filter piDividesExact,
        ((gaussH w : ℤ) : ℚ) := by
  refine Finset.sum_bij'
    (fun z _hz => gaussMul pi5 z)
    (fun w _hw => gaussPiDiv w)
    ?hi ?hj ?left ?right ?h
  · intro z hz
    rw [Finset.mem_filter]
    constructor
    · have hz' := hz
      rw [normShellByNorm, Finset.mem_filter] at hz'
      have hzNorm : gaussNormSq z = (M : ℤ) := by
        simpa [gaussNormSq] using hz'.2
      have hnorm : (gaussMul pi5 z).1 ^ 2 + (gaussMul pi5 z).2 ^ 2 =
          ((5 * M : ℕ) : ℤ) := by
        have hmul := gaussNormSq_mul pi5 z
        rw [gaussNormSq_pi5, hzNorm] at hmul
        simpa [gaussNormSq, Nat.cast_mul] using hmul
      have hbox := mem_normShellBoxByNorm_of_norm_eq (M := 5 * M) hnorm
      simp [normShellByNorm, hbox.1, hbox.2, hnorm]
    · exact piDividesExact_gaussMul_pi5 z
  · intro w hw
    rw [Finset.mem_filter] at hw
    rcases hw with ⟨hwShell, hwPi⟩
    have hwShell' := hwShell
    rw [normShellByNorm, Finset.mem_filter] at hwShell'
    have hwNorm : gaussNormSq w = ((5 * M : ℕ) : ℤ) := by
      simpa [gaussNormSq] using hwShell'.2
    have hright := gaussMul_pi5_gaussPiDiv_of_piDividesExact hwPi
    have hnormDiv : gaussNormSq (gaussPiDiv w) = (M : ℤ) := by
      have hnormEq := congrArg gaussNormSq hright
      rw [gaussNormSq_mul, gaussNormSq_pi5, hwNorm] at hnormEq
      apply mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num)
      simpa [Nat.cast_mul] using hnormEq
    have hbox := mem_normShellBoxByNorm_of_norm_eq
      (M := M) (by simpa [gaussNormSq] using hnormDiv)
    rw [normShellByNorm, Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr ⟨hbox.1, hbox.2⟩
    · simpa [gaussNormSq] using hnormDiv
  · intro z hz
    exact gaussPiDiv_gaussMul_pi5 z
  · intro w hw
    rw [Finset.mem_filter] at hw
    exact gaussMul_pi5_gaussPiDiv_of_piDividesExact hw.2
  · intro z hz
    rfl

theorem normShellHSumByNorm_piBar_reindex (M : ℕ) :
    (∑ z ∈ normShellByNorm M,
        ((gaussH (gaussMul piBar5 z) : ℤ) : ℚ)) =
      ∑ w ∈ (normShellByNorm (5 * M)).filter piBarDividesExact,
        ((gaussH w : ℤ) : ℚ) := by
  refine Finset.sum_bij'
    (fun z _hz => gaussMul piBar5 z)
    (fun w _hw => gaussPiBarDiv w)
    ?hi ?hj ?left ?right ?h
  · intro z hz
    rw [Finset.mem_filter]
    constructor
    · have hz' := hz
      rw [normShellByNorm, Finset.mem_filter] at hz'
      have hzNorm : gaussNormSq z = (M : ℤ) := by
        simpa [gaussNormSq] using hz'.2
      have hnorm : (gaussMul piBar5 z).1 ^ 2 + (gaussMul piBar5 z).2 ^ 2 =
          ((5 * M : ℕ) : ℤ) := by
        have hmul := gaussNormSq_mul piBar5 z
        rw [gaussNormSq_piBar5, hzNorm] at hmul
        simpa [gaussNormSq, Nat.cast_mul] using hmul
      have hbox := mem_normShellBoxByNorm_of_norm_eq (M := 5 * M) hnorm
      simp [normShellByNorm, hbox.1, hbox.2, hnorm]
    · exact piBarDividesExact_gaussMul_piBar5 z
  · intro w hw
    rw [Finset.mem_filter] at hw
    rcases hw with ⟨hwShell, hwPiBar⟩
    have hwShell' := hwShell
    rw [normShellByNorm, Finset.mem_filter] at hwShell'
    have hwNorm : gaussNormSq w = ((5 * M : ℕ) : ℤ) := by
      simpa [gaussNormSq] using hwShell'.2
    have hright := gaussMul_piBar5_gaussPiBarDiv_of_piBarDividesExact hwPiBar
    have hnormDiv : gaussNormSq (gaussPiBarDiv w) = (M : ℤ) := by
      have hnormEq := congrArg gaussNormSq hright
      rw [gaussNormSq_mul, gaussNormSq_piBar5, hwNorm] at hnormEq
      apply mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num)
      simpa [Nat.cast_mul] using hnormEq
    have hbox := mem_normShellBoxByNorm_of_norm_eq
      (M := M) (by simpa [gaussNormSq] using hnormDiv)
    rw [normShellByNorm, Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr ⟨hbox.1, hbox.2⟩
    · simpa [gaussNormSq] using hnormDiv
  · intro z hz
    exact gaussPiBarDiv_gaussMul_piBar5 z
  · intro w hw
    rw [Finset.mem_filter] at hw
    exact gaussMul_piBar5_gaussPiBarDiv_of_piBarDividesExact hw.2
  · intro z hz
    rfl

theorem normShellHSumByNorm_five_filter_decomp (M : ℕ) :
    normShellHSumByNorm (5 * M) =
      (∑ z ∈ (normShellByNorm (5 * M)).filter piDividesExact,
        ((gaussH z : ℤ) : ℚ)) +
      (∑ z ∈ (normShellByNorm (5 * M)).filter piBarDividesExact,
        ((gaussH z : ℤ) : ℚ)) -
      ∑ z ∈ (normShellByNorm (5 * M)).filter
          (fun z => piDividesExact z ∧ piBarDividesExact z),
        ((gaussH z : ℤ) : ℚ) := by
  let S := normShellByNorm (5 * M)
  let W : GaussianInt → ℚ := fun z => ((gaussH z : ℤ) : ℚ)
  have hcover : ∀ z ∈ S, piDividesExact z ∨ piBarDividesExact z := by
    intro z hz
    have hz' := hz
    dsimp [S] at hz'
    rw [normShellByNorm, Finset.mem_filter] at hz'
    have hnorm : gaussNormSq z = ((5 * M : ℕ) : ℤ) := by
      simpa [gaussNormSq] using hz'.2
    apply pi_or_piBarDividesExact_of_norm_mod_five_zero
    rw [hnorm]
    omega
  have hpoint : ∀ z ∈ S,
      W z =
        (if piDividesExact z then W z else 0) +
          (if piBarDividesExact z then W z else 0) -
          (if piDividesExact z ∧ piBarDividesExact z then W z else 0) := by
    intro z hz
    rcases hcover z hz with hpi | hpibar
    · by_cases hbar : piBarDividesExact z <;> simp [W, hpi, hbar]
    · by_cases hpi : piDividesExact z <;> simp [W, hpi, hpibar]
  calc
    normShellHSumByNorm (5 * M)
        = ∑ z ∈ S, W z := by
            simp [normShellHSumByNorm, S, W]
    _ = ∑ z ∈ S,
          ((if piDividesExact z then W z else 0) +
            (if piBarDividesExact z then W z else 0) -
            (if piDividesExact z ∧ piBarDividesExact z then W z else 0)) := by
            apply Finset.sum_congr rfl
            intro z hz
            exact hpoint z hz
    _ =
      (∑ z ∈ S, if piDividesExact z then W z else 0) +
      (∑ z ∈ S, if piBarDividesExact z then W z else 0) -
      ∑ z ∈ S, if piDividesExact z ∧ piBarDividesExact z then W z else 0 := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ =
      (∑ z ∈ S.filter piDividesExact, W z) +
      (∑ z ∈ S.filter piBarDividesExact, W z) -
      ∑ z ∈ S.filter (fun z => piDividesExact z ∧ piBarDividesExact z), W z := by
        rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
    _ =
      (∑ z ∈ (normShellByNorm (5 * M)).filter piDividesExact,
        ((gaussH z : ℤ) : ℚ)) +
      (∑ z ∈ (normShellByNorm (5 * M)).filter piBarDividesExact,
        ((gaussH z : ℤ) : ℚ)) -
      ∑ z ∈ (normShellByNorm (5 * M)).filter
          (fun z => piDividesExact z ∧ piBarDividesExact z),
        ((gaussH z : ℤ) : ℚ) := by
        simp [S, W]

theorem normShellHSumByNorm_pi_filters_add (M : ℕ) :
    (∑ z ∈ (normShellByNorm (5 * M)).filter piDividesExact,
        ((gaussH z : ℤ) : ℚ)) +
      (∑ z ∈ (normShellByNorm (5 * M)).filter piBarDividesExact,
        ((gaussH z : ℤ) : ℚ)) =
      -6 * normShellHSumByNorm M := by
  rw [← normShellHSumByNorm_pi_reindex M,
    ← normShellHSumByNorm_piBar_reindex M]
  calc
    (∑ z ∈ normShellByNorm M, ((gaussH (gaussMul pi5 z) : ℤ) : ℚ)) +
        (∑ z ∈ normShellByNorm M, ((gaussH (gaussMul piBar5 z) : ℤ) : ℚ))
        = ∑ z ∈ normShellByNorm M,
            (((gaussH (gaussMul pi5 z) : ℤ) : ℚ) +
              ((gaussH (gaussMul piBar5 z) : ℤ) : ℚ)) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ z ∈ normShellByNorm M, -6 * ((gaussH z : ℤ) : ℚ) := by
            apply Finset.sum_congr rfl
            intro z _hz
            rcases z with ⟨a, b⟩
            exact_mod_cast gaussH_pi5_add_piBar5 a b
    _ = -6 * normShellHSumByNorm M := by
            rw [← Finset.mul_sum]
            simp [normShellHSumByNorm]

theorem normShellHSumByNorm_inter_filter_reindex_of_five_dvd
    (M : ℕ) (hM : M % 5 = 0) :
    (∑ z ∈ (normShellByNorm (5 * M)).filter
        (fun z => piDividesExact z ∧ piBarDividesExact z),
        ((gaussH z : ℤ) : ℚ)) =
      25 * normShellHSumByNorm (M / 5) := by
  have hdiv : 5 ∣ M := Nat.dvd_of_mod_eq_zero hM
  have hMmul : 5 * (M / 5) = M := Nat.mul_div_cancel' hdiv
  have hMcast : (M : ℤ) = 5 * ((M / 5 : ℕ) : ℤ) := by
    exact_mod_cast hMmul.symm
  have hbij :
      (∑ z ∈ normShellByNorm (M / 5),
          ((gaussH (gaussMul (5,0) z) : ℤ) : ℚ)) =
        ∑ w ∈ (normShellByNorm (5 * M)).filter
            (fun w => piDividesExact w ∧ piBarDividesExact w),
          ((gaussH w : ℤ) : ℚ) := by
    refine Finset.sum_bij'
      (fun z _hz => gaussMul (5,0) z)
      (fun w _hw => gaussFiveDiv w)
      ?hi ?hj ?left ?right ?h
    · intro z hz
      rw [Finset.mem_filter]
      constructor
      · have hz' := hz
        rw [normShellByNorm, Finset.mem_filter] at hz'
        have hzNorm : gaussNormSq z = ((M / 5 : ℕ) : ℤ) := by
          simpa [gaussNormSq] using hz'.2
        have hnorm : (gaussMul (5,0) z).1 ^ 2 + (gaussMul (5,0) z).2 ^ 2 =
            ((5 * M : ℕ) : ℤ) := by
          have hmul := gaussNormSq_mul (5,0) z
          have hfive : gaussNormSq (5,0) = 25 := by norm_num [gaussNormSq]
          rw [hfive, hzNorm] at hmul
          have htarget : gaussNormSq (gaussMul (5,0) z) = ((5 * M : ℕ) : ℤ) := by
            rw [hmul]
            norm_num [Nat.cast_mul]
            nlinarith
          simpa [gaussNormSq] using htarget
        have hbox := mem_normShellBoxByNorm_of_norm_eq (M := 5 * M) hnorm
        rw [normShellByNorm, Finset.mem_filter]
        constructor
        · simpa [gaussMul_five_left] using Finset.mem_product.mpr ⟨hbox.1, hbox.2⟩
        · simpa [gaussMul_five_left, Nat.cast_mul] using hnorm
      · have hcoords : (gaussMul (5,0) z).1 % 5 = 0 ∧
            (gaussMul (5,0) z).2 % 5 = 0 := by
          rcases z with ⟨a, b⟩
          simp [gaussMul]
        exact pi_and_piBarDividesExact_of_five_dvd_coords hcoords.1 hcoords.2
    · intro w hw
      rw [Finset.mem_filter] at hw
      rcases hw with ⟨hwShell, hboth⟩
      have hcoords := five_dvd_coords_of_pi_and_piBarDividesExact hboth.1 hboth.2
      have hright := gaussMul_five_gaussFiveDiv_of_five_dvd_coords hcoords.1 hcoords.2
      have hwShell' := hwShell
      rw [normShellByNorm, Finset.mem_filter] at hwShell'
      have hwNorm : gaussNormSq w = ((5 * M : ℕ) : ℤ) := by
        simpa [gaussNormSq] using hwShell'.2
      have hnormDiv : gaussNormSq (gaussFiveDiv w) = ((M / 5 : ℕ) : ℤ) := by
        have hnormEq := congrArg gaussNormSq hright
        rw [gaussNormSq_mul] at hnormEq
        have hfive : gaussNormSq (5,0) = 25 := by norm_num [gaussNormSq]
        rw [hfive, hwNorm] at hnormEq
        norm_num [Nat.cast_mul] at hnormEq
        nlinarith
      have hbox := mem_normShellBoxByNorm_of_norm_eq
        (M := M / 5) (by simpa [gaussNormSq] using hnormDiv)
      rw [normShellByNorm, Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨hbox.1, hbox.2⟩
      · simpa [gaussNormSq] using hnormDiv
    · intro z hz
      exact gaussFiveDiv_gaussMul_five z
    · intro w hw
      rw [Finset.mem_filter] at hw
      have hcoords := five_dvd_coords_of_pi_and_piBarDividesExact hw.2.1 hw.2.2
      exact gaussMul_five_gaussFiveDiv_of_five_dvd_coords hcoords.1 hcoords.2
    · intro z hz
      rfl
  calc
    (∑ z ∈ (normShellByNorm (5 * M)).filter
        (fun z => piDividesExact z ∧ piBarDividesExact z),
        ((gaussH z : ℤ) : ℚ))
        = ∑ z ∈ normShellByNorm (M / 5),
            ((gaussH (gaussMul (5,0) z) : ℤ) : ℚ) := hbij.symm
    _ = ∑ z ∈ normShellByNorm (M / 5),
          25 * ((gaussH z : ℤ) : ℚ) := by
          apply Finset.sum_congr rfl
          intro z _hz
          exact_mod_cast gaussH_five_mul z
    _ = 25 * normShellHSumByNorm (M / 5) := by
          rw [← Finset.mul_sum]
          simp [normShellHSumByNorm]

theorem normShellHSumByNorm_inter_filter_eq_zero_of_not_five_dvd
    (M : ℕ) (hM : M % 5 ≠ 0) :
    (∑ z ∈ (normShellByNorm (5 * M)).filter
        (fun z => piDividesExact z ∧ piBarDividesExact z),
        ((gaussH z : ℤ) : ℚ)) = 0 := by
  have hMZ : ((M : ℤ) % 5) ≠ 0 := by omega
  apply Finset.sum_eq_zero
  intro z hz
  rw [Finset.mem_filter] at hz
  rcases hz with ⟨hzShell, hboth⟩
  rcases z with ⟨a, b⟩
  have hcoords := five_dvd_coords_of_pi_and_piBarDividesExact hboth.1 hboth.2
  have hadvd : (5 : ℤ) ∣ a := (Int.dvd_iff_emod_eq_zero).mpr hcoords.1
  have hbdvd : (5 : ℤ) ∣ b := (Int.dvd_iff_emod_eq_zero).mpr hcoords.2
  rcases hadvd with ⟨a0, ha0⟩
  rcases hbdvd with ⟨b0, hb0⟩
  rw [normShellByNorm, Finset.mem_filter] at hzShell
  have hnorm : a ^ 2 + b ^ 2 = ((5 * M : ℕ) : ℤ) := by
    simpa [gaussNormSq] using hzShell.2
  rw [ha0, hb0] at hnorm
  norm_num [Nat.cast_mul] at hnorm
  have hMeq : (M : ℤ) = 5 * (a0 ^ 2 + b0 ^ 2) := by
    nlinarith
  have hMzero : ((M : ℤ) % 5) = 0 := by
    rw [hMeq]
    omega
  exact False.elim (hMZ hMzero)

theorem normShellHSumByNorm_five_mul_recurrence_of_five_dvd
    (M : ℕ) (hM : M % 5 = 0) :
    normShellHSumByNorm (5 * M) =
      -6 * normShellHSumByNorm M - 25 * normShellHSumByNorm (M / 5) := by
  rw [normShellHSumByNorm_five_filter_decomp,
    normShellHSumByNorm_pi_filters_add,
    normShellHSumByNorm_inter_filter_reindex_of_five_dvd M hM]

theorem normShellHSumByNorm_five_mul_recurrence_of_not_five_dvd
    (M : ℕ) (hM : M % 5 ≠ 0) :
    normShellHSumByNorm (5 * M) =
      -6 * normShellHSumByNorm M := by
  rw [normShellHSumByNorm_five_filter_decomp,
    normShellHSumByNorm_pi_filters_add,
    normShellHSumByNorm_inter_filter_eq_zero_of_not_five_dvd M hM]
  ring

theorem normShellKSumByNorm_pi_reindex (M : ℕ) :
    (∑ z ∈ normShellByNorm M,
        ((gaussK (gaussMul pi5 z) : ℤ) : ℚ)) =
      ∑ w ∈ (normShellByNorm (5 * M)).filter piDividesExact,
        ((gaussK w : ℤ) : ℚ) := by
  refine Finset.sum_bij'
    (fun z _hz => gaussMul pi5 z)
    (fun w _hw => gaussPiDiv w)
    ?hi ?hj ?left ?right ?h
  · intro z hz
    rw [Finset.mem_filter]
    constructor
    · have hz' := hz
      rw [normShellByNorm, Finset.mem_filter] at hz'
      have hzNorm : gaussNormSq z = (M : ℤ) := by
        simpa [gaussNormSq] using hz'.2
      have hnorm : (gaussMul pi5 z).1 ^ 2 + (gaussMul pi5 z).2 ^ 2 =
          ((5 * M : ℕ) : ℤ) := by
        have hmul := gaussNormSq_mul pi5 z
        rw [gaussNormSq_pi5, hzNorm] at hmul
        simpa [gaussNormSq, Nat.cast_mul] using hmul
      have hbox := mem_normShellBoxByNorm_of_norm_eq (M := 5 * M) hnorm
      simp [normShellByNorm, hbox.1, hbox.2, hnorm]
    · exact piDividesExact_gaussMul_pi5 z
  · intro w hw
    rw [Finset.mem_filter] at hw
    rcases hw with ⟨hwShell, hwPi⟩
    have hwShell' := hwShell
    rw [normShellByNorm, Finset.mem_filter] at hwShell'
    have hwNorm : gaussNormSq w = ((5 * M : ℕ) : ℤ) := by
      simpa [gaussNormSq] using hwShell'.2
    have hright := gaussMul_pi5_gaussPiDiv_of_piDividesExact hwPi
    have hnormDiv : gaussNormSq (gaussPiDiv w) = (M : ℤ) := by
      have hnormEq := congrArg gaussNormSq hright
      rw [gaussNormSq_mul, gaussNormSq_pi5, hwNorm] at hnormEq
      apply mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num)
      simpa [Nat.cast_mul] using hnormEq
    have hbox := mem_normShellBoxByNorm_of_norm_eq
      (M := M) (by simpa [gaussNormSq] using hnormDiv)
    rw [normShellByNorm, Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr ⟨hbox.1, hbox.2⟩
    · simpa [gaussNormSq] using hnormDiv
  · intro z hz
    exact gaussPiDiv_gaussMul_pi5 z
  · intro w hw
    rw [Finset.mem_filter] at hw
    exact gaussMul_pi5_gaussPiDiv_of_piDividesExact hw.2
  · intro z hz
    rfl

theorem gaussK_eq_zero_of_piBarDividesExact {z : GaussianInt}
    (hz : piBarDividesExact z) :
    gaussK z = 0 := by
  have hmul := gaussMul_piBar5_gaussPiBarDiv_of_piBarDividesExact hz
  rw [← hmul]
  rcases gaussPiBarDiv z with ⟨a, b⟩
  exact gaussK_piBar5_mul a b

theorem gaussK_gaussMul_five_eq_zero (z : GaussianInt) :
    gaussK (gaussMul (5,0) z) = 0 := by
  rcases z with ⟨a, b⟩
  simpa [gaussMul_five_left] using gaussK_of_five_dvd_coords a b

theorem gaussK_gaussMul_pi5_eq_zero_of_piBarDividesExact {z : GaussianInt}
    (hz : piBarDividesExact z) :
    gaussK (gaussMul pi5 z) = 0 := by
  have hmul := gaussMul_piBar5_gaussPiBarDiv_of_piBarDividesExact hz
  rw [← hmul]
  rw [← gaussMul_assoc, gaussMul_pi5_piBar5]
  exact gaussK_gaussMul_five_eq_zero (gaussPiBarDiv z)

theorem gaussK_gaussMul_pi5_pi5_eq_zero_of_piBarDividesExact {z : GaussianInt}
    (hz : piBarDividesExact z) :
    gaussK (gaussMul pi5 (gaussMul pi5 z)) = 0 := by
  have hmul := gaussMul_piBar5_gaussPiBarDiv_of_piBarDividesExact hz
  rw [← hmul]
  rw [show gaussMul pi5 (gaussMul pi5 (gaussMul piBar5 (gaussPiBarDiv z))) =
      gaussMul (5,0) (gaussMul pi5 (gaussPiBarDiv z)) by
    rcases gaussPiBarDiv z with ⟨a, b⟩
    ext <;> simp [gaussMul, pi5, piBar5] <;> ring]
  exact gaussK_gaussMul_five_eq_zero (gaussMul pi5 (gaussPiBarDiv z))

theorem wronskianSelector_exists_of_piDividesExact_not_piBar
    (a b : ℤ) (hpi : piDividesExact (a,b))
    (hbar : ¬ piBarDividesExact (a,b)) :
    (-a - 3 * b) % 5 = 2 ∨ (-3 * a + b) % 5 = 2 ∨
      (a + 3 * b) % 5 = 2 ∨ (3 * a - b) % 5 = 2 := by
  unfold piDividesExact at hpi
  change ¬ ((a - 2 * b) % 5 = 0 ∧ (2 * a + b) % 5 = 0) at hbar
  have hb0 : b % 5 ≠ 0 := by
    intro hb
    apply hbar
    constructor <;> omega
  have hb_nonneg : 0 ≤ b % 5 :=
    Int.emod_nonneg b (by norm_num : (5 : ℤ) ≠ 0)
  have hb_lt : b % 5 < 5 :=
    Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 5)
  have hbcases : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by
    omega
  rcases hbcases with hb1 | hb2 | hb3 | hb4
  · right
    left
    omega
  · right
    right
    left
    omega
  · left
    omega
  · right
    right
    right
    omega

theorem wronskianSelector_exists_of_not_piBarDividesExact
    (a b : ℤ) (hbar : ¬ piBarDividesExact (a,b)) :
    (-a - 3 * b) % 5 = 2 ∨ (-3 * a + b) % 5 = 2 ∨
      (a + 3 * b) % 5 = 2 ∨ (3 * a - b) % 5 = 2 := by
  by_cases h5 : (a ^ 2 + b ^ 2) % 5 ≠ 0
  · exact wronskianSelector_exists_int a b h5
  · have h5zero : gaussNormSq (a,b) % 5 = 0 := by
      simp [gaussNormSq]
      omega
    rcases pi_or_piBarDividesExact_of_norm_mod_five_zero (a,b) h5zero with hpi | hpibar
    · exact wronskianSelector_exists_of_piDividesExact_not_piBar a b hpi hbar
    · exact False.elim (hbar hpibar)

theorem two_mul_neg_wronskianCore_eq_piEndpointPart (a b : ℤ)
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1) :
    2 * (-wronskianCore a b) = piEndpointPart (a,b) := by
  let N : ℤ := (-a - 3 * b) ^ 2 - (3 * a - b) ^ 2
  have hNdiv : 8 ∣ N := by
    simpa [N] using
      wronskianCore_num_dvd_eight_of_norm_odd (a := a) (b := b) hodd
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  change 4 * (2 * (-(N / 8))) = 4 * piEndpointPart (a,b)
  rw [show 4 * (2 * (-(N / 8))) = -(8 * (N / 8)) by ring]
  rw [show 8 * (N / 8) = N by
    simpa [mul_comm] using Int.ediv_mul_cancel hNdiv]
  simp [N, piEndpointPart, gaussA, gaussB]
  ring

theorem two_mul_gaussK_eq_eps_piEndpointPart_of_not_piBarDividesExact
    (z : GaussianInt) (hodd : gaussNormSq z % 2 = 1)
    (hbar : ¬ piBarDividesExact z) :
    2 * gaussK z = gaussEps z.1 * piEndpointPart z := by
  rcases z with ⟨a, b⟩
  have hodd' : (a ^ 2 + b ^ 2) % 2 = 1 := by
    simpa [gaussNormSq] using hodd
  have hsel := wronskianSelector_exists_of_not_piBarDividesExact a b hbar
  rw [gaussK_eq_neg_eps_mul_core_of_selector hodd' hsel]
  rw [← two_mul_neg_wronskianCore_eq_piEndpointPart a b hodd']
  ring

theorem not_piBarDividesExact_gaussMul_pi5_of_not {z : GaussianInt}
    (hbar : ¬ piBarDividesExact z) :
    ¬ piBarDividesExact (gaussMul pi5 z) := by
  rcases z with ⟨a, b⟩
  intro h
  apply hbar
  unfold piBarDividesExact at h ⊢
  simp [gaussMul, pi5] at h ⊢
  omega

@[simp] theorem gaussEps_gaussMul_pi5_fst (z : GaussianInt) :
    gaussEps (gaussMul pi5 z).1 = gaussEps z.1 := by
  rcases z with ⟨a, b⟩
  simp [gaussMul_pi5_left]

theorem gaussNormSq_gaussMul_pi5_mod_two {z : GaussianInt}
    (hodd : gaussNormSq z % 2 = 1) :
    gaussNormSq (gaussMul pi5 z) % 2 = 1 := by
  rw [gaussNormSq_mul, gaussNormSq_pi5]
  omega

theorem gaussK_pi5_second_order_of_norm_odd (z : GaussianInt)
    (hodd : gaussNormSq z % 2 = 1) :
    gaussK (gaussMul pi5 (gaussMul pi5 z)) =
      -6 * gaussK (gaussMul pi5 z) - 25 * gaussK z := by
  by_cases hbar : piBarDividesExact z
  · rw [gaussK_eq_zero_of_piBarDividesExact hbar,
      gaussK_gaussMul_pi5_eq_zero_of_piBarDividesExact hbar,
      gaussK_gaussMul_pi5_pi5_eq_zero_of_piBarDividesExact hbar]
    ring
  · have hbar1 : ¬ piBarDividesExact (gaussMul pi5 z) :=
      not_piBarDividesExact_gaussMul_pi5_of_not hbar
    have hbar2 : ¬ piBarDividesExact (gaussMul pi5 (gaussMul pi5 z)) :=
      not_piBarDividesExact_gaussMul_pi5_of_not hbar1
    have hodd1 : gaussNormSq (gaussMul pi5 z) % 2 = 1 :=
      gaussNormSq_gaussMul_pi5_mod_two hodd
    have hodd2 : gaussNormSq (gaussMul pi5 (gaussMul pi5 z)) % 2 = 1 :=
      gaussNormSq_gaussMul_pi5_mod_two hodd1
    have hK0 := two_mul_gaussK_eq_eps_piEndpointPart_of_not_piBarDividesExact
      z hodd hbar
    have hK1 := two_mul_gaussK_eq_eps_piEndpointPart_of_not_piBarDividesExact
      (gaussMul pi5 z) hodd1 hbar1
    have hK2 := two_mul_gaussK_eq_eps_piEndpointPart_of_not_piBarDividesExact
      (gaussMul pi5 (gaussMul pi5 z)) hodd2 hbar2
    have hK1' :
        2 * gaussK (gaussMul pi5 z) =
          gaussEps z.1 * piEndpointPart (gaussMul pi5 z) := by
      simpa using hK1
    have hK2' :
        2 * gaussK (gaussMul pi5 (gaussMul pi5 z)) =
          gaussEps z.1 * piEndpointPart (gaussMul pi5 (gaussMul pi5 z)) := by
      simpa using hK2
    have hrec := piEndpointPart_pi5_pi5 z
    apply mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num)
    calc
      2 * gaussK (gaussMul pi5 (gaussMul pi5 z))
          = gaussEps z.1 * piEndpointPart (gaussMul pi5 (gaussMul pi5 z)) := by
              exact hK2'
      _ = gaussEps z.1 *
            (-6 * piEndpointPart (gaussMul pi5 z) - 25 * piEndpointPart z) := by
              rw [hrec]
      _ = -6 * (gaussEps z.1 * piEndpointPart (gaussMul pi5 z)) -
            25 * (gaussEps z.1 * piEndpointPart z) := by ring
      _ = -6 * (2 * gaussK (gaussMul pi5 z)) - 25 * (2 * gaussK z) := by
              rw [← hK1', ← hK0]
      _ = 2 * (-6 * gaussK (gaussMul pi5 z) - 25 * gaussK z) := by ring

theorem normShellKSumByNorm_five_eq_pi_filter (M : ℕ) :
    normShellKSumByNorm (5 * M) =
      ∑ z ∈ (normShellByNorm (5 * M)).filter piDividesExact,
        ((gaussK z : ℤ) : ℚ) := by
  let S := normShellByNorm (5 * M)
  let W : GaussianInt → ℚ := fun z => ((gaussK z : ℤ) : ℚ)
  have hcover : ∀ z ∈ S, piDividesExact z ∨ piBarDividesExact z := by
    intro z hz
    have hz' := hz
    dsimp [S] at hz'
    rw [normShellByNorm, Finset.mem_filter] at hz'
    have hnorm : gaussNormSq z = ((5 * M : ℕ) : ℤ) := by
      simpa [gaussNormSq] using hz'.2
    apply pi_or_piBarDividesExact_of_norm_mod_five_zero
    rw [hnorm]
    omega
  have hpoint : ∀ z ∈ S, W z = if piDividesExact z then W z else 0 := by
    intro z hz
    rcases hcover z hz with hpi | hpibar
    · simp [W, hpi]
    · by_cases hpi : piDividesExact z
      · simp [W, hpi]
      · have hk0 : gaussK z = 0 := gaussK_eq_zero_of_piBarDividesExact hpibar
        simp [W, hpi, hk0]
  calc
    normShellKSumByNorm (5 * M)
        = ∑ z ∈ S, W z := by
            simp [normShellKSumByNorm, S, W]
    _ = ∑ z ∈ S, if piDividesExact z then W z else 0 := by
            apply Finset.sum_congr rfl
            intro z hz
            exact hpoint z hz
    _ = ∑ z ∈ S.filter piDividesExact, W z := by
            rw [← Finset.sum_filter]
    _ = ∑ z ∈ (normShellByNorm (5 * M)).filter piDividesExact,
        ((gaussK z : ℤ) : ℚ) := by
            simp [S, W]

theorem normShellKSumByNorm_five_eq_pi_sum (M : ℕ) :
    normShellKSumByNorm (5 * M) =
      ∑ z ∈ normShellByNorm M, ((gaussK (gaussMul pi5 z) : ℤ) : ℚ) := by
  rw [normShellKSumByNorm_five_eq_pi_filter,
    ← normShellKSumByNorm_pi_reindex]

theorem gaussConj_mem_normShellByNorm {M : ℕ} {z : GaussianInt}
    (hz : z ∈ normShellByNorm M) :
    gaussConj z ∈ normShellByNorm M := by
  rw [normShellByNorm, Finset.mem_filter] at hz ⊢
  rcases hz with ⟨_hbox, hnorm⟩
  have hnorm' : (gaussConj z).1 ^ 2 + (gaussConj z).2 ^ 2 = (M : ℤ) := by
    simpa [gaussConj] using hnorm
  have hbox := mem_normShellBoxByNorm_of_norm_eq (M := M) hnorm'
  constructor
  · exact Finset.mem_product.mpr ⟨hbox.1, hbox.2⟩
  · exact hnorm'

@[simp] theorem gaussConj_gaussConj (z : GaussianInt) :
    gaussConj (gaussConj z) = z := by
  rcases z with ⟨a, b⟩
  simp [gaussConj]

theorem normShellK_pi_sum_recurrence_of_not_five_dvd
    (M : ℕ) (hoddM : ((M : ℤ) % 2) = 1) (h5M : ((M : ℤ) % 5) ≠ 0) :
    (∑ z ∈ normShellByNorm M, ((gaussK (gaussMul pi5 z) : ℤ) : ℚ)) =
      -6 * normShellKSumByNorm M := by
  let F : GaussianInt → ℚ := fun z => ((gaussK (gaussMul pi5 z) : ℤ) : ℚ)
  let G : GaussianInt → ℚ := fun z => ((gaussK z : ℤ) : ℚ)
  have hconj_sum : ∀ F' : GaussianInt → ℚ,
      (∑ z ∈ normShellByNorm M, F' (gaussConj z)) =
        ∑ z ∈ normShellByNorm M, F' z := by
    intro F'
    refine Finset.sum_bij'
      (fun z _hz => gaussConj z)
      (fun z _hz => gaussConj z)
      ?hi ?hj ?left ?right ?h
    · intro z hz
      exact gaussConj_mem_normShellByNorm hz
    · intro z hz
      exact gaussConj_mem_normShellByNorm hz
    · intro z hz
      simp
    · intro z hz
      simp
    · intro z hz
      rfl
  have hdouble : ∀ F' : GaussianInt → ℚ,
      2 * (∑ z ∈ normShellByNorm M, F' z) =
        ∑ z ∈ normShellByNorm M, (F' z + F' (gaussConj z)) := by
    intro F'
    calc
      2 * (∑ z ∈ normShellByNorm M, F' z)
          = (∑ z ∈ normShellByNorm M, F' z) +
              (∑ z ∈ normShellByNorm M, F' z) := by ring
      _ = (∑ z ∈ normShellByNorm M, F' z) +
              (∑ z ∈ normShellByNorm M, F' (gaussConj z)) := by
              rw [hconj_sum F']
      _ = ∑ z ∈ normShellByNorm M, (F' z + F' (gaussConj z)) := by
              rw [Finset.sum_add_distrib]
  have hpair_sum :
      (∑ z ∈ normShellByNorm M, (F z + F (gaussConj z))) =
        ∑ z ∈ normShellByNorm M, -6 * (G z + G (gaussConj z)) := by
    apply Finset.sum_congr rfl
    intro z hz
    rcases z with ⟨a, b⟩
    rw [normShellByNorm, Finset.mem_filter] at hz
    have hnorm : a ^ 2 + b ^ 2 = (M : ℤ) := by
      simpa [gaussNormSq] using hz.2
    have hodd : (a ^ 2 + b ^ 2) % 2 = 1 := by
      rw [hnorm]
      exact hoddM
    have h5 : (a ^ 2 + b ^ 2) % 5 ≠ 0 := by
      rw [hnorm]
      exact h5M
    have hrec := gaussK_pi5_conj_pair_recurrence a b hodd h5
    have hrecQ :
        ((gaussK (gaussMul pi5 (a,b)) : ℤ) : ℚ) +
            ((gaussK (gaussMul pi5 (a,-b)) : ℤ) : ℚ) =
          -6 * (((gaussK (a,b) : ℤ) : ℚ) +
            ((gaussK (a,-b) : ℤ) : ℚ)) := by
      exact_mod_cast hrec
    simpa only [F, G, gaussConj, gaussMul_pi5_left] using hrecQ
  have htwice :
      2 * (∑ z ∈ normShellByNorm M, F z) =
        2 * (-6 * ∑ z ∈ normShellByNorm M, G z) := by
    calc
      2 * (∑ z ∈ normShellByNorm M, F z)
          = ∑ z ∈ normShellByNorm M, (F z + F (gaussConj z)) := hdouble F
      _ = ∑ z ∈ normShellByNorm M, -6 * (G z + G (gaussConj z)) := hpair_sum
      _ = -6 * ∑ z ∈ normShellByNorm M, (G z + G (gaussConj z)) := by
          rw [← Finset.mul_sum]
      _ = -6 * (2 * ∑ z ∈ normShellByNorm M, G z) := by
          rw [← hdouble G]
      _ = 2 * (-6 * ∑ z ∈ normShellByNorm M, G z) := by ring
  have hmain :
      (∑ z ∈ normShellByNorm M, F z) =
        -6 * ∑ z ∈ normShellByNorm M, G z :=
    mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0) htwice
  simpa [F, G, normShellKSumByNorm] using hmain

theorem normShellByNorm_pi_filter_sum_reindex
    (M : ℕ) (F : GaussianInt → ℚ) :
    (∑ z ∈ normShellByNorm M, F (gaussMul pi5 z)) =
      ∑ w ∈ (normShellByNorm (5 * M)).filter piDividesExact, F w := by
  refine Finset.sum_bij'
    (fun z _hz => gaussMul pi5 z)
    (fun w _hw => gaussPiDiv w)
    ?hi ?hj ?left ?right ?h
  · intro z hz
    rw [Finset.mem_filter]
    constructor
    · have hz' := hz
      rw [normShellByNorm, Finset.mem_filter] at hz'
      have hzNorm : gaussNormSq z = (M : ℤ) := by
        simpa [gaussNormSq] using hz'.2
      have hnorm : (gaussMul pi5 z).1 ^ 2 + (gaussMul pi5 z).2 ^ 2 =
          ((5 * M : ℕ) : ℤ) := by
        have hmul := gaussNormSq_mul pi5 z
        rw [gaussNormSq_pi5, hzNorm] at hmul
        simpa [gaussNormSq, Nat.cast_mul] using hmul
      have hbox := mem_normShellBoxByNorm_of_norm_eq (M := 5 * M) hnorm
      simp [normShellByNorm, hbox.1, hbox.2, hnorm]
    · exact piDividesExact_gaussMul_pi5 z
  · intro w hw
    rw [Finset.mem_filter] at hw
    rcases hw with ⟨hwShell, hwPi⟩
    have hwShell' := hwShell
    rw [normShellByNorm, Finset.mem_filter] at hwShell'
    have hwNorm : gaussNormSq w = ((5 * M : ℕ) : ℤ) := by
      simpa [gaussNormSq] using hwShell'.2
    have hright := gaussMul_pi5_gaussPiDiv_of_piDividesExact hwPi
    have hnormDiv : gaussNormSq (gaussPiDiv w) = (M : ℤ) := by
      have hnormEq := congrArg gaussNormSq hright
      rw [gaussNormSq_mul, gaussNormSq_pi5, hwNorm] at hnormEq
      apply mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num)
      simpa [Nat.cast_mul] using hnormEq
    have hbox := mem_normShellBoxByNorm_of_norm_eq
      (M := M) (by simpa [gaussNormSq] using hnormDiv)
    rw [normShellByNorm, Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr ⟨hbox.1, hbox.2⟩
    · simpa [gaussNormSq] using hnormDiv
  · intro z hz
    exact gaussPiDiv_gaussMul_pi5 z
  · intro w hw
    rw [Finset.mem_filter] at hw
    exact gaussMul_pi5_gaussPiDiv_of_piDividesExact hw.2
  · intro z hz
    rfl

theorem normShellK_pi_sum_five_eq_pi_pi_sum (M : ℕ) :
    (∑ z ∈ normShellByNorm (5 * M),
        ((gaussK (gaussMul pi5 z) : ℤ) : ℚ)) =
      ∑ z ∈ normShellByNorm M,
        ((gaussK (gaussMul pi5 (gaussMul pi5 z)) : ℤ) : ℚ) := by
  let S := normShellByNorm (5 * M)
  let W : GaussianInt → ℚ := fun z => ((gaussK (gaussMul pi5 z) : ℤ) : ℚ)
  have hcover : ∀ z ∈ S, piDividesExact z ∨ piBarDividesExact z := by
    intro z hz
    have hz' := hz
    dsimp [S] at hz'
    rw [normShellByNorm, Finset.mem_filter] at hz'
    have hnorm : gaussNormSq z = ((5 * M : ℕ) : ℤ) := by
      simpa [gaussNormSq] using hz'.2
    apply pi_or_piBarDividesExact_of_norm_mod_five_zero
    rw [hnorm]
    omega
  have hpoint : ∀ z ∈ S, W z = if piDividesExact z then W z else 0 := by
    intro z hz
    rcases hcover z hz with hpi | hpibar
    · simp [W, hpi]
    · by_cases hpi : piDividesExact z
      · simp [W, hpi]
      · have hk0 : gaussK (gaussMul pi5 z) = 0 :=
          gaussK_gaussMul_pi5_eq_zero_of_piBarDividesExact hpibar
        simp [W, hpi, hk0]
  calc
    (∑ z ∈ normShellByNorm (5 * M),
        ((gaussK (gaussMul pi5 z) : ℤ) : ℚ))
        = ∑ z ∈ S, W z := by
            simp [S, W]
    _ = ∑ z ∈ S, if piDividesExact z then W z else 0 := by
            apply Finset.sum_congr rfl
            intro z hz
            exact hpoint z hz
    _ = ∑ z ∈ S.filter piDividesExact, W z := by
            rw [← Finset.sum_filter]
    _ = ∑ z ∈ normShellByNorm M,
          W (gaussMul pi5 z) := by
            rw [← normShellByNorm_pi_filter_sum_reindex M W]
    _ = ∑ z ∈ normShellByNorm M,
        ((gaussK (gaussMul pi5 (gaussMul pi5 z)) : ℤ) : ℚ) := by
            simp [W]

theorem normShellK_pi_sum_second_recurrence
    (M : ℕ) (hoddM : ((M : ℤ) % 2) = 1) :
    (∑ z ∈ normShellByNorm M,
        ((gaussK (gaussMul pi5 (gaussMul pi5 z)) : ℤ) : ℚ)) =
      -6 * (∑ z ∈ normShellByNorm M,
        ((gaussK (gaussMul pi5 z) : ℤ) : ℚ)) -
        25 * normShellKSumByNorm M := by
  calc
    (∑ z ∈ normShellByNorm M,
        ((gaussK (gaussMul pi5 (gaussMul pi5 z)) : ℤ) : ℚ))
        = ∑ z ∈ normShellByNorm M,
            (-6 * ((gaussK (gaussMul pi5 z) : ℤ) : ℚ) -
              25 * ((gaussK z : ℤ) : ℚ)) := by
            apply Finset.sum_congr rfl
            intro z hz
            have hz' := hz
            rw [normShellByNorm, Finset.mem_filter] at hz'
            have hnorm : gaussNormSq z = (M : ℤ) := by
              simpa [gaussNormSq] using hz'.2
            have hodd : gaussNormSq z % 2 = 1 := by
              rw [hnorm]
              exact hoddM
            have hrec := gaussK_pi5_second_order_of_norm_odd z hodd
            exact_mod_cast hrec
    _ = -6 * (∑ z ∈ normShellByNorm M,
          ((gaussK (gaussMul pi5 z) : ℤ) : ℚ)) -
        25 * normShellKSumByNorm M := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          simp [normShellKSumByNorm]

theorem normShellKSumByNorm_five_mul_recurrence_of_not_five_dvd
    (M : ℕ) (hoddM : ((M : ℤ) % 2) = 1) (hM : M % 5 ≠ 0) :
    normShellKSumByNorm (5 * M) =
      -6 * normShellKSumByNorm M := by
  rw [normShellKSumByNorm_five_eq_pi_sum]
  exact normShellK_pi_sum_recurrence_of_not_five_dvd M hoddM (by omega)

theorem normShellKSumByNorm_five_mul_recurrence_of_five_dvd
    (M : ℕ) (hoddM : ((M : ℤ) % 2) = 1) (hM : M % 5 = 0) :
    normShellKSumByNorm (5 * M) =
      -6 * normShellKSumByNorm M - 25 * normShellKSumByNorm (M / 5) := by
  have hdiv : 5 ∣ M := Nat.dvd_of_mod_eq_zero hM
  have hMmul : 5 * (M / 5) = M := Nat.mul_div_cancel' hdiv
  have hoddDiv : (((M / 5 : ℕ) : ℤ) % 2) = 1 := by
    have hcast : (M : ℤ) = 5 * ((M / 5 : ℕ) : ℤ) := by
      exact_mod_cast hMmul.symm
    omega
  calc
    normShellKSumByNorm (5 * M)
        = ∑ z ∈ normShellByNorm M,
            ((gaussK (gaussMul pi5 z) : ℤ) : ℚ) := by
            rw [normShellKSumByNorm_five_eq_pi_sum]
    _ = ∑ z ∈ normShellByNorm (5 * (M / 5)),
            ((gaussK (gaussMul pi5 z) : ℤ) : ℚ) := by
            rw [hMmul]
    _ = ∑ z ∈ normShellByNorm (M / 5),
          ((gaussK (gaussMul pi5 (gaussMul pi5 z)) : ℤ) : ℚ) := by
          rw [normShellK_pi_sum_five_eq_pi_pi_sum]
    _ = -6 * (∑ z ∈ normShellByNorm (M / 5),
          ((gaussK (gaussMul pi5 z) : ℤ) : ℚ)) -
        25 * normShellKSumByNorm (M / 5) := by
          rw [normShellK_pi_sum_second_recurrence (M / 5) hoddDiv]
    _ = -6 * normShellKSumByNorm M - 25 * normShellKSumByNorm (M / 5) := by
          rw [← normShellKSumByNorm_five_eq_pi_sum (M / 5), hMmul]

theorem normShellByNorm_four_mul_add_one_eq_fullNormShell (N : ℕ) :
    normShellByNorm (4 * N + 1) = fullNormShell N := by
  apply Finset.ext
  intro z
  constructor
  · intro hz
    rw [normShellByNorm, Finset.mem_filter] at hz
    rcases hz with ⟨_hbox, hnorm⟩
    have hnorm' : z.1 ^ 2 + z.2 ^ 2 = 4 * (N : ℤ) + 1 := by
      have hcast : (((4 * N + 1 : ℕ) : ℤ) = 4 * (N : ℤ) + 1) := by
        norm_num
      rwa [hcast] at hnorm
    have hbox : z.1 ∈ normShellBox N ∧ z.2 ∈ normShellBox N := by
      have hA_sq : z.1 ^ 2 ≤ 4 * (N : ℤ) + 1 := by
        have hB : 0 ≤ z.2 ^ 2 := sq_nonneg z.2
        nlinarith
      have hB_sq : z.2 ^ 2 ≤ 4 * (N : ℤ) + 1 := by
        have hA : 0 ≤ z.1 ^ 2 := sq_nonneg z.1
        nlinarith
      constructor
      · simp [normShellBox]
        constructor
        · by_contra hlt
          push_neg at hlt
          nlinarith
        · by_contra hgt
          push_neg at hgt
          nlinarith
      · simp [normShellBox]
        constructor
        · by_contra hlt
          push_neg at hlt
          nlinarith
        · by_contra hgt
          push_neg at hgt
          nlinarith
    simp [fullNormShell, hbox.1, hbox.2, hnorm']
  · intro hz
    rw [fullNormShell, Finset.mem_filter] at hz
    rcases hz with ⟨_hbox, hnorm⟩
    have hnorm' : z.1 ^ 2 + z.2 ^ 2 = ((4 * N + 1 : ℕ) : ℤ) := by
      have hcast : (((4 * N + 1 : ℕ) : ℤ) = 4 * (N : ℤ) + 1) := by
        norm_num
      rwa [hcast]
    have hbox := mem_normShellBoxByNorm_of_norm_eq (M := 4 * N + 1) hnorm'
    simp [normShellByNorm, hbox.1, hbox.2, hnorm']

theorem normShellHSumByNorm_four_mul_add_one (N : ℕ) :
    normShellHSumByNorm (4 * N + 1) =
      ∑ z ∈ fullNormShell N, ((gaussH z : ℤ) : ℚ) := by
  simp [normShellHSumByNorm, normShellByNorm_four_mul_add_one_eq_fullNormShell]

theorem normShellKSumByNorm_four_mul_add_one (N : ℕ) :
    normShellKSumByNorm (4 * N + 1) = fullNormShellKSum N := by
  simp [normShellKSumByNorm, fullNormShellKSum,
    normShellByNorm_four_mul_add_one_eq_fullNormShell]

def pentagonalSectorInverse (z : GaussianInt) : ℤ × ℤ :=
  (((-z.1 - 3 * z.2 + 3) / 10), ((3 * z.1 - z.2 + 1) / 10))

def pentagonalSelectedRotation (z : GaussianInt) : Fin 4 :=
  if (-z.1 - 3 * z.2) % 5 = 2 then ⟨0, by norm_num⟩
  else if (-3 * z.1 + z.2) % 5 = 2 then ⟨1, by norm_num⟩
  else if (z.1 + 3 * z.2) % 5 = 2 then ⟨2, by norm_num⟩
  else ⟨3, by norm_num⟩

def pentagonalSelectedInverseRotation (z : GaussianInt) : Fin 4 :=
  match (pentagonalSelectedRotation z).1 with
  | 0 => ⟨0, by norm_num⟩
  | 1 => ⟨3, by norm_num⟩
  | 2 => ⟨2, by norm_num⟩
  | _ => ⟨1, by norm_num⟩

def pentagonalSectorRepresentative (z : GaussianInt) : GaussianInt :=
  gaussUnitRotate (pentagonalSelectedRotation z) z

def pentagonalUnitOrbitDomain (N : ℕ) : Finset (Fin 4 × GaussianInt) :=
  (Finset.univ : Finset (Fin 4)).product (pentagonalSector N)

def pentagonalUnitOrbitPoint (x : Fin 4 × GaussianInt) : GaussianInt :=
  gaussUnitRotate x.1 x.2

def pentagonalUnitOrbitImage (N : ℕ) : Finset GaussianInt :=
  (pentagonalUnitOrbitDomain N).image pentagonalUnitOrbitPoint

def pentagonalFullShellInverse (z : GaussianInt) : Fin 4 × GaussianInt :=
  (pentagonalSelectedInverseRotation z, pentagonalSectorRepresentative z)

def jacobiOrbitPoint (i : Fin 4) (rs : ℕ × ℕ) : GaussianInt :=
  let z := jacobiToGauss rs.1 rs.2
  match i.1 with
  | 0 => z
  | 1 => (z.2, z.1)
  | 2 => (-z.2, -z.1)
  | _ => (-z.1, -z.2)

def jacobiOrbitDomain (N : ℕ) : Finset (Fin 4 × (ℕ × ℕ)) :=
  (Finset.univ : Finset (Fin 4)).product (jacobiShellPairs N)

def oddAbsIndex (x : ℤ) : ℕ :=
  (x.natAbs - 1) / 2

def fullShellInversePair (z : GaussianInt) : ℕ × ℕ :=
  (oddAbsIndex (z.1 + z.2), oddAbsIndex (z.1 - z.2))

def fullShellInverseSign (z : GaussianInt) : Fin 4 :=
  if 0 < z.1 - z.2 then
    if 0 < z.1 + z.2 then ⟨0, by norm_num⟩ else ⟨2, by norm_num⟩
  else
    if 0 < z.1 + z.2 then ⟨1, by norm_num⟩ else ⟨3, by norm_num⟩

def fullShellInverse (z : GaussianInt) : Fin 4 × (ℕ × ℕ) :=
  (fullShellInverseSign z, fullShellInversePair z)

theorem mem_normShellBox_of_norm_eq {N : ℕ} {A B : ℤ}
    (h : A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1) :
    A ∈ normShellBox N ∧ B ∈ normShellBox N := by
  have hA_sq : A ^ 2 ≤ 4 * (N : ℤ) + 1 := by
    have hB : 0 ≤ B ^ 2 := sq_nonneg B
    nlinarith
  have hB_sq : B ^ 2 ≤ 4 * (N : ℤ) + 1 := by
    have hA : 0 ≤ A ^ 2 := sq_nonneg A
    nlinarith
  constructor
  · simp [normShellBox]
    constructor
    · by_contra hlt
      push_neg at hlt
      nlinarith
    · by_contra hgt
      push_neg at hgt
      nlinarith
  · simp [normShellBox]
    constructor
    · by_contra hlt
      push_neg at hlt
      nlinarith
    · by_contra hgt
      push_neg at hgt
      nlinarith

theorem pentagonalToGauss_mem_pentagonalSector {N : ℕ} {kl : ℤ × ℤ}
    (hkl : kl ∈ pentagonalShellPairs N) :
    pentagonalToGauss kl.1 kl.2 ∈ pentagonalSector N := by
  rcases kl with ⟨k, l⟩
  rw [pentagonalShellPairs, Finset.mem_filter] at hkl
  have hsum : pentagonal014Exp k + pentagonal023Exp l = N := hkl.2
  have hnorm : (pentagonalToGauss k l).1 ^ 2 + (pentagonalToGauss k l).2 ^ 2 =
      4 * (N : ℤ) + 1 := by
    simpa [gaussNormSq] using pentagonalToGauss_norm_of_exp_sum hsum
  have hbox := mem_normShellBox_of_norm_eq (N := N) hnorm
  have hfull : pentagonalToGauss k l ∈ fullNormShell N := by
    simp [fullNormShell, hbox.1, hbox.2, hnorm]
  have hsel := pentagonalToGauss_selector k l
  rw [pentagonalSector, Finset.mem_filter]
  constructor
  · exact hfull
  · constructor
    · rw [hsel.1]
      omega
    · rw [hsel.2]
      omega

@[simp] theorem pentagonalSectorInverse_pentagonalToGauss (k l : ℤ) :
    pentagonalSectorInverse (pentagonalToGauss k l) = (k, l) := by
  have hsel := pentagonalToGauss_selector k l
  ext
  · unfold pentagonalSectorInverse
    rw [hsel.1]
    rw [show (10 * k - 3 + 3) = 10 * k by ring]
    exact Int.mul_ediv_cancel_left k (by norm_num : (10 : ℤ) ≠ 0)
  · unfold pentagonalSectorInverse
    rw [hsel.2]
    rw [show (10 * l - 1 + 1) = 10 * l by ring]
    exact Int.mul_ediv_cancel_left l (by norm_num : (10 : ℤ) ≠ 0)

theorem gaussian_eq_of_pentagonal_linear_eq {z w : GaussianInt}
    (hx : -z.1 - 3 * z.2 = -w.1 - 3 * w.2)
    (hy : 3 * z.1 - z.2 = 3 * w.1 - w.2) :
    z = w := by
  rcases z with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  ext <;> omega

theorem jacobiOrbitPoint_norm (i : Fin 4) (rs : ℕ × ℕ) :
    (jacobiOrbitPoint i rs).1 ^ 2 + (jacobiOrbitPoint i rs).2 ^ 2 =
      gaussNormSq (jacobiToGauss rs.1 rs.2) := by
  fin_cases i <;> simp [jacobiOrbitPoint, gaussNormSq] <;> ring

theorem jacobiOrbitPoint_mem_fullNormShell (N : ℕ) (x : Fin 4 × (ℕ × ℕ))
    (hx : x ∈ jacobiOrbitDomain N) :
    jacobiOrbitPoint x.1 x.2 ∈ fullNormShell N := by
  rcases x with ⟨i, rs⟩
  rcases rs with ⟨r, s⟩
  have hxpair : (r, s) ∈ jacobiShellPairs N := by
    simpa [jacobiOrbitDomain] using hx
  rw [jacobiShellPairs, Finset.mem_filter] at hxpair
  have htri : triangularIndex r + triangularIndex s = N := hxpair.2
  have hnorm : (jacobiOrbitPoint i (r, s)).1 ^ 2 +
      (jacobiOrbitPoint i (r, s)).2 ^ 2 = 4 * (N : ℤ) + 1 := by
    rw [jacobiOrbitPoint_norm, jacobiToGauss_norm]
    exact_mod_cast congrArg (fun t : ℕ => 4 * t + 1) htri
  have hbox := mem_normShellBox_of_norm_eq (N := N) hnorm
  simp [fullNormShell, hbox.1, hbox.2, hnorm]

@[simp] theorem gaussH_neg_left (a b : ℤ) :
    gaussH (-a,b) = gaussH (a,b) := by
  simp [gaussH]

@[simp] theorem gaussH_neg_right (a b : ℤ) :
    gaussH (a,-b) = gaussH (a,b) := by
  simp [gaussH]

theorem gaussH_swap_of_norm_odd {a b : ℤ}
    (hodd : (a ^ 2 + b ^ 2) % 2 = 1) :
    gaussH (b,a) = gaussH (a,b) := by
  have hopp : gaussEps b = -gaussEps a := gaussEps_opposite_of_norm_odd hodd
  simp [gaussH, hopp]
  ring

theorem jacobiOrbitPoint_gaussH (i : Fin 4) (rs : ℕ × ℕ) :
    gaussH (jacobiOrbitPoint i rs) = gaussH (jacobiToGauss rs.1 rs.2) := by
  rcases rs with ⟨r, s⟩
  have hodd : ((jacobiToGauss r s).1 ^ 2 + (jacobiToGauss r s).2 ^ 2) % 2 = 1 := by
    rw [← gaussNormSq, jacobiToGauss_norm]
    omega
  fin_cases i
  · simp [jacobiOrbitPoint]
  · simpa [jacobiOrbitPoint] using
      gaussH_swap_of_norm_odd (a := (jacobiToGauss r s).1)
        (b := (jacobiToGauss r s).2) hodd
  · simpa [jacobiOrbitPoint] using
      gaussH_swap_of_norm_odd (a := (jacobiToGauss r s).1)
        (b := (jacobiToGauss r s).2) hodd
  · simp [jacobiOrbitPoint]

theorem int_natAbs_mod_two_of_odd {x : ℤ} (hodd : x % 2 = 1) :
    x.natAbs % 2 = 1 := by
  rcases Int.natAbs_eq x with hx | hx
  · rw [hx] at hodd
    exact_mod_cast hodd
  · rw [hx] at hodd
    have h : ((x.natAbs : ℤ) % 2 = 1) := by omega
    exact_mod_cast h

theorem two_mul_oddAbsIndex_add_one {x : ℤ} (hodd : x % 2 = 1) :
    2 * ((oddAbsIndex x : ℕ) : ℤ) + 1 = (x.natAbs : ℤ) := by
  have hn : x.natAbs % 2 = 1 := int_natAbs_mod_two_of_odd hodd
  have hnat : 2 * ((x.natAbs - 1) / 2) + 1 = x.natAbs := by omega
  exact_mod_cast hnat

theorem oddAbsIndex_of_pos_odd (n : ℕ) :
    oddAbsIndex (2 * (n : ℤ) + 1) = n := by
  unfold oddAbsIndex
  have hnat : (2 * (n : ℤ) + 1).natAbs = 2 * n + 1 := by
    have hnatInt : (((2 * (n : ℤ) + 1).natAbs : ℕ) : ℤ) =
        2 * (n : ℤ) + 1 := by
      exact Int.natAbs_of_nonneg (by omega)
    omega
  rw [hnat]
  omega

theorem oddAbsIndex_of_neg_odd (n : ℕ) :
    oddAbsIndex (-(2 * (n : ℤ) + 1)) = n := by
  unfold oddAbsIndex
  have hnat : (-(2 * (n : ℤ) + 1)).natAbs = 2 * n + 1 := by
    have hnatInt : (((-(2 * (n : ℤ) + 1)).natAbs : ℕ) : ℤ) =
        2 * (n : ℤ) + 1 := by
      rw [Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    omega
  rw [hnat]
  omega

theorem oddAbsIndex_square_formula {x : ℤ} (hodd : x % 2 = 1) :
    8 * (triangularIndex (oddAbsIndex x) : ℤ) + 1 = x ^ 2 := by
  let n := oddAbsIndex x
  have h2n : 2 * (n : ℤ) + 1 = (x.natAbs : ℤ) :=
    two_mul_oddAbsIndex_add_one hodd
  have htri := two_mul_int_triangularIndex n
  calc
    8 * (triangularIndex n : ℤ) + 1
        = 4 * (2 * (triangularIndex n : ℤ)) + 1 := by ring
    _ = 4 * ((n : ℤ) * ((n : ℤ) + 1)) + 1 := by rw [htri]
    _ = (2 * (n : ℤ) + 1) ^ 2 := by ring
    _ = ((x.natAbs : ℤ)) ^ 2 := by rw [h2n]
    _ = x ^ 2 := by
      simp [pow_two]

theorem rs_odd_of_norm_shell {N : ℕ} {A B : ℤ}
    (h : A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1) :
    (A - B) % 2 = 1 ∧ (A + B) % 2 = 1 := by
  have hodd : (A ^ 2 + B ^ 2) % 2 = 1 := by
    rw [h]
    omega
  let qa := A / 2
  let qb := B / 2
  let ra := A % 2
  let rb := B % 2
  have hra_nonneg : 0 ≤ ra := Int.emod_nonneg A (by norm_num : (2 : ℤ) ≠ 0)
  have hra_lt : ra < 2 := Int.emod_lt_of_pos A (by norm_num : (0 : ℤ) < 2)
  have hrb_nonneg : 0 ≤ rb := Int.emod_nonneg B (by norm_num : (2 : ℤ) ≠ 0)
  have hrb_lt : rb < 2 := Int.emod_lt_of_pos B (by norm_num : (0 : ℤ) < 2)
  have ha : A = 2 * qa + ra := by
    calc
      A = 2 * (A / 2) + A % 2 := by rw [Int.mul_ediv_add_emod]
      _ = 2 * qa + ra := by rfl
  have hb : B = 2 * qb + rb := by
    calc
      B = 2 * (B / 2) + B % 2 := by rw [Int.mul_ediv_add_emod]
      _ = 2 * qb + rb := by rfl
  rw [ha, hb] at hodd ⊢
  interval_cases ra <;> interval_cases rb <;> simp at hodd ⊢
  all_goals try ring_nf at hodd
  all_goals omega

theorem pentagonalToGauss_pentagonalSectorInverse {N : ℕ} {z : GaussianInt}
    (hz : z ∈ pentagonalSector N) :
    pentagonalToGauss (pentagonalSectorInverse z).1 (pentagonalSectorInverse z).2 = z := by
  rcases z with ⟨A, B⟩
  rw [pentagonalSector, Finset.mem_filter] at hz
  rcases hz with ⟨hfull, hsec⟩
  rw [fullNormShell, Finset.mem_filter] at hfull
  have hnorm : A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1 := hfull.2
  have hRodd : (A - B) % 2 = 1 := (rs_odd_of_norm_shell hnorm).1
  have hSodd : (A + B) % 2 = 1 := (rs_odd_of_norm_shell hnorm).2
  let x : ℤ := -A - 3 * B
  let y : ℤ := 3 * A - B
  have hx5 : x % 5 = 2 := by simpa [x] using hsec.1
  have hy5 : y % 5 = 4 := by simpa [y] using hsec.2
  have hx2 : x % 2 = 1 := by
    dsimp [x] at *
    omega
  have hy2 : y % 2 = 1 := by
    dsimp [y] at *
    omega
  have hxdiv : (10 : ℤ) ∣ x + 3 := by omega
  have hydiv : (10 : ℤ) ∣ y + 1 := by omega
  let k : ℤ := (x + 3) / 10
  let l : ℤ := (y + 1) / 10
  have hk : 10 * k - 3 = x := by
    have hmul : k * 10 = x + 3 := by
      simpa [k] using Int.ediv_mul_cancel hxdiv
    omega
  have hl : 10 * l - 1 = y := by
    have hmul : l * 10 = y + 1 := by
      simpa [l] using Int.ediv_mul_cancel hydiv
    omega
  change pentagonalToGauss k l = (A, B)
  apply gaussian_eq_of_pentagonal_linear_eq
  · rw [(pentagonalToGauss_selector k l).1, hk]
  · rw [(pentagonalToGauss_selector k l).2, hl]

theorem pentagonalSectorPred_of_rot0_selector {a b : ℤ}
    (h0 : (-a - 3 * b) % 5 = 2) :
    pentagonalSectorPred (a,b) := by
  unfold pentagonalSectorPred
  constructor
  · exact h0
  · omega

theorem pentagonalSectorPred_of_rot1_selector {a b : ℤ}
    (h1 : (-3 * a + b) % 5 = 2) :
    pentagonalSectorPred (-b,a) := by
  unfold pentagonalSectorPred
  constructor <;> omega

theorem pentagonalSectorPred_of_rot2_selector {a b : ℤ}
    (h2 : (a + 3 * b) % 5 = 2) :
    pentagonalSectorPred (-a,-b) := by
  unfold pentagonalSectorPred
  constructor <;> omega

theorem pentagonalSectorPred_of_rot3_selector {a b : ℤ}
    (h3 : (3 * a - b) % 5 = 2) :
    pentagonalSectorPred (b,-a) := by
  unfold pentagonalSectorPred
  constructor <;> omega

theorem gaussK_eq_zero_of_no_pentagonalSector_rotation {a b : ℤ}
    (h0 : ¬ pentagonalSectorPred (a,b))
    (h1 : ¬ pentagonalSectorPred (-b,a))
    (h2 : ¬ pentagonalSectorPred (-a,-b))
    (h3 : ¬ pentagonalSectorPred (b,-a)) :
    gaussK (a,b) = 0 := by
  apply gaussK_eq_zero_of_no_selector
  · intro hs
    exact h0 (pentagonalSectorPred_of_rot0_selector hs)
  · intro hs
    exact h1 (pentagonalSectorPred_of_rot1_selector hs)
  · intro hs
    exact h2 (pentagonalSectorPred_of_rot2_selector hs)
  · intro hs
    exact h3 (pentagonalSectorPred_of_rot3_selector hs)

theorem gaussUnitRotate_norm_eq (i : Fin 4) (z : GaussianInt) :
    (gaussUnitRotate i z).1 ^ 2 + (gaussUnitRotate i z).2 ^ 2 =
      z.1 ^ 2 + z.2 ^ 2 := by
  rcases z with ⟨a, b⟩
  fin_cases i <;> simp [gaussUnitRotate] <;> ring

theorem gaussUnitRotate_mem_fullNormShell {N : ℕ} {z : GaussianInt}
    (hz : z ∈ fullNormShell N) (i : Fin 4) :
    gaussUnitRotate i z ∈ fullNormShell N := by
  rw [fullNormShell, Finset.mem_filter] at hz ⊢
  rcases hz with ⟨_hbox, hnorm⟩
  have hnorm' : (gaussUnitRotate i z).1 ^ 2 + (gaussUnitRotate i z).2 ^ 2 =
      4 * (N : ℤ) + 1 := by
    rw [gaussUnitRotate_norm_eq, hnorm]
  have hbox := mem_normShellBox_of_norm_eq (N := N) hnorm'
  constructor
  · exact Finset.mem_product.mpr ⟨hbox.1, hbox.2⟩
  · exact hnorm'

theorem pentagonalSectorPred_selectedRotation {a b : ℤ}
    (h5 : (a ^ 2 + b ^ 2) % 5 ≠ 0) :
    pentagonalSectorPred (gaussUnitRotate (pentagonalSelectedRotation (a,b)) (a,b)) := by
  rcases wronskianSelector_exists_int a b h5 with h0 | h1 | h2 | h3
  · simp [pentagonalSelectedRotation, h0, gaussUnitRotate,
      pentagonalSectorPred_of_rot0_selector h0]
  · by_cases h0 : (-a - 3 * b) % 5 = 2
    · simp [pentagonalSelectedRotation, h0, gaussUnitRotate,
        pentagonalSectorPred_of_rot0_selector h0]
    · have h1' : (-(3 * a) + b) % 5 = 2 := by omega
      simp [pentagonalSelectedRotation, h0, h1', gaussUnitRotate,
        pentagonalSectorPred_of_rot1_selector h1]
  · by_cases h0 : (-a - 3 * b) % 5 = 2
    · simp [pentagonalSelectedRotation, h0, gaussUnitRotate,
        pentagonalSectorPred_of_rot0_selector h0]
    · by_cases h1 : (-3 * a + b) % 5 = 2
      · have h1' : (-(3 * a) + b) % 5 = 2 := by omega
        simp [pentagonalSelectedRotation, h0, h1', gaussUnitRotate,
          pentagonalSectorPred_of_rot1_selector h1]
      · have h1' : ¬ (-(3 * a) + b) % 5 = 2 := by omega
        simp [pentagonalSelectedRotation, h0, h1', h2, gaussUnitRotate,
          pentagonalSectorPred_of_rot2_selector h2]
  · by_cases h0 : (-a - 3 * b) % 5 = 2
    · simp [pentagonalSelectedRotation, h0, gaussUnitRotate,
        pentagonalSectorPred_of_rot0_selector h0]
    · by_cases h1 : (-3 * a + b) % 5 = 2
      · have h1' : (-(3 * a) + b) % 5 = 2 := by omega
        simp [pentagonalSelectedRotation, h0, h1', gaussUnitRotate,
          pentagonalSectorPred_of_rot1_selector h1]
      · by_cases h2 : (a + 3 * b) % 5 = 2
        · have h1' : ¬ (-(3 * a) + b) % 5 = 2 := by omega
          simp [pentagonalSelectedRotation, h0, h1', h2, gaussUnitRotate,
            pentagonalSectorPred_of_rot2_selector h2]
        · have h1' : ¬ (-(3 * a) + b) % 5 = 2 := by omega
          simp [pentagonalSelectedRotation, h0, h1', h2, gaussUnitRotate,
            pentagonalSectorPred_of_rot3_selector h3]

theorem pentagonalSectorRepresentative_mem {N : ℕ} {z : GaussianInt}
    (hz : z ∈ fullNormShell N) (h5N : (4 * (N : ℤ) + 1) % 5 ≠ 0) :
    pentagonalSectorRepresentative z ∈ pentagonalSector N := by
  rw [pentagonalSector, Finset.mem_filter]
  constructor
  · apply gaussUnitRotate_mem_fullNormShell hz
  · rw [fullNormShell, Finset.mem_filter] at hz
    have hnorm : z.1 ^ 2 + z.2 ^ 2 = 4 * (N : ℤ) + 1 := hz.2
    apply pentagonalSectorPred_selectedRotation
    rw [hnorm]
    exact h5N

theorem pentagonalSelectedInverseRotation_spec (z : GaussianInt) :
    gaussUnitRotate (pentagonalSelectedInverseRotation z)
        (pentagonalSectorRepresentative z) = z := by
  rcases z with ⟨a, b⟩
  unfold pentagonalSelectedInverseRotation pentagonalSectorRepresentative pentagonalSelectedRotation
  by_cases h0 : (-a - 3 * b) % 5 = 2
  · simp [h0, gaussUnitRotate]
  · by_cases h1 : (-(3 * a) + b) % 5 = 2
    · simp [h0, h1, gaussUnitRotate]
    · by_cases h2 : (a + 3 * b) % 5 = 2
      · simp [h0, h1, h2, gaussUnitRotate]
      · simp [h0, h1, h2, gaussUnitRotate]

theorem pentagonalUnitOrbitPoint_mem_fullNormShell {N : ℕ}
    {x : Fin 4 × GaussianInt} (hx : x ∈ pentagonalUnitOrbitDomain N) :
    pentagonalUnitOrbitPoint x ∈ fullNormShell N := by
  rcases x with ⟨i, z⟩
  have hzsector : z ∈ pentagonalSector N := by
    simpa [pentagonalUnitOrbitDomain] using hx
  rw [pentagonalSector, Finset.mem_filter] at hzsector
  exact gaussUnitRotate_mem_fullNormShell hzsector.1 i

theorem pentagonalUnitOrbitImage_subset_fullNormShell (N : ℕ) :
    pentagonalUnitOrbitImage N ⊆ fullNormShell N := by
  intro z hz
  rw [pentagonalUnitOrbitImage] at hz
  rcases Finset.mem_image.mp hz with ⟨x, hx, hxz⟩
  rw [← hxz]
  exact pentagonalUnitOrbitPoint_mem_fullNormShell hx

theorem mem_pentagonalUnitOrbitImage_of_sector_rot0 {N : ℕ} {a b : ℤ}
    (hz : (a,b) ∈ fullNormShell N)
    (hsec : pentagonalSectorPred (a,b)) :
    (a,b) ∈ pentagonalUnitOrbitImage N := by
  rw [pentagonalUnitOrbitImage, Finset.mem_image]
  refine ⟨(⟨0, by norm_num⟩, (a,b)), ?_, ?_⟩
  · simp [pentagonalUnitOrbitDomain, pentagonalSector, hz, hsec]
  · simp [pentagonalUnitOrbitPoint, gaussUnitRotate]

theorem mem_pentagonalUnitOrbitImage_of_sector_rot1 {N : ℕ} {a b : ℤ}
    (hz : (a,b) ∈ fullNormShell N)
    (hsec : pentagonalSectorPred (-b,a)) :
    (a,b) ∈ pentagonalUnitOrbitImage N := by
  have hfull : (-b,a) ∈ fullNormShell N := by
    simpa [gaussUnitRotate] using
      (gaussUnitRotate_mem_fullNormShell hz ⟨1, by norm_num⟩)
  rw [pentagonalUnitOrbitImage, Finset.mem_image]
  refine ⟨(⟨3, by norm_num⟩, (-b,a)), ?_, ?_⟩
  · simp [pentagonalUnitOrbitDomain, pentagonalSector, hfull, hsec]
  · simp [pentagonalUnitOrbitPoint, gaussUnitRotate]

theorem mem_pentagonalUnitOrbitImage_of_sector_rot2 {N : ℕ} {a b : ℤ}
    (hz : (a,b) ∈ fullNormShell N)
    (hsec : pentagonalSectorPred (-a,-b)) :
    (a,b) ∈ pentagonalUnitOrbitImage N := by
  have hfull : (-a,-b) ∈ fullNormShell N := by
    simpa [gaussUnitRotate] using
      (gaussUnitRotate_mem_fullNormShell hz ⟨2, by norm_num⟩)
  rw [pentagonalUnitOrbitImage, Finset.mem_image]
  refine ⟨(⟨2, by norm_num⟩, (-a,-b)), ?_, ?_⟩
  · simp [pentagonalUnitOrbitDomain, pentagonalSector, hfull, hsec]
  · simp [pentagonalUnitOrbitPoint, gaussUnitRotate]

theorem mem_pentagonalUnitOrbitImage_of_sector_rot3 {N : ℕ} {a b : ℤ}
    (hz : (a,b) ∈ fullNormShell N)
    (hsec : pentagonalSectorPred (b,-a)) :
    (a,b) ∈ pentagonalUnitOrbitImage N := by
  have hfull : (b,-a) ∈ fullNormShell N := by
    simpa [gaussUnitRotate] using
      (gaussUnitRotate_mem_fullNormShell hz ⟨3, by norm_num⟩)
  rw [pentagonalUnitOrbitImage, Finset.mem_image]
  refine ⟨(⟨1, by norm_num⟩, (b,-a)), ?_, ?_⟩
  · simp [pentagonalUnitOrbitDomain, pentagonalSector, hfull, hsec]
  · simp [pentagonalUnitOrbitPoint, gaussUnitRotate]

theorem gaussK_eq_zero_of_fullNormShell_not_pentagonalUnitOrbitImage {N : ℕ}
    {z : GaussianInt} (hz : z ∈ fullNormShell N)
    (hnot : z ∉ pentagonalUnitOrbitImage N) :
    gaussK z = 0 := by
  rcases z with ⟨a, b⟩
  apply gaussK_eq_zero_of_no_pentagonalSector_rotation
  · intro hsec
    exact hnot (mem_pentagonalUnitOrbitImage_of_sector_rot0 hz hsec)
  · intro hsec
    exact hnot (mem_pentagonalUnitOrbitImage_of_sector_rot1 hz hsec)
  · intro hsec
    exact hnot (mem_pentagonalUnitOrbitImage_of_sector_rot2 hz hsec)
  · intro hsec
    exact hnot (mem_pentagonalUnitOrbitImage_of_sector_rot3 hz hsec)

theorem pentagonalFullShellInverse_mem_unitOrbitDomain {N : ℕ} {z : GaussianInt}
    (hz : z ∈ fullNormShell N) (h5N : (4 * (N : ℤ) + 1) % 5 ≠ 0) :
    pentagonalFullShellInverse z ∈ pentagonalUnitOrbitDomain N := by
  simp [pentagonalFullShellInverse, pentagonalUnitOrbitDomain,
    pentagonalSectorRepresentative_mem hz h5N]

theorem pentagonalUnitOrbitPoint_fullShellInverse (z : GaussianInt) :
    pentagonalUnitOrbitPoint (pentagonalFullShellInverse z) = z := by
  exact pentagonalSelectedInverseRotation_spec z

theorem pentagonalFullShellInverse_unitOrbitPoint {N : ℕ}
    {x : Fin 4 × GaussianInt} (hx : x ∈ pentagonalUnitOrbitDomain N) :
    pentagonalFullShellInverse (pentagonalUnitOrbitPoint x) = x := by
  rcases x with ⟨i, z⟩
  rcases z with ⟨a, b⟩
  have hzsector : (a,b) ∈ pentagonalSector N := by
    simpa [pentagonalUnitOrbitDomain] using hx
  rw [pentagonalSector, Finset.mem_filter] at hzsector
  have hfull : (a,b) ∈ fullNormShell N := hzsector.1
  have hpred : pentagonalSectorPred (a,b) := hzsector.2
  unfold pentagonalSectorPred at hpred
  have h0 : (-a - 3 * b) % 5 = 2 := hpred.1
  have hy : (3 * a - b) % 5 = 4 := hpred.2
  fin_cases i
  · simp [pentagonalFullShellInverse, pentagonalUnitOrbitPoint,
      pentagonalSectorRepresentative, pentagonalSelectedInverseRotation,
      pentagonalSelectedRotation, gaussUnitRotate, h0]
  · have hnot0 : ¬ (b - 3 * a) % 5 = 2 := by
      omega
    have hnot1 : ¬ (3 * b + a) % 5 = 2 := by
      omega
    have hnot2 : ¬ (-b + 3 * a) % 5 = 2 := by omega
    simp [pentagonalFullShellInverse, pentagonalUnitOrbitPoint,
      pentagonalSectorRepresentative, pentagonalSelectedInverseRotation,
      pentagonalSelectedRotation, gaussUnitRotate, hnot0, hnot1, hnot2]
  · have hnot0 : ¬ (a + 3 * b) % 5 = 2 := by omega
    have hnot1 : ¬ (3 * a + -b) % 5 = 2 := by omega
    have h2 : (-a + -(3 * b)) % 5 = 2 := by omega
    simp [pentagonalFullShellInverse, pentagonalUnitOrbitPoint,
      pentagonalSectorRepresentative, pentagonalSelectedInverseRotation,
      pentagonalSelectedRotation, gaussUnitRotate, hnot0, hnot1, h2]
  · have hnot0 : ¬ (-b + 3 * a) % 5 = 2 := by omega
    have h1 : (-(3 * b) + -a) % 5 = 2 := by omega
    simp [pentagonalFullShellInverse, pentagonalUnitOrbitPoint,
      pentagonalSectorRepresentative, pentagonalSelectedInverseRotation,
      pentagonalSelectedRotation, gaussUnitRotate, hnot0, h1]

theorem pentagonalUnitOrbitImage_sum_eq_unitOrbitDomain_sum (N : ℕ) :
    (∑ z ∈ pentagonalUnitOrbitImage N, ((gaussK z : ℤ) : ℚ)) =
      ∑ x ∈ pentagonalUnitOrbitDomain N,
        ((gaussK (pentagonalUnitOrbitPoint x) : ℤ) : ℚ) := by
  unfold pentagonalUnitOrbitImage
  rw [Finset.sum_image]
  intro x hx y hy hxy
  have h := congrArg pentagonalFullShellInverse hxy
  rw [pentagonalFullShellInverse_unitOrbitPoint hx,
    pentagonalFullShellInverse_unitOrbitPoint hy] at h
  exact h

theorem fullNormShellKSum_eq_pentagonalUnitOrbitImage_sum (N : ℕ) :
    fullNormShellKSum N =
      ∑ z ∈ pentagonalUnitOrbitImage N, ((gaussK z : ℤ) : ℚ) := by
  unfold fullNormShellKSum
  have hsub : pentagonalUnitOrbitImage N ⊆ fullNormShell N :=
    pentagonalUnitOrbitImage_subset_fullNormShell N
  have hsum :
      (∑ z ∈ pentagonalUnitOrbitImage N, ((gaussK z : ℤ) : ℚ)) =
        ∑ z ∈ fullNormShell N, ((gaussK z : ℤ) : ℚ) := by
    apply Finset.sum_subset hsub
    intro z hzfull hznot
    have hz0 := gaussK_eq_zero_of_fullNormShell_not_pentagonalUnitOrbitImage hzfull hznot
    simp [hz0]
  exact hsum.symm

theorem pentagonalUnitOrbitDomain_sum_eq_fullNormShellKSum_of_t0 (N : ℕ)
    (h5N : (4 * (N : ℤ) + 1) % 5 ≠ 0) :
    (∑ x ∈ pentagonalUnitOrbitDomain N,
        ((gaussK (pentagonalUnitOrbitPoint x) : ℤ) : ℚ)) =
      fullNormShellKSum N := by
  unfold fullNormShellKSum
  refine Finset.sum_bij'
    (fun x hx => pentagonalUnitOrbitPoint x)
    (fun z hz => pentagonalFullShellInverse z)
    ?hi ?hj ?left ?right ?h
  · intro x hx
    exact pentagonalUnitOrbitPoint_mem_fullNormShell hx
  · intro z hz
    exact pentagonalFullShellInverse_mem_unitOrbitDomain hz h5N
  · intro x hx
    exact pentagonalFullShellInverse_unitOrbitPoint hx
  · intro z hz
    exact pentagonalUnitOrbitPoint_fullShellInverse z
  · intro x hx
    rfl

theorem pentagonalUnitOrbitDomain_sum_eq_four_pentagonalSector_sum_gaussK (N : ℕ) :
    (∑ x ∈ pentagonalUnitOrbitDomain N,
        ((gaussK (pentagonalUnitOrbitPoint x) : ℤ) : ℚ)) =
      4 * ∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ) := by
  calc
    (∑ x ∈ pentagonalUnitOrbitDomain N,
        ((gaussK (pentagonalUnitOrbitPoint x) : ℤ) : ℚ))
        = ∑ i : Fin 4, ∑ z ∈ pentagonalSector N,
            ((gaussK (gaussUnitRotate i z) : ℤ) : ℚ) := by
            simp [pentagonalUnitOrbitDomain, pentagonalUnitOrbitPoint,
              Finset.sum_product]
    _ = ∑ z ∈ pentagonalSector N, ∑ i : Fin 4,
            ((gaussK (gaussUnitRotate i z) : ℤ) : ℚ) := by
            rw [Finset.sum_comm]
    _ = ∑ z ∈ pentagonalSector N, 4 * ((gaussK z : ℤ) : ℚ) := by
            apply Finset.sum_congr rfl
            intro z hz
            rcases z with ⟨a, b⟩
            rw [Fin.sum_univ_four]
            simp [gaussUnitRotate]
            ring
    _ = 4 * ∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ) := by
            rw [Finset.mul_sum]

theorem fullNormShellKSum_eq_four_pentagonalSector_sum_gaussK (N : ℕ) :
    fullNormShellKSum N =
      4 * ∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ) := by
  rw [fullNormShellKSum_eq_pentagonalUnitOrbitImage_sum,
    pentagonalUnitOrbitImage_sum_eq_unitOrbitDomain_sum]
  exact pentagonalUnitOrbitDomain_sum_eq_four_pentagonalSector_sum_gaussK N

theorem pentagonalSector_sum_gaussK_eq_fullNormShellKSum_div (N : ℕ) :
    (∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ)) =
      fullNormShellKSum N / 4 := by
  have h := fullNormShellKSum_eq_four_pentagonalSector_sum_gaussK N
  calc
    (∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ))
        = (4 * ∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ)) / 4 := by ring
    _ = fullNormShellKSum N / 4 := by rw [← h]

theorem fullNormShellKSum_eq_four_pentagonalSector_sum_gaussK_of_t0 (N : ℕ)
    (h5N : (4 * (N : ℤ) + 1) % 5 ≠ 0) :
    fullNormShellKSum N =
      4 * ∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ) := by
  rw [← pentagonalUnitOrbitDomain_sum_eq_fullNormShellKSum_of_t0 N h5N]
  exact pentagonalUnitOrbitDomain_sum_eq_four_pentagonalSector_sum_gaussK N

theorem normShellBox_sum_gaussK_eq_gaussH_of_t0 (N : ℕ) (A : ℤ)
    (h5N : (4 * (N : ℤ) + 1) % 5 ≠ 0) :
    (∑ B ∈ normShellBox N,
        if A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1 then
          ((gaussK (A,B) : ℤ) : ℚ)
        else 0) =
      ∑ B ∈ normShellBox N,
        if A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1 then
          ((gaussH (A,B) : ℤ) : ℚ)
        else 0 := by
  let FK : ℤ → ℚ := fun B =>
    if A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1 then
      ((gaussK (A,B) : ℤ) : ℚ)
    else 0
  let FH : ℤ → ℚ := fun B =>
    if A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1 then
      ((gaussH (A,B) : ℤ) : ℚ)
    else 0
  have hneg_sum : ∀ F : ℤ → ℚ,
      (∑ B ∈ normShellBox N, F (-B)) = ∑ B ∈ normShellBox N, F B := by
    intro F
    refine Finset.sum_bij'
      (fun B _hB => -B)
      (fun B _hB => -B)
      ?hi ?hj ?left ?right ?h
    · intro B hB
      simp only [normShellBox, Finset.mem_Icc] at hB ⊢
      omega
    · intro B hB
      simp only [normShellBox, Finset.mem_Icc] at hB ⊢
      omega
    · intro B hB
      simp
    · intro B hB
      simp
    · intro B hB
      rfl
  have hdouble : ∀ F : ℤ → ℚ,
      2 * (∑ B ∈ normShellBox N, F B) =
        ∑ B ∈ normShellBox N, (F B + F (-B)) := by
    intro F
    calc
      2 * (∑ B ∈ normShellBox N, F B)
          = (∑ B ∈ normShellBox N, F B) +
              (∑ B ∈ normShellBox N, F B) := by ring
      _ = (∑ B ∈ normShellBox N, F B) +
              (∑ B ∈ normShellBox N, F (-B)) := by
              rw [hneg_sum F]
      _ = ∑ B ∈ normShellBox N, (F B + F (-B)) := by
              rw [Finset.sum_add_distrib]
  have hpair_sum :
      (∑ B ∈ normShellBox N, (FK B + FK (-B))) =
        ∑ B ∈ normShellBox N, (FH B + FH (-B)) := by
    apply Finset.sum_congr rfl
    intro B hB
    by_cases hnorm : A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1
    · have hnorm_neg : A ^ 2 + (-B) ^ 2 = 4 * (N : ℤ) + 1 := by
        rw [show (-B) ^ 2 = B ^ 2 by ring]
        exact hnorm
      have hodd : (A ^ 2 + B ^ 2) % 2 = 1 := by
        rw [hnorm]
        omega
      have h5 : (A ^ 2 + B ^ 2) % 5 ≠ 0 := by
        rw [hnorm]
        exact h5N
      have hpairZ := gaussK_pair_eq_gaussH_pair_sum_t0 (a := A) (b := B) hodd h5
      calc
        FK B + FK (-B)
            = (((gaussK (A,B) + gaussK (A,-B) : ℤ) : ℚ)) := by
                simp [FK, hnorm]
        _ = (((gaussH (A,B) + gaussH (A,-B) : ℤ) : ℚ)) := by
                exact_mod_cast hpairZ
        _ = FH B + FH (-B) := by
                simp [FH, hnorm]
    · have hnorm_neg : A ^ 2 + (-B) ^ 2 ≠ 4 * (N : ℤ) + 1 := by
        intro h
        apply hnorm
        rw [← h]
        ring
      simp [FK, FH, hnorm]
  have htwice :
      2 * (∑ B ∈ normShellBox N, FK B) =
        2 * (∑ B ∈ normShellBox N, FH B) := by
    calc
      2 * (∑ B ∈ normShellBox N, FK B)
          = ∑ B ∈ normShellBox N, (FK B + FK (-B)) := hdouble FK
      _ = ∑ B ∈ normShellBox N, (FH B + FH (-B)) := hpair_sum
      _ = 2 * (∑ B ∈ normShellBox N, FH B) := (hdouble FH).symm
  have hmain : (∑ B ∈ normShellBox N, FK B) =
      ∑ B ∈ normShellBox N, FH B :=
    mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0) htwice
  simpa [FK, FH] using hmain

theorem fullNormShellKSum_eq_fullNormShellHSum_of_t0 (N : ℕ)
    (h5N : (4 * (N : ℤ) + 1) % 5 ≠ 0) :
    fullNormShellKSum N =
      ∑ z ∈ fullNormShell N, ((gaussH z : ℤ) : ℚ) := by
  unfold fullNormShellKSum fullNormShell
  rw [Finset.sum_filter, Finset.sum_filter]
  have hKprod :
      (∑ z ∈ (normShellBox N).product (normShellBox N),
        if z.1 ^ 2 + z.2 ^ 2 = 4 * (N : ℤ) + 1 then
          ((gaussK z : ℤ) : ℚ)
        else 0) =
        ∑ A ∈ normShellBox N, ∑ B ∈ normShellBox N,
          if A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1 then
            ((gaussK (A,B) : ℤ) : ℚ)
          else 0 := by
    exact Finset.sum_product (normShellBox N) (normShellBox N)
      (fun z : ℤ × ℤ =>
        if z.1 ^ 2 + z.2 ^ 2 = 4 * (N : ℤ) + 1 then
          ((gaussK z : ℤ) : ℚ)
        else 0)
  have hHprod :
      (∑ z ∈ (normShellBox N).product (normShellBox N),
        if z.1 ^ 2 + z.2 ^ 2 = 4 * (N : ℤ) + 1 then
          ((gaussH z : ℤ) : ℚ)
        else 0) =
        ∑ A ∈ normShellBox N, ∑ B ∈ normShellBox N,
          if A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1 then
            ((gaussH (A,B) : ℤ) : ℚ)
          else 0 := by
    exact Finset.sum_product (normShellBox N) (normShellBox N)
      (fun z : ℤ × ℤ =>
        if z.1 ^ 2 + z.2 ^ 2 = 4 * (N : ℤ) + 1 then
          ((gaussH z : ℤ) : ℚ)
        else 0)
  rw [hKprod, hHprod]
  apply Finset.sum_congr rfl
  intro A hA
  exact normShellBox_sum_gaussK_eq_gaussH_of_t0 N A h5N

theorem pentagonalSector_sum_gaussK_eq_fullNormShellHSum_div_of_t0 (N : ℕ)
    (h5N : (4 * (N : ℤ) + 1) % 5 ≠ 0) :
    (∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ)) =
      (∑ z ∈ fullNormShell N, ((gaussH z : ℤ) : ℚ)) / 4 := by
  have h4 :
      4 * (∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ)) =
        ∑ z ∈ fullNormShell N, ((gaussH z : ℤ) : ℚ) := by
    rw [← fullNormShellKSum_eq_four_pentagonalSector_sum_gaussK_of_t0 N h5N,
      fullNormShellKSum_eq_fullNormShellHSum_of_t0 N h5N]
  calc
    (∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ))
        = (4 * (∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ))) / 4 := by ring
    _ = (∑ z ∈ fullNormShell N, ((gaussH z : ℤ) : ℚ)) / 4 := by rw [h4]

theorem pentagonalSectorInverse_mem_pentagonalShellPairs {N : ℕ} {z : GaussianInt}
    (hz : z ∈ pentagonalSector N) :
    pentagonalSectorInverse z ∈ pentagonalShellPairs N := by
  let kl := pentagonalSectorInverse z
  have hto : pentagonalToGauss kl.1 kl.2 = z := by
    simpa [kl] using pentagonalToGauss_pentagonalSectorInverse hz
  rw [pentagonalSector, Finset.mem_filter] at hz
  rcases hz with ⟨hfull, _hsec⟩
  rw [fullNormShell, Finset.mem_filter] at hfull
  have hnorm_z : z.1 ^ 2 + z.2 ^ 2 = 4 * (N : ℤ) + 1 := hfull.2
  have hnorm_kl : gaussNormSq (pentagonalToGauss kl.1 kl.2) = 4 * (N : ℤ) + 1 := by
    rw [hto]
    exact hnorm_z
  have hsum_int : ((pentagonal014Exp kl.1 + pentagonal023Exp kl.2 : ℕ) : ℤ) = N := by
    rw [pentagonalToGauss_norm] at hnorm_kl
    norm_num [Nat.cast_add] at hnorm_kl
    omega
  have hsum_nat : pentagonal014Exp kl.1 + pentagonal023Exp kl.2 = N := by
    exact_mod_cast hsum_int
  have hk_mem_small :
      kl.1 ∈ Finset.Icc (-(pentagonal014Exp kl.1 + 1 : ℤ))
        (pentagonal014Exp kl.1 + 1 : ℤ) :=
    pentagonal014Exp_mem_Icc_of_eq (k := kl.1) rfl
  have hl_mem_small :
      kl.2 ∈ Finset.Icc (-(pentagonal023Exp kl.2 + 1 : ℤ))
        (pentagonal023Exp kl.2 + 1 : ℤ) :=
    pentagonal023Exp_mem_Icc_of_eq (k := kl.2) rfl
  have hk_mem : kl.1 ∈ Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ) := by
    have hle : pentagonal014Exp kl.1 ≤ N := by omega
    simp only [Finset.mem_Icc] at hk_mem_small ⊢
    constructor <;> omega
  have hl_mem : kl.2 ∈ Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ) := by
    have hle : pentagonal023Exp kl.2 ≤ N := by omega
    simp only [Finset.mem_Icc] at hl_mem_small ⊢
    constructor <;> omega
  rw [pentagonalShellPairs, Finset.mem_filter]
  constructor
  · exact Finset.mem_product.mpr ⟨hk_mem, hl_mem⟩
  · exact hsum_nat

theorem fullShellInversePair_mem {N : ℕ} {z : GaussianInt}
    (hz : z ∈ fullNormShell N) :
    fullShellInversePair z ∈ jacobiShellPairs N := by
  rcases z with ⟨A, B⟩
  rw [fullNormShell, Finset.mem_filter] at hz
  rcases hz with ⟨_hbox, hnorm⟩
  have hRodd : (A - B) % 2 = 1 := (rs_odd_of_norm_shell hnorm).1
  have hSodd : (A + B) % 2 = 1 := (rs_odd_of_norm_shell hnorm).2
  let r := oddAbsIndex (A + B)
  let s := oddAbsIndex (A - B)
  have hRtri := oddAbsIndex_square_formula hRodd
  have hStri := oddAbsIndex_square_formula hSodd
  have hRS : (A - B) ^ 2 + (A + B) ^ 2 = 8 * (N : ℤ) + 2 := by
    calc
      (A - B) ^ 2 + (A + B) ^ 2 = 2 * (A ^ 2 + B ^ 2) := by ring
      _ = 8 * (N : ℤ) + 2 := by rw [hnorm]; ring
  have htri_int : ((triangularIndex r + triangularIndex s : ℕ) : ℤ) = N := by
    have hsum : 8 * ((triangularIndex r : ℤ) + (triangularIndex s : ℤ)) + 2 =
        8 * (N : ℤ) + 2 := by
      calc
        8 * ((triangularIndex r : ℤ) + (triangularIndex s : ℤ)) + 2
            = (8 * (triangularIndex r : ℤ) + 1) +
                (8 * (triangularIndex s : ℤ) + 1) := by ring
        _ = (A + B) ^ 2 + (A - B) ^ 2 := by
              rw [show 8 * (triangularIndex r : ℤ) + 1 = (A + B) ^ 2 by
                simpa [r] using hStri]
              rw [show 8 * (triangularIndex s : ℤ) + 1 = (A - B) ^ 2 by
                simpa [s] using hRtri]
        _ = 8 * (N : ℤ) + 2 := by
              rw [← hRS]
              ring
    norm_num [Nat.cast_add]
    omega
  have htri_nat : triangularIndex r + triangularIndex s = N := by
    exact_mod_cast htri_int
  have hrle : r < N + 1 := by
    have hr_tri_le : triangularIndex r ≤ N := by omega
    have hr_self_le : r ≤ triangularIndex r := by
      simpa [triangularIndex] using k_le_triangular r
    omega
  have hsle : s < N + 1 := by
    have hs_tri_le : triangularIndex s ≤ N := by omega
    have hs_self_le : s ≤ triangularIndex s := by
      simpa [triangularIndex] using k_le_triangular s
    omega
  simp [fullShellInversePair, jacobiShellPairs, r, s, hrle, hsle, htri_nat]

theorem fullShellInverse_mem_jacobiOrbitDomain {N : ℕ} {z : GaussianInt}
    (hz : z ∈ fullNormShell N) :
    fullShellInverse z ∈ jacobiOrbitDomain N := by
  simp [fullShellInverse, jacobiOrbitDomain, fullShellInversePair_mem hz]

theorem fullShellInverse_jacobiOrbitPoint
    (x : Fin 4 × (ℕ × ℕ)) :
    fullShellInverse (jacobiOrbitPoint x.1 x.2) = x := by
  rcases x with ⟨i, rs⟩
  rcases rs with ⟨r, s⟩
  fin_cases i
  · have hR : 0 < (jacobiToGauss r s).1 - (jacobiToGauss r s).2 := by
      rw [jacobiToGauss_R_eq]
      omega
    have hRlt : (jacobiToGauss r s).2 < (jacobiToGauss r s).1 := by omega
    have hS : 0 < (jacobiToGauss r s).1 + (jacobiToGauss r s).2 := by
      rw [jacobiToGauss_S_eq]
      omega
    have hsign : fullShellInverseSign (jacobiToGauss r s) = ⟨0, by norm_num⟩ := by
      simp [fullShellInverseSign, hRlt, hS]
    have hpair : fullShellInversePair (jacobiToGauss r s) = (r, s) := by
      ext <;> simp [fullShellInversePair, jacobiToGauss_R_eq,
        jacobiToGauss_S_eq, oddAbsIndex_of_pos_odd]
    simp [fullShellInverse, jacobiOrbitPoint, hsign, hpair]
  · have hR : ¬ 0 < (jacobiToGauss r s).2 - (jacobiToGauss r s).1 := by
      rw [show (jacobiToGauss r s).2 - (jacobiToGauss r s).1 =
          -((jacobiToGauss r s).1 - (jacobiToGauss r s).2) by ring]
      rw [jacobiToGauss_R_eq]
      omega
    have hRle : (jacobiToGauss r s).2 ≤ (jacobiToGauss r s).1 := by
      rw [show (jacobiToGauss r s).2 ≤ (jacobiToGauss r s).1 ↔
          0 ≤ (jacobiToGauss r s).1 - (jacobiToGauss r s).2 by omega]
      rw [jacobiToGauss_R_eq]
      omega
    have hS : 0 < (jacobiToGauss r s).2 + (jacobiToGauss r s).1 := by
      rw [show (jacobiToGauss r s).2 + (jacobiToGauss r s).1 =
          (jacobiToGauss r s).1 + (jacobiToGauss r s).2 by ring]
      rw [jacobiToGauss_S_eq]
      omega
    have hsign :
        fullShellInverseSign ((jacobiToGauss r s).2, (jacobiToGauss r s).1) =
          ⟨1, by norm_num⟩ := by
      simp [fullShellInverseSign, hRle, hS]
    have hpair :
        fullShellInversePair ((jacobiToGauss r s).2, (jacobiToGauss r s).1) =
          (r, s) := by
      ext
      · simp [fullShellInversePair]
        rw [show (jacobiToGauss r s).2 + (jacobiToGauss r s).1 =
            (jacobiToGauss r s).1 + (jacobiToGauss r s).2 by ring]
        rw [jacobiToGauss_S_eq, oddAbsIndex_of_pos_odd]
      · simp [fullShellInversePair]
        rw [show (jacobiToGauss r s).2 - (jacobiToGauss r s).1 =
            -((jacobiToGauss r s).1 - (jacobiToGauss r s).2) by ring]
        rw [jacobiToGauss_R_eq, oddAbsIndex_of_neg_odd]
    simp [fullShellInverse, jacobiOrbitPoint, hsign, hpair]
  · have hR : 0 < -(jacobiToGauss r s).2 - -(jacobiToGauss r s).1 := by
      rw [show -(jacobiToGauss r s).2 - -(jacobiToGauss r s).1 =
          (jacobiToGauss r s).1 - (jacobiToGauss r s).2 by ring]
      rw [jacobiToGauss_R_eq]
      omega
    have hRlt : (jacobiToGauss r s).2 < (jacobiToGauss r s).1 := by
      rw [show (jacobiToGauss r s).2 < (jacobiToGauss r s).1 ↔
          0 < (jacobiToGauss r s).1 - (jacobiToGauss r s).2 by omega]
      rw [jacobiToGauss_R_eq]
      omega
    have hS : ¬ 0 < -(jacobiToGauss r s).2 + -(jacobiToGauss r s).1 := by
      rw [show -(jacobiToGauss r s).2 + -(jacobiToGauss r s).1 =
          -((jacobiToGauss r s).1 + (jacobiToGauss r s).2) by ring]
      rw [jacobiToGauss_S_eq]
      omega
    have hsign :
        fullShellInverseSign (-(jacobiToGauss r s).2, -(jacobiToGauss r s).1) =
          ⟨2, by norm_num⟩ := by
      simp [fullShellInverseSign, hRlt, hS]
    have hpair :
        fullShellInversePair (-(jacobiToGauss r s).2, -(jacobiToGauss r s).1) =
          (r, s) := by
      ext
      · simp [fullShellInversePair]
        rw [show -(jacobiToGauss r s).2 + -(jacobiToGauss r s).1 =
            -((jacobiToGauss r s).1 + (jacobiToGauss r s).2) by ring]
        rw [jacobiToGauss_S_eq, oddAbsIndex_of_neg_odd]
      · simp [fullShellInversePair]
        rw [show -(jacobiToGauss r s).2 + (jacobiToGauss r s).1 =
            (jacobiToGauss r s).1 - (jacobiToGauss r s).2 by ring]
        rw [jacobiToGauss_R_eq, oddAbsIndex_of_pos_odd]
    simp [fullShellInverse, jacobiOrbitPoint, hsign, hpair]
  · have hR : ¬ 0 < -(jacobiToGauss r s).1 - -(jacobiToGauss r s).2 := by
      rw [show -(jacobiToGauss r s).1 - -(jacobiToGauss r s).2 =
          -((jacobiToGauss r s).1 - (jacobiToGauss r s).2) by ring]
      rw [jacobiToGauss_R_eq]
      omega
    have hRle : (jacobiToGauss r s).2 ≤ (jacobiToGauss r s).1 := by
      rw [show (jacobiToGauss r s).2 ≤ (jacobiToGauss r s).1 ↔
          0 ≤ (jacobiToGauss r s).1 - (jacobiToGauss r s).2 by omega]
      rw [jacobiToGauss_R_eq]
      omega
    have hS : ¬ 0 < -(jacobiToGauss r s).1 + -(jacobiToGauss r s).2 := by
      rw [show -(jacobiToGauss r s).1 + -(jacobiToGauss r s).2 =
          -((jacobiToGauss r s).1 + (jacobiToGauss r s).2) by ring]
      rw [jacobiToGauss_S_eq]
      omega
    have hsign :
        fullShellInverseSign (-(jacobiToGauss r s).1, -(jacobiToGauss r s).2) =
          ⟨3, by norm_num⟩ := by
      simp [fullShellInverseSign, hRle, hS]
    have hpair :
        fullShellInversePair (-(jacobiToGauss r s).1, -(jacobiToGauss r s).2) =
          (r, s) := by
      ext
      · simp [fullShellInversePair]
        rw [show -(jacobiToGauss r s).1 + -(jacobiToGauss r s).2 =
            -((jacobiToGauss r s).1 + (jacobiToGauss r s).2) by ring]
        rw [jacobiToGauss_S_eq, oddAbsIndex_of_neg_odd]
      · simp [fullShellInversePair]
        rw [show -(jacobiToGauss r s).1 + (jacobiToGauss r s).2 =
            -((jacobiToGauss r s).1 - (jacobiToGauss r s).2) by ring]
        rw [jacobiToGauss_R_eq, oddAbsIndex_of_neg_odd]
    simp [fullShellInverse, jacobiOrbitPoint, hsign, hpair]

theorem gaussian_eq_of_sub_add_eq {z w : GaussianInt}
    (hR : z.1 - z.2 = w.1 - w.2)
    (hS : z.1 + z.2 = w.1 + w.2) :
    z = w := by
  rcases z with ⟨a, b⟩
  rcases w with ⟨c, d⟩
  ext <;> omega

theorem int_natAbs_eq_of_pos {x : ℤ} (hx : 0 < x) :
    (x.natAbs : ℤ) = x := by
  exact Int.natAbs_of_nonneg (by omega)

theorem int_natAbs_eq_neg_of_not_pos_odd {x : ℤ}
    (hodd : x % 2 = 1) (hx : ¬ 0 < x) :
    (x.natAbs : ℤ) = -x := by
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero] at hodd
    norm_num at hodd
  have hxneg : x < 0 := by omega
  have h := Int.natAbs_of_nonneg (a := -x) (by omega : 0 ≤ -x)
  rwa [Int.natAbs_neg] at h

theorem jacobiOrbitPoint_fullShellInverse {N : ℕ} {z : GaussianInt}
    (hz : z ∈ fullNormShell N) :
    jacobiOrbitPoint (fullShellInverse z).1 (fullShellInverse z).2 = z := by
  rcases z with ⟨A, B⟩
  rw [fullNormShell, Finset.mem_filter] at hz
  rcases hz with ⟨_hbox, hnorm⟩
  let R : ℤ := A - B
  let S : ℤ := A + B
  let r : ℕ := oddAbsIndex S
  let s : ℕ := oddAbsIndex R
  have hRodd : R % 2 = 1 := by
    simpa [R] using (rs_odd_of_norm_shell hnorm).1
  have hSodd : S % 2 = 1 := by
    simpa [S] using (rs_odd_of_norm_shell hnorm).2
  have hRidx : 2 * (s : ℤ) + 1 = (R.natAbs : ℤ) := by
    simpa [s] using two_mul_oddAbsIndex_add_one hRodd
  have hSidx : 2 * (r : ℤ) + 1 = (S.natAbs : ℤ) := by
    simpa [r] using two_mul_oddAbsIndex_add_one hSodd
  have hpair : fullShellInversePair (A, B) = (r, s) := rfl
  by_cases hRpos : 0 < R
  · by_cases hSpos : 0 < S
    · have hRabs : (R.natAbs : ℤ) = R := int_natAbs_eq_of_pos hRpos
      have hSabs : (S.natAbs : ℤ) = S := int_natAbs_eq_of_pos hSpos
      have hRlt : B < A := by
        dsimp [R] at hRpos
        omega
      have hsign : fullShellInverseSign (A, B) = ⟨0, by norm_num⟩ := by
        simp [fullShellInverseSign, S, hRlt, hSpos]
      rw [fullShellInverse, hsign, hpair]
      change jacobiToGauss r s = (A, B)
      apply gaussian_eq_of_sub_add_eq
      · rw [jacobiToGauss_R_eq, hRidx, hRabs]
      · rw [jacobiToGauss_S_eq, hSidx, hSabs]
    · have hRabs : (R.natAbs : ℤ) = R := int_natAbs_eq_of_pos hRpos
      have hSabs : (S.natAbs : ℤ) = -S :=
        int_natAbs_eq_neg_of_not_pos_odd hSodd hSpos
      have hRlt : B < A := by
        dsimp [R] at hRpos
        omega
      have hsign : fullShellInverseSign (A, B) = ⟨2, by norm_num⟩ := by
        simp [fullShellInverseSign, S, hRlt, hSpos]
      rw [fullShellInverse, hsign, hpair]
      change (-(jacobiToGauss r s).2, -(jacobiToGauss r s).1) = (A, B)
      apply gaussian_eq_of_sub_add_eq
      · rw [show -(jacobiToGauss r s).2 - -(jacobiToGauss r s).1 =
            (jacobiToGauss r s).1 - (jacobiToGauss r s).2 by ring]
        rw [jacobiToGauss_R_eq, hRidx, hRabs]
      · rw [show -(jacobiToGauss r s).2 + -(jacobiToGauss r s).1 =
            -((jacobiToGauss r s).1 + (jacobiToGauss r s).2) by ring]
        rw [jacobiToGauss_S_eq, hSidx, hSabs]
        ring
  · by_cases hSpos : 0 < S
    · have hRabs : (R.natAbs : ℤ) = -R :=
        int_natAbs_eq_neg_of_not_pos_odd hRodd hRpos
      have hSabs : (S.natAbs : ℤ) = S := int_natAbs_eq_of_pos hSpos
      have hRle : A ≤ B := by
        dsimp [R] at hRpos
        omega
      have hsign : fullShellInverseSign (A, B) = ⟨1, by norm_num⟩ := by
        simp [fullShellInverseSign, S, hRle, hSpos]
      rw [fullShellInverse, hsign, hpair]
      change ((jacobiToGauss r s).2, (jacobiToGauss r s).1) = (A, B)
      apply gaussian_eq_of_sub_add_eq
      · rw [show (jacobiToGauss r s).2 - (jacobiToGauss r s).1 =
            -((jacobiToGauss r s).1 - (jacobiToGauss r s).2) by ring]
        rw [jacobiToGauss_R_eq, hRidx, hRabs]
        ring
      · rw [show (jacobiToGauss r s).2 + (jacobiToGauss r s).1 =
            (jacobiToGauss r s).1 + (jacobiToGauss r s).2 by ring]
        rw [jacobiToGauss_S_eq, hSidx, hSabs]
    · have hRabs : (R.natAbs : ℤ) = -R :=
        int_natAbs_eq_neg_of_not_pos_odd hRodd hRpos
      have hSabs : (S.natAbs : ℤ) = -S :=
        int_natAbs_eq_neg_of_not_pos_odd hSodd hSpos
      have hRle : A ≤ B := by
        dsimp [R] at hRpos
        omega
      have hsign : fullShellInverseSign (A, B) = ⟨3, by norm_num⟩ := by
        simp [fullShellInverseSign, S, hRle, hSpos]
      rw [fullShellInverse, hsign, hpair]
      change (-(jacobiToGauss r s).1, -(jacobiToGauss r s).2) = (A, B)
      apply gaussian_eq_of_sub_add_eq
      · rw [show -(jacobiToGauss r s).1 - -(jacobiToGauss r s).2 =
            -((jacobiToGauss r s).1 - (jacobiToGauss r s).2) by ring]
        rw [jacobiToGauss_R_eq, hRidx, hRabs]
        ring
      · rw [show -(jacobiToGauss r s).1 + -(jacobiToGauss r s).2 =
            -((jacobiToGauss r s).1 + (jacobiToGauss r s).2) by ring]
        rw [jacobiToGauss_S_eq, hSidx, hSabs]
        ring

theorem jacobiOrbitDomain_sum_eq_fullNormShell_sum (N : ℕ) :
    (∑ x ∈ jacobiOrbitDomain N,
        ((gaussH (jacobiOrbitPoint x.1 x.2) : ℤ) : ℚ)) =
      ∑ z ∈ fullNormShell N, ((gaussH z : ℤ) : ℚ) := by
  refine Finset.sum_bij'
    (fun x hx => jacobiOrbitPoint x.1 x.2)
    (fun z hz => fullShellInverse z)
    ?hi ?hj ?left ?right ?h
  · intro x hx
    exact jacobiOrbitPoint_mem_fullNormShell N x hx
  · intro z hz
    exact fullShellInverse_mem_jacobiOrbitDomain hz
  · intro x hx
    exact fullShellInverse_jacobiOrbitPoint x
  · intro z hz
    exact jacobiOrbitPoint_fullShellInverse hz
  · intro x hx
    rfl

theorem jacobiOrbitDomain_sum_eq_four_jacobiShellPairs_sum (N : ℕ) :
    (∑ x ∈ jacobiOrbitDomain N,
        ((gaussH (jacobiOrbitPoint x.1 x.2) : ℤ) : ℚ)) =
      4 * ∑ rs ∈ jacobiShellPairs N,
        ((gaussH (jacobiToGauss rs.1 rs.2) : ℤ) : ℚ) := by
  calc
    (∑ x ∈ jacobiOrbitDomain N,
        ((gaussH (jacobiOrbitPoint x.1 x.2) : ℤ) : ℚ))
        = ∑ i : Fin 4, ∑ rs ∈ jacobiShellPairs N,
            ((gaussH (jacobiOrbitPoint i rs) : ℤ) : ℚ) := by
            simp [jacobiOrbitDomain, Finset.sum_product]
    _ = ∑ rs ∈ jacobiShellPairs N, ∑ i : Fin 4,
            ((gaussH (jacobiOrbitPoint i rs) : ℤ) : ℚ) := by
            rw [Finset.sum_comm]
    _ = ∑ rs ∈ jacobiShellPairs N,
            4 * ((gaussH (jacobiToGauss rs.1 rs.2) : ℤ) : ℚ) := by
            apply Finset.sum_congr rfl
            intro rs hrs
            calc
              (∑ i : Fin 4, ((gaussH (jacobiOrbitPoint i rs) : ℤ) : ℚ))
                  = ∑ i : Fin 4,
                      ((gaussH (jacobiToGauss rs.1 rs.2) : ℤ) : ℚ) := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    rw [jacobiOrbitPoint_gaussH]
              _ = 4 * ((gaussH (jacobiToGauss rs.1 rs.2) : ℤ) : ℚ) := by
                    rw [Fin.sum_univ_four]
                    ring
    _ = 4 * ∑ rs ∈ jacobiShellPairs N,
            ((gaussH (jacobiToGauss rs.1 rs.2) : ℤ) : ℚ) := by
            rw [Finset.mul_sum]

theorem fullNormShell_sum_eq_four_jacobiShellPairs_sum (N : ℕ) :
    (∑ z ∈ fullNormShell N, ((gaussH z : ℤ) : ℚ)) =
      4 * ∑ rs ∈ jacobiShellPairs N,
        ((gaussH (jacobiToGauss rs.1 rs.2) : ℤ) : ℚ) := by
  rw [← jacobiOrbitDomain_sum_eq_fullNormShell_sum N]
  exact jacobiOrbitDomain_sum_eq_four_jacobiShellPairs_sum N

theorem jacobiThetaSquareCoeffExpanded_eq_jacobiShellPairs_sum (N : ℕ) :
    jacobiThetaSquareCoeffExpanded N =
      ∑ rs ∈ jacobiShellPairs N,
        ((gaussH (jacobiToGauss rs.1 rs.2) : ℤ) : ℚ) := by
  unfold jacobiThetaSquareCoeffExpanded jacobiShellPairs
  rw [Finset.sum_filter]
  have hleft :
      (∑ r ∈ Finset.range (N + 1),
        ∑ s ∈ Finset.range (N + 1),
          if triangularIndex r + triangularIndex s = N then
            jacobiSignAt r * jacobiSignAt s
          else 0) =
        ∑ rs ∈ (Finset.range (N + 1)).product (Finset.range (N + 1)),
          if triangularIndex rs.1 + triangularIndex rs.2 = N then
            jacobiSignAt rs.1 * jacobiSignAt rs.2
          else 0 := by
    exact (Finset.sum_product (Finset.range (N + 1)) (Finset.range (N + 1))
      (fun rs : ℕ × ℕ =>
        if triangularIndex rs.1 + triangularIndex rs.2 = N then
          jacobiSignAt rs.1 * jacobiSignAt rs.2
        else 0)).symm
  rw [hleft]
  apply Finset.sum_congr rfl
  intro rs _hrs
  rcases rs with ⟨r, s⟩
  by_cases h : triangularIndex r + triangularIndex s = N
  · simp [h, jacobiExpandedWeight_eq_gaussH]
  · simp [h]

theorem fullNormShellHQuarterSum_eq_fullNormShell_sum_div (N : ℕ) :
    fullNormShellHQuarterSum N =
      (∑ z ∈ fullNormShell N, ((gaussH z : ℤ) : ℚ)) / 4 := by
  have hsum :
      (∑ A ∈ normShellBox N,
        ∑ B ∈ normShellBox N,
          if A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1 then
            ((gaussH (A,B) : ℤ) : ℚ)
          else 0) =
        ∑ z ∈ fullNormShell N, ((gaussH z : ℤ) : ℚ) := by
    unfold fullNormShell
    rw [Finset.sum_filter]
    have hleft :
        (∑ A ∈ normShellBox N,
          ∑ B ∈ normShellBox N,
            if A ^ 2 + B ^ 2 = 4 * (N : ℤ) + 1 then
              ((gaussH (A,B) : ℤ) : ℚ)
            else 0) =
          ∑ z ∈ (normShellBox N).product (normShellBox N),
            if z.1 ^ 2 + z.2 ^ 2 = 4 * (N : ℤ) + 1 then
              ((gaussH z : ℤ) : ℚ)
            else 0 := by
      exact (Finset.sum_product (normShellBox N) (normShellBox N)
        (fun z : ℤ × ℤ =>
          if z.1 ^ 2 + z.2 ^ 2 = 4 * (N : ℤ) + 1 then
            ((gaussH z : ℤ) : ℚ)
          else 0)).symm
    rw [hleft]
  unfold fullNormShellHQuarterSum
  rw [hsum]

theorem jacobiThetaSquareCoeffExpanded_eq_fullNormShellHQuarterSum (N : ℕ) :
    jacobiThetaSquareCoeffExpanded N = fullNormShellHQuarterSum N := by
  rw [jacobiThetaSquareCoeffExpanded_eq_jacobiShellPairs_sum,
    fullNormShellHQuarterSum_eq_fullNormShell_sum_div,
    fullNormShell_sum_eq_four_jacobiShellPairs_sum]
  ring

theorem jacobiThetaSquareCoeff_eq_fullNormShellHQuarterSum (N : ℕ) :
    jacobiThetaSquareCoeff N = fullNormShellHQuarterSum N := by
  rw [jacobiThetaSquareCoeff_eq_expanded,
    jacobiThetaSquareCoeffExpanded_eq_fullNormShellHQuarterSum]

theorem pentagonalWronskianCoeffExpanded_eq_pentagonalShellPairs_sum_gaussK (N : ℕ) :
    pentagonalWronskianCoeffExpanded N =
      ∑ kl ∈ pentagonalShellPairs N,
        ((gaussK (pentagonalToGauss kl.1 kl.2) : ℤ) : ℚ) := by
  unfold pentagonalWronskianCoeffExpanded pentagonalShellPairs
  rw [Finset.sum_filter]
  have hleft :
      (∑ k ∈ Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ),
        ∑ l ∈ Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ),
          if pentagonal014Exp k + pentagonal023Exp l = N then
            pentagonalCoeffPairWeight k l
          else 0) =
        ∑ kl ∈
          (Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ)).product
            (Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ)),
          if pentagonal014Exp kl.1 + pentagonal023Exp kl.2 = N then
            pentagonalCoeffPairWeight kl.1 kl.2
          else 0 := by
    exact (Finset.sum_product
      (Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ))
      (Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ))
      (fun kl : ℤ × ℤ =>
        if pentagonal014Exp kl.1 + pentagonal023Exp kl.2 = N then
          pentagonalCoeffPairWeight kl.1 kl.2
        else 0)).symm
  rw [hleft]
  apply Finset.sum_congr rfl
  intro kl _hkl
  rcases kl with ⟨k, l⟩
  by_cases h : pentagonal014Exp k + pentagonal023Exp l = N
  · simp [h, pentagonalCoeffPairWeight_eq_gaussK]
  · simp [h]

theorem pentagonalShellPairs_sum_gaussK_eq_pentagonalSector_sum_gaussK (N : ℕ) :
    (∑ kl ∈ pentagonalShellPairs N,
        ((gaussK (pentagonalToGauss kl.1 kl.2) : ℤ) : ℚ)) =
      ∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ) := by
  refine Finset.sum_bij'
    (fun kl hkl => pentagonalToGauss kl.1 kl.2)
    (fun z hz => pentagonalSectorInverse z)
    ?hi ?hj ?left ?right ?h
  · intro kl hkl
    exact pentagonalToGauss_mem_pentagonalSector hkl
  · intro z hz
    exact pentagonalSectorInverse_mem_pentagonalShellPairs hz
  · intro kl hkl
    rcases kl with ⟨k, l⟩
    exact pentagonalSectorInverse_pentagonalToGauss k l
  · intro z hz
    exact pentagonalToGauss_pentagonalSectorInverse hz
  · intro kl hkl
    rfl

theorem pentagonalWronskianCoeffExpanded_eq_pentagonalSector_sum_gaussK (N : ℕ) :
    pentagonalWronskianCoeffExpanded N =
      ∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ) := by
  rw [pentagonalWronskianCoeffExpanded_eq_pentagonalShellPairs_sum_gaussK,
    pentagonalShellPairs_sum_gaussK_eq_pentagonalSector_sum_gaussK]

theorem pentagonalWronskianCoeffExpanded_eq_fullNormShellKSum_div (N : ℕ) :
    pentagonalWronskianCoeffExpanded N = fullNormShellKSum N / 4 := by
  rw [pentagonalWronskianCoeffExpanded_eq_pentagonalSector_sum_gaussK,
    pentagonalSector_sum_gaussK_eq_fullNormShellKSum_div]

theorem pentagonalSector_sum_gaussK_eq_fullNormShellHQuarterSum_of_t0 (N : ℕ)
    (h5N : (4 * (N : ℤ) + 1) % 5 ≠ 0) :
    (∑ z ∈ pentagonalSector N, ((gaussK z : ℤ) : ℚ)) =
      fullNormShellHQuarterSum N := by
  rw [fullNormShellHQuarterSum_eq_fullNormShell_sum_div]
  exact pentagonalSector_sum_gaussK_eq_fullNormShellHSum_div_of_t0 N h5N

theorem pentagonalWronskianCoeffExpanded_eq_fullNormShellHQuarterSum_of_t0
    (N : ℕ) (h5N : (4 * (N : ℤ) + 1) % 5 ≠ 0) :
    pentagonalWronskianCoeffExpanded N = fullNormShellHQuarterSum N := by
  rw [pentagonalWronskianCoeffExpanded_eq_pentagonalSector_sum_gaussK,
    pentagonalSector_sum_gaussK_eq_fullNormShellHQuarterSum_of_t0 N h5N]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem jacobiThetaSquareCoeffExpanded_eq_fullNormShellHQuarterSum_le_fifty :
    ∀ N : ℕ, N ≤ 50 → jacobiThetaSquareCoeffExpanded N = fullNormShellHQuarterSum N := by
  intro N _hN
  exact jacobiThetaSquareCoeffExpanded_eq_fullNormShellHQuarterSum N

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem pentagonalWronskianCoeffExpanded_eq_fullNormShellHQuarterSum_le_fifty :
    ∀ N : ℕ, N ≤ 50 → pentagonalWronskianCoeffExpanded N = fullNormShellHQuarterSum N := by
  native_decide

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem expanded_coeff_identity_le_fifty :
    ∀ N : ℕ, N ≤ 50 → pentagonalWronskianCoeffExpanded N = jacobiThetaSquareCoeffExpanded N := by
  intro N hN
  rw [pentagonalWronskianCoeffExpanded_eq_fullNormShellHQuarterSum_le_fifty N hN,
    jacobiThetaSquareCoeffExpanded_eq_fullNormShellHQuarterSum_le_fifty N hN]

theorem pentagonalWronskianCoeff_eq_expanded (N : ℕ) :
    pentagonalWronskianCoeff N = pentagonalWronskianCoeffExpanded N := by
  let B : Finset ℤ := Finset.Icc (-(N + 1 : ℤ)) (N + 1 : ℤ)
  have hbase : (∑ ij ∈ Finset.antidiagonal N,
      pentagonal014Coeff ℚ ij.1 * pentagonal023Coeff ℚ ij.2) =
      ∑ k ∈ B, ∑ l ∈ B,
        if pentagonal014Exp k + pentagonal023Exp l = N then
          negOnePowInt ℚ k * negOnePowInt ℚ l else 0 := by
    calc
      (∑ ij ∈ Finset.antidiagonal N,
        pentagonal014Coeff ℚ ij.1 * pentagonal023Coeff ℚ ij.2)
          = ∑ ij ∈ Finset.antidiagonal N,
              (∑ k ∈ B, if pentagonal014Exp k = ij.1 then negOnePowInt ℚ k else 0) *
                (∑ l ∈ B, if pentagonal023Exp l = ij.2 then negOnePowInt ℚ l else 0) := by
              apply Finset.sum_congr rfl
              intro ij hij
              have hsum : ij.1 + ij.2 = N := by
                simpa [Finset.mem_antidiagonal] using hij
              have hle1 : ij.1 ≤ N := by omega
              have hle2 : ij.2 ≤ N := by omega
              rw [pentagonal014Coeff_eq_sum_Icc_of_le (n := ij.1) (N := N) hle1]
              rw [pentagonal023Coeff_eq_sum_Icc_of_le (n := ij.2) (N := N) hle2]
          _ = ∑ k ∈ B, ∑ l ∈ B,
            if pentagonal014Exp k + pentagonal023Exp l = N then
              negOnePowInt ℚ k * negOnePowInt ℚ l else 0 := by
              exact antidiagonal_indicator_product N B B pentagonal014Exp pentagonal023Exp
                (fun k => negOnePowInt ℚ k) (fun l => negOnePowInt ℚ l)
  have hder1 : (∑ ij ∈ Finset.antidiagonal N,
      pentagonal023Coeff ℚ ij.1 * pentagonal014Coeff ℚ ij.2 * (ij.2 : ℚ)) =
      ∑ l ∈ B, ∑ k ∈ B,
        if pentagonal023Exp l + pentagonal014Exp k = N then
          negOnePowInt ℚ l * negOnePowInt ℚ k * (pentagonal014Exp k : ℚ) else 0 := by
    calc
      (∑ ij ∈ Finset.antidiagonal N,
        pentagonal023Coeff ℚ ij.1 * pentagonal014Coeff ℚ ij.2 * (ij.2 : ℚ))
          = ∑ ij ∈ Finset.antidiagonal N,
              (∑ l ∈ B, if pentagonal023Exp l = ij.1 then negOnePowInt ℚ l else 0) *
                (∑ k ∈ B, if pentagonal014Exp k = ij.2 then negOnePowInt ℚ k else 0) *
                (ij.2 : ℚ) := by
              apply Finset.sum_congr rfl
              intro ij hij
              have hsum : ij.1 + ij.2 = N := by
                simpa [Finset.mem_antidiagonal] using hij
              have hle1 : ij.1 ≤ N := by omega
              have hle2 : ij.2 ≤ N := by omega
              rw [pentagonal023Coeff_eq_sum_Icc_of_le (n := ij.1) (N := N) hle1]
              rw [pentagonal014Coeff_eq_sum_Icc_of_le (n := ij.2) (N := N) hle2]
          _ = ∑ l ∈ B, ∑ k ∈ B,
            if pentagonal023Exp l + pentagonal014Exp k = N then
              negOnePowInt ℚ l * negOnePowInt ℚ k * (pentagonal014Exp k : ℚ) else 0 := by
              exact antidiagonal_indicator_product_rightWeight N B B pentagonal023Exp pentagonal014Exp
                (fun l => negOnePowInt ℚ l) (fun k => negOnePowInt ℚ k)
  have hder2 : (∑ ij ∈ Finset.antidiagonal N,
      pentagonal014Coeff ℚ ij.1 * pentagonal023Coeff ℚ ij.2 * (ij.2 : ℚ)) =
      ∑ k ∈ B, ∑ l ∈ B,
        if pentagonal014Exp k + pentagonal023Exp l = N then
          negOnePowInt ℚ k * negOnePowInt ℚ l * (pentagonal023Exp l : ℚ) else 0 := by
    calc
      (∑ ij ∈ Finset.antidiagonal N,
        pentagonal014Coeff ℚ ij.1 * pentagonal023Coeff ℚ ij.2 * (ij.2 : ℚ))
          = ∑ ij ∈ Finset.antidiagonal N,
              (∑ k ∈ B, if pentagonal014Exp k = ij.1 then negOnePowInt ℚ k else 0) *
                (∑ l ∈ B, if pentagonal023Exp l = ij.2 then negOnePowInt ℚ l else 0) *
                (ij.2 : ℚ) := by
              apply Finset.sum_congr rfl
              intro ij hij
              have hsum : ij.1 + ij.2 = N := by
                simpa [Finset.mem_antidiagonal] using hij
              have hle1 : ij.1 ≤ N := by omega
              have hle2 : ij.2 ≤ N := by omega
              rw [pentagonal014Coeff_eq_sum_Icc_of_le (n := ij.1) (N := N) hle1]
              rw [pentagonal023Coeff_eq_sum_Icc_of_le (n := ij.2) (N := N) hle2]
          _ = ∑ k ∈ B, ∑ l ∈ B,
            if pentagonal014Exp k + pentagonal023Exp l = N then
              negOnePowInt ℚ k * negOnePowInt ℚ l * (pentagonal023Exp l : ℚ) else 0 := by
              exact antidiagonal_indicator_product_rightWeight N B B pentagonal014Exp pentagonal023Exp
                (fun k => negOnePowInt ℚ k) (fun l => negOnePowInt ℚ l)
  unfold pentagonalWronskianCoeff pentagonalWronskianCoeffExpanded pentagonalCoeffPairWeight
  rw [hbase, hder1, hder2]
  have hder1_reindexed :
      (∑ l ∈ B, ∑ k ∈ B,
        if pentagonal023Exp l + pentagonal014Exp k = N then
          negOnePowInt ℚ l * negOnePowInt ℚ k * (pentagonal014Exp k : ℚ) else 0) =
      ∑ k ∈ B, ∑ l ∈ B,
        if pentagonal014Exp k + pentagonal023Exp l = N then
          negOnePowInt ℚ k * negOnePowInt ℚ l * (pentagonal014Exp k : ℚ) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _hk
    apply Finset.sum_congr rfl
    intro l _hl
    by_cases h : pentagonal014Exp k + pentagonal023Exp l = N
    · have h' : pentagonal023Exp l + pentagonal014Exp k = N := by omega
      simp [h, h', mul_comm, mul_assoc]
    · have h' : pentagonal023Exp l + pentagonal014Exp k ≠ N := by omega
      simp [h, h']
  rw [hder1_reindexed]
  simp only [B]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases h : pentagonal014Exp k + pentagonal023Exp l = N
  · simp [h]
    ring
  · simp [h]

theorem coeff_identity_of_expanded_identity (N : ℕ)
    (h : pentagonalWronskianCoeffExpanded N = jacobiThetaSquareCoeffExpanded N) :
    pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  rw [pentagonalWronskianCoeff_eq_expanded, jacobiThetaSquareCoeff_eq_expanded]
  exact h

theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_t0
    (N : ℕ) (h5N : (4 * (N : ℤ) + 1) % 5 ≠ 0) :
    pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  rw [pentagonalWronskianCoeff_eq_expanded,
    pentagonalWronskianCoeffExpanded_eq_fullNormShellHQuarterSum_of_t0 N h5N,
    jacobiThetaSquareCoeff_eq_fullNormShellHQuarterSum]

theorem nat_eq_four_mul_sub_one_div_four_add_one_of_int_mod_four_eq_one
    (M : ℕ) (hM4 : ((M : ℤ) % 4) = 1) :
    M = 4 * ((M - 1) / 4) + 1 := by
  have hMmod : M % 4 = 1 := by
    omega
  omega

theorem nat_pos_of_int_mod_four_eq_one
    (M : ℕ) (hM4 : ((M : ℤ) % 4) = 1) :
    0 < M := by
  omega

theorem nat_div_five_mod_four_one_of_mod_four_one
    (M : ℕ) (hM4 : ((M : ℤ) % 4) = 1) (hM5 : M % 5 = 0) :
    (((M / 5 : ℕ) : ℤ) % 4) = 1 := by
  have hdiv : 5 ∣ M := Nat.dvd_of_mod_eq_zero hM5
  have hMmul : 5 * (M / 5) = M := Nat.mul_div_cancel' hdiv
  have hcast : (M : ℤ) = 5 * ((M / 5 : ℕ) : ℤ) := by
    exact_mod_cast hMmul.symm
  omega

theorem nat_div_five_mod_two_one_of_mod_four_one
    (M : ℕ) (hM4 : ((M : ℤ) % 4) = 1) (hM5 : M % 5 = 0) :
    (((M / 5 : ℕ) : ℤ) % 2) = 1 := by
  have hm4 := nat_div_five_mod_four_one_of_mod_four_one M hM4 hM5
  omega

theorem normShellKSumByNorm_eq_normShellHSumByNorm_of_mod_four_one
    (M : ℕ) (hM4 : ((M : ℤ) % 4) = 1) :
    normShellKSumByNorm M = normShellHSumByNorm M := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
      by_cases hM5 : M % 5 = 0
      · have hMpos : 0 < M := nat_pos_of_int_mod_four_eq_one M hM4
        let m : ℕ := M / 5
        have hMmul : 5 * m = M := by
          exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hM5)
        have hm4 : ((m : ℤ) % 4) = 1 := by
          dsimp [m]
          exact nat_div_five_mod_four_one_of_mod_four_one M hM4 hM5
        have hmodd : ((m : ℤ) % 2) = 1 := by
          dsimp [m]
          exact nat_div_five_mod_two_one_of_mod_four_one M hM4 hM5
        have hm_lt : m < M := by
          dsimp [m]
          omega
        have ihm : normShellKSumByNorm m = normShellHSumByNorm m :=
          ih m hm_lt hm4
        by_cases hm5 : m % 5 = 0
        · have hmdiv4 : (((m / 5 : ℕ) : ℤ) % 4) = 1 :=
            nat_div_five_mod_four_one_of_mod_four_one m hm4 hm5
          have hmdiv_lt : m / 5 < M := by
            have hm_nonneg : m / 5 ≤ m := Nat.div_le_self m 5
            omega
          have ihmdiv :
              normShellKSumByNorm (m / 5) = normShellHSumByNorm (m / 5) :=
            ih (m / 5) hmdiv_lt hmdiv4
          calc
            normShellKSumByNorm M
                = normShellKSumByNorm (5 * m) := by rw [hMmul]
            _ = -6 * normShellKSumByNorm m -
                  25 * normShellKSumByNorm (m / 5) := by
                  rw [normShellKSumByNorm_five_mul_recurrence_of_five_dvd
                    m hmodd hm5]
            _ = -6 * normShellHSumByNorm m -
                  25 * normShellHSumByNorm (m / 5) := by
                  rw [ihm, ihmdiv]
            _ = normShellHSumByNorm (5 * m) := by
                  rw [normShellHSumByNorm_five_mul_recurrence_of_five_dvd m hm5]
            _ = normShellHSumByNorm M := by rw [hMmul]
        · calc
            normShellKSumByNorm M
                = normShellKSumByNorm (5 * m) := by rw [hMmul]
            _ = -6 * normShellKSumByNorm m := by
                  rw [normShellKSumByNorm_five_mul_recurrence_of_not_five_dvd
                    m hmodd hm5]
            _ = -6 * normShellHSumByNorm m := by rw [ihm]
            _ = normShellHSumByNorm (5 * m) := by
                  rw [normShellHSumByNorm_five_mul_recurrence_of_not_five_dvd m hm5]
            _ = normShellHSumByNorm M := by rw [hMmul]
      · let N : ℕ := (M - 1) / 4
        have hMeq : M = 4 * N + 1 := by
          dsimp [N]
          exact nat_eq_four_mul_sub_one_div_four_add_one_of_int_mod_four_eq_one M hM4
        have h5N : (4 * (N : ℤ) + 1) % 5 ≠ 0 := by
          have hM5Z : ((M : ℤ) % 5) ≠ 0 := by omega
          rw [hMeq] at hM5Z
          exact hM5Z
        calc
          normShellKSumByNorm M
              = normShellKSumByNorm (4 * N + 1) := by rw [hMeq]
          _ = fullNormShellKSum N := normShellKSumByNorm_four_mul_add_one N
          _ = ∑ z ∈ fullNormShell N, ((gaussH z : ℤ) : ℚ) :=
                fullNormShellKSum_eq_fullNormShellHSum_of_t0 N h5N
          _ = normShellHSumByNorm (4 * N + 1) :=
                (normShellHSumByNorm_four_mul_add_one N).symm
          _ = normShellHSumByNorm M := by rw [hMeq]

theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_normShell_eq
    (N : ℕ)
    (h :
      normShellKSumByNorm (4 * N + 1) =
        normShellHSumByNorm (4 * N + 1)) :
    pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  calc
    pentagonalWronskianCoeff N
        = fullNormShellKSum N / 4 := by
            rw [pentagonalWronskianCoeff_eq_expanded,
              pentagonalWronskianCoeffExpanded_eq_fullNormShellKSum_div]
    _ = normShellKSumByNorm (4 * N + 1) / 4 := by
            rw [normShellKSumByNorm_four_mul_add_one]
    _ = normShellHSumByNorm (4 * N + 1) / 4 := by
            rw [h]
    _ = (∑ z ∈ fullNormShell N, ((gaussH z : ℤ) : ℚ)) / 4 := by
            rw [normShellHSumByNorm_four_mul_add_one]
    _ = fullNormShellHQuarterSum N := by
            rw [fullNormShellHQuarterSum_eq_fullNormShell_sum_div]
    _ = jacobiThetaSquareCoeff N := by
            rw [jacobiThetaSquareCoeff_eq_fullNormShellHQuarterSum]

theorem jacobiThetaSquareCoeff_eq_fullNormShellHQuarterSum_le_fifty :
    ∀ N : ℕ, N ≤ 50 → jacobiThetaSquareCoeff N = fullNormShellHQuarterSum N := by
  intro N hN
  rw [jacobiThetaSquareCoeff_eq_expanded,
    jacobiThetaSquareCoeffExpanded_eq_fullNormShellHQuarterSum_le_fifty N hN]

theorem pentagonalWronskianCoeff_eq_fullNormShellHQuarterSum_le_fifty :
    ∀ N : ℕ, N ≤ 50 → pentagonalWronskianCoeff N = fullNormShellHQuarterSum N := by
  intro N hN
  rw [pentagonalWronskianCoeff_eq_expanded,
    pentagonalWronskianCoeffExpanded_eq_fullNormShellHQuarterSum_le_fifty N hN]

theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_via_fullNormShell_le_fifty :
    ∀ N : ℕ, N ≤ 50 → pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  intro N hN
  rw [pentagonalWronskianCoeff_eq_fullNormShellHQuarterSum_le_fifty N hN,
    jacobiThetaSquareCoeff_eq_fullNormShellHQuarterSum_le_fifty N hN]

theorem coeff_pentagonal_wronskian_lhs (N : ℕ) :
    (pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
      5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
           pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ))).coeff N =
      pentagonalWronskianCoeff N := by
  change
    (pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
      PowerSeries.C (5 : ℚ) *
        (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
          pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ))).coeff N =
      pentagonalWronskianCoeff N
  rw [map_add, PowerSeries.coeff_C_mul]
  simp [pentagonalWronskianCoeff, PowerSeries.coeff_mul, coeff_thetaOp]
  ring_nf

theorem coeff_jacobiThetaPS_sq (N : ℕ) :
    ((jacobiThetaPS ℚ)^2).coeff N = jacobiThetaSquareCoeff N := by
  simp [jacobiThetaSquareCoeff, pow_two, PowerSeries.coeff_mul]

/-- If the finite double-sum identity holds in every degree, the independent
pentagonal-level Wronskian follows immediately from Jacobi cube. -/
theorem wronskian_at_pentagonal_level_of_coeff_identity
    (hcoeff : ∀ N : ℕ, pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N) :
    pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
      5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
           pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ)) =
    (qPochInfPS ℚ) ^ 6 := by
  rw [qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two]
  ext N
  rw [coeff_pentagonal_wronskian_lhs, coeff_jacobiThetaPS_sq, hcoeff N]

/-- Coefficient form of the new route: an independent proof of the
quintuple-product logarithmic derivative identity closes the Wronskian
coefficient identity in every degree. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_quintupleProduct_log_derivative
    (hlog :
      quintupleLogFactor =
        (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹)
    (N : ℕ) :
    pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  have hlog' :
      (1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * (thetaLog P014 - thetaLog P023) =
        (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹ := by
    simpa [quintupleLogFactor] using hlog
  have hw :
      pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
          5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
               pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ)) =
        (qPochInfPS ℚ) ^ 6 := by
    simpa [P014, P023] using
      wronskian_of_quintupleProduct_log_derivative_identity hlog'
  have hcoeff := congrArg (fun f : ℚ⟦X⟧ => f.coeff N) hw
  change
    (pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
        5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
             pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ))).coeff N =
      ((qPochInfPS ℚ) ^ 6).coeff N at hcoeff
  rw [coeff_pentagonal_wronskian_lhs] at hcoeff
  rw [qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two] at hcoeff
  rw [coeff_jacobiThetaPS_sq] at hcoeff
  exact hcoeff

/-- Multiplicative AP-sigma eta-quotient form of the same route.  This is the
coefficient-level handoff target for a formal proof of Chan's residue-class
Lambert identity. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_apSigma_mul_expandFive
    (h :
      apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5)
    (N : ℕ) :
    pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  exact
    pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_quintupleProduct_log_derivative
      (quintupleProduct_log_derivative_identity_of_apSigma_mul_expandFive h) N

/-- Direct product-side Lambert identity route to the Wronskian coefficient
identity.  This is the recurrence-free endpoint for proving
`1 + 5*Σ* = η(q)^5/η(q^5)`. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_apSigma_eq_etaQuotientProductSide
    (h : apSigmaLambertFactor = etaQuotientProductSide)
    (N : ℕ) :
    pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  exact pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_apSigma_mul_expandFive
    (by rw [h]; exact etaQuotientProductSide_mul_expandFive_eq_qPoch_pow_five) N

/-- A direct theta-image proof of Chan's AP-sigma eta quotient would close the
Wronskian coefficient identity. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_apSigma_thetaOp_eq
    (hθ : thetaOp apSigmaLambertFactor = thetaOp etaQuotientProductSide)
    (N : ℕ) :
    pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  exact pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_apSigma_eq_etaQuotientProductSide
    (apSigmaLambertFactor_eq_etaQuotientProductSide_iff_thetaOp_eq.mpr hθ) N

/-- Sturm-bound route to the Wronskian coefficient identity.  This isolates the
remaining modular-form input to the specialized bound for the cleared
AP-sigma eta-product gap. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_sturm_bound_one
    (hsturm : APSigmaEtaProductGapSturmBoundOne) (N : ℕ) :
    pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  exact pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_apSigma_mul_expandFive
    (apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_of_sturm_bound_one hsturm) N

/-- Residual form of the quintuple-product route: the pure integer AP-sigma
theta-log residual is now the single remaining arithmetic input. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_apSigma_residual_zero
    (hres : ∀ n : ℕ, apSigmaLambertThetaResidualZ n = 0)
    (N : ℕ) :
    pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  exact pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_apSigma_mul_expandFive
    (apSigmaLambert_mul_expandFive_eq_qPoch_pow_five_of_residual_zero hres) N

/-- A finite recurrence for the AP-sigma residual would close the complete
Wronskian coefficient identity through the quintuple-product route. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_apSigma_residual_recurrence
    (c : ℕ → ℤ) (d : ℕ)
    (hrec : ∀ n : ℕ, 200 < n →
      apSigmaLambertThetaResidualZ n =
        ∑ i ∈ Finset.range d, c i * apSigmaLambertThetaResidualZ (n - (i + 1)))
    (N : ℕ) :
    pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  exact pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_apSigma_residual_zero
    (apSigmaLambertThetaResidualZ_eq_zero_of_linear_recurrence_after_twohundred c d hrec) N

/-- Series-level version of the same bridge: once the AP-sigma eta quotient is
proved in multiplicative form, the pentagonal-level Wronskian follows without
the 5-string coefficient argument. -/
theorem wronskian_at_pentagonal_level_of_apSigma_mul_expandFive
    (h :
      apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5) :
    pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
      5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
           pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ)) =
    (qPochInfPS ℚ) ^ 6 := by
  exact wronskian_at_pentagonal_level_of_coeff_identity
    (pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_apSigma_mul_expandFive h)

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
/-- The coefficient identity checked by native computation through degree `50`. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_le_fifty :
    ∀ N : ℕ, N ≤ 50 → pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  native_decide

/-- The remaining independent mathematical core: the 5-string or recurrence
argument should prove this finite double-sum identity for every degree. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff
    (N : ℕ) :
    pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  apply pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_of_normShell_eq
  exact normShellKSumByNorm_eq_normShellHSumByNorm_of_mod_four_one
    (4 * N + 1) (by omega)

/-- The coefficient identity through degree `100`, now derived from the
expanded executable coefficient model. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_le_hundred :
    ∀ N : ℕ, N ≤ 100 → pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  native_decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
/-- The coefficient identity through degree `200`, checked directly by the
expanded executable coefficient model. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_le_two_hundred :
    ∀ N : ℕ, N ≤ 200 → pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  native_decide

/-- The coefficient identity through degree `250`, derived from the all-degree
bridge. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_le_two_hundred_fifty :
    ∀ N : ℕ, N ≤ 250 → pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  intro N _hN
  exact pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff N

/-- The coefficient identity through degree `500`, derived from the all-degree
bridge. -/
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_le_five_hundred_branch :
    ∀ N : ℕ, N ≤ 500 → pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N := by
  intro N _hN
  exact pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff N

/-- **Pentagonal-level Wronskian, independent of Chan 11.7 except for the
single coefficient identity above.** -/
theorem wronskian_at_pentagonal_level :
    pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
      5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
           pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ)) =
    (qPochInfPS ℚ) ^ 6 := by
  exact wronskian_at_pentagonal_level_of_coeff_identity
    pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff

/-- The quintuple-product logarithmic-derivative identity in formal power
series form.  This is the divided version of the pentagonal Wronskian, with
division represented by multiplication by the inverse of `(X^5;X^5)_∞`. -/
theorem quintupleProduct_log_derivative_identity :
    (1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * (thetaLog P014 - thetaLog P023) =
      (qPochInfPS ℚ) ^ 5 * expandFiveQpochRat⁻¹ := by
  apply quintupleProduct_log_derivative_identity_of_wronskian
  simpa [P014, P023] using wronskian_at_pentagonal_level

end Ch15WronskianIndependent
end Pending
end QseriesFormalization
