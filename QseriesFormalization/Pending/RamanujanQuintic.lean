import QseriesFormalization.Chapter19
import QseriesFormalization.Pending.Chapter16_MBI_Proof
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Ramanujan quintic cyclotomic infrastructure

This file builds a small, reusable formal-power-series layer for the
root-of-unity product route toward Hirschhorn's quintic product identity.

The results below are deliberately finite/product-local: they prove the
`X ↦ cX` power-series homomorphism API and the fifth-root finite factor
collapse.  They do not assert the infinite-product quotient or the final
`core * P5 = E^11` identity.
-/

namespace QseriesFormalization
namespace Pending
namespace RamanujanQuintic

open Finset
open PowerSeries
open scoped PowerSeries
open QseriesFormalization.PartIV.Ch19

/-! ## Scaling the variable -/

/-- The power-series ring homomorphism `f(X) ↦ f(c X)`.  This is Mathlib's
`PowerSeries.rescale`, exposed under the name used by the quintic route. -/
noncomputable abbrev scaleX {R : Type*} [CommSemiring R] (c : R) :
    R⟦X⟧ →+* R⟦X⟧ :=
  PowerSeries.rescale c

@[simp] theorem coeff_scaleX {R : Type*} [CommSemiring R]
    (c : R) (φ : R⟦X⟧) (n : ℕ) :
    (scaleX c φ).coeff n = φ.coeff n * c ^ n := by
  rw [scaleX, PowerSeries.coeff_rescale]
  ring

@[simp] theorem scaleX_X {R : Type*} [CommRing R] (c : R) :
    scaleX c (PowerSeries.X : R⟦X⟧) = PowerSeries.C c * PowerSeries.X := by
  simp [scaleX]

@[simp] theorem scaleX_X_pow {R : Type*} [CommRing R] (c : R) (m : ℕ) :
    scaleX c ((PowerSeries.X : R⟦X⟧) ^ m) =
      PowerSeries.C (c ^ m) * PowerSeries.X ^ m := by
  rw [map_pow, scaleX_X, mul_pow, ← map_pow (PowerSeries.C : R →+* R⟦X⟧)]

@[simp] theorem scaleX_oneSubXPow {R : Type*} [CommRing R] (c : R) (k : ℕ) :
    scaleX c (oneSubXPow R k) =
      1 - PowerSeries.C (c ^ (k + 1)) * PowerSeries.X ^ (k + 1) := by
  unfold oneSubXPow
  rw [map_sub, map_one, scaleX_X_pow]

theorem scaleX_qPochFinitePS {R : Type*} [CommRing R] (c : R) (N : ℕ) :
    scaleX c (qPochFinitePS R N) =
      ∏ k ∈ Finset.range N,
        ((1 : R⟦X⟧) -
          PowerSeries.C (c ^ (k + 1)) * PowerSeries.X ^ (k + 1)) := by
  simp [qPochFinitePS, scaleX_oneSubXPow]

/-- Scaling commutes with `expand p` after replacing the scale factor by
`c^p` on the unexpanded series. -/
theorem scaleX_expand {R : Type*} [CommRing R] (c : R)
    (p : ℕ) (hp : p ≠ 0) (φ : R⟦X⟧) :
    scaleX c (PowerSeries.expand p hp φ) =
      PowerSeries.expand p hp (scaleX (c ^ p) φ) := by
  ext n
  rw [coeff_scaleX, PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  by_cases hdiv : p ∣ n
  · have hpow : c ^ n = (c ^ p) ^ (n / p) := by
      obtain ⟨q, hq⟩ := hdiv
      subst n
      rw [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hp), pow_mul]
    simp [hdiv, hpow]
    ring
  · simp [hdiv]

/-! ## Fifth-root finite factor collapse -/

/-- If `μ` is a primitive fifth root, then the five linear factors
`∏_{j=0}^4 (1 - μ^j y)` collapse to `1 - y^5`.

This is the local algebraic factor used by the finite q-Pochhammer collapse
below. -/
theorem prod_one_sub_primitive_fifth {A : Type*} [CommRing A] [IsDomain A]
    {μ y : A} (hμ : IsPrimitiveRoot μ 5) :
    ∏ j : Fin 5, (1 - μ ^ (j : ℕ) * y) = 1 - y ^ 5 := by
  have hsum : ∑ i ∈ Finset.range 5, μ ^ i = 0 :=
    hμ.geom_sum_eq_zero (by norm_num)
  have hpow : μ ^ 5 = 1 := hμ.pow_eq_one
  norm_num [Fin.prod_univ_five] at hsum ⊢
  have hsum' : 1 + μ + μ ^ 2 + μ ^ 3 + μ ^ 4 = 0 := by
    norm_num [Finset.sum_range_succ] at hsum ⊢
    simpa [add_assoc] using hsum
  have hμ4 : μ ^ 4 = -(1 + μ + μ ^ 2 + μ ^ 3) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_assoc, add_comm, add_left_comm] using hsum'
  have hμ6 : μ ^ 6 = μ := by
    calc
      μ ^ 6 = μ ^ 5 * μ := by ring
      _ = μ := by rw [hpow, one_mul]
  have hμ7 : μ ^ 7 = μ ^ 2 := by
    calc
      μ ^ 7 = μ ^ 5 * μ ^ 2 := by ring
      _ = μ ^ 2 := by rw [hpow, one_mul]
  have hμ8 : μ ^ 8 = μ ^ 3 := by
    calc
      μ ^ 8 = μ ^ 5 * μ ^ 3 := by ring
      _ = μ ^ 3 := by rw [hpow, one_mul]
  have hμ9 : μ ^ 9 = μ ^ 4 := by
    calc
      μ ^ 9 = μ ^ 5 * μ ^ 4 := by ring
      _ = μ ^ 4 := by rw [hpow, one_mul]
  rw [hμ4]
  ring_nf
  rw [hpow, hμ6, hμ7, hμ8, hμ9]
  rw [hμ4]
  ring_nf

/-- Power-series version of `prod_one_sub_primitive_fifth`, with the root of
unity embedded as a constant power series. -/
theorem prod_one_sub_primitive_fifth_powerSeries {R : Type*}
    [CommRing R] [IsDomain R] {μ : R} (Y : R⟦X⟧)
    (hμ : IsPrimitiveRoot μ 5) :
    ∏ j : Fin 5, (1 - PowerSeries.C (μ ^ (j : ℕ)) * Y) = 1 - Y ^ 5 := by
  have hCμ : IsPrimitiveRoot (PowerSeries.C μ : R⟦X⟧) 5 :=
    hμ.map_of_injective (PowerSeries.C_injective (R := R))
  simpa only [map_pow] using
    (prod_one_sub_primitive_fifth (A := R⟦X⟧) (μ := PowerSeries.C μ)
      (y := Y) hCμ)

/-- Homogeneous form of the primitive fifth-root factor collapse:
`∏ (a - μ^j b) = a^5 - b^5`.  This avoids introducing inverses and is the
algebraic shape needed for root-of-unity factorizations of product
differences. -/
theorem prod_sub_primitive_fifth {A : Type*} [CommRing A] [IsDomain A]
    {μ a b : A} (hμ : IsPrimitiveRoot μ 5) :
    ∏ j : Fin 5, (a - μ ^ (j : ℕ) * b) = a ^ 5 - b ^ 5 := by
  have hsum : ∑ i ∈ Finset.range 5, μ ^ i = 0 :=
    hμ.geom_sum_eq_zero (by norm_num)
  have hpow : μ ^ 5 = 1 := hμ.pow_eq_one
  norm_num [Fin.prod_univ_five] at hsum ⊢
  have hsum' : 1 + μ + μ ^ 2 + μ ^ 3 + μ ^ 4 = 0 := by
    norm_num [Finset.sum_range_succ] at hsum ⊢
    simpa [add_assoc] using hsum
  have hμ4 : μ ^ 4 = -(1 + μ + μ ^ 2 + μ ^ 3) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_assoc, add_comm, add_left_comm] using hsum'
  have hμ6 : μ ^ 6 = μ := by
    calc
      μ ^ 6 = μ ^ 5 * μ := by ring
      _ = μ := by rw [hpow, one_mul]
  have hμ7 : μ ^ 7 = μ ^ 2 := by
    calc
      μ ^ 7 = μ ^ 5 * μ ^ 2 := by ring
      _ = μ ^ 2 := by rw [hpow, one_mul]
  have hμ8 : μ ^ 8 = μ ^ 3 := by
    calc
      μ ^ 8 = μ ^ 5 * μ ^ 3 := by ring
      _ = μ ^ 3 := by rw [hpow, one_mul]
  have hμ9 : μ ^ 9 = μ ^ 4 := by
    calc
      μ ^ 9 = μ ^ 5 * μ ^ 4 := by ring
      _ = μ ^ 4 := by rw [hpow, one_mul]
  rw [hμ4]
  ring_nf
  rw [hpow, hμ6, hμ7, hμ8, hμ9]
  rw [hμ4]
  ring_nf

/-- Power-series homogeneous fifth-root factor collapse. -/
theorem prod_sub_primitive_fifth_powerSeries {R : Type*}
    [CommRing R] [IsDomain R] {μ : R} (A B : R⟦X⟧)
    (hμ : IsPrimitiveRoot μ 5) :
    ∏ j : Fin 5, (A - PowerSeries.C (μ ^ (j : ℕ)) * B) = A ^ 5 - B ^ 5 := by
  have hCμ : IsPrimitiveRoot (PowerSeries.C μ : R⟦X⟧) 5 :=
    hμ.map_of_injective (PowerSeries.C_injective (R := R))
  simpa only [map_pow] using
    (prod_sub_primitive_fifth (A := R⟦X⟧) (μ := PowerSeries.C μ)
      (a := A) (b := B) hCμ)

/-- One Euler factor collapsed after multiplying its five root-of-unity
rescalings.

If the exponent is divisible by `5`, all five root multipliers are `1`; if not,
`ζ^m` is again primitive and the factors collapse to `1 - X^(5m)`. -/
theorem prod_scaleX_one_sub_X_pow_fifth {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (m : ℕ) :
    ∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) ((1 : R⟦X⟧) - PowerSeries.X ^ m) =
      if 5 ∣ m then
        ((1 : R⟦X⟧) - PowerSeries.X ^ m) ^ 5
      else
        (1 : R⟦X⟧) - PowerSeries.X ^ (5 * m) := by
  have hfactor : ∀ j : Fin 5,
      scaleX (ζ ^ (j : ℕ)) ((1 : R⟦X⟧) - PowerSeries.X ^ m) =
        1 - PowerSeries.C ((ζ ^ m) ^ (j : ℕ)) * PowerSeries.X ^ m := by
    intro j
    rw [map_sub, map_one, scaleX_X_pow]
    congr 2
    exact congrArg PowerSeries.C (by rw [← pow_mul, ← pow_mul, mul_comm])
  by_cases hdiv : 5 ∣ m
  · rw [if_pos hdiv]
    obtain ⟨a, rfl⟩ := hdiv
    have hzeta : ζ ^ (5 * a) = 1 := by
      rw [pow_mul, hζ.pow_eq_one, one_pow]
    calc
      ∏ j : Fin 5, scaleX (ζ ^ (j : ℕ))
          ((1 : R⟦X⟧) - PowerSeries.X ^ (5 * a))
          = ∏ _j : Fin 5, ((1 : R⟦X⟧) - PowerSeries.X ^ (5 * a)) := by
            apply Finset.prod_congr rfl
            intro j _hj
            rw [hfactor, hzeta]
            simp
      _ = ((1 : R⟦X⟧) - PowerSeries.X ^ (5 * a)) ^ 5 := by
            simp
  · rw [if_neg hdiv]
    have hcop : m.Coprime 5 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).2 hdiv).symm
    have hζm : IsPrimitiveRoot (ζ ^ m) 5 :=
      hζ.pow_of_coprime m hcop
    calc
      ∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) ((1 : R⟦X⟧) - PowerSeries.X ^ m)
          = ∏ j : Fin 5,
              (1 - PowerSeries.C ((ζ ^ m) ^ (j : ℕ)) * PowerSeries.X ^ m) := by
            apply Finset.prod_congr rfl
            intro j _hj
            rw [hfactor]
      _ = (1 : R⟦X⟧) - (PowerSeries.X ^ m) ^ 5 := by
            simpa using
              (prod_one_sub_primitive_fifth_powerSeries
                (R := R) (μ := ζ ^ m) (Y := PowerSeries.X ^ m) hζm)
      _ = (1 : R⟦X⟧) - PowerSeries.X ^ (5 * m) := by
            rw [← pow_mul]
            congr 1
            ring

theorem prod_scaleX_oneSubXPow_fifth {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (k : ℕ) :
    ∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (oneSubXPow R k) =
      if 5 ∣ k + 1 then
        (oneSubXPow R k) ^ 5
      else
        (1 : R⟦X⟧) - PowerSeries.X ^ (5 * (k + 1)) := by
  simpa [oneSubXPow] using
    (prod_scaleX_one_sub_X_pow_fifth (R := R) hζ (k + 1))

/-- Finite q-Pochhammer version of the fifth-root product collapse.  This is a
finite approximation to the desired infinite product quotient; no convergence
or infinite-product interchange is asserted here. -/
theorem prod_scaleX_qPochFinitePS_fifth_collapse {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (N : ℕ) :
    ∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (qPochFinitePS R N) =
      ∏ k ∈ Finset.range N,
        if 5 ∣ k + 1 then
          (oneSubXPow R k) ^ 5
        else
          (1 : R⟦X⟧) - PowerSeries.X ^ (5 * (k + 1)) := by
  unfold qPochFinitePS
  calc
    ∏ j : Fin 5,
        scaleX (ζ ^ (j : ℕ)) (∏ k ∈ Finset.range N, oneSubXPow R k)
        = ∏ j : Fin 5, ∏ k ∈ Finset.range N,
            scaleX (ζ ^ (j : ℕ)) (oneSubXPow R k) := by
          apply Finset.prod_congr rfl
          intro j _hj
          rw [map_prod]
    _ = ∏ k ∈ Finset.range N, ∏ j : Fin 5,
            scaleX (ζ ^ (j : ℕ)) (oneSubXPow R k) := by
          rw [Finset.prod_comm]
    _ = ∏ k ∈ Finset.range N,
          if 5 ∣ k + 1 then
            (oneSubXPow R k) ^ 5
          else
            (1 : R⟦X⟧) - PowerSeries.X ^ (5 * (k + 1)) := by
          apply Finset.prod_congr rfl
          intro k _hk
          exact prod_scaleX_oneSubXPow_fifth (R := R) hζ k

/-! ## The concrete fifth cyclotomic field over `ℚ` -/

noncomputable abbrev QuinticCyclotomicField : Type :=
  CyclotomicField 5 ℚ

/-- A chosen primitive fifth root in `CyclotomicField 5 ℚ`. -/
noncomputable def quinticZeta : QuinticCyclotomicField :=
  IsCyclotomicExtension.zeta 5 ℚ QuinticCyclotomicField

@[simp] theorem quinticZeta_isPrimitiveRoot :
    IsPrimitiveRoot quinticZeta 5 := by
  exact IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)

/-- Concrete finite collapse over `CyclotomicField 5 ℚ`. -/
theorem quinticCyclotomic_qPochFinitePS_fifth_collapse (N : ℕ) :
    ∏ j : Fin 5,
        scaleX (quinticZeta ^ (j : ℕ))
          (qPochFinitePS QuinticCyclotomicField N) =
      ∏ k ∈ Finset.range N,
        if 5 ∣ k + 1 then
          (oneSubXPow QuinticCyclotomicField k) ^ 5
        else
          (1 : QuinticCyclotomicField⟦X⟧) -
            PowerSeries.X ^ (5 * (k + 1)) := by
  exact prod_scaleX_qPochFinitePS_fifth_collapse
    (R := QuinticCyclotomicField) quinticZeta_isPrimitiveRoot N

/-! ## Gaussian periods for primitive fifth roots -/

/-- The Gaussian period `ζ + ζ^4`. -/
noncomputable def quinticPeriodAlpha {R : Type*} [CommRing R] (ζ : R) : R :=
  ζ + ζ ^ 4

/-- The Gaussian period `ζ^2 + ζ^3`. -/
noncomputable def quinticPeriodBeta {R : Type*} [CommRing R] (ζ : R) : R :=
  ζ ^ 2 + ζ ^ 3

theorem quinticPeriod_sum {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    quinticPeriodAlpha ζ + quinticPeriodBeta ζ = -1 := by
  have hsum : ∑ i ∈ Finset.range 5, ζ ^ i = 0 :=
    hζ.geom_sum_eq_zero (by norm_num)
  norm_num [Finset.sum_range_succ] at hsum
  have hsum' : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    simpa [add_assoc] using hsum
  have hζ4 : ζ ^ 4 = -(1 + ζ + ζ ^ 2 + ζ ^ 3) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_assoc, add_comm, add_left_comm] using hsum'
  unfold quinticPeriodAlpha quinticPeriodBeta
  rw [hζ4]
  ring

theorem quinticPeriod_mul {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    quinticPeriodAlpha ζ * quinticPeriodBeta ζ = -1 := by
  have hsum : ∑ i ∈ Finset.range 5, ζ ^ i = 0 :=
    hζ.geom_sum_eq_zero (by norm_num)
  have hpow : ζ ^ 5 = 1 := hζ.pow_eq_one
  norm_num [Finset.sum_range_succ] at hsum
  have hsum' : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    simpa [add_assoc] using hsum
  have hζ4 : ζ ^ 4 = -(1 + ζ + ζ ^ 2 + ζ ^ 3) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_assoc, add_comm, add_left_comm] using hsum'
  have hζ6 : ζ ^ 6 = ζ := by
    calc
      ζ ^ 6 = ζ ^ 5 * ζ := by ring
      _ = ζ := by rw [hpow, one_mul]
  have hζ7 : ζ ^ 7 = ζ ^ 2 := by
    calc
      ζ ^ 7 = ζ ^ 5 * ζ ^ 2 := by ring
      _ = ζ ^ 2 := by rw [hpow, one_mul]
  unfold quinticPeriodAlpha quinticPeriodBeta
  calc
    (ζ + ζ ^ 4) * (ζ ^ 2 + ζ ^ 3)
        = ζ ^ 3 + ζ ^ 4 + ζ ^ 6 + ζ ^ 7 := by ring
    _ = ζ ^ 3 + ζ ^ 4 + ζ + ζ ^ 2 := by rw [hζ6, hζ7]
    _ = -1 := by
      rw [hζ4]
      ring

theorem quinticPeriodAlpha_sq {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (quinticPeriodAlpha ζ) ^ 2 = -quinticPeriodAlpha ζ + 1 := by
  let α : R := quinticPeriodAlpha ζ
  let β : R := quinticPeriodBeta ζ
  have hsum : α + β = -1 := by
    simpa [α, β] using quinticPeriod_sum (R := R) hζ
  have hprod : α * β = -1 := by
    simpa [α, β] using quinticPeriod_mul (R := R) hζ
  change α ^ 2 = -α + 1
  calc
    α ^ 2 = α ^ 2 + (α * β + 1) := by rw [hprod]; ring
    _ = α * (α + β) + 1 := by ring
    _ = α * (-1) + 1 := by rw [hsum]
    _ = -α + 1 := by ring

theorem quinticPeriodBeta_sq {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (quinticPeriodBeta ζ) ^ 2 = -quinticPeriodBeta ζ + 1 := by
  let α : R := quinticPeriodAlpha ζ
  let β : R := quinticPeriodBeta ζ
  have hsum : α + β = -1 := by
    simpa [α, β] using quinticPeriod_sum (R := R) hζ
  have hprod : α * β = -1 := by
    simpa [α, β, mul_comm] using quinticPeriod_mul (R := R) hζ
  change β ^ 2 = -β + 1
  calc
    β ^ 2 = β ^ 2 + (β * α + 1) := by
      rw [show β * α = α * β by ring, hprod]
      ring
    _ = β * (β + α) + 1 := by ring
    _ = β * (-1) + 1 := by rw [show β + α = -1 by simpa [add_comm] using hsum]
    _ = -β + 1 := by ring

theorem quinticPeriodAlpha_quadratic {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (quinticPeriodAlpha ζ) ^ 2 + quinticPeriodAlpha ζ - 1 = 0 := by
  rw [quinticPeriodAlpha_sq (R := R) hζ]
  ring

theorem quinticPeriodBeta_quadratic {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (quinticPeriodBeta ζ) ^ 2 + quinticPeriodBeta ζ - 1 = 0 := by
  rw [quinticPeriodBeta_sq (R := R) hζ]
  ring

theorem quinticPeriodAlpha_pow_five {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (quinticPeriodAlpha ζ) ^ 5 = 5 * quinticPeriodAlpha ζ - 3 := by
  let α : R := quinticPeriodAlpha ζ
  have hsq : α ^ 2 = -α + 1 := by
    simpa [α] using quinticPeriodAlpha_sq (R := R) hζ
  change α ^ 5 = 5 * α - 3
  calc
    α ^ 5 = α * (α ^ 2) ^ 2 := by ring
    _ = α * (-α + 1) ^ 2 := by rw [hsq]
    _ = α * (α ^ 2 - 2 * α + 1) := by ring
    _ = α * ((-α + 1) - 2 * α + 1) := by rw [hsq]
    _ = -3 * α ^ 2 + 2 * α := by ring
    _ = 5 * α - 3 := by rw [hsq]; ring

theorem quinticPeriodBeta_pow_five {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (quinticPeriodBeta ζ) ^ 5 = 5 * quinticPeriodBeta ζ - 3 := by
  let β : R := quinticPeriodBeta ζ
  have hsq : β ^ 2 = -β + 1 := by
    simpa [β] using quinticPeriodBeta_sq (R := R) hζ
  change β ^ 5 = 5 * β - 3
  calc
    β ^ 5 = β * (β ^ 2) ^ 2 := by ring
    _ = β * (-β + 1) ^ 2 := by rw [hsq]
    _ = β * (β ^ 2 - 2 * β + 1) := by ring
    _ = β * ((-β + 1) - 2 * β + 1) := by rw [hsq]
    _ = -3 * β ^ 2 + 2 * β := by ring
    _ = 5 * β - 3 := by rw [hsq]; ring

theorem quinticPeriod_pow_five_sum {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (quinticPeriodAlpha ζ) ^ 5 + (quinticPeriodBeta ζ) ^ 5 = -11 := by
  rw [quinticPeriodAlpha_pow_five (R := R) hζ,
    quinticPeriodBeta_pow_five (R := R) hζ]
  calc
    5 * quinticPeriodAlpha ζ - 3 + (5 * quinticPeriodBeta ζ - 3)
        = 5 * (quinticPeriodAlpha ζ + quinticPeriodBeta ζ) - 6 := by ring
    _ = -11 := by rw [quinticPeriod_sum (R := R) hζ]; ring

theorem quinticPeriod_pow_five_mul {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (quinticPeriodAlpha ζ) ^ 5 * (quinticPeriodBeta ζ) ^ 5 = -1 := by
  rw [quinticPeriodAlpha_pow_five (R := R) hζ,
    quinticPeriodBeta_pow_five (R := R) hζ]
  have hsum : quinticPeriodAlpha ζ + quinticPeriodBeta ζ = -1 :=
    quinticPeriod_sum (R := R) hζ
  have hprod : quinticPeriodAlpha ζ * quinticPeriodBeta ζ = -1 :=
    quinticPeriod_mul (R := R) hζ
  calc
    (5 * quinticPeriodAlpha ζ - 3) * (5 * quinticPeriodBeta ζ - 3)
        =
      25 * (quinticPeriodAlpha ζ * quinticPeriodBeta ζ) -
        15 * (quinticPeriodAlpha ζ + quinticPeriodBeta ζ) + 9 := by ring
    _ = -1 := by rw [hsum, hprod]; ring

theorem neg_quinticPeriod_pow_five_sum {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    -((quinticPeriodAlpha ζ) ^ 5) + -((quinticPeriodBeta ζ) ^ 5) = 11 := by
  calc
    -((quinticPeriodAlpha ζ) ^ 5) + -((quinticPeriodBeta ζ) ^ 5)
        = -((quinticPeriodAlpha ζ) ^ 5 + (quinticPeriodBeta ζ) ^ 5) := by ring
    _ = 11 := by rw [quinticPeriod_pow_five_sum (R := R) hζ]; ring

theorem neg_quinticPeriod_pow_five_mul {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    -((quinticPeriodAlpha ζ) ^ 5) * -((quinticPeriodBeta ζ) ^ 5) = -1 := by
  calc
    -((quinticPeriodAlpha ζ) ^ 5) * -((quinticPeriodBeta ζ) ^ 5)
        = (quinticPeriodAlpha ζ) ^ 5 * (quinticPeriodBeta ζ) ^ 5 := by ring
    _ = -1 := quinticPeriod_pow_five_mul (R := R) hζ

/-! ## Local quadratic factors behind the §8.6 product route -/

/-- The quadratic Euler factor `1 - γ X^m + X^(2m)`. -/
noncomputable def quinticQuadraticFactor {R : Type*} [CommRing R]
    (γ : R) (m : ℕ) : R⟦X⟧ :=
  (1 : R⟦X⟧) - PowerSeries.C γ * PowerSeries.X ^ m +
    PowerSeries.X ^ (2 * m)

theorem quintic_zeta_pow_five_mul_add {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n r : ℕ) :
    ζ ^ (5 * n + r) = ζ ^ r := by
  calc
    ζ ^ (5 * n + r) = ζ ^ (5 * n) * ζ ^ r := by rw [pow_add]
    _ = (ζ ^ 5) ^ n * ζ ^ r := by rw [pow_mul]
    _ = ζ ^ r := by rw [hζ.pow_eq_one, one_pow, one_mul]

theorem quinticPeriod_pair14_five_mul_add_one {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ζ ^ (5 * n + 1) + (ζ ^ 4) ^ (5 * n + 1) =
      quinticPeriodAlpha ζ := by
  rw [← pow_mul]
  rw [quintic_zeta_pow_five_mul_add (R := R) hζ n 1]
  have h : 4 * (5 * n + 1) = 5 * (4 * n) + 4 := by ring
  rw [h, quintic_zeta_pow_five_mul_add (R := R) hζ (4 * n) 4]
  simp [quinticPeriodAlpha]

theorem quinticPeriod_pair14_five_mul_add_two {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ζ ^ (5 * n + 2) + (ζ ^ 4) ^ (5 * n + 2) =
      quinticPeriodBeta ζ := by
  rw [← pow_mul]
  rw [quintic_zeta_pow_five_mul_add (R := R) hζ n 2]
  have h : 4 * (5 * n + 2) = 5 * (4 * n + 1) + 3 := by ring
  rw [h, quintic_zeta_pow_five_mul_add (R := R) hζ (4 * n + 1) 3]
  simp [quinticPeriodBeta]

theorem quinticPeriod_pair14_five_mul_add_three {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ζ ^ (5 * n + 3) + (ζ ^ 4) ^ (5 * n + 3) =
      quinticPeriodBeta ζ := by
  rw [← pow_mul]
  rw [quintic_zeta_pow_five_mul_add (R := R) hζ n 3]
  have h : 4 * (5 * n + 3) = 5 * (4 * n + 2) + 2 := by ring
  rw [h, quintic_zeta_pow_five_mul_add (R := R) hζ (4 * n + 2) 2]
  simp [quinticPeriodBeta, add_comm]

theorem quinticPeriod_pair14_five_mul_add_four {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ζ ^ (5 * n + 4) + (ζ ^ 4) ^ (5 * n + 4) =
      quinticPeriodAlpha ζ := by
  rw [← pow_mul]
  rw [quintic_zeta_pow_five_mul_add (R := R) hζ n 4]
  have h : 4 * (5 * n + 4) = 5 * (4 * n + 3) + 1 := by ring
  rw [h, quintic_zeta_pow_five_mul_add (R := R) hζ (4 * n + 3) 1]
  simp [quinticPeriodAlpha, add_comm]

theorem scaleX_period_pair14_one_sub_X_pow {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (m : ℕ) :
    scaleX ζ ((1 : R⟦X⟧) - PowerSeries.X ^ m) *
        scaleX (ζ ^ 4) ((1 : R⟦X⟧) - PowerSeries.X ^ m) =
      quinticQuadraticFactor (ζ ^ m + (ζ ^ 4) ^ m) m := by
  have hprod : ζ ^ m * (ζ ^ 4) ^ m = 1 := by
    calc
      ζ ^ m * (ζ ^ 4) ^ m = ζ ^ m * ζ ^ (4 * m) := by rw [pow_mul]
      _ = ζ ^ (m + 4 * m) := by rw [← pow_add]
      _ = ζ ^ (5 * m) := by
        congr 1
        ring
      _ = (ζ ^ 5) ^ m := by rw [pow_mul]
      _ = 1 := by rw [hζ.pow_eq_one, one_pow]
  have hprodC :
      PowerSeries.C (ζ ^ m) * PowerSeries.C ((ζ ^ 4) ^ m) =
        (1 : R⟦X⟧) := by
    rw [← map_mul, hprod, map_one]
  rw [map_sub, map_one, scaleX_X_pow, map_sub, map_one, scaleX_X_pow]
  unfold quinticQuadraticFactor
  calc
    (1 - PowerSeries.C (ζ ^ m) * PowerSeries.X ^ m) *
        (1 - PowerSeries.C ((ζ ^ 4) ^ m) * PowerSeries.X ^ m)
        =
      1 - (PowerSeries.C (ζ ^ m) + PowerSeries.C ((ζ ^ 4) ^ m)) *
          PowerSeries.X ^ m +
        (PowerSeries.C (ζ ^ m) * PowerSeries.C ((ζ ^ 4) ^ m)) *
          PowerSeries.X ^ (2 * m) := by
          ring
    _ =
      1 - PowerSeries.C (ζ ^ m + (ζ ^ 4) ^ m) * PowerSeries.X ^ m +
        PowerSeries.X ^ (2 * m) := by
          rw [← map_add, hprodC]
          ring

theorem scaleX_period_pair23_one_sub_X_pow {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (m : ℕ) :
    scaleX (ζ ^ 2) ((1 : R⟦X⟧) - PowerSeries.X ^ m) *
        scaleX (ζ ^ 3) ((1 : R⟦X⟧) - PowerSeries.X ^ m) =
      quinticQuadraticFactor ((ζ ^ 2) ^ m + (ζ ^ 3) ^ m) m := by
  have hprod : (ζ ^ 2) ^ m * (ζ ^ 3) ^ m = 1 := by
    calc
      (ζ ^ 2) ^ m * (ζ ^ 3) ^ m = ζ ^ (2 * m) * ζ ^ (3 * m) := by
        rw [pow_mul, pow_mul]
      _ = ζ ^ (2 * m + 3 * m) := by rw [← pow_add]
      _ = ζ ^ (5 * m) := by
        congr 1
        ring
      _ = (ζ ^ 5) ^ m := by rw [pow_mul]
      _ = 1 := by rw [hζ.pow_eq_one, one_pow]
  have hprodC :
      PowerSeries.C ((ζ ^ 2) ^ m) * PowerSeries.C ((ζ ^ 3) ^ m) =
        (1 : R⟦X⟧) := by
    rw [← map_mul, hprod, map_one]
  rw [map_sub, map_one, scaleX_X_pow, map_sub, map_one, scaleX_X_pow]
  unfold quinticQuadraticFactor
  calc
    (1 - PowerSeries.C ((ζ ^ 2) ^ m) * PowerSeries.X ^ m) *
        (1 - PowerSeries.C ((ζ ^ 3) ^ m) * PowerSeries.X ^ m)
        =
      1 - (PowerSeries.C ((ζ ^ 2) ^ m) + PowerSeries.C ((ζ ^ 3) ^ m)) *
          PowerSeries.X ^ m +
        (PowerSeries.C ((ζ ^ 2) ^ m) * PowerSeries.C ((ζ ^ 3) ^ m)) *
          PowerSeries.X ^ (2 * m) := by
          ring
    _ =
      1 - PowerSeries.C ((ζ ^ 2) ^ m + (ζ ^ 3) ^ m) *
          PowerSeries.X ^ m +
        PowerSeries.X ^ (2 * m) := by
          rw [← map_add, hprodC]
          ring

/-- Local residue-`1` quadratic factor for the `(ζ,ζ^4)` pair. -/
theorem section86_pair14_residue_one_local_factor {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    scaleX ζ (oneSubXPow R (5 * n)) *
        scaleX (ζ ^ 4) (oneSubXPow R (5 * n)) =
      quinticQuadraticFactor (quinticPeriodAlpha ζ) (5 * n + 1) := by
  calc
    scaleX ζ (oneSubXPow R (5 * n)) *
        scaleX (ζ ^ 4) (oneSubXPow R (5 * n))
        =
      quinticQuadraticFactor
        (ζ ^ (5 * n + 1) + (ζ ^ 4) ^ (5 * n + 1)) (5 * n + 1) := by
        simpa [oneSubXPow] using
          scaleX_period_pair14_one_sub_X_pow (R := R) hζ (5 * n + 1)
    _ = quinticQuadraticFactor (quinticPeriodAlpha ζ) (5 * n + 1) := by
        rw [quinticPeriod_pair14_five_mul_add_one (R := R) hζ n]

/-- Local residue-`2` quadratic factor for the `(ζ,ζ^4)` pair. -/
theorem section86_pair14_residue_two_local_factor {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    scaleX ζ (oneSubXPow R (5 * n + 1)) *
        scaleX (ζ ^ 4) (oneSubXPow R (5 * n + 1)) =
      quinticQuadraticFactor (quinticPeriodBeta ζ) (5 * n + 2) := by
  calc
    scaleX ζ (oneSubXPow R (5 * n + 1)) *
        scaleX (ζ ^ 4) (oneSubXPow R (5 * n + 1))
        =
      quinticQuadraticFactor
        (ζ ^ (5 * n + 2) + (ζ ^ 4) ^ (5 * n + 2)) (5 * n + 2) := by
        simpa [oneSubXPow] using
          scaleX_period_pair14_one_sub_X_pow (R := R) hζ (5 * n + 2)
    _ = quinticQuadraticFactor (quinticPeriodBeta ζ) (5 * n + 2) := by
        rw [quinticPeriod_pair14_five_mul_add_two (R := R) hζ n]

/-- Local residue-`3` quadratic factor for the `(ζ,ζ^4)` pair. -/
theorem section86_pair14_residue_three_local_factor {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    scaleX ζ (oneSubXPow R (5 * n + 2)) *
        scaleX (ζ ^ 4) (oneSubXPow R (5 * n + 2)) =
      quinticQuadraticFactor (quinticPeriodBeta ζ) (5 * n + 3) := by
  calc
    scaleX ζ (oneSubXPow R (5 * n + 2)) *
        scaleX (ζ ^ 4) (oneSubXPow R (5 * n + 2))
        =
      quinticQuadraticFactor
        (ζ ^ (5 * n + 3) + (ζ ^ 4) ^ (5 * n + 3)) (5 * n + 3) := by
        simpa [oneSubXPow] using
          scaleX_period_pair14_one_sub_X_pow (R := R) hζ (5 * n + 3)
    _ = quinticQuadraticFactor (quinticPeriodBeta ζ) (5 * n + 3) := by
        rw [quinticPeriod_pair14_five_mul_add_three (R := R) hζ n]

/-- Local residue-`4` quadratic factor for the `(ζ,ζ^4)` pair. -/
theorem section86_pair14_residue_four_local_factor {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    scaleX ζ (oneSubXPow R (5 * n + 3)) *
        scaleX (ζ ^ 4) (oneSubXPow R (5 * n + 3)) =
      quinticQuadraticFactor (quinticPeriodAlpha ζ) (5 * n + 4) := by
  calc
    scaleX ζ (oneSubXPow R (5 * n + 3)) *
        scaleX (ζ ^ 4) (oneSubXPow R (5 * n + 3))
        =
      quinticQuadraticFactor
        (ζ ^ (5 * n + 4) + (ζ ^ 4) ^ (5 * n + 4)) (5 * n + 4) := by
        simpa [oneSubXPow] using
          scaleX_period_pair14_one_sub_X_pow (R := R) hζ (5 * n + 4)
    _ = quinticQuadraticFactor (quinticPeriodAlpha ζ) (5 * n + 4) := by
        rw [quinticPeriod_pair14_five_mul_add_four (R := R) hζ n]

theorem scaleX_period_pair14_qPochFinitePS {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (N : ℕ) :
    scaleX ζ (qPochFinitePS R N) *
        scaleX (ζ ^ 4) (qPochFinitePS R N) =
      ∏ k ∈ Finset.range N,
        quinticQuadraticFactor (ζ ^ (k + 1) + (ζ ^ 4) ^ (k + 1)) (k + 1) := by
  unfold qPochFinitePS
  rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _hk
  simpa [oneSubXPow] using
    scaleX_period_pair14_one_sub_X_pow (R := R) hζ (k + 1)

theorem scaleX_period_pair23_qPochFinitePS {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (N : ℕ) :
    scaleX (ζ ^ 2) (qPochFinitePS R N) *
        scaleX (ζ ^ 3) (qPochFinitePS R N) =
      ∏ k ∈ Finset.range N,
        quinticQuadraticFactor ((ζ ^ 2) ^ (k + 1) + (ζ ^ 3) ^ (k + 1)) (k + 1) := by
  unfold qPochFinitePS
  rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _hk
  simpa [oneSubXPow] using
    scaleX_period_pair23_one_sub_X_pow (R := R) hζ (k + 1)

/-! ## Algebraic §8.5 factor-pair reduction -/

/-- The compressed quintic core written with arbitrary `H,G`.  This is only
an algebraic expression; it does not assert Hirschhorn's product identity. -/
noncomputable def quinticProductCore (R : Type*) [CommRing R] (H G : R⟦X⟧) : R⟦X⟧ :=
  G ^ 10 - (11 : R⟦X⟧) * PowerSeries.X * H ^ 5 * G ^ 5 -
    PowerSeries.X ^ 2 * H ^ 10

/-- If two scalars have symmetric functions `α + β = 11` and `αβ = -1`,
then the two Hirschhorn §8.5 factors multiply to the rational quintic core.
This is the algebraic descent step; the existence of such factors is not
asserted here. -/
theorem quintic_factor_pair_mul_eq_core {R : Type*} [CommRing R]
    (α β : R) (H G : R⟦X⟧)
    (hsum : α + β = (11 : R)) (hprod : α * β = (-1 : R)) :
    (G ^ 5 - PowerSeries.C β * PowerSeries.X * H ^ 5) *
        (G ^ 5 - PowerSeries.C α * PowerSeries.X * H ^ 5) =
      quinticProductCore R H G := by
  have hsumC :
      PowerSeries.C α + PowerSeries.C β = (11 : R⟦X⟧) := by
    rw [← map_add, hsum]
    exact (map_natCast (PowerSeries.C : R →+* R⟦X⟧) 11).symm
  have hprodC :
      PowerSeries.C α * PowerSeries.C β = (-1 : R⟦X⟧) := by
    rw [← map_mul, hprod, map_neg, map_one]
  unfold quinticProductCore
  calc
    (G ^ 5 - PowerSeries.C β * PowerSeries.X * H ^ 5) *
        (G ^ 5 - PowerSeries.C α * PowerSeries.X * H ^ 5)
        =
      G ^ 10 -
        (PowerSeries.C α + PowerSeries.C β) * PowerSeries.X * H ^ 5 * G ^ 5 +
        (PowerSeries.C α * PowerSeries.C β) * PowerSeries.X ^ 2 * H ^ 10 := by
          ring
    _ =
      G ^ 10 - (11 : R⟦X⟧) * PowerSeries.X * H ^ 5 * G ^ 5 -
        PowerSeries.X ^ 2 * H ^ 10 := by
          rw [hsumC, hprodC]
          ring

/-- The §8.5 symmetric core factorization with the Gaussian-period convention
coming from `α = ζ + ζ^4`, `β = ζ^2 + ζ^3`.  For this convention
`α^5 + β^5 = -11`, so the core uses the pair `-α^5, -β^5`. -/
theorem quintic_factor_pair_mul_eq_core_of_gaussian_periods {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (H G : R⟦X⟧) :
    (G ^ 5 - PowerSeries.C (-((quinticPeriodBeta ζ) ^ 5)) *
          PowerSeries.X * H ^ 5) *
        (G ^ 5 - PowerSeries.C (-((quinticPeriodAlpha ζ) ^ 5)) *
          PowerSeries.X * H ^ 5) =
      quinticProductCore R H G := by
  exact
    quintic_factor_pair_mul_eq_core (R := R)
      (-((quinticPeriodAlpha ζ) ^ 5)) (-((quinticPeriodBeta ζ) ^ 5)) H G
      (neg_quinticPeriod_pow_five_sum (R := R) hζ)
      (neg_quinticPeriod_pow_five_mul (R := R) hζ)

/-- The same symmetric factorization specialized to the theta-series core
used by `Ch16MBIProof`. -/
theorem ramanujanMod5ProductCoreThetaRat_eq_factor_pair
    (α β : ℚ) (hsum : α + β = (11 : ℚ)) (hprod : α * β = (-1 : ℚ)) :
    ((QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal023SeriesPS ℚ) ^ 5 -
        PowerSeries.C β * PowerSeries.X *
          (QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014SeriesPS ℚ) ^ 5) *
      ((QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal023SeriesPS ℚ) ^ 5 -
        PowerSeries.C α * PowerSeries.X *
          (QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014SeriesPS ℚ) ^ 5) =
        QseriesFormalization.Pending.Ch16MBIProof.ramanujanMod5ProductCoreThetaRat := by
  simpa [quinticProductCore,
    QseriesFormalization.Pending.Ch16MBIProof.ramanujanMod5ProductCoreThetaRat,
    mul_assoc] using
    (quintic_factor_pair_mul_eq_core (R := ℚ) α β
      (QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014SeriesPS ℚ)
      (QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal023SeriesPS ℚ)
      hsum hprod)

/-- Conditional bridge from the two-factor Hirschhorn §8.5 product to the
clean quintic identity expected by the existing MBI wrapper. -/
theorem clean_quintic_of_factor_pair_product
    (α β : ℚ) (hsum : α + β = (11 : ℚ)) (hprod : α * β = (-1 : ℚ))
    (hfactor :
      (((QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal023SeriesPS ℚ) ^ 5 -
          PowerSeries.C β * PowerSeries.X *
            (QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014SeriesPS ℚ) ^ 5) *
        ((QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal023SeriesPS ℚ) ^ 5 -
          PowerSeries.C α * PowerSeries.X *
            (QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014SeriesPS ℚ) ^ 5)) *
          PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) =
        (qPochInfPS ℚ) ^ 11) :
      QseriesFormalization.Pending.Ch16MBIProof.ramanujanMod5ProductCoreThetaRat *
          PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) =
        (qPochInfPS ℚ) ^ 11 := by
  rw [← ramanujanMod5ProductCoreThetaRat_eq_factor_pair α β hsum hprod]
  exact hfactor

/-- Conditional final assembly: the compressed `E₀` bridge plus the §8.5
two-factor product identity imply the formal Most Beautiful Identity through
the already-proved `Ch16MBIProof` wrappers. -/
theorem most_beautiful_identity_of_compressed_E5_zero_bridge_and_factor_pair_product
    (α β : ℚ) (hsum : α + β = (11 : ℚ)) (hprod : α * β = (-1 : ℚ))
    (hE0 :
      QseriesFormalization.Pending.Ch16MBIProof.compressedSection5 ℚ 0 (qPochInfPS ℚ) *
          QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014SeriesPS ℚ =
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) *
          QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal023SeriesPS ℚ)
    (hfactor :
      (((QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal023SeriesPS ℚ) ^ 5 -
          PowerSeries.C β * PowerSeries.X *
            (QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014SeriesPS ℚ) ^ 5) *
        ((QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal023SeriesPS ℚ) ^ 5 -
          PowerSeries.C α * PowerSeries.X *
            (QseriesFormalization.Pending.JTPFormalPSPentagonal.pentagonal014SeriesPS ℚ) ^ 5)) *
          PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) =
        (qPochInfPS ℚ) ^ 11) :
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4)) : ℚ⟦X⟧)
      =
    5 •
      ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)) ^ 5 *
        (partitionGenFun ℚ) ^ 6) := by
  exact
    QseriesFormalization.Pending.Ch16MBIProof.most_beautiful_identity_of_compressed_theta_clean_quintic
      hE0 (clean_quintic_of_factor_pair_product α β hsum hprod hfactor)

end RamanujanQuintic
end Pending
end QseriesFormalization
