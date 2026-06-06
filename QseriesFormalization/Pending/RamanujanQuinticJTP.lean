import QseriesFormalization.Pending.RamanujanQuintic
import QseriesFormalization.Pending.JTP_FormalPS_Pentagonal
import QseriesFormalization.Pending.Chapter16_MBI_Proof
import QseriesFormalization.Chapter02
import QseriesFormalization.Chapter03

/-!
# Ramanujan quintic: JTP-at-a-fifth-root scaffolding

This file keeps the `a = eta` bookkeeping for Hirschhorn §8.3 separate from
the older finite product/cyclotomic infrastructure in `RamanujanQuintic`.

The main convention issue is that `RamanujanQuintic.quinticPeriodAlpha/Beta`
are the Gaussian periods

* `ζ + ζ^4`, `ζ^2 + ζ^3`, with sum `-1`;

whereas Hirschhorn §8.3 writes the golden-ratio pair with sum `1`.  The
definitions below expose the book's pair as the negatives of the appropriate
Gaussian periods.
-/

namespace QseriesFormalization
namespace Pending
namespace RamanujanQuinticJTP

open Finset
open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.Ch16MBIProof

/-! ## The §8.3 period convention -/

/-- Hirschhorn's `α = (1 + sqrt 5) / 2`, represented from a primitive fifth
root by `-(ζ^2 + ζ^3)`. -/
noncomputable def bookAlpha {R : Type*} [CommRing R] (ζ : R) : R :=
  -quinticPeriodBeta ζ

/-- Hirschhorn's `β = (1 - sqrt 5) / 2`, represented from a primitive fifth
root by `-(ζ + ζ^4)`. -/
noncomputable def bookBeta {R : Type*} [CommRing R] (ζ : R) : R :=
  -quinticPeriodAlpha ζ

theorem bookPeriod_sum {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    bookAlpha ζ + bookBeta ζ = (1 : R) := by
  unfold bookAlpha bookBeta
  have h := quinticPeriod_sum (R := R) hζ
  linear_combination -h

theorem bookPeriod_mul {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    bookAlpha ζ * bookBeta ζ = (-1 : R) := by
  unfold bookAlpha bookBeta
  simpa [mul_comm] using quinticPeriod_mul (R := R) hζ

theorem bookAlpha_sq {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (bookAlpha ζ) ^ 2 = bookAlpha ζ + 1 := by
  unfold bookAlpha
  rw [neg_sq, quinticPeriodBeta_sq (R := R) hζ]

theorem bookBeta_sq {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (bookBeta ζ) ^ 2 = bookBeta ζ + 1 := by
  unfold bookBeta
  rw [neg_sq, quinticPeriodAlpha_sq (R := R) hζ]

theorem bookAlpha_pow_five {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (bookAlpha ζ) ^ 5 = 5 * bookAlpha ζ + 3 := by
  unfold bookAlpha
  rw [neg_pow]
  norm_num
  rw [quinticPeriodBeta_pow_five (R := R) hζ]
  ring

theorem bookBeta_pow_five {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (bookBeta ζ) ^ 5 = 5 * bookBeta ζ + 3 := by
  unfold bookBeta
  rw [neg_pow]
  norm_num
  rw [quinticPeriodAlpha_pow_five (R := R) hζ]
  ring

theorem bookPeriod_pow_five_sum {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (bookAlpha ζ) ^ 5 + (bookBeta ζ) ^ 5 = (11 : R) := by
  rw [bookAlpha_pow_five (R := R) hζ, bookBeta_pow_five (R := R) hζ]
  calc
    5 * bookAlpha ζ + 3 + (5 * bookBeta ζ + 3)
        = 5 * (bookAlpha ζ + bookBeta ζ) + 6 := by ring
    _ = (11 : R) := by rw [bookPeriod_sum (R := R) hζ]; ring

theorem bookPeriod_pow_five_mul {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (bookAlpha ζ) ^ 5 * (bookBeta ζ) ^ 5 = (-1 : R) := by
  rw [bookAlpha_pow_five (R := R) hζ, bookBeta_pow_five (R := R) hζ]
  have hsum := bookPeriod_sum (R := R) hζ
  have hprod := bookPeriod_mul (R := R) hζ
  calc
    (5 * bookAlpha ζ + 3) * (5 * bookBeta ζ + 3)
        =
      25 * (bookAlpha ζ * bookBeta ζ) +
        15 * (bookAlpha ζ + bookBeta ζ) + 9 := by ring
    _ = (-1 : R) := by rw [hsum, hprod]; ring

theorem bookAlpha_quadratic {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (bookAlpha ζ) ^ 2 - bookAlpha ζ - 1 = 0 := by
  rw [bookAlpha_sq (R := R) hζ]
  ring

theorem bookBeta_quadratic {R : Type*} [CommRing R] [IsDomain R]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 5) :
    (bookBeta ζ) ^ 2 - bookBeta ζ - 1 = 0 := by
  rw [bookBeta_sq (R := R) hζ]
  ring

/-! ## Local factors for the `a = η²` specialization -/

theorem quinticPeriod_pair14_five_mul_add_zero {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    ζ ^ (5 * n) + (ζ ^ 4) ^ (5 * n) = (2 : R) := by
  have hz0 : ζ ^ (5 * n) = (1 : R) := by
    calc
      ζ ^ (5 * n) = ζ ^ (5 * n + 0) := by rfl
      _ = ζ ^ 0 := by rw [quintic_zeta_pow_five_mul_add (R := R) hζ n 0]
      _ = 1 := by simp
  have hz4 : (ζ ^ 4) ^ (5 * n) = (1 : R) := by
    calc
      (ζ ^ 4) ^ (5 * n) = ζ ^ (4 * (5 * n)) := by
        exact (pow_mul ζ 4 (5 * n)).symm
      _ = ζ ^ (5 * (4 * n) + 0) := by congr 1; ring
      _ = ζ ^ 0 := by
        rw [quintic_zeta_pow_five_mul_add (R := R) hζ (4 * n) 0]
      _ = 1 := by simp
  rw [hz0, hz4]
  ring

theorem quinticPeriod_pair23_five_mul_add_zero {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    (ζ ^ 2) ^ (5 * n) + (ζ ^ 3) ^ (5 * n) = (2 : R) := by
  rw [show (ζ ^ 2) ^ (5 * n) = ζ ^ (2 * (5 * n)) by
    exact (pow_mul ζ 2 (5 * n)).symm]
  rw [show (ζ ^ 3) ^ (5 * n) = ζ ^ (3 * (5 * n)) by
    exact (pow_mul ζ 3 (5 * n)).symm]
  have h2 : 2 * (5 * n) = 5 * (2 * n) + 0 := by ring
  have h3 : 3 * (5 * n) = 5 * (3 * n) + 0 := by ring
  rw [h2, h3]
  rw [quintic_zeta_pow_five_mul_add (R := R) hζ (2 * n) 0,
    quintic_zeta_pow_five_mul_add (R := R) hζ (3 * n) 0]
  ring

theorem quinticPeriod_pair23_five_mul_add_one {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    (ζ ^ 2) ^ (5 * n + 1) + (ζ ^ 3) ^ (5 * n + 1) =
      quinticPeriodBeta ζ := by
  rw [show (ζ ^ 2) ^ (5 * n + 1) = ζ ^ (2 * (5 * n + 1)) by
    exact (pow_mul ζ 2 (5 * n + 1)).symm]
  rw [show (ζ ^ 3) ^ (5 * n + 1) = ζ ^ (3 * (5 * n + 1)) by
    exact (pow_mul ζ 3 (5 * n + 1)).symm]
  have h2 : 2 * (5 * n + 1) = 5 * (2 * n) + 2 := by ring
  have h3 : 3 * (5 * n + 1) = 5 * (3 * n) + 3 := by ring
  rw [h2, h3]
  rw [quintic_zeta_pow_five_mul_add (R := R) hζ (2 * n) 2,
    quintic_zeta_pow_five_mul_add (R := R) hζ (3 * n) 3]
  simp [quinticPeriodBeta]

theorem quinticPeriod_pair23_five_mul_add_two {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    (ζ ^ 2) ^ (5 * n + 2) + (ζ ^ 3) ^ (5 * n + 2) =
      quinticPeriodAlpha ζ := by
  rw [show (ζ ^ 2) ^ (5 * n + 2) = ζ ^ (2 * (5 * n + 2)) by
    exact (pow_mul ζ 2 (5 * n + 2)).symm]
  rw [show (ζ ^ 3) ^ (5 * n + 2) = ζ ^ (3 * (5 * n + 2)) by
    exact (pow_mul ζ 3 (5 * n + 2)).symm]
  have h2 : 2 * (5 * n + 2) = 5 * (2 * n) + 4 := by ring
  have h3 : 3 * (5 * n + 2) = 5 * (3 * n + 1) + 1 := by ring
  rw [h2, h3]
  rw [quintic_zeta_pow_five_mul_add (R := R) hζ (2 * n) 4,
    quintic_zeta_pow_five_mul_add (R := R) hζ (3 * n + 1) 1]
  simp [quinticPeriodAlpha, add_comm]

theorem quinticPeriod_pair23_five_mul_add_three {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    (ζ ^ 2) ^ (5 * n + 3) + (ζ ^ 3) ^ (5 * n + 3) =
      quinticPeriodAlpha ζ := by
  rw [show (ζ ^ 2) ^ (5 * n + 3) = ζ ^ (2 * (5 * n + 3)) by
    exact (pow_mul ζ 2 (5 * n + 3)).symm]
  rw [show (ζ ^ 3) ^ (5 * n + 3) = ζ ^ (3 * (5 * n + 3)) by
    exact (pow_mul ζ 3 (5 * n + 3)).symm]
  have h2 : 2 * (5 * n + 3) = 5 * (2 * n + 1) + 1 := by ring
  have h3 : 3 * (5 * n + 3) = 5 * (3 * n + 1) + 4 := by ring
  rw [h2, h3]
  rw [quintic_zeta_pow_five_mul_add (R := R) hζ (2 * n + 1) 1,
    quintic_zeta_pow_five_mul_add (R := R) hζ (3 * n + 1) 4]
  simp [quinticPeriodAlpha]

theorem quinticPeriod_pair23_five_mul_add_four {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    (ζ ^ 2) ^ (5 * n + 4) + (ζ ^ 3) ^ (5 * n + 4) =
      quinticPeriodBeta ζ := by
  rw [show (ζ ^ 2) ^ (5 * n + 4) = ζ ^ (2 * (5 * n + 4)) by
    exact (pow_mul ζ 2 (5 * n + 4)).symm]
  rw [show (ζ ^ 3) ^ (5 * n + 4) = ζ ^ (3 * (5 * n + 4)) by
    exact (pow_mul ζ 3 (5 * n + 4)).symm]
  have h2 : 2 * (5 * n + 4) = 5 * (2 * n + 1) + 3 := by ring
  have h3 : 3 * (5 * n + 4) = 5 * (3 * n + 2) + 2 := by ring
  rw [h2, h3]
  rw [quintic_zeta_pow_five_mul_add (R := R) hζ (2 * n + 1) 3,
    quintic_zeta_pow_five_mul_add (R := R) hζ (3 * n + 2) 2]
  simp [quinticPeriodBeta, add_comm]

/-- Local residue-`1` quadratic factor for the `(ζ²,ζ³)` pair. -/
theorem section83_pair23_residue_one_local_factor {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    scaleX (ζ ^ 2) (oneSubXPow R (5 * n)) *
        scaleX (ζ ^ 3) (oneSubXPow R (5 * n)) =
      quinticQuadraticFactor (quinticPeriodBeta ζ) (5 * n + 1) := by
  calc
    scaleX (ζ ^ 2) (oneSubXPow R (5 * n)) *
        scaleX (ζ ^ 3) (oneSubXPow R (5 * n))
        =
      quinticQuadraticFactor
        ((ζ ^ 2) ^ (5 * n + 1) + (ζ ^ 3) ^ (5 * n + 1)) (5 * n + 1) := by
        simpa [oneSubXPow] using
          scaleX_period_pair23_one_sub_X_pow (R := R) hζ (5 * n + 1)
    _ = quinticQuadraticFactor (quinticPeriodBeta ζ) (5 * n + 1) := by
        rw [quinticPeriod_pair23_five_mul_add_one (R := R) hζ n]

/-- Local residue-`2` quadratic factor for the `(ζ²,ζ³)` pair. -/
theorem section83_pair23_residue_two_local_factor {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    scaleX (ζ ^ 2) (oneSubXPow R (5 * n + 1)) *
        scaleX (ζ ^ 3) (oneSubXPow R (5 * n + 1)) =
      quinticQuadraticFactor (quinticPeriodAlpha ζ) (5 * n + 2) := by
  calc
    scaleX (ζ ^ 2) (oneSubXPow R (5 * n + 1)) *
        scaleX (ζ ^ 3) (oneSubXPow R (5 * n + 1))
        =
      quinticQuadraticFactor
        ((ζ ^ 2) ^ (5 * n + 2) + (ζ ^ 3) ^ (5 * n + 2)) (5 * n + 2) := by
        simpa [oneSubXPow] using
          scaleX_period_pair23_one_sub_X_pow (R := R) hζ (5 * n + 2)
    _ = quinticQuadraticFactor (quinticPeriodAlpha ζ) (5 * n + 2) := by
        rw [quinticPeriod_pair23_five_mul_add_two (R := R) hζ n]

/-- Local residue-`3` quadratic factor for the `(ζ²,ζ³)` pair. -/
theorem section83_pair23_residue_three_local_factor {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    scaleX (ζ ^ 2) (oneSubXPow R (5 * n + 2)) *
        scaleX (ζ ^ 3) (oneSubXPow R (5 * n + 2)) =
      quinticQuadraticFactor (quinticPeriodAlpha ζ) (5 * n + 3) := by
  calc
    scaleX (ζ ^ 2) (oneSubXPow R (5 * n + 2)) *
        scaleX (ζ ^ 3) (oneSubXPow R (5 * n + 2))
        =
      quinticQuadraticFactor
        ((ζ ^ 2) ^ (5 * n + 3) + (ζ ^ 3) ^ (5 * n + 3)) (5 * n + 3) := by
        simpa [oneSubXPow] using
          scaleX_period_pair23_one_sub_X_pow (R := R) hζ (5 * n + 3)
    _ = quinticQuadraticFactor (quinticPeriodAlpha ζ) (5 * n + 3) := by
        rw [quinticPeriod_pair23_five_mul_add_three (R := R) hζ n]

/-- Local residue-`4` quadratic factor for the `(ζ²,ζ³)` pair. -/
theorem section83_pair23_residue_four_local_factor {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    scaleX (ζ ^ 2) (oneSubXPow R (5 * n + 3)) *
        scaleX (ζ ^ 3) (oneSubXPow R (5 * n + 3)) =
      quinticQuadraticFactor (quinticPeriodBeta ζ) (5 * n + 4) := by
  calc
    scaleX (ζ ^ 2) (oneSubXPow R (5 * n + 3)) *
        scaleX (ζ ^ 3) (oneSubXPow R (5 * n + 3))
        =
      quinticQuadraticFactor
        ((ζ ^ 2) ^ (5 * n + 4) + (ζ ^ 3) ^ (5 * n + 4)) (5 * n + 4) := by
        simpa [oneSubXPow] using
          scaleX_period_pair23_one_sub_X_pow (R := R) hζ (5 * n + 4)
    _ = quinticQuadraticFactor (quinticPeriodBeta ζ) (5 * n + 4) := by
        rw [quinticPeriod_pair23_five_mul_add_four (R := R) hζ n]

/-! ## Book-period form of the §8.3 quadratic factors -/

theorem quadraticFactor_pair14_eq_bookBeta {R : Type*} [CommRing R]
    (ζ : R) (m : ℕ) :
    quinticQuadraticFactor (quinticPeriodAlpha ζ) m =
      (1 : R⟦X⟧) + PowerSeries.C (bookBeta ζ) * PowerSeries.X ^ m +
        PowerSeries.X ^ (2 * m) := by
  unfold quinticQuadraticFactor bookBeta
  rw [map_neg]
  ring

theorem quadraticFactor_pair23_eq_bookAlpha {R : Type*} [CommRing R]
    (ζ : R) (m : ℕ) :
    quinticQuadraticFactor (quinticPeriodBeta ζ) m =
      (1 : R⟦X⟧) + PowerSeries.C (bookAlpha ζ) * PowerSeries.X ^ m +
        PowerSeries.X ^ (2 * m) := by
  unfold quinticQuadraticFactor bookAlpha
  rw [map_neg]
  ring

/-! ## The fifth-power algebra used after the §8.3 factor identities -/

theorem prod_sub_scaled_primitive_fifth_powerSeries {R : Type*}
    [CommRing R] [IsDomain R] {μ c : R} (A B : R⟦X⟧)
    (hμ : IsPrimitiveRoot μ 5) :
    ∏ j : Fin 5, (A - PowerSeries.C (μ ^ (j : ℕ) * c) * B) =
      A ^ 5 - PowerSeries.C (c ^ 5) * B ^ 5 := by
  calc
    ∏ j : Fin 5, (A - PowerSeries.C (μ ^ (j : ℕ) * c) * B)
        =
      ∏ j : Fin 5, (A - PowerSeries.C (μ ^ (j : ℕ)) *
        (PowerSeries.C c * B)) := by
        apply Finset.prod_congr rfl
        intro j _hj
        rw [map_mul]
        ring
    _ = A ^ 5 - (PowerSeries.C c * B) ^ 5 := by
        exact prod_sub_primitive_fifth_powerSeries
          (R := R) (μ := μ) A (PowerSeries.C c * B) hμ
    _ = A ^ 5 - PowerSeries.C (c ^ 5) * B ^ 5 := by
        rw [mul_pow, map_pow]

theorem quintic_factor_pair_mul_eq_core_of_book_periods {R : Type*}
    [CommRing R] [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 5) (H G : R⟦X⟧) :
    (G ^ 5 - PowerSeries.C ((bookBeta ζ) ^ 5) *
          PowerSeries.X * H ^ 5) *
        (G ^ 5 - PowerSeries.C ((bookAlpha ζ) ^ 5) *
          PowerSeries.X * H ^ 5) =
      quinticProductCore R H G := by
  exact
    quintic_factor_pair_mul_eq_core (R := R)
      ((bookAlpha ζ) ^ 5) ((bookBeta ζ) ^ 5) H G
      (bookPeriod_pow_five_sum (R := R) hζ)
      (bookPeriod_pow_five_mul (R := R) hζ)

/-! ## Names for the two `A,B` series in Hirschhorn §8.3 -/

/-- `A = (q^10,q^15,q^25;q^25)_∞`, written in the compressed variable as
`G(X^5)`. -/
noncomputable def section83A (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS R)

/-- `B = (q^5,q^20,q^25;q^25)_∞`, written in the compressed variable as
`H(X^5)`. -/
noncomputable def section83B (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS R)

/-- The right-hand side of Hirschhorn (8.3.2), in this file's period
convention: `A - α q B = A + (ζ²+ζ³) q B`. -/
noncomputable def section83_rhs_pair14 {R : Type*} [CommRing R] (ζ : R) : R⟦X⟧ :=
  section83A R + PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X * section83B R

/-- The right-hand side of Hirschhorn (8.3.1), in this file's period
convention: `A - β q B = A + (ζ+ζ⁴) q B`. -/
noncomputable def section83_rhs_pair23 {R : Type*} [CommRing R] (ζ : R) : R⟦X⟧ :=
  section83A R + PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X * section83B R

/-! ## Free-constant Euler factors for the §8.3 JTP product side -/

/-- The formal factor `1 - c X^(n+1)`.  This is the product-side atom for
`(c q; q)_∞`, where the scalar `c` is independent of the exponent. -/
noncomputable def constQFactorPS (c : ℂ) (n : ℕ) : ℂ⟦X⟧ :=
  (1 : ℂ⟦X⟧) - PowerSeries.C c * PowerSeries.X ^ (n + 1)

@[simp] theorem constQFactorPS_def (c : ℂ) (n : ℕ) :
    constQFactorPS c n =
      (1 : ℂ⟦X⟧) - PowerSeries.C c * PowerSeries.X ^ (n + 1) := rfl

/-- The formal q-Pochhammer product `(c q; q)_∞`. -/
noncomputable def constQPochInfPS (c : ℂ) : ℂ⟦X⟧ :=
  ∏' n : ℕ, constQFactorPS c n

/-- `∏(1 - c X^(n+1))` converges in the coefficientwise topology. -/
theorem multipliable_constQFactorPS (c : ℂ) :
    Multipliable fun n : ℕ => constQFactorPS c n := by
  simp_rw [constQFactorPS, sub_eq_add_neg]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun k =>
    Filter.eventually_atTop.mpr ⟨k, ?_⟩
  intro n hn
  rw [PowerSeries.order_neg]
  have hle :
      (PowerSeries.X ^ (n + 1) : ℂ⟦X⟧).order ≤
        (PowerSeries.C c * PowerSeries.X ^ (n + 1) : ℂ⟦X⟧).order := by
    rw [← PowerSeries.smul_eq_C_mul]
    exact PowerSeries.le_order_smul (φ := (PowerSeries.X : ℂ⟦X⟧) ^ (n + 1)) (a := c)
  rw [PowerSeries.order_X_pow] at hle
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hn) hle

/-- HasProd form of `constQPochInfPS`. -/
theorem hasProd_constQFactorPS (c : ℂ) :
    HasProd (fun n : ℕ => constQFactorPS c n) (constQPochInfPS c) :=
  (multipliable_constQFactorPS c).hasProd

/-- The `c = 1` free-constant product is the existing Euler product
`qPochInfPS ℂ`. -/
theorem constQPochInfPS_one :
    constQPochInfPS 1 = qPochInfPS ℂ := by
  rw [constQPochInfPS]
  simpa [constQFactorPS] using
    (qPochInfPS_eq_tprod ℂ).symm

/-- Per-`n` product factor for `(z q, z⁻¹ q, q; q)_∞`. -/
noncomputable def section83JTPTripleFactorPS (z : ℂ) (n : ℕ) : ℂ⟦X⟧ :=
  constQFactorPS 1 n * constQFactorPS z n * constQFactorPS z⁻¹ n

/-- Formal product side of the shifted two-variable JTP
`(z q, z⁻¹ q, q; q)_∞`. -/
noncomputable def section83JTPProductPS (z : ℂ) : ℂ⟦X⟧ :=
  constQPochInfPS 1 * constQPochInfPS z * constQPochInfPS z⁻¹

/-- The shifted JTP product is the `tprod` of the per-`n` triple factors. -/
theorem hasProd_section83JTPTripleFactorPS (z : ℂ) :
    HasProd (fun n : ℕ => section83JTPTripleFactorPS z n)
      (section83JTPProductPS z) := by
  unfold section83JTPTripleFactorPS section83JTPProductPS
  exact ((hasProd_constQFactorPS 1).mul (hasProd_constQFactorPS z)).mul
    (hasProd_constQFactorPS z⁻¹)

theorem section83JTPProductPS_eq_tprod (z : ℂ) :
    section83JTPProductPS z = ∏' n : ℕ, section83JTPTripleFactorPS z n :=
  (hasProd_section83JTPTripleFactorPS z).tprod_eq.symm

lemma coeff_mul_constQFactorPS_eq_of_lt
    (P : ℂ⟦X⟧) (c : ℂ) (k N : ℕ) (hk : k < N + 1) :
    (P * constQFactorPS c N).coeff k = P.coeff k := by
  rw [constQFactorPS, mul_sub, mul_one]
  rw [show P * (PowerSeries.C c * PowerSeries.X ^ (N + 1)) =
      (P * PowerSeries.C c) * PowerSeries.X ^ (N + 1) by ring]
  rw [map_sub, PowerSeries.coeff_mul_X_pow']
  simp [Nat.not_le_of_gt hk]

theorem partial_prod_section83JTPTripleFactorPS_coeff_stable
    (z : ℂ) (k N : ℕ) (hN : k ≤ N) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range (N + 1), section83JTPTripleFactorPS z n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n) := by
  rw [Finset.prod_range_succ]
  change PowerSeries.coeff k
      ((∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n) *
        (constQFactorPS 1 N * constQFactorPS z N * constQFactorPS z⁻¹ N)) =
    PowerSeries.coeff k (∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n)
  let P : ℂ⟦X⟧ := ∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n
  calc
    PowerSeries.coeff k (P * (constQFactorPS 1 N * constQFactorPS z N *
        constQFactorPS z⁻¹ N))
        = PowerSeries.coeff k (((P * constQFactorPS 1 N) *
          constQFactorPS z N) * constQFactorPS z⁻¹ N) := by
          congr 1
          ring_nf
    _ = PowerSeries.coeff k ((P * constQFactorPS 1 N) * constQFactorPS z N) :=
        coeff_mul_constQFactorPS_eq_of_lt ((P * constQFactorPS 1 N) *
          constQFactorPS z N) z⁻¹ k N (by omega)
    _ = PowerSeries.coeff k (P * constQFactorPS 1 N) :=
        coeff_mul_constQFactorPS_eq_of_lt (P * constQFactorPS 1 N) z k N (by omega)
    _ = PowerSeries.coeff k P :=
        coeff_mul_constQFactorPS_eq_of_lt P 1 k N (by omega)

theorem partial_prod_section83JTPTripleFactorPS_coeff_eq
    (z : ℂ) (k N M : ℕ) (hkN : k ≤ N) (hNM : N ≤ M) :
    PowerSeries.coeff k
        (∏ n ∈ Finset.range M, section83JTPTripleFactorPS z n) =
      PowerSeries.coeff k
        (∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n) := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M _ ih =>
      rw [partial_prod_section83JTPTripleFactorPS_coeff_stable z k M (by omega), ih]

theorem coeff_section83JTPProductPS_eq_coeff_partial (z : ℂ) (k : ℕ) :
    (section83JTPProductPS z).coeff k =
      (∏ n ∈ Finset.range (k + 1), section83JTPTripleFactorPS z n).coeff k := by
  have h_tendsto : Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n) atTop
      (𝓝 (section83JTPProductPS z)) :=
    (hasProd_section83JTPTripleFactorPS z).tendsto_prod_nat
  have h_coeff_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n)) atTop
      (𝓝 (PowerSeries.coeff k (section83JTPProductPS z))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℂ k).tendsto _).comp h_tendsto
  have h_const_tendsto : Tendsto
      (fun N : ℕ => PowerSeries.coeff k
        (∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n)) atTop
      (𝓝 (PowerSeries.coeff k
        (∏ n ∈ Finset.range (k + 1), section83JTPTripleFactorPS z n))) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨k + 1, fun N hN =>
      (partial_prod_section83JTPTripleFactorPS_coeff_eq z k (k + 1) N
        (by omega) hN).symm⟩
  exact tendsto_nhds_unique h_coeff_tendsto h_const_tendsto

lemma norm_coeff_mul_constQFactorPS_complex_le
    (P : ℂ⟦X⟧) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ k : ℕ, ‖P.coeff k‖ ≤ B) (c : ℂ) (hc : ‖c‖ ≤ 1) (k N : ℕ) :
    ‖(P * constQFactorPS c N).coeff k‖ ≤ 2 * B := by
  rw [constQFactorPS, mul_sub, mul_one]
  rw [show P * (PowerSeries.C c * PowerSeries.X ^ (N + 1)) =
      (P * PowerSeries.C c) * PowerSeries.X ^ (N + 1) by ring]
  rw [map_sub, PowerSeries.coeff_mul_X_pow']
  by_cases hle : N + 1 ≤ k
  · rw [if_pos hle]
    calc
      ‖P.coeff k - (P * PowerSeries.C c).coeff (k - (N + 1))‖
          ≤ ‖P.coeff k‖ + ‖(P * PowerSeries.C c).coeff (k - (N + 1))‖ :=
        norm_sub_le _ _
      _ ≤ B + B := by
        refine add_le_add (hP k) ?_
        rw [PowerSeries.coeff_mul_C, norm_mul]
        calc
          ‖P.coeff (k - (N + 1))‖ * ‖c‖ ≤ B * 1 :=
            mul_le_mul (hP (k - (N + 1))) hc (norm_nonneg _) hB
          _ = B := by ring
      _ = 2 * B := by ring
  · rw [if_neg hle, sub_zero]
    linarith [hP k]

lemma norm_coeff_mul_section83JTPTripleFactorPS_complex_le
    (P : ℂ⟦X⟧) (B : ℝ) (hB : 0 ≤ B)
    (hP : ∀ k : ℕ, ‖P.coeff k‖ ≤ B) (z : ℂ)
    (hz : ‖z‖ ≤ 1) (hzinv : ‖z⁻¹‖ ≤ 1) (k N : ℕ) :
    ‖(P * section83JTPTripleFactorPS z N).coeff k‖ ≤ 8 * B := by
  have hP1 : ∀ k : ℕ, ‖(P * constQFactorPS 1 N).coeff k‖ ≤ 2 * B :=
    fun k => norm_coeff_mul_constQFactorPS_complex_le P B hB hP 1 (by norm_num) k N
  have hP2 : ∀ k : ℕ,
      ‖((P * constQFactorPS 1 N) * constQFactorPS z N).coeff k‖ ≤
        2 * (2 * B) :=
    fun k => norm_coeff_mul_constQFactorPS_complex_le
      (P * constQFactorPS 1 N) (2 * B) (by nlinarith) hP1 z hz k N
  calc
    ‖(P * section83JTPTripleFactorPS z N).coeff k‖ =
        ‖(((P * constQFactorPS 1 N) * constQFactorPS z N) *
          constQFactorPS z⁻¹ N).coeff k‖ := by
        congr 1
        rw [section83JTPTripleFactorPS]
        ring_nf
    _ ≤ 2 * (2 * (2 * B)) :=
        norm_coeff_mul_constQFactorPS_complex_le
          ((P * constQFactorPS 1 N) * constQFactorPS z N)
          (2 * (2 * B)) (by nlinarith) hP2 z⁻¹ hzinv k N
    _ = 8 * B := by ring

lemma norm_coeff_partial_section83JTPTripleFactorPS_complex_le
    (z : ℂ) (hz : ‖z‖ ≤ 1) (hzinv : ‖z⁻¹‖ ≤ 1) (N k : ℕ) :
    ‖(∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n).coeff k‖ ≤
      (8 : ℝ) ^ N := by
  revert k
  induction N with
  | zero =>
      intro k
      by_cases hk : k = 0 <;> simp [hk]
  | succ N ih =>
      intro k
      rw [Finset.prod_range_succ]
      calc
        ‖((∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n) *
            section83JTPTripleFactorPS z N).coeff k‖
            ≤ 8 * (8 : ℝ) ^ N :=
          norm_coeff_mul_section83JTPTripleFactorPS_complex_le
            (∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n)
            ((8 : ℝ) ^ N) (by positivity) (fun j => ih j) z hz hzinv k N
        _ = (8 : ℝ) ^ (N + 1) := by
          rw [pow_succ]
          ring

lemma norm_coeff_section83JTPProductPS_complex_le
    (z : ℂ) (hz : ‖z‖ ≤ 1) (hzinv : ‖z⁻¹‖ ≤ 1) (k : ℕ) :
    ‖(section83JTPProductPS z).coeff k‖ ≤ (8 : ℝ) ^ (k + 1) := by
  rw [coeff_section83JTPProductPS_eq_coeff_partial z k]
  exact norm_coeff_partial_section83JTPTripleFactorPS_complex_le z hz hzinv (k + 1) k

lemma norm_coeff_partial_section83JTPTripleFactorPS_complex_le_uniform
    (z : ℂ) (hz : ‖z‖ ≤ 1) (hzinv : ‖z⁻¹‖ ≤ 1) (N k : ℕ) :
    ‖(∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n).coeff k‖ ≤
      (8 : ℝ) ^ (k + 1) := by
  by_cases hN : N ≤ k + 1
  · exact le_trans (norm_coeff_partial_section83JTPTripleFactorPS_complex_le z hz hzinv N k)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) hN)
  · have hle : k + 1 ≤ N := Nat.le_of_not_ge hN
    rw [partial_prod_section83JTPTripleFactorPS_coeff_eq z k (k + 1) N
      (by omega) hle]
    exact norm_coeff_partial_section83JTPTripleFactorPS_complex_le z hz hzinv (k + 1) k

/-! ### Analytic product attached to the free-constant formal product -/

/-- Analytic factor `1 - c q^(n+1)`. -/
def constQFactorAnalytic (c q : ℂ) (n : ℕ) : ℂ :=
  1 - c * q ^ (n + 1)

/-- Analytic per-`n` factor for `(z q, z⁻¹ q, q; q)_∞`. -/
noncomputable def section83JTPTripleFactorAnalytic (z q : ℂ) (n : ℕ) : ℂ :=
  constQFactorAnalytic 1 q n * constQFactorAnalytic z q n *
    constQFactorAnalytic z⁻¹ q n

/-- Analytic product side of `(z q, z⁻¹ q, q; q)_∞`. -/
noncomputable def section83JTPProductAnalytic (z q : ℂ) : ℂ :=
  (∏' n : ℕ, constQFactorAnalytic 1 q n) *
    (∏' n : ℕ, constQFactorAnalytic z q n) *
      (∏' n : ℕ, constQFactorAnalytic z⁻¹ q n)

private theorem summable_norm_constQFactorAnalytic_tail
    (c q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖-(c * q) * q ^ n‖ := by
  exact PartI.Ch02.summable_norm_mul_geometric_complex (-(c * q)) q hq

theorem multipliable_constQFactorAnalytic (c q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => constQFactorAnalytic c q n := by
  have h := multipliable_one_add_of_summable
    (summable_norm_constQFactorAnalytic_tail c q hq)
  refine h.congr fun n => ?_
  simp only [constQFactorAnalytic]
  rw [show q ^ (n + 1) = q * q ^ n by
    rw [show n + 1 = 1 + n by omega, pow_add, pow_one]]
  ring

theorem tendsto_section83JTPProductAnalytic_partial
    (z q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto
      (fun N : ℕ => ∏ n ∈ Finset.range N, section83JTPTripleFactorAnalytic z q n)
      atTop (𝓝 (section83JTPProductAnalytic z q)) := by
  have h1 := (multipliable_constQFactorAnalytic 1 q hq).tendsto_prod_tprod_nat
  have hz := (multipliable_constQFactorAnalytic z q hq).tendsto_prod_tprod_nat
  have hzinv := (multipliable_constQFactorAnalytic z⁻¹ q hq).tendsto_prod_tprod_nat
  simpa [section83JTPProductAnalytic, section83JTPTripleFactorAnalytic,
    Finset.prod_mul_distrib, mul_assoc] using ((h1.mul hz).mul hzinv)

private lemma norm_of_sq_eq_lt_one {Y q : ℂ} (hYq : Y ^ 2 = q) (hq : ‖q‖ < 1) :
    ‖Y‖ < 1 := by
  have hY_sq : ‖Y‖ ^ 2 = ‖q‖ := by
    rw [← norm_pow, hYq]
  have hY_nonneg : 0 ≤ ‖Y‖ := norm_nonneg _
  rw [← hY_sq] at hq
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by simpa using hq)

private lemma jacobiProductEvenFactor_reparam
    (q Y : ℂ) (hYq : Y ^ 2 = q) (n : ℕ) :
    PartI.Ch02.jacobiProductEvenFactor Y n = constQFactorAnalytic 1 q n := by
  simp [PartI.Ch02.jacobiProductEvenFactor, constQFactorAnalytic]
  rw [show Y ^ (2 * (n + 1)) = (Y ^ 2) ^ (n + 1) by rw [pow_mul], hYq]

private lemma jacobiProductOddFactor_reparam
    (z q Y : ℂ) (hYq : Y ^ 2 = q) (n : ℕ) :
    PartI.Ch02.jacobiProductOddFactor Y (-(z * Y)) n =
      constQFactorAnalytic z q n := by
  simp [PartI.Ch02.jacobiProductOddFactor, constQFactorAnalytic]
  have hpow :
      Y * Y ^ (2 * (n + 1) - 1) = q ^ (n + 1) := by
    have hsucc : 2 * (n + 1) - 1 + 1 = 2 * (n + 1) := by omega
    calc
      Y * Y ^ (2 * (n + 1) - 1) = Y ^ (2 * (n + 1) - 1 + 1) := by
        rw [← pow_succ']
      _ = Y ^ (2 * (n + 1)) := by rw [hsucc]
      _ = (Y ^ 2) ^ (n + 1) := by rw [pow_mul]
      _ = q ^ (n + 1) := by rw [hYq]
  rw [show z * Y * Y ^ (2 * (n + 1) - 1) =
      z * (Y * Y ^ (2 * (n + 1) - 1)) by ring, hpow]
  ring

private lemma jacobiProductOddFactor_inv_reparam_zero
    (z Y : ℂ) (hz : z ≠ 0) (hY : Y ≠ 0) :
    PartI.Ch02.jacobiProductOddFactor Y (-(z * Y))⁻¹ 0 = 1 - z⁻¹ := by
  simp [PartI.Ch02.jacobiProductOddFactor]
  field_simp [hz, hY]
  ring

private lemma jacobiProductOddFactor_inv_reparam_tail
    (z q Y : ℂ) (hz : z ≠ 0) (hY : Y ≠ 0) (hYq : Y ^ 2 = q) (n : ℕ) :
    PartI.Ch02.jacobiProductOddFactor Y (-(z * Y))⁻¹ (n + 1) =
      constQFactorAnalytic z⁻¹ q n := by
  simp [PartI.Ch02.jacobiProductOddFactor, constQFactorAnalytic]
  have hpow :
      Y ^ (2 * (n + 1 + 1) - 1) = Y * q ^ (n + 1) := by
    have hexp : 2 * (n + 1 + 1) - 1 = 2 * (n + 1) + 1 := by omega
    rw [hexp, pow_succ']
    rw [show Y ^ (2 * (n + 1)) = (Y ^ 2) ^ (n + 1) by rw [pow_mul], hYq]
  rw [hpow]
  field_simp [hz, hY]
  ring

/-- Product-side bookkeeping for the `Y² = q`, `z_JTP = -(zY)`
specialisation of Chapter 2. -/
theorem jacobiInfiniteProduct_reparam_section83
    (z q Y : ℂ) (hz : z ≠ 0) (hY : Y ≠ 0) (hYq : Y ^ 2 = q)
    (hq : ‖q‖ < 1) :
    PartI.Ch02.jacobiInfiniteProduct Y (-(z * Y)) =
      (1 - z⁻¹) * section83JTPProductAnalytic z q := by
  have hYnorm : ‖Y‖ < 1 := norm_of_sq_eq_lt_one hYq hq
  rw [PartI.Ch02.jacobiInfiniteProduct_eq_tprod_components Y (-(z * Y)) hYnorm]
  have h_even :
      (∏' n : ℕ, PartI.Ch02.jacobiProductEvenFactor Y n) =
        ∏' n : ℕ, constQFactorAnalytic 1 q n :=
    tprod_congr fun n => jacobiProductEvenFactor_reparam q Y hYq n
  have h_odd :
      (∏' n : ℕ, PartI.Ch02.jacobiProductOddFactor Y (-(z * Y)) n) =
        ∏' n : ℕ, constQFactorAnalytic z q n :=
    tprod_congr fun n => jacobiProductOddFactor_reparam z q Y hYq n
  have h_tail_mult :
      Multipliable fun n : ℕ =>
        PartI.Ch02.jacobiProductOddFactor Y (-(z * Y))⁻¹ (n + 1) := by
    exact (multipliable_constQFactorAnalytic z⁻¹ q hq).congr
      fun n => (jacobiProductOddFactor_inv_reparam_tail z q Y hz hY hYq n).symm
  have h_inv :
      (∏' n : ℕ, PartI.Ch02.jacobiProductOddFactor Y (-(z * Y))⁻¹ n) =
        (1 - z⁻¹) * ∏' n : ℕ, constQFactorAnalytic z⁻¹ q n := by
    rw [tprod_eq_zero_mul' h_tail_mult]
    rw [jacobiProductOddFactor_inv_reparam_zero z Y hz hY]
    congr 1
    exact tprod_congr fun n =>
      jacobiProductOddFactor_inv_reparam_tail z q Y hz hY hYq n
  rw [h_even, h_odd, h_inv]
  simp [section83JTPProductAnalytic]
  ring

private lemma int_two_dvd_mul_self_add_one (n : ℤ) : (2 : ℤ) ∣ n * (n + 1) := by
  rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨m * (n + 1), by rw [hm]; ring⟩
  · exact ⟨n * (m + 1), by rw [hm]; ring⟩

private lemma zpow_sq_add_self_reparam
    (q Y : ℂ) (hYq : Y ^ 2 = q) (n : ℤ) :
    Y ^ (n ^ 2 + n) = q ^ (n * (n + 1) / 2) := by
  have hdiv : (2 : ℤ) ∣ n * (n + 1) := int_two_dvd_mul_self_add_one n
  have hmul : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
    rw [show 2 * (n * (n + 1) / 2) = (n * (n + 1) / 2) * 2 by ring]
    exact Int.ediv_mul_cancel hdiv
  calc
    Y ^ (n ^ 2 + n) = Y ^ (n * (n + 1)) := by ring_nf
    _ = Y ^ (2 * (n * (n + 1) / 2)) := by rw [hmul]
    _ = (Y ^ (2 : ℤ)) ^ (n * (n + 1) / 2) := by rw [zpow_mul]
    _ = (Y ^ 2) ^ (n * (n + 1) / 2) := by rfl
    _ = q ^ (n * (n + 1) / 2) := by rw [hYq]

/-- Series-side bookkeeping for the same Chapter 2 reparametrisation. -/
theorem jacobiInfiniteSeries_reparam_triangular
    (z q Y : ℂ) (hY : Y ≠ 0) (hYq : Y ^ 2 = q) :
    PartI.Ch02.jacobiInfiniteSeries Y (-(z * Y)) =
      ∑' n : ℤ, (-z : ℂ) ^ n * q ^ (n * (n + 1) / 2) := by
  rw [PartI.Ch02.jacobiInfiniteSeries]
  refine tsum_congr fun n => ?_
  have hbase : (-(z * Y) : ℂ) = (-z) * Y := by ring
  rw [hbase, mul_zpow]
  have hmul : Y ^ n * Y ^ (n ^ 2) = Y ^ (n + n ^ 2) := by
    rw [← zpow_add₀ hY]
  rw [show ((-z : ℂ) ^ n * Y ^ n) * Y ^ (n ^ 2) =
      (-z : ℂ) ^ n * (Y ^ n * Y ^ (n ^ 2)) by ring]
  rw [hmul, show n + n ^ 2 = n ^ 2 + n by ring]
  rw [zpow_sq_add_self_reparam q Y hYq n]

/-- Chapter 2 JTP in the shifted `section83JTPProductAnalytic` convention,
away from `q = 0`. -/
theorem one_sub_inv_mul_section83JTPProductAnalytic_eq_triangular_tsum_of_ne_zero
    (z q : ℂ) (hz : z ≠ 0) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (1 - z⁻¹) * section83JTPProductAnalytic z q =
      ∑' n : ℤ, (-z : ℂ) ^ n * q ^ (n * (n + 1) / 2) := by
  obtain ⟨Y, hYq⟩ := IsAlgClosed.exists_pow_nat_eq q (n := 2) (by norm_num)
  have hY : Y ≠ 0 := by
    intro hY0
    apply hq0
    rw [← hYq, hY0]
    ring
  have hYnorm : ‖Y‖ < 1 := norm_of_sq_eq_lt_one hYq hq
  have harg : (-(z * Y) : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero hz hY)
  rw [← jacobiInfiniteProduct_reparam_section83 z q Y hz hY hYq hq]
  rw [PartI.Ch02.jacobiTripleProduct Y (-(z * Y)) hYnorm harg]
  rw [jacobiInfiniteSeries_reparam_triangular z q Y hY hYq]

/-! ### Bilateral triangular terms for the fifth-root period collapse -/

private noncomputable def section83TriangularTerm (z q : ℂ) (n : ℤ) : ℂ :=
  (-z : ℂ) ^ n * q ^ (n * (n + 1) / 2)

private noncomputable def section83PairedTriangularTerm (z q : ℂ) (n : ℕ) : ℂ :=
  section83TriangularTerm z q n +
    section83TriangularTerm z q (-(n + 1 : ℤ))

private noncomputable def section83ATerm (q : ℂ) (k : ℤ) : ℂ :=
  (-1 : ℂ) ^ k * (q ^ 5) ^ (k * (5 * k - 1) / 2)

private noncomputable def section83BTerm (q : ℂ) (k : ℤ) : ℂ :=
  (-1 : ℂ) ^ k * (q ^ 5) ^ (k * (5 * k - 3) / 2)

private lemma int_two_dvd_mul_five_mul_sub_one (k : ℤ) :
    (2 : ℤ) ∣ k * (5 * k - 1) := by
  have hbase : (2 : ℤ) ∣ k * (k - 1) := by
    have h := int_two_dvd_mul_self_add_one (k - 1)
    convert h using 1
    ring
  have hfour : (2 : ℤ) ∣ 4 * k * k := by
    convert dvd_mul_of_dvd_left (by norm_num : (2 : ℤ) ∣ 4) (k * k) using 1
    ring
  convert dvd_add hbase hfour using 1
  ring

private lemma int_two_dvd_mul_five_mul_sub_three (k : ℤ) :
    (2 : ℤ) ∣ k * (5 * k - 3) := by
  have hbase : (2 : ℤ) ∣ k * (k - 1) := by
    have h := int_two_dvd_mul_self_add_one (k - 1)
    convert h using 1
    ring
  have htwo : (2 : ℤ) ∣ 2 * k * (2 * k - 1) := by
    convert dvd_mul_right (2 : ℤ) (k * (2 * k - 1)) using 1
    ring
  convert dvd_add hbase htwo using 1
  ring

private lemma int_mul_ediv_two (b a : ℤ) (h : (2 : ℤ) ∣ a) :
    b * (a / 2) = b * a / 2 :=
  (Int.mul_ediv_assoc b h).symm

private lemma zpow_five_pow (q : ℂ) (e : ℤ) :
    (q ^ 5) ^ e = q ^ ((5 : ℤ) * e) := by
  change (q ^ (5 : ℤ)) ^ e = q ^ ((5 : ℤ) * e)
  rw [zpow_mul]

private lemma neg_one_zpow_neg_natCast (m : ℕ) :
    (-1 : ℂ) ^ (-(m : ℤ)) = (-1 : ℂ) ^ m := by
  rw [zpow_neg, zpow_natCast]
  exact inv_eq_of_mul_eq_one_right (by
    have hsquare : ((-1 : ℂ) ^ m) ^ 2 = 1 := by
      rw [← pow_mul]
      simp
    simpa [pow_two] using hsquare)

private lemma neg_one_zpow_natCast_add_one (m : ℕ) :
    (-1 : ℂ) ^ ((m : ℤ) + 1) = -((-1 : ℂ) ^ m) := by
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  rw [zpow_natCast]
  norm_num

private lemma neg_z_zpow_five_mul (z : ℂ) (hz5 : z ^ 5 = 1) (m : ℕ) :
    (-z : ℂ) ^ (5 * (m : ℤ)) = (-1 : ℂ) ^ m := by
  rw [zpow_mul]
  have hbase : (-z : ℂ) ^ (5 : ℤ) = (-1 : ℂ) := by
    rw [show ((-z : ℂ) ^ (5 : ℤ)) = (-z) ^ (5 : ℕ) by rfl]
    rw [neg_pow]
    norm_num
    rw [hz5]
  rw [hbase, zpow_natCast]

private lemma neg_z_zpow_five_mul_coeff_zero
    {z : ℂ} (hz5 : z ^ 5 = 1) (hz : z ≠ 0) (m : ℕ) :
    (-z : ℂ) ^ (5 * (m : ℤ)) + (-z : ℂ) ^ (-(5 * (m : ℤ) + 1)) =
      (-1 : ℂ) ^ m * (1 - z ^ 4) := by
  have hnz : (-z : ℂ) ≠ 0 := neg_ne_zero.mpr hz
  rw [neg_z_zpow_five_mul z hz5 m]
  rw [show (-(5 * (m : ℤ) + 1) : ℤ) = -(5 * (m : ℤ)) - 1 by ring]
  rw [zpow_sub₀ hnz]
  rw [show (-z : ℂ) ^ (-(5 * (m : ℤ))) =
      ((-z : ℂ) ^ (5 * (m : ℤ)))⁻¹ by rw [zpow_neg]]
  rw [neg_z_zpow_five_mul z hz5 m]
  rw [show ((-z : ℂ) ^ (1 : ℤ)) = -z by simp]
  field_simp [hz]
  have hsquare : ((-1 : ℂ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  rw [hsquare]
  simp only [one_mul]
  rw [show z * (1 - z ^ 4) = z - z ^ 5 by ring]
  rw [hz5]
  ring

private lemma neg_z_zpow_five_mul_coeff_one
    {z : ℂ} (hz5 : z ^ 5 = 1) (hz : z ≠ 0) (m : ℕ) :
    (-z : ℂ) ^ (5 * (m : ℤ) + 1) + (-z : ℂ) ^ (-(5 * (m : ℤ) + 2)) =
      (-1 : ℂ) ^ m * (z ^ 3 - z) := by
  have hnz : (-z : ℂ) ≠ 0 := neg_ne_zero.mpr hz
  rw [zpow_add₀ hnz, neg_z_zpow_five_mul z hz5 m]
  rw [show ((-z : ℂ) ^ (1 : ℤ)) = -z by simp]
  rw [show (-(5 * (m : ℤ) + 2) : ℤ) = -(5 * (m : ℤ)) - 2 by ring]
  rw [zpow_sub₀ hnz]
  rw [show (-z : ℂ) ^ (-(5 * (m : ℤ))) =
      ((-z : ℂ) ^ (5 * (m : ℤ)))⁻¹ by rw [zpow_neg]]
  rw [neg_z_zpow_five_mul z hz5 m]
  rw [show ((-z : ℂ) ^ (2 : ℤ)) = z ^ 2 by
    rw [show ((-z : ℂ) ^ (2 : ℤ)) = (-z) ^ (2 : ℕ) by rfl]
    ring]
  field_simp [hz]
  have hsquare : ((-1 : ℂ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  rw [hsquare]
  simp only [one_mul]
  rw [show z ^ 3 * (z ^ 2 - 1) = z ^ 5 - z ^ 3 by ring]
  rw [hz5]
  ring

private lemma neg_z_zpow_five_mul_coeff_two
    {z : ℂ} (hz5 : z ^ 5 = 1) (hz : z ≠ 0) (m : ℕ) :
    (-z : ℂ) ^ (5 * (m : ℤ) + 2) + (-z : ℂ) ^ (-(5 * (m : ℤ) + 3)) = 0 := by
  have hnz : (-z : ℂ) ≠ 0 := neg_ne_zero.mpr hz
  rw [zpow_add₀ hnz, neg_z_zpow_five_mul z hz5 m]
  rw [show ((-z : ℂ) ^ (2 : ℤ)) = z ^ 2 by
    rw [show ((-z : ℂ) ^ (2 : ℤ)) = (-z) ^ (2 : ℕ) by rfl]
    ring]
  rw [show (-(5 * (m : ℤ) + 3) : ℤ) = -(5 * (m : ℤ)) - 3 by ring]
  rw [zpow_sub₀ hnz]
  rw [show (-z : ℂ) ^ (-(5 * (m : ℤ))) =
      ((-z : ℂ) ^ (5 * (m : ℤ)))⁻¹ by rw [zpow_neg]]
  rw [neg_z_zpow_five_mul z hz5 m]
  rw [show ((-z : ℂ) ^ (3 : ℤ)) = -z ^ 3 by
    rw [show ((-z : ℂ) ^ (3 : ℤ)) = (-z) ^ (3 : ℕ) by rfl]
    ring]
  field_simp [hz]
  have hsquare : ((-1 : ℂ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  rw [hsquare]
  rw [hz5]
  ring

private lemma neg_z_zpow_five_mul_coeff_three
    {z : ℂ} (hz5 : z ^ 5 = 1) (hz : z ≠ 0) (m : ℕ) :
    (-z : ℂ) ^ (5 * (m : ℤ) + 3) + (-z : ℂ) ^ (-(5 * (m : ℤ) + 4)) =
      (-1 : ℂ) ^ m * (z - z ^ 3) := by
  have hnz : (-z : ℂ) ≠ 0 := neg_ne_zero.mpr hz
  rw [zpow_add₀ hnz, neg_z_zpow_five_mul z hz5 m]
  rw [show ((-z : ℂ) ^ (3 : ℤ)) = -z ^ 3 by
    rw [show ((-z : ℂ) ^ (3 : ℤ)) = (-z) ^ (3 : ℕ) by rfl]
    ring]
  rw [show (-(5 * (m : ℤ) + 4) : ℤ) = -(5 * (m : ℤ)) - 4 by ring]
  rw [zpow_sub₀ hnz]
  rw [show (-z : ℂ) ^ (-(5 * (m : ℤ))) =
      ((-z : ℂ) ^ (5 * (m : ℤ)))⁻¹ by rw [zpow_neg]]
  rw [neg_z_zpow_five_mul z hz5 m]
  rw [show ((-z : ℂ) ^ (4 : ℤ)) = z ^ 4 by
    rw [show ((-z : ℂ) ^ (4 : ℤ)) = (-z) ^ (4 : ℕ) by rfl]
    ring]
  field_simp [hz]
  have hsquare : ((-1 : ℂ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  rw [hsquare]
  simp only [one_mul]
  have h7 : z ^ 7 = z ^ 2 := by
    calc
      z ^ 7 = z ^ 5 * z ^ 2 := by ring
      _ = z ^ 2 := by rw [hz5]; ring
  rw [hz5, h7]
  ring

private lemma neg_z_zpow_five_mul_coeff_four
    {z : ℂ} (hz5 : z ^ 5 = 1) (hz : z ≠ 0) (m : ℕ) :
    (-z : ℂ) ^ (5 * (m : ℤ) + 4) + (-z : ℂ) ^ (-(5 * (m : ℤ) + 5)) =
      (-1 : ℂ) ^ m * (z ^ 4 - 1) := by
  have hnz : (-z : ℂ) ≠ 0 := neg_ne_zero.mpr hz
  rw [zpow_add₀ hnz, neg_z_zpow_five_mul z hz5 m]
  rw [show ((-z : ℂ) ^ (4 : ℤ)) = z ^ 4 by
    rw [show ((-z : ℂ) ^ (4 : ℤ)) = (-z) ^ (4 : ℕ) by rfl]
    ring]
  rw [show (-(5 * (m : ℤ) + 5) : ℤ) = -(5 * ((m : ℤ) + 1)) by ring]
  rw [show (-z : ℂ) ^ (-(5 * ((m : ℤ) + 1))) =
      ((-z : ℂ) ^ (5 * ((m : ℤ) + 1)))⁻¹ by rw [zpow_neg]]
  rw [zpow_mul]
  have hbase : (-z : ℂ) ^ (5 : ℤ) = (-1 : ℂ) := by
    rw [show ((-z : ℂ) ^ (5 : ℤ)) = (-z) ^ (5 : ℕ) by rfl]
    rw [neg_pow]
    norm_num
    rw [hz5]
  rw [hbase, neg_one_zpow_natCast_add_one m]
  field_simp
  have hsquare : ((-1 : ℂ) ^ m) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  rw [hsquare]
  ring

private lemma section83PairedTriangularTerm_eq_coeff_mul
    (z q : ℂ) (n : ℕ) :
    section83PairedTriangularTerm z q n =
      (((-z : ℂ) ^ (n : ℤ) + (-z : ℂ) ^ (-(n + 1 : ℤ))) *
        q ^ ((n : ℤ) * ((n : ℤ) + 1) / 2)) := by
  unfold section83PairedTriangularTerm section83TriangularTerm
  have hexp :
      (-(n + 1 : ℤ)) * (-(n + 1 : ℤ) + 1) / 2 =
        (n : ℤ) * ((n : ℤ) + 1) / 2 := by
    ring_nf
  rw [hexp]
  ring

private lemma q_zpow_section83A_neg (q : ℂ) (m : ℕ) :
    q ^ (((5 * (m : ℤ)) * (5 * (m : ℤ) + 1)) / 2) =
      (q ^ 5) ^ ((-(m : ℤ)) * (5 * (-(m : ℤ)) - 1) / 2) := by
  have hdiv : (2 : ℤ) ∣ (-(m : ℤ)) * (5 * (-(m : ℤ)) - 1) :=
    int_two_dvd_mul_five_mul_sub_one (-(m : ℤ))
  rw [zpow_five_pow]
  congr 1
  rw [int_mul_ediv_two 5 _ hdiv]
  ring_nf

private lemma q_zpow_section83A_pos (q : ℂ) (m : ℕ) :
    q ^ (((5 * (m : ℤ) + 4) * (5 * (m : ℤ) + 5)) / 2) =
      (q ^ 5) ^ (((m : ℤ) + 1) * (5 * ((m : ℤ) + 1) - 1) / 2) := by
  have hdiv : (2 : ℤ) ∣ ((m : ℤ) + 1) * (5 * ((m : ℤ) + 1) - 1) :=
    int_two_dvd_mul_five_mul_sub_one ((m : ℤ) + 1)
  rw [zpow_five_pow]
  congr 1
  rw [int_mul_ediv_two 5 _ hdiv]
  ring_nf

private lemma q_zpow_section83B_neg (q : ℂ) (hq : q ≠ 0) (m : ℕ) :
    q ^ (((5 * (m : ℤ) + 1) * (5 * (m : ℤ) + 2)) / 2) =
      q * (q ^ 5) ^ ((-(m : ℤ)) * (5 * (-(m : ℤ)) - 3) / 2) := by
  have hdiv : (2 : ℤ) ∣ (-(m : ℤ)) * (5 * (-(m : ℤ)) - 3) :=
    int_two_dvd_mul_five_mul_sub_three (-(m : ℤ))
  rw [zpow_five_pow]
  rw [show q * q ^ ((5 : ℤ) * ((-(m : ℤ)) * (5 * (-(m : ℤ)) - 3) / 2)) =
      q ^ (1 : ℤ) *
        q ^ ((5 : ℤ) * ((-(m : ℤ)) * (5 * (-(m : ℤ)) - 3) / 2)) by simp]
  rw [← zpow_add₀ hq]
  congr 1
  rw [int_mul_ediv_two 5 _ hdiv]
  have hA : (2 : ℤ) ∣ (m : ℤ) * 15 + (m : ℤ) ^ 2 * 25 := by
    convert dvd_mul_of_dvd_right hdiv 5 using 1
    ring
  ring_nf
  rw [show 2 + (m : ℤ) * 15 + (m : ℤ) ^ 2 * 25 =
      2 + ((m : ℤ) * 15 + (m : ℤ) ^ 2 * 25) by ring]
  rw [Int.add_ediv_of_dvd_right hA]
  ring

private lemma q_zpow_section83B_pos (q : ℂ) (hq : q ≠ 0) (m : ℕ) :
    q ^ (((5 * (m : ℤ) + 3) * (5 * (m : ℤ) + 4)) / 2) =
      q * (q ^ 5) ^ (((m : ℤ) + 1) * (5 * ((m : ℤ) + 1) - 3) / 2) := by
  have hdiv : (2 : ℤ) ∣ ((m : ℤ) + 1) * (5 * ((m : ℤ) + 1) - 3) :=
    int_two_dvd_mul_five_mul_sub_three ((m : ℤ) + 1)
  rw [zpow_five_pow]
  rw [show q * q ^ ((5 : ℤ) * (((m : ℤ) + 1) *
        (5 * ((m : ℤ) + 1) - 3) / 2)) =
      q ^ (1 : ℤ) *
        q ^ ((5 : ℤ) * (((m : ℤ) + 1) *
          (5 * ((m : ℤ) + 1) - 3) / 2)) by simp]
  rw [← zpow_add₀ hq]
  congr 1
  rw [int_mul_ediv_two 5 _ hdiv]
  have hA10 : (2 : ℤ) ∣ 10 + (m : ℤ) * 35 + (m : ℤ) ^ 2 * 25 := by
    convert dvd_mul_of_dvd_right hdiv 5 using 1
    ring
  have hA : (2 : ℤ) ∣ (m : ℤ) * 35 + (m : ℤ) ^ 2 * 25 := by
    convert dvd_sub hA10 (by norm_num : (2 : ℤ) ∣ 10) using 1
    ring
  ring_nf
  rw [show 12 + (m : ℤ) * 35 + (m : ℤ) ^ 2 * 25 =
      12 + ((m : ℤ) * 35 + (m : ℤ) ^ 2 * 25) by ring]
  rw [show 10 + (m : ℤ) * 35 + (m : ℤ) ^ 2 * 25 =
      10 + ((m : ℤ) * 35 + (m : ℤ) ^ 2 * 25) by ring]
  rw [Int.add_ediv_of_dvd_right hA]
  rw [Int.add_ediv_of_dvd_right hA]
  ring

private lemma section83PairedTriangularTerm_residue_zero
    {z q : ℂ} (hz5 : z ^ 5 = 1) (hz : z ≠ 0) (m : ℕ) :
    section83PairedTriangularTerm z q (5 * m) =
      (1 - z ^ 4) * section83ATerm q (-(m : ℤ)) := by
  rw [section83PairedTriangularTerm_eq_coeff_mul]
  rw [show ((5 * m : ℕ) : ℤ) = 5 * (m : ℤ) by norm_num]
  rw [show (((5 * (m : ℤ)) + 1 : ℤ) = 5 * (m : ℤ) + 1) by ring]
  rw [neg_z_zpow_five_mul_coeff_zero hz5 hz m]
  rw [q_zpow_section83A_neg]
  unfold section83ATerm
  rw [neg_one_zpow_neg_natCast]
  ring

private lemma section83PairedTriangularTerm_residue_one
    {z q : ℂ} (hz5 : z ^ 5 = 1) (hz : z ≠ 0) (hq : q ≠ 0) (m : ℕ) :
    section83PairedTriangularTerm z q (5 * m + 1) =
      (z ^ 3 - z) * q * section83BTerm q (-(m : ℤ)) := by
  rw [section83PairedTriangularTerm_eq_coeff_mul]
  rw [show ((5 * m + 1 : ℕ) : ℤ) = 5 * (m : ℤ) + 1 by norm_num]
  rw [show (5 * (m : ℤ) + 1 + 1 : ℤ) = 5 * (m : ℤ) + 2 by ring]
  rw [neg_z_zpow_five_mul_coeff_one hz5 hz m]
  rw [q_zpow_section83B_neg q hq]
  unfold section83BTerm
  rw [neg_one_zpow_neg_natCast]
  ring

private lemma section83PairedTriangularTerm_residue_two
    {z q : ℂ} (hz5 : z ^ 5 = 1) (hz : z ≠ 0) (m : ℕ) :
    section83PairedTriangularTerm z q (5 * m + 2) = 0 := by
  rw [section83PairedTriangularTerm_eq_coeff_mul]
  rw [show ((5 * m + 2 : ℕ) : ℤ) = 5 * (m : ℤ) + 2 by norm_num]
  rw [show (5 * (m : ℤ) + 2 + 1 : ℤ) = 5 * (m : ℤ) + 3 by ring]
  rw [neg_z_zpow_five_mul_coeff_two hz5 hz m]
  ring

private lemma section83PairedTriangularTerm_residue_three
    {z q : ℂ} (hz5 : z ^ 5 = 1) (hz : z ≠ 0) (hq : q ≠ 0) (m : ℕ) :
    section83PairedTriangularTerm z q (5 * m + 3) =
      (z ^ 3 - z) * q * section83BTerm q ((m : ℤ) + 1) := by
  rw [section83PairedTriangularTerm_eq_coeff_mul]
  rw [show ((5 * m + 3 : ℕ) : ℤ) = 5 * (m : ℤ) + 3 by norm_num]
  rw [show (5 * (m : ℤ) + 3 + 1 : ℤ) = 5 * (m : ℤ) + 4 by ring]
  rw [neg_z_zpow_five_mul_coeff_three hz5 hz m]
  rw [q_zpow_section83B_pos q hq]
  unfold section83BTerm
  rw [neg_one_zpow_natCast_add_one]
  ring

private lemma section83PairedTriangularTerm_residue_four
    {z q : ℂ} (hz5 : z ^ 5 = 1) (hz : z ≠ 0) (m : ℕ) :
    section83PairedTriangularTerm z q (5 * m + 4) =
      (1 - z ^ 4) * section83ATerm q ((m : ℤ) + 1) := by
  rw [section83PairedTriangularTerm_eq_coeff_mul]
  rw [show ((5 * m + 4 : ℕ) : ℤ) = 5 * (m : ℤ) + 4 by norm_num]
  rw [show (5 * (m : ℤ) + 4 + 1 : ℤ) = 5 * (m : ℤ) + 5 by ring]
  rw [neg_z_zpow_five_mul_coeff_four hz5 hz m]
  rw [q_zpow_section83A_pos]
  unfold section83ATerm
  rw [neg_one_zpow_natCast_add_one]
  ring

private lemma jacobiSeriesTerm_reparam_triangular
    (z q Y : ℂ) (hY : Y ≠ 0) (hYq : Y ^ 2 = q) (n : ℤ) :
    (-(z * Y) : ℂ) ^ n * Y ^ (n ^ 2) =
      section83TriangularTerm z q n := by
  unfold section83TriangularTerm
  have hbase : (-(z * Y) : ℂ) = (-z) * Y := by ring
  rw [hbase, mul_zpow]
  have hmul : Y ^ n * Y ^ (n ^ 2) = Y ^ (n + n ^ 2) := by
    rw [← zpow_add₀ hY]
  rw [show ((-z : ℂ) ^ n * Y ^ n) * Y ^ (n ^ 2) =
      (-z : ℂ) ^ n * (Y ^ n * Y ^ (n ^ 2)) by ring]
  rw [hmul, show n + n ^ 2 = n ^ 2 + n by ring]
  rw [zpow_sq_add_self_reparam q Y hYq n]

private theorem summable_section83TriangularTerm_of_ne_zero
    (z q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    Summable fun n : ℤ => section83TriangularTerm z q n := by
  obtain ⟨Y, hYq⟩ := IsAlgClosed.exists_pow_nat_eq q (n := 2) (by norm_num)
  have hY : Y ≠ 0 := by
    intro hY0
    apply hq0
    rw [← hYq, hY0]
    ring
  have hYnorm : ‖Y‖ < 1 := norm_of_sq_eq_lt_one hYq hq
  exact (PartI.Ch02.summable_jacobiInfiniteSeries_terms Y (-(z * Y)) hYnorm).congr
    fun n => jacobiSeriesTerm_reparam_triangular z q Y hY hYq n

private lemma norm_pow_five_lt_one {q : ℂ} (hq : ‖q‖ < 1) :
    ‖q ^ 5‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)

private theorem summable_section83ATerm (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun k : ℤ => section83ATerm q k := by
  have hq5 : ‖q ^ 5‖ < 1 := norm_pow_five_lt_one hq
  exact (summable_pentagonal023ThetaTerm (q ^ 5) hq5).congr fun k => by
    simpa [section83ATerm] using (pentagonal023_zpow_term_eq_thetaTerm (q ^ 5) k).symm

private theorem summable_section83BTerm (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun k : ℤ => section83BTerm q k := by
  have hq5 : ‖q ^ 5‖ < 1 := norm_pow_five_lt_one hq
  exact (summable_pentagonal014ThetaTerm (q ^ 5) hq5).congr fun k => by
    simpa [section83BTerm] using (pentagonal014_zpow_term_eq_thetaTerm (q ^ 5) k).symm

set_option maxHeartbeats 800000 in
private theorem section83ATerm_tsum_halves (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' m : ℕ, section83ATerm q (-(m : ℤ))) +
        (∑' m : ℕ, section83ATerm q ((m : ℤ) + 1)) =
      pentagonal023Analytic (q ^ 5) := by
  let b : ℤ → ℂ := fun k => section83ATerm q (-k)
  have hA : Summable fun k : ℤ => section83ATerm q k := summable_section83ATerm q hq
  have hb : Summable b := (Equiv.summable_iff (Equiv.neg ℤ)).mpr hA
  have hb_nat : Summable fun n : ℕ => b n :=
    hb.comp_injective Int.ofNat_injective
  have hb_neg : Summable fun n : ℕ => b (-(n + 1 : ℤ)) :=
    hb.comp_injective (fun a b h => by omega)
  have hsplit := tsum_of_nat_of_neg_add_one hb_nat hb_neg
  have hleft : (∑' k : ℤ, b k) = ∑' k : ℤ, section83ATerm q k := by
    exact (Equiv.neg ℤ).tsum_eq (section83ATerm q)
  rw [hleft] at hsplit
  calc
    (∑' m : ℕ, section83ATerm q (-(m : ℤ))) +
        (∑' m : ℕ, section83ATerm q ((m : ℤ) + 1))
        = (∑' n : ℕ, b n) + (∑' n : ℕ, b (-(n + 1 : ℤ))) := rfl
    _ = ∑' k : ℤ, section83ATerm q k := hsplit.symm
    _ = pentagonal023Analytic (q ^ 5) := rfl

set_option maxHeartbeats 800000 in
private theorem section83BTerm_tsum_halves (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' m : ℕ, section83BTerm q (-(m : ℤ))) +
        (∑' m : ℕ, section83BTerm q ((m : ℤ) + 1)) =
      pentagonal014Analytic (q ^ 5) := by
  let b : ℤ → ℂ := fun k => section83BTerm q (-k)
  have hB : Summable fun k : ℤ => section83BTerm q k := summable_section83BTerm q hq
  have hb : Summable b := (Equiv.summable_iff (Equiv.neg ℤ)).mpr hB
  have hb_nat : Summable fun n : ℕ => b n :=
    hb.comp_injective Int.ofNat_injective
  have hb_neg : Summable fun n : ℕ => b (-(n + 1 : ℤ)) :=
    hb.comp_injective (fun a b h => by omega)
  have hsplit := tsum_of_nat_of_neg_add_one hb_nat hb_neg
  have hleft : (∑' k : ℤ, b k) = ∑' k : ℤ, section83BTerm q k := by
    exact (Equiv.neg ℤ).tsum_eq (section83BTerm q)
  rw [hleft] at hsplit
  calc
    (∑' m : ℕ, section83BTerm q (-(m : ℤ))) +
        (∑' m : ℕ, section83BTerm q ((m : ℤ) + 1))
        = (∑' n : ℕ, b n) + (∑' n : ℕ, b (-(n + 1 : ℤ))) := rfl
    _ = ∑' k : ℤ, section83BTerm q k := hsplit.symm
    _ = pentagonal014Analytic (q ^ 5) := rfl

set_option maxHeartbeats 800000 in
private theorem section83_triangular_tsum_period_collapse_of_ne_zero
    {z q : ℂ} (hz5 : z ^ 5 = 1) (hz : z ≠ 0)
    (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (∑' n : ℤ, section83TriangularTerm z q n) =
      (1 - z ^ 4) * pentagonal023Analytic (q ^ 5) +
        (z ^ 3 - z) * q * pentagonal014Analytic (q ^ 5) := by
  let g : ℕ → ℂ := section83PairedTriangularTerm z q
  have hf : Summable fun n : ℤ => section83TriangularTerm z q n :=
    summable_section83TriangularTerm_of_ne_zero z q hq hq0
  have hg : Summable g := by
    change Summable fun n : ℕ =>
      section83TriangularTerm z q n + section83TriangularTerm z q (-((n : ℤ) + 1))
    exact hf.nat_add_neg_add_one
  have hpair :
      (∑' n : ℕ, g n) = ∑' n : ℤ, section83TriangularTerm z q n := by
    simpa [g, section83PairedTriangularTerm, section83TriangularTerm] using
      tsum_nat_add_neg_add_one hf
  have hsplit :
      (∑' n : ℕ, g n) =
        ∑ j : ZMod 5, ∑' m : ℕ, g (j.val + 5 * m) :=
    Nat.sumByResidueClasses (f := g) hg 5
  have h0 :
      (∑' m : ℕ, g (0 + 5 * m)) =
        (1 - z ^ 4) * (∑' m : ℕ, section83ATerm q (-(m : ℤ))) := by
    calc
      (∑' m : ℕ, g (0 + 5 * m))
          = ∑' m : ℕ, (1 - z ^ 4) * section83ATerm q (-(m : ℤ)) := by
            apply tsum_congr
            intro m
            change section83PairedTriangularTerm z q (0 + 5 * m) =
              (1 - z ^ 4) * section83ATerm q (-(m : ℤ))
            simpa [zero_add] using section83PairedTriangularTerm_residue_zero hz5 hz m
      _ = (1 - z ^ 4) * (∑' m : ℕ, section83ATerm q (-(m : ℤ))) := by
            rw [tsum_mul_left]
  have h1 :
      (∑' m : ℕ, g (1 + 5 * m)) =
        ((z ^ 3 - z) * q) * (∑' m : ℕ, section83BTerm q (-(m : ℤ))) := by
    calc
      (∑' m : ℕ, g (1 + 5 * m))
          = ∑' m : ℕ, ((z ^ 3 - z) * q) * section83BTerm q (-(m : ℤ)) := by
            apply tsum_congr
            intro m
            change section83PairedTriangularTerm z q (1 + 5 * m) =
              ((z ^ 3 - z) * q) * section83BTerm q (-(m : ℤ))
            rw [show 1 + 5 * m = 5 * m + 1 by omega]
            exact section83PairedTriangularTerm_residue_one hz5 hz hq0 m
      _ = ((z ^ 3 - z) * q) * (∑' m : ℕ, section83BTerm q (-(m : ℤ))) := by
            rw [tsum_mul_left]
  have h2 :
      (∑' m : ℕ, g (2 + 5 * m)) = 0 := by
    calc
      (∑' m : ℕ, g (2 + 5 * m))
          = ∑' _m : ℕ, (0 : ℂ) := by
            apply tsum_congr
            intro m
            change section83PairedTriangularTerm z q (2 + 5 * m) = 0
            rw [show 2 + 5 * m = 5 * m + 2 by omega]
            exact section83PairedTriangularTerm_residue_two hz5 hz m
      _ = 0 := by simp
  have h3 :
      (∑' m : ℕ, g (3 + 5 * m)) =
        ((z ^ 3 - z) * q) * (∑' m : ℕ, section83BTerm q ((m : ℤ) + 1)) := by
    calc
      (∑' m : ℕ, g (3 + 5 * m))
          = ∑' m : ℕ, ((z ^ 3 - z) * q) * section83BTerm q ((m : ℤ) + 1) := by
            apply tsum_congr
            intro m
            change section83PairedTriangularTerm z q (3 + 5 * m) =
              ((z ^ 3 - z) * q) * section83BTerm q ((m : ℤ) + 1)
            rw [show 3 + 5 * m = 5 * m + 3 by omega]
            exact section83PairedTriangularTerm_residue_three hz5 hz hq0 m
      _ = ((z ^ 3 - z) * q) * (∑' m : ℕ, section83BTerm q ((m : ℤ) + 1)) := by
            rw [tsum_mul_left]
  have h4 :
      (∑' m : ℕ, g (4 + 5 * m)) =
        (1 - z ^ 4) * (∑' m : ℕ, section83ATerm q ((m : ℤ) + 1)) := by
    calc
      (∑' m : ℕ, g (4 + 5 * m))
          = ∑' m : ℕ, (1 - z ^ 4) * section83ATerm q ((m : ℤ) + 1) := by
            apply tsum_congr
            intro m
            change section83PairedTriangularTerm z q (4 + 5 * m) =
              (1 - z ^ 4) * section83ATerm q ((m : ℤ) + 1)
            rw [show 4 + 5 * m = 5 * m + 4 by omega]
            exact section83PairedTriangularTerm_residue_four hz5 hz m
      _ = (1 - z ^ 4) * (∑' m : ℕ, section83ATerm q ((m : ℤ) + 1)) := by
            rw [tsum_mul_left]
  rw [← hpair, hsplit]
  have hsplit5 :
      (∑ j : ZMod 5, ∑' m : ℕ, g (j.val + 5 * m)) =
        (∑' m : ℕ, g (0 + 5 * m)) +
            (∑' m : ℕ, g (1 + 5 * m)) +
          (∑' m : ℕ, g (2 + 5 * m)) +
        (∑' m : ℕ, g (3 + 5 * m)) +
      (∑' m : ℕ, g (4 + 5 * m)) := by
    rw [← Equiv.sum_comp (ZMod.finEquiv 5).toEquiv
      (fun j : ZMod 5 => ∑' m : ℕ, g (j.val + 5 * m))]
    rw [Fin.sum_univ_five]
    have hval0 : (((ZMod.finEquiv 5).toEquiv (0 : Fin 5)).val) = 0 := by decide
    have hval1 : (((ZMod.finEquiv 5).toEquiv (1 : Fin 5)).val) = 1 := by decide
    have hval2 : (((ZMod.finEquiv 5).toEquiv (2 : Fin 5)).val) = 2 := by decide
    have hval3 : (((ZMod.finEquiv 5).toEquiv (3 : Fin 5)).val) = 3 := by decide
    have hval4 : (((ZMod.finEquiv 5).toEquiv (4 : Fin 5)).val) = 4 := by decide
    rw [hval0, hval1, hval2, hval3, hval4]
  rw [hsplit5]
  rw [h0, h1, h2, h3, h4]
  have hA := section83ATerm_tsum_halves q hq
  have hB := section83BTerm_tsum_halves q hq
  calc
    (1 - z ^ 4) * (∑' m : ℕ, section83ATerm q (-(m : ℤ))) +
          ((z ^ 3 - z) * q) * (∑' m : ℕ, section83BTerm q (-(m : ℤ))) +
        0 +
        ((z ^ 3 - z) * q) * (∑' m : ℕ, section83BTerm q ((m : ℤ) + 1)) +
        (1 - z ^ 4) * (∑' m : ℕ, section83ATerm q ((m : ℤ) + 1))
        =
      (1 - z ^ 4) *
          ((∑' m : ℕ, section83ATerm q (-(m : ℤ))) +
            (∑' m : ℕ, section83ATerm q ((m : ℤ) + 1))) +
        ((z ^ 3 - z) * q) *
          ((∑' m : ℕ, section83BTerm q (-(m : ℤ))) +
            (∑' m : ℕ, section83BTerm q ((m : ℤ) + 1))) := by ring
    _ = (1 - z ^ 4) * pentagonal023Analytic (q ^ 5) +
        ((z ^ 3 - z) * q) * pentagonal014Analytic (q ^ 5) := by
          rw [hA, hB]
    _ = (1 - z ^ 4) * pentagonal023Analytic (q ^ 5) +
        (z ^ 3 - z) * q * pentagonal014Analytic (q ^ 5) := by ring

lemma hasSum_coeff_mul_constQFactorPS_complex
    (P : ℂ⟦X⟧) (q p c : ℂ) (N : ℕ)
    (hP : HasSum (fun k : ℕ => P.coeff k * q ^ k) p) :
    HasSum (fun k : ℕ => (P * constQFactorPS c N).coeff k * q ^ k)
      (p * (1 - c * q ^ (N + 1))) := by
  let d : ℕ := N + 1
  let shift : ℕ → ℂ := fun k =>
    (if d ≤ k then (P * PowerSeries.C c).coeff (k - d) else 0) * q ^ k
  have htail : HasSum (fun n : ℕ => shift (n + d)) (p * c * q ^ d) := by
    have hmul : HasSum (fun n : ℕ => (P.coeff n * q ^ n) * (c * q ^ d))
        (p * (c * q ^ d)) :=
      hP.mul_right (c * q ^ d)
    simpa [mul_assoc] using hmul.congr_fun (by
      intro n
      dsimp [shift]
      rw [if_pos (by omega), show n + d - d = n by omega, PowerSeries.coeff_mul_C,
        pow_add]
      ring)
  have hshift_full : HasSum shift (p * c * q ^ d) := by
    have hfull := (hasSum_nat_add_iff d).mp htail
    have hzero : (∑ i ∈ Finset.range d, shift i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      dsimp [shift]
      rw [if_neg (Nat.not_le_of_gt (Finset.mem_range.mp hi))]
      simp
    simpa [hzero, mul_assoc] using hfull
  have hdiff : HasSum
      (fun k : ℕ => P.coeff k * q ^ k - shift k) (p - p * c * q ^ d) :=
    hP.sub hshift_full
  have hsum : HasSum
      (fun k : ℕ => (P * constQFactorPS c N).coeff k * q ^ k)
      (p - p * c * q ^ d) := by
    refine hdiff.congr_fun ?_
    intro k
    dsimp [shift, d]
    change
      (P * ((1 : ℂ⟦X⟧) - PowerSeries.C c * PowerSeries.X ^ (N + 1))).coeff k *
          q ^ k =
        P.coeff k * q ^ k -
          (if N + 1 ≤ k then (P * PowerSeries.C c).coeff (k - (N + 1)) else 0) *
            q ^ k
    rw [mul_sub, mul_one]
    rw [show P * (PowerSeries.C c * PowerSeries.X ^ (N + 1)) =
        (P * PowerSeries.C c) * PowerSeries.X ^ (N + 1) by ring]
    rw [map_sub, PowerSeries.coeff_mul_X_pow']
    by_cases hle : N + 1 ≤ k <;> ring
  have hval : p - p * c * q ^ d = p * (1 - c * q ^ (N + 1)) := by
    dsimp [d]
    ring
  simpa [hval] using hsum

lemma hasSum_coeff_mul_section83JTPTripleFactorPS_complex
    (P : ℂ⟦X⟧) (q p z : ℂ) (N : ℕ)
    (hP : HasSum (fun k : ℕ => P.coeff k * q ^ k) p) :
    HasSum (fun k : ℕ => (P * section83JTPTripleFactorPS z N).coeff k * q ^ k)
      (p * section83JTPTripleFactorAnalytic z q N) := by
  have h1 := hasSum_coeff_mul_constQFactorPS_complex P q p 1 N hP
  have h2 := hasSum_coeff_mul_constQFactorPS_complex (P * constQFactorPS 1 N) q
    (p * (1 - 1 * q ^ (N + 1))) z N h1
  have h3 := hasSum_coeff_mul_constQFactorPS_complex
    ((P * constQFactorPS 1 N) * constQFactorPS z N) q
    ((p * (1 - 1 * q ^ (N + 1))) * (1 - z * q ^ (N + 1))) z⁻¹ N h2
  convert h3 using 1
  · ext k
    rw [section83JTPTripleFactorPS]
    ring_nf
  · rw [section83JTPTripleFactorAnalytic, constQFactorAnalytic,
      constQFactorAnalytic, constQFactorAnalytic]
    ring

lemma hasSum_coeff_partial_section83JTPTripleFactorPS_complex
    (z q : ℂ) (N : ℕ) :
    HasSum (fun k : ℕ =>
        (∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n).coeff k * q ^ k)
      (∏ n ∈ Finset.range N, section83JTPTripleFactorAnalytic z q n) := by
  induction N with
  | zero =>
      simpa using (hasSum_single (0 : ℕ)
        (f := fun k : ℕ => ((1 : ℂ⟦X⟧).coeff k) * q ^ k)
        (by
          intro b hb
          simp [PowerSeries.coeff_one, hb]))
  | succ N ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      exact hasSum_coeff_mul_section83JTPTripleFactorPS_complex
        (∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n) q
        (∏ n ∈ Finset.range N, section83JTPTripleFactorAnalytic z q n) z N ih

theorem hasSum_section83JTPProductPS_coeff_mul_pow_of_norm_lt_one_sixteenth
    (z q : ℂ) (hz : ‖z‖ ≤ 1) (hzinv : ‖z⁻¹‖ ≤ 1)
    (hq : ‖q‖ < (1 / 16 : ℝ)) :
    HasSum (fun k : ℕ => (section83JTPProductPS z).coeff k * q ^ k)
      (section83JTPProductAnalytic z q) := by
  let f : ℕ → ℕ → ℂ := fun N k =>
    (∏ n ∈ Finset.range N, section83JTPTripleFactorPS z n).coeff k * q ^ k
  let g : ℕ → ℂ := fun k => (section83JTPProductPS z).coeff k * q ^ k
  let bound : ℕ → ℝ := fun k => (8 : ℝ) ^ (k + 1) * ‖q‖ ^ k
  have hbound_sum : Summable bound :=
    summable_pentagonalProduct_bound_of_norm_lt_one_sixteenth hq
  have hab : ∀ k : ℕ, Tendsto (fun N : ℕ => f N k) atTop (𝓝 (g k)) := by
    intro k
    apply tendsto_nhds_of_eventually_eq
    refine Filter.eventually_atTop.mpr ⟨k + 1, ?_⟩
    intro N hN
    dsimp [f, g]
    rw [partial_prod_section83JTPTripleFactorPS_coeff_eq z k (k + 1) N
      (by omega) hN]
    rw [← coeff_section83JTPProductPS_eq_coeff_partial z k]
  have h_bound : ∀ᶠ N in atTop, ∀ k : ℕ, ‖f N k‖ ≤ bound k :=
    Filter.Eventually.of_forall fun N => by
      intro k
      dsimp [f, bound]
      rw [norm_mul, norm_pow]
      gcongr
      exact norm_coeff_partial_section83JTPTripleFactorPS_complex_le_uniform
        z hz hzinv N k
  have h_tsum : Tendsto (fun N : ℕ => ∑' k : ℕ, f N k) atTop
      (𝓝 (∑' k : ℕ, g k)) :=
    tendsto_tsum_of_dominated_convergence hbound_sum hab h_bound
  have h_finite : ∀ N : ℕ, (∑' k : ℕ, f N k) =
      ∏ n ∈ Finset.range N, section83JTPTripleFactorAnalytic z q n := by
    intro N
    exact (hasSum_coeff_partial_section83JTPTripleFactorPS_complex z q N).tsum_eq
  have hq_unit : ‖q‖ < 1 := by nlinarith [hq]
  have h_partial := tendsto_section83JTPProductAnalytic_partial z q hq_unit
  have h_tsum_analytic : Tendsto (fun N : ℕ => ∑' k : ℕ, f N k) atTop
      (𝓝 (section83JTPProductAnalytic z q)) :=
    Filter.Tendsto.congr (fun N => (h_finite N).symm) h_partial
  have h_eq : (∑' k : ℕ, g k) = section83JTPProductAnalytic z q :=
    tendsto_nhds_unique h_tsum h_tsum_analytic
  have hg_summable : Summable g := by
    refine hbound_sum.of_norm_bounded ?_
    intro k
    dsimp [g, bound]
    rw [norm_mul, norm_pow]
    gcongr
    exact norm_coeff_section83JTPProductPS_complex_le z hz hzinv k
  simpa [g, h_eq] using hg_summable.hasSum

noncomputable def section83JTPProductCoeffFMLS (z : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (section83JTPProductPS z).coeff n)

theorem one_sixteenth_le_section83JTPProductCoeffFMLS_radius
    (z : ℂ) (hz : ‖z‖ ≤ 1) (hzinv : ‖z⁻¹‖ ≤ 1) :
    ((1 / 16 : NNReal) : ENNReal) ≤ (section83JTPProductCoeffFMLS z).radius := by
  refine FormalMultilinearSeries.le_radius_of_bound
    (section83JTPProductCoeffFMLS z) 8 (r := (1 / 16 : NNReal)) ?_
  intro n
  rw [section83JTPProductCoeffFMLS, FormalMultilinearSeries.ofScalars_norm]
  calc
    ‖(section83JTPProductPS z).coeff n‖ * ((1 / 16 : NNReal) : ℝ) ^ n
        ≤ (8 : ℝ) ^ (n + 1) * ((1 / 16 : NNReal) : ℝ) ^ n := by
        gcongr
        exact norm_coeff_section83JTPProductPS_complex_le z hz hzinv n
    _ = 8 * ((1 / 2 : ℝ) ^ n) := by
        rw [pow_succ]
        rw [show (8 : ℝ) ^ n * 8 * ((1 / 16 : NNReal) : ℝ) ^ n =
          8 * (((8 : ℝ) * ((1 / 16 : NNReal) : ℝ)) ^ n) by
            rw [mul_pow]
            ring]
        norm_num
    _ ≤ 8 := by
        have hpow : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith

theorem hasFPowerSeriesOnBall_section83JTPProductAnalytic_productCoeff_small
    (z : ℂ) (hz : ‖z‖ ≤ 1) (hzinv : ‖z⁻¹‖ ≤ 1) :
    HasFPowerSeriesOnBall (section83JTPProductAnalytic z)
      (section83JTPProductCoeffFMLS z) 0 ((1 / 16 : NNReal) : ENNReal) := by
  refine ⟨one_sixteenth_le_section83JTPProductCoeffFMLS_radius z hz hzinv, by norm_num, ?_⟩
  intro y hy
  rw [zero_add]
  have hy_norm : ‖y‖ < (1 / 16 : ℝ) := by
    have h_radius : (((1 / 16 : NNReal) : ENNReal) =
        ENNReal.ofReal (1 / 16 : ℝ)) := by
      rw [ENNReal.coe_nnreal_eq]
      congr
    have h_ball : y ∈ Metric.ball (0 : ℂ) (1 / 16 : ℝ) := by
      rw [h_radius, Metric.emetric_ball] at hy
      exact hy
    have hdist : dist y (0 : ℂ) < (1 / 16 : ℝ) := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at hdist
  have h := hasSum_section83JTPProductPS_coeff_mul_pow_of_norm_lt_one_sixteenth
    z y hz hzinv hy_norm
  convert h using 1
  funext n
  rw [section83JTPProductCoeffFMLS, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

/-! ### Keystone-style transfer for the two §8.3 factors

The declarations below deliberately isolate the remaining analytic theorem:
the RHS period-collapse Taylor expansion must be proved for the same analytic
product.  Once that is available, `eq_formalMultilinearSeries` gives the formal
identity exactly as in `JTP_FormalPS_Pentagonal`.
-/

noncomputable def section83RhsPair14FMLS (ζ : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (section83_rhs_pair14 ζ).coeff n)

noncomputable def section83RhsPair23FMLS (ζ : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (section83_rhs_pair23 ζ).coeff n)

lemma norm_eq_one_of_primitive_fifth_complex {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    ‖ζ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by norm_num)

lemma norm_inv_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    ‖z⁻¹‖ = 1 := by
  rw [norm_inv, hz]
  norm_num

private lemma section83JTPProductAnalytic_zero (z : ℂ) :
    section83JTPProductAnalytic z 0 = 1 := by
  simp [section83JTPProductAnalytic, constQFactorAnalytic, tprod_one]

private lemma inv_eq_pow_four_of_pow_five {z : ℂ} (hz5 : z ^ 5 = 1) :
    z⁻¹ = z ^ 4 := by
  apply inv_eq_of_mul_eq_one_right
  calc
    z * z ^ 4 = z ^ 5 := by ring
    _ = 1 := hz5

private lemma one_sub_pow_four_ne_zero_of_primitive_fifth
    {z : ℂ} (hz : IsPrimitiveRoot z 5) :
    1 - z ^ 4 ≠ 0 := by
  intro h
  have hz4 : z ^ 4 = 1 := (sub_eq_zero.mp h).symm
  exact hz.pow_ne_one_of_pos_of_lt (by norm_num : 4 ≠ 0) (by norm_num : 4 < 5) hz4

private lemma zeta_three_sub_eq_one_sub_pow_four_mul_beta
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    ζ ^ 3 - ζ = (1 - ζ ^ 4) * quinticPeriodBeta ζ := by
  unfold quinticPeriodBeta
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have h6 : ζ ^ 6 = ζ := by
    calc
      ζ ^ 6 = ζ ^ (5 + 1) := by norm_num
      _ = ζ ^ 5 * ζ := by rw [pow_add, pow_one]
      _ = ζ := by rw [h5]; ring
  have h7 : ζ ^ 7 = ζ ^ 2 := by
    calc
      ζ ^ 7 = ζ ^ (5 + 2) := by norm_num
      _ = ζ ^ 5 * ζ ^ 2 := by rw [pow_add]
      _ = ζ ^ 2 := by rw [h5]; ring
  calc
    ζ ^ 3 - ζ = ζ ^ 2 + ζ ^ 3 - ζ ^ 6 - ζ ^ 7 := by rw [h6, h7]; ring
    _ = (1 - ζ ^ 4) * (ζ ^ 2 + ζ ^ 3) := by ring

private lemma zeta_sq_three_sub_eq_one_sub_pow_four_mul_alpha
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (ζ ^ 2) ^ 3 - ζ ^ 2 =
      (1 - (ζ ^ 2) ^ 4) * quinticPeriodAlpha ζ := by
  unfold quinticPeriodAlpha
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have h6 : ζ ^ 6 = ζ := by
    calc
      ζ ^ 6 = ζ ^ (5 + 1) := by norm_num
      _ = ζ ^ 5 * ζ := by rw [pow_add, pow_one]
      _ = ζ := by rw [h5]; ring
  have h9 : ζ ^ 9 = ζ ^ 4 := by
    calc
      ζ ^ 9 = ζ ^ (5 + 4) := by norm_num
      _ = ζ ^ 5 * ζ ^ 4 := by rw [pow_add]
      _ = ζ ^ 4 := by rw [h5]; ring
  have h12 : ζ ^ 12 = ζ ^ 2 := by
    calc
      ζ ^ 12 = ζ ^ (5 + 7) := by norm_num
      _ = ζ ^ 5 * ζ ^ 7 := by rw [pow_add]
      _ = ζ ^ 7 := by rw [h5]; ring
      _ = ζ ^ (5 + 2) := by norm_num
      _ = ζ ^ 5 * ζ ^ 2 := by rw [pow_add]
      _ = ζ ^ 2 := by rw [h5]; ring
  calc
    (ζ ^ 2) ^ 3 - ζ ^ 2 = ζ - ζ ^ 2 := by rw [show (ζ ^ 2) ^ 3 = ζ ^ 6 by ring, h6]
    _ = ζ + ζ ^ 4 - ζ ^ 9 - ζ ^ 12 := by rw [h9, h12]; ring
    _ = (1 - (ζ ^ 2) ^ 4) * (ζ + ζ ^ 4) := by ring

private theorem section83JTPProductAnalytic_eq_rhs_pair14_eval
    {ζ q : ℂ} (hζ : IsPrimitiveRoot ζ 5) (hq : ‖q‖ < 1) :
    section83JTPProductAnalytic ζ q =
      pentagonal023Analytic (q ^ 5) +
        quinticPeriodBeta ζ * q * pentagonal014Analytic (q ^ 5) := by
  by_cases hq0 : q = 0
  · subst q
    simp [section83JTPProductAnalytic_zero, pentagonal023Analytic_zero]
  · have hz0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
    have htri :=
      one_sub_inv_mul_section83JTPProductAnalytic_eq_triangular_tsum_of_ne_zero
        ζ q hz0 hq hq0
    have hcollapse :=
      section83_triangular_tsum_period_collapse_of_ne_zero
        hζ.pow_eq_one hz0 hq hq0
    have hcollapse' :
        (∑' n : ℤ, (-ζ) ^ n * q ^ (n * (n + 1) / 2)) =
          (1 - ζ ^ 4) * pentagonal023Analytic (q ^ 5) +
            (ζ ^ 3 - ζ) * q * pentagonal014Analytic (q ^ 5) := by
      simpa [section83TriangularTerm] using hcollapse
    rw [hcollapse'] at htri
    have hinv : ζ⁻¹ = ζ ^ 4 := inv_eq_pow_four_of_pow_five hζ.pow_eq_one
    have hbeta := zeta_three_sub_eq_one_sub_pow_four_mul_beta hζ
    rw [hinv, hbeta] at htri
    have hscalar : 1 - ζ ^ 4 ≠ 0 :=
      one_sub_pow_four_ne_zero_of_primitive_fifth hζ
    apply mul_left_cancel₀ hscalar
    calc
      (1 - ζ ^ 4) * section83JTPProductAnalytic ζ q =
          (1 - ζ ^ 4) * pentagonal023Analytic (q ^ 5) +
            (1 - ζ ^ 4) * quinticPeriodBeta ζ * q *
              pentagonal014Analytic (q ^ 5) := by
          simpa [mul_assoc] using htri
      _ = (1 - ζ ^ 4) *
          (pentagonal023Analytic (q ^ 5) +
            quinticPeriodBeta ζ * q * pentagonal014Analytic (q ^ 5)) := by ring

private theorem section83JTPProductAnalytic_eq_rhs_pair23_eval
    {ζ q : ℂ} (hζ : IsPrimitiveRoot ζ 5) (hq : ‖q‖ < 1) :
    section83JTPProductAnalytic (ζ ^ 2) q =
      pentagonal023Analytic (q ^ 5) +
        quinticPeriodAlpha ζ * q * pentagonal014Analytic (q ^ 5) := by
  by_cases hq0 : q = 0
  · subst q
    simp [section83JTPProductAnalytic_zero, pentagonal023Analytic_zero]
  · have hζ2 : IsPrimitiveRoot (ζ ^ 2) 5 :=
      hζ.pow_of_coprime 2 (by norm_num)
    have hz0 : ζ ^ 2 ≠ 0 := hζ2.ne_zero (by norm_num)
    have htri :=
      one_sub_inv_mul_section83JTPProductAnalytic_eq_triangular_tsum_of_ne_zero
        (ζ ^ 2) q hz0 hq hq0
    have hcollapse :=
      section83_triangular_tsum_period_collapse_of_ne_zero
        hζ2.pow_eq_one hz0 hq hq0
    have hcollapse' :
        (∑' n : ℤ, (-(ζ ^ 2)) ^ n * q ^ (n * (n + 1) / 2)) =
          (1 - (ζ ^ 2) ^ 4) * pentagonal023Analytic (q ^ 5) +
            ((ζ ^ 2) ^ 3 - ζ ^ 2) * q * pentagonal014Analytic (q ^ 5) := by
      simpa [section83TriangularTerm] using hcollapse
    rw [hcollapse'] at htri
    have hinv : (ζ ^ 2)⁻¹ = (ζ ^ 2) ^ 4 :=
      inv_eq_pow_four_of_pow_five hζ2.pow_eq_one
    have halpha := zeta_sq_three_sub_eq_one_sub_pow_four_mul_alpha hζ
    rw [hinv, halpha] at htri
    have hscalar : 1 - (ζ ^ 2) ^ 4 ≠ 0 :=
      one_sub_pow_four_ne_zero_of_primitive_fifth hζ2
    apply mul_left_cancel₀ hscalar
    calc
      (1 - (ζ ^ 2) ^ 4) * section83JTPProductAnalytic (ζ ^ 2) q =
          (1 - (ζ ^ 2) ^ 4) * pentagonal023Analytic (q ^ 5) +
            (1 - (ζ ^ 2) ^ 4) * quinticPeriodAlpha ζ * q *
              pentagonal014Analytic (q ^ 5) := by
          simpa [mul_assoc] using htri
      _ = (1 - (ζ ^ 2) ^ 4) *
          (pentagonal023Analytic (q ^ 5) +
            quinticPeriodAlpha ζ * q * pentagonal014Analytic (q ^ 5)) := by ring

@[simp] private theorem coeff_section83A_complex (n : ℕ) :
    (section83A ℂ).coeff n =
      if 5 ∣ n then pentagonal023Coeff ℂ (n / 5) else 0 := by
  rw [section83A, PowerSeries.coeff_expand]
  by_cases hdiv : 5 ∣ n <;> simp [hdiv]

@[simp] private theorem coeff_section83B_complex (n : ℕ) :
    (section83B ℂ).coeff n =
      if 5 ∣ n then pentagonal014Coeff ℂ (n / 5) else 0 := by
  rw [section83B, PowerSeries.coeff_expand]
  by_cases hdiv : 5 ∣ n <;> simp [hdiv]

private theorem hasSum_section83A_coeff_mul_pow (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (section83A ℂ).coeff n * q ^ n)
      (pentagonal023Analytic (q ^ 5)) := by
  let e : ℕ → ℕ := fun k => 5 * k
  let f : ℕ → ℂ := fun n => (section83A ℂ).coeff n * q ^ n
  have he : Function.Injective e := by
    intro a b h
    dsimp [e] at h
    omega
  have hzero : ∀ n, n ∉ Set.range e → f n = 0 := by
    intro n hn
    dsimp [f]
    have hnot : ¬ 5 ∣ n := by
      intro hdiv
      rcases hdiv with ⟨k, hk⟩
      apply hn
      refine ⟨k, ?_⟩
      dsimp [e]
      omega
    simp [hnot]
  have hcomp : HasSum (f ∘ e) (pentagonal023Analytic (q ^ 5)) := by
    have hbase := hasSum_pentagonal023Coeff_mul_pow (q ^ 5) (norm_pow_five_lt_one hq)
    simpa [f, e, Function.comp_def, pentagonal023Analytic_eq_thetaNat, pow_mul] using hbase
  exact (he.hasSum_iff hzero).mp hcomp

private theorem hasSum_section83B_coeff_mul_pow (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (section83B ℂ).coeff n * q ^ n)
      (pentagonal014Analytic (q ^ 5)) := by
  let e : ℕ → ℕ := fun k => 5 * k
  let f : ℕ → ℂ := fun n => (section83B ℂ).coeff n * q ^ n
  have he : Function.Injective e := by
    intro a b h
    dsimp [e] at h
    omega
  have hzero : ∀ n, n ∉ Set.range e → f n = 0 := by
    intro n hn
    dsimp [f]
    have hnot : ¬ 5 ∣ n := by
      intro hdiv
      rcases hdiv with ⟨k, hk⟩
      apply hn
      refine ⟨k, ?_⟩
      dsimp [e]
      omega
    simp [hnot]
  have hcomp : HasSum (f ∘ e) (pentagonal014Analytic (q ^ 5)) := by
    have hbase := hasSum_pentagonal014Coeff_mul_pow (q ^ 5) (norm_pow_five_lt_one hq)
    simpa [f, e, Function.comp_def, pentagonal014Analytic_eq_thetaNat, pow_mul] using hbase
  exact (he.hasSum_iff hzero).mp hcomp

private theorem hasSum_X_mul_section83B_coeff_mul_pow (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (PowerSeries.X * section83B ℂ).coeff n * q ^ n)
      (q * pentagonal014Analytic (q ^ 5)) := by
  let f : ℕ → ℂ := fun n => (PowerSeries.X * section83B ℂ).coeff n * q ^ n
  have htail : HasSum (fun n : ℕ => f (n + 1))
      (q * pentagonal014Analytic (q ^ 5)) := by
    have hB := hasSum_section83B_coeff_mul_pow q hq
    have hmul := HasSum.mul_left q hB
    convert hmul using 1
    funext n
    dsimp [f]
    rw [PowerSeries.coeff_succ_X_mul]
    rw [show q ^ (n + 1) = q * q ^ n by rw [pow_succ']]
    ring
  have hfull := (hasSum_nat_add_iff (f := f) 1).mp htail
  have hf0 : f 0 = 0 := by
    dsimp [f]
    rw [PowerSeries.coeff_zero_X_mul]
    simp
  simpa [hf0] using hfull

private theorem hasSum_section83_rhs_pair14_coeff_mul_pow
    (ζ q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (section83_rhs_pair14 ζ).coeff n * q ^ n)
    (pentagonal023Analytic (q ^ 5) +
        quinticPeriodBeta ζ * q * pentagonal014Analytic (q ^ 5)) := by
  have hA := hasSum_section83A_coeff_mul_pow q hq
  have hB := HasSum.mul_left (quinticPeriodBeta ζ)
    (hasSum_X_mul_section83B_coeff_mul_pow q hq)
  have hsum := hA.add hB
  convert hsum using 1
  · funext n
    rw [section83_rhs_pair14, map_add]
    rw [show PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X * section83B ℂ =
        PowerSeries.C (quinticPeriodBeta ζ) * (PowerSeries.X * section83B ℂ) by ring]
    rw [PowerSeries.coeff_C_mul]
    ring
  · ring

private theorem hasSum_section83_rhs_pair23_coeff_mul_pow
    (ζ q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (section83_rhs_pair23 ζ).coeff n * q ^ n)
      (pentagonal023Analytic (q ^ 5) +
        quinticPeriodAlpha ζ * q * pentagonal014Analytic (q ^ 5)) := by
  have hA := hasSum_section83A_coeff_mul_pow q hq
  have hB := HasSum.mul_left (quinticPeriodAlpha ζ)
    (hasSum_X_mul_section83B_coeff_mul_pow q hq)
  have hsum := hA.add hB
  convert hsum using 1
  · funext n
    rw [section83_rhs_pair23, map_add]
    rw [show PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X * section83B ℂ =
        PowerSeries.C (quinticPeriodAlpha ζ) * (PowerSeries.X * section83B ℂ) by ring]
    rw [PowerSeries.coeff_C_mul]
    ring
  · ring

private theorem one_le_section83RhsPair14FMLS_radius (ζ : ℂ) :
    (1 : ENNReal) ≤ (section83RhsPair14FMLS ζ).radius := by
  rw [show (1 : ENNReal) = ((1 : NNReal) : ENNReal) by simp]
  apply ENNReal.le_of_forall_nnreal_lt
  intro s hs
  rw [ENNReal.coe_lt_coe] at hs
  have hq_norm : ‖((s : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
    exact_mod_cast hs
  have h_sum := (hasSum_section83_rhs_pair14_coeff_mul_pow
    ζ ((s : ℝ) : ℂ) hq_norm).summable
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have h_sum_norm := h_sum.norm
  have h_eq :
      (fun n : ℕ => ‖section83RhsPair14FMLS ζ n‖ * (s : ℝ) ^ n) =
        (fun n : ℕ => ‖(section83_rhs_pair14 ζ).coeff n * (((s : ℝ) : ℂ)) ^ n‖) := by
    funext n
    rw [section83RhsPair14FMLS, FormalMultilinearSeries.ofScalars_norm]
    rw [norm_mul, norm_pow]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
  rw [h_eq]
  exact h_sum_norm

private theorem one_le_section83RhsPair23FMLS_radius (ζ : ℂ) :
    (1 : ENNReal) ≤ (section83RhsPair23FMLS ζ).radius := by
  rw [show (1 : ENNReal) = ((1 : NNReal) : ENNReal) by simp]
  apply ENNReal.le_of_forall_nnreal_lt
  intro s hs
  rw [ENNReal.coe_lt_coe] at hs
  have hq_norm : ‖((s : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
    exact_mod_cast hs
  have h_sum := (hasSum_section83_rhs_pair23_coeff_mul_pow
    ζ ((s : ℝ) : ℂ) hq_norm).summable
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  have h_sum_norm := h_sum.norm
  have h_eq :
      (fun n : ℕ => ‖section83RhsPair23FMLS ζ n‖ * (s : ℝ) ^ n) =
        (fun n : ℕ => ‖(section83_rhs_pair23 ζ).coeff n * (((s : ℝ) : ℂ)) ^ n‖) := by
    funext n
    rw [section83RhsPair23FMLS, FormalMultilinearSeries.ofScalars_norm]
    rw [norm_mul, norm_pow]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
  rw [h_eq]
  exact h_sum_norm

private theorem hasFPowerSeriesOnBall_section83_rhs_pair14
    (ζ : ℂ) :
    HasFPowerSeriesOnBall
      (fun q : ℂ => pentagonal023Analytic (q ^ 5) +
        quinticPeriodBeta ζ * q * pentagonal014Analytic (q ^ 5))
      (section83RhsPair14FMLS ζ) 0 1 := by
  refine ⟨one_le_section83RhsPair14FMLS_radius ζ, by positivity, ?_⟩
  intro y hy
  rw [zero_add]
  have hy_norm : ‖y‖ < 1 := by
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    have h_ball : y ∈ Metric.ball (0 : ℂ) 1 := by
      rw [h1, Metric.emetric_ball] at hy
      exact hy
    have h2 : dist y (0 : ℂ) < 1 := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at h2
  have h := hasSum_section83_rhs_pair14_coeff_mul_pow ζ y hy_norm
  convert h using 1
  funext n
  rw [section83RhsPair14FMLS, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

private theorem hasFPowerSeriesOnBall_section83_rhs_pair23
    (ζ : ℂ) :
    HasFPowerSeriesOnBall
      (fun q : ℂ => pentagonal023Analytic (q ^ 5) +
        quinticPeriodAlpha ζ * q * pentagonal014Analytic (q ^ 5))
      (section83RhsPair23FMLS ζ) 0 1 := by
  refine ⟨one_le_section83RhsPair23FMLS_radius ζ, by positivity, ?_⟩
  intro y hy
  rw [zero_add]
  have hy_norm : ‖y‖ < 1 := by
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    have h_ball : y ∈ Metric.ball (0 : ℂ) 1 := by
      rw [h1, Metric.emetric_ball] at hy
      exact hy
    have h2 : dist y (0 : ℂ) < 1 := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at h2
  have h := hasSum_section83_rhs_pair23_coeff_mul_pow ζ y hy_norm
  convert h using 1
  funext n
  rw [section83RhsPair23FMLS, FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]

theorem hasFPowerSeriesOnBall_section83JTPProductAnalytic_rhs_pair14
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    HasFPowerSeriesOnBall (section83JTPProductAnalytic ζ)
      (section83RhsPair14FMLS ζ) 0 1 := by
  refine (hasFPowerSeriesOnBall_section83_rhs_pair14 ζ).congr ?_
  intro q hq
  have hq_norm : ‖q‖ < 1 := by
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    have h_ball : q ∈ Metric.ball (0 : ℂ) 1 := by
      rw [h1, Metric.emetric_ball] at hq
      exact hq
    have h2 : dist q (0 : ℂ) < 1 := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at h2
  exact (section83JTPProductAnalytic_eq_rhs_pair14_eval hζ hq_norm).symm

theorem hasFPowerSeriesOnBall_section83JTPProductAnalytic_rhs_pair23
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    HasFPowerSeriesOnBall (section83JTPProductAnalytic (ζ ^ 2))
      (section83RhsPair23FMLS ζ) 0 1 := by
  refine (hasFPowerSeriesOnBall_section83_rhs_pair23 ζ).congr ?_
  intro q hq
  have hq_norm : ‖q‖ < 1 := by
    have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := by simp
    have h_ball : q ∈ Metric.ball (0 : ℂ) 1 := by
      rw [h1, Metric.emetric_ball] at hq
      exact hq
    have h2 : dist q (0 : ℂ) < 1 := Metric.mem_ball.mp h_ball
    rwa [dist_zero_right] at h2
  exact (section83JTPProductAnalytic_eq_rhs_pair23_eval hζ hq_norm).symm

theorem section83JTPProductPS_eq_rhs_pair14_of_rhs_taylor
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (hrhs :
      HasFPowerSeriesOnBall (section83JTPProductAnalytic ζ)
        (section83RhsPair14FMLS ζ) 0 1) :
    section83JTPProductPS ζ = section83_rhs_pair14 ζ := by
  have hz : ‖ζ‖ ≤ 1 := le_of_eq (norm_eq_one_of_primitive_fifth_complex hζ)
  have hzinv : ‖ζ⁻¹‖ ≤ 1 :=
    le_of_eq (norm_inv_eq_one_of_norm_eq_one (norm_eq_one_of_primitive_fifth_complex hζ))
  have h_fps_prod : HasFPowerSeriesAt (section83JTPProductAnalytic ζ)
      (section83JTPProductCoeffFMLS ζ) 0 :=
    ⟨((1 / 16 : NNReal) : ENNReal),
      hasFPowerSeriesOnBall_section83JTPProductAnalytic_productCoeff_small ζ hz hzinv⟩
  have h_fps_rhs : HasFPowerSeriesAt (section83JTPProductAnalytic ζ)
      (section83RhsPair14FMLS ζ) 0 :=
    ⟨1, hrhs⟩
  have h_unique : section83JTPProductCoeffFMLS ζ = section83RhsPair14FMLS ζ :=
    h_fps_prod.eq_formalMultilinearSeries h_fps_rhs
  ext n
  have h_prod_coeff : (section83JTPProductCoeffFMLS ζ).coeff n =
      (section83JTPProductPS ζ).coeff n := by
    simp [section83JTPProductCoeffFMLS]
  have h_rhs_coeff : (section83RhsPair14FMLS ζ).coeff n =
      (section83_rhs_pair14 ζ).coeff n := by
    simp [section83RhsPair14FMLS]
  rw [← h_prod_coeff, ← h_rhs_coeff, h_unique]

theorem section83JTPProductPS_eq_rhs_pair23_of_rhs_taylor
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (hrhs :
      HasFPowerSeriesOnBall (section83JTPProductAnalytic (ζ ^ 2))
        (section83RhsPair23FMLS ζ) 0 1) :
    section83JTPProductPS (ζ ^ 2) = section83_rhs_pair23 ζ := by
  have hznorm : ‖ζ ^ 2‖ = 1 := by
    rw [norm_pow, norm_eq_one_of_primitive_fifth_complex hζ, one_pow]
  have hz : ‖ζ ^ 2‖ ≤ 1 := le_of_eq hznorm
  have hzinv : ‖(ζ ^ 2)⁻¹‖ ≤ 1 :=
    le_of_eq (norm_inv_eq_one_of_norm_eq_one hznorm)
  have h_fps_prod : HasFPowerSeriesAt (section83JTPProductAnalytic (ζ ^ 2))
      (section83JTPProductCoeffFMLS (ζ ^ 2)) 0 :=
    ⟨((1 / 16 : NNReal) : ENNReal),
      hasFPowerSeriesOnBall_section83JTPProductAnalytic_productCoeff_small
        (ζ ^ 2) hz hzinv⟩
  have h_fps_rhs : HasFPowerSeriesAt (section83JTPProductAnalytic (ζ ^ 2))
      (section83RhsPair23FMLS ζ) 0 :=
    ⟨1, hrhs⟩
  have h_unique : section83JTPProductCoeffFMLS (ζ ^ 2) = section83RhsPair23FMLS ζ :=
    h_fps_prod.eq_formalMultilinearSeries h_fps_rhs
  ext n
  have h_prod_coeff : (section83JTPProductCoeffFMLS (ζ ^ 2)).coeff n =
      (section83JTPProductPS (ζ ^ 2)).coeff n := by
    simp [section83JTPProductCoeffFMLS]
  have h_rhs_coeff : (section83RhsPair23FMLS ζ).coeff n =
      (section83_rhs_pair23 ζ).coeff n := by
    simp [section83RhsPair23FMLS]
  rw [← h_prod_coeff, ← h_rhs_coeff, h_unique]

theorem section83JTPProductPS_eq_rhs_pair14
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    section83JTPProductPS ζ = section83_rhs_pair14 ζ :=
  section83JTPProductPS_eq_rhs_pair14_of_rhs_taylor hζ
    (hasFPowerSeriesOnBall_section83JTPProductAnalytic_rhs_pair14 hζ)

theorem section83JTPProductPS_eq_rhs_pair23
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    section83JTPProductPS (ζ ^ 2) = section83_rhs_pair23 ζ :=
  section83JTPProductPS_eq_rhs_pair23_of_rhs_taylor hζ
    (hasFPowerSeriesOnBall_section83JTPProductAnalytic_rhs_pair23 hζ)

/-! ## Infinite fifth-root product collapse -/

private def finFiveSigmaNatEquivNat : (Sigma fun _ : Fin 5 => ℕ) ≃ ℕ where
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

private theorem continuous_scaleX_complex (c : ℂ) :
    Continuous (scaleX c : ℂ⟦X⟧ → ℂ⟦X⟧) := by
  rw [continuous_iff_continuousAt]
  intro φ
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp_rw [coeff_scaleX]
  exact ((PowerSeries.WithPiTopology.continuous_coeff ℂ n).tendsto φ).mul
    tendsto_const_nhds

private theorem scaleX_qPochInfPS_eq_tprod_complex (c : ℂ) :
    scaleX c (qPochInfPS ℂ) = ∏' n : ℕ, scaleX c (oneSubXPow ℂ n) := by
  rw [qPochInfPS_eq_tprod ℂ]
  rw [(multipliable_one_sub_X_pow_succ ℂ).map_tprod (scaleX c)
    (continuous_scaleX_complex c)]
  rfl

private theorem hasProd_scaleX_oneSubXPow_complex (c : ℂ) :
    HasProd (fun n : ℕ => scaleX c (oneSubXPow ℂ n))
      (scaleX c (qPochInfPS ℂ)) := by
  have hbase : HasProd (fun n : ℕ => oneSubXPow ℂ n) (qPochInfPS ℂ) := by
    rw [qPochInfPS_eq_tprod ℂ]
    exact (multipliable_one_sub_X_pow_succ ℂ).hasProd
  exact hbase.map (scaleX c) (continuous_scaleX_complex c)

private noncomputable def fifthCollapseFactor (n : ℕ) : ℂ⟦X⟧ :=
  if 5 ∣ n + 1 then
    (oneSubXPow ℂ n)^5
  else
    (1 : ℂ⟦X⟧) - PowerSeries.X ^ (5 * (n + 1))

private theorem hasProd_fifthCollapseFactor_of_scaleX
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    HasProd fifthCollapseFactor
      (∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) := by
  have hprod :
      HasProd
        (fun n : ℕ => ∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (oneSubXPow ℂ n))
        (∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) := by
    exact hasProd_prod (s := (Finset.univ : Finset (Fin 5)))
      (f := fun (j : Fin 5) (n : ℕ) =>
        scaleX (ζ ^ (j : ℕ)) (oneSubXPow ℂ n))
      (a := fun j : Fin 5 => scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ))
      (by
        intro j _hj
        exact hasProd_scaleX_oneSubXPow_complex (ζ ^ (j : ℕ)))
  exact hprod.congr_fun fun n =>
    (prod_scaleX_oneSubXPow_fifth (R := ℂ) hζ n).symm

private theorem hasProd_apFactorPS_pow_five_complex :
    HasProd (fun n : ℕ => (apFactorPS ℂ 5 5 n)^5)
      ((qPochAPPS ℂ 5 5)^5) := by
  have h := hasProd_prod (s := (Finset.univ : Finset (Fin 5)))
    (f := fun (_ : Fin 5) (n : ℕ) => apFactorPS ℂ 5 5 n)
    (a := fun (_ : Fin 5) => qPochAPPS ℂ 5 5)
    (by
      intro _ _
      exact hasProd_qPochAPPS ℂ 5 5 (by norm_num))
  simpa using h

private theorem hasProd_fifthCollapseFactor_fiber
    (i : Fin 5) :
    HasProd
      (fun n : ℕ => fifthCollapseFactor (finFiveSigmaNatEquivNat ⟨i, n⟩))
      (match i with
        | ⟨0, _⟩ => qPochAPPS ℂ 5 25
        | ⟨1, _⟩ => qPochAPPS ℂ 10 25
        | ⟨2, _⟩ => qPochAPPS ℂ 15 25
        | ⟨3, _⟩ => qPochAPPS ℂ 20 25
        | ⟨4, _⟩ => (qPochAPPS ℂ 5 5)^5) := by
  fin_cases i
  · convert hasProd_qPochAPPS ℂ 5 25 (by norm_num) using 1
    ext n
    have hnot : ¬ 5 ∣ 5 * n + 0 + 1 := by omega
    simp [fifthCollapseFactor, finFiveSigmaNatEquivNat, apFactorPS, hnot]
    congr 1
    ring_nf
  · convert hasProd_qPochAPPS ℂ 10 25 (by norm_num) using 1
    ext n
    have hnot : ¬ 5 ∣ 5 * n + 1 + 1 := by omega
    simp [fifthCollapseFactor, finFiveSigmaNatEquivNat, apFactorPS, hnot]
    congr 1
    ring_nf
  · convert hasProd_qPochAPPS ℂ 15 25 (by norm_num) using 1
    ext n
    have hnot : ¬ 5 ∣ 5 * n + 2 + 1 := by omega
    simp [fifthCollapseFactor, finFiveSigmaNatEquivNat, apFactorPS, hnot]
    congr 1
    ring_nf
  · convert hasProd_qPochAPPS ℂ 20 25 (by norm_num) using 1
    ext n
    have hnot : ¬ 5 ∣ 5 * n + 3 + 1 := by omega
    simp [fifthCollapseFactor, finFiveSigmaNatEquivNat, apFactorPS, hnot]
    congr 1
    ring_nf
  · convert hasProd_apFactorPS_pow_five_complex using 1
    ext n
    have hdiv : 5 ∣ 5 * n + 4 + 1 := by
      refine ⟨n + 1, by ring_nf⟩
    have hidx : 5 * n + 4 + 1 = 5 + 5 * n := by omega
    simp [fifthCollapseFactor, finFiveSigmaNatEquivNat, oneSubXPow, apFactorPS, hidx]

private theorem prod_scaleX_qPochInfPS_fifth_collapse_AP_complex
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) =
      qPochAPPS ℂ 5 25 * qPochAPPS ℂ 10 25 * qPochAPPS ℂ 15 25 *
        qPochAPPS ℂ 20 25 * (qPochAPPS ℂ 5 5)^5 := by
  let e : (Sigma fun _ : Fin 5 => ℕ) ≃ ℕ := finFiveSigmaNatEquivNat
  let g : Fin 5 → ℂ⟦X⟧ :=
    fun i =>
      match i with
      | ⟨0, _⟩ => qPochAPPS ℂ 5 25
      | ⟨1, _⟩ => qPochAPPS ℂ 10 25
      | ⟨2, _⟩ => qPochAPPS ℂ 15 25
      | ⟨3, _⟩ => qPochAPPS ℂ 20 25
      | ⟨4, _⟩ => (qPochAPPS ℂ 5 5)^5
  have hnat := hasProd_fifthCollapseFactor_of_scaleX hζ
  have hsig : HasProd (fifthCollapseFactor ∘ e)
      (∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) :=
    (Equiv.hasProd_iff e).mpr hnat
  have hfiber : ∀ i : Fin 5,
      HasProd (fun n : ℕ => (fifthCollapseFactor ∘ e) ⟨i, n⟩) (g i) := by
    intro i
    simpa [e, g] using hasProd_fifthCollapseFactor_fiber i
  have hfin : HasProd g
      (∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) :=
    hsig.sigma hfiber
  have hfin' : HasProd g (∏ i : Fin 5, g i) := hasProd_fintype _
  have hprod :
      (∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) =
        ∏ i : Fin 5, g i :=
    hfin.unique hfin'
  rw [hprod]
  norm_num [g, Fin.prod_univ_five]

private theorem expand_qPochInfPS_eq_qPochAPPS_complex
    (s : ℕ) (hs : s ≠ 0) :
    PowerSeries.expand s hs (qPochInfPS ℂ) = qPochAPPS ℂ s s := by
  rw [qPochInfPS_eq_tprod ℂ]
  rw [(multipliable_one_sub_X_pow_succ ℂ).map_tprod
    (PowerSeries.expand s hs) (continuous_expand ℂ s hs)]
  unfold qPochAPPS
  apply tprod_congr
  intro n
  calc
    PowerSeries.expand s hs ((1 : ℂ⟦X⟧) - PowerSeries.X ^ (n + 1))
        = (1 : ℂ⟦X⟧) - PowerSeries.X ^ (s * (n + 1)) := by
          rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
    _ = apFactorPS ℂ s s n := by
          rw [apFactorPS]
          congr 1
          ring_nf

private theorem qPochAPPS_five_five_split_twentyfive_complex :
    qPochAPPS ℂ 5 5 =
      qPochAPPS ℂ 5 25 * qPochAPPS ℂ 10 25 * qPochAPPS ℂ 15 25 *
        qPochAPPS ℂ 20 25 * qPochAPPS ℂ 25 25 := by
  let f : ℕ → ℂ⟦X⟧ := fun n => apFactorPS ℂ 5 5 n
  let e : (Sigma fun _ : Fin 5 => ℕ) ≃ ℕ := finFiveSigmaNatEquivNat
  let g : Fin 5 → ℂ⟦X⟧ :=
    fun i => qPochAPPS ℂ (5 * (i.val + 1)) 25
  have hf : HasProd f (qPochAPPS ℂ 5 5) :=
    hasProd_qPochAPPS ℂ 5 5 (by norm_num)
  have hsig : HasProd (f ∘ e) (qPochAPPS ℂ 5 5) :=
    (Equiv.hasProd_iff e).mpr hf
  have hfiber : ∀ i : Fin 5,
      HasProd (fun n : ℕ => (f ∘ e) ⟨i, n⟩) (g i) := by
    intro i
    convert hasProd_qPochAPPS ℂ (5 * (i.val + 1)) 25 (by norm_num) using 1
    ext n
    simp [f, e, finFiveSigmaNatEquivNat, apFactorPS]
    congr 1
    ring_nf
  have hfin : HasProd g (qPochAPPS ℂ 5 5) := hsig.sigma hfiber
  have hfin' : HasProd g (∏ i : Fin 5, g i) := hasProd_fintype _
  have hprod : qPochAPPS ℂ 5 5 = ∏ i : Fin 5, g i :=
    hfin.unique hfin'
  rw [hprod]
  norm_num [g, Fin.prod_univ_five]

theorem prod_scaleX_qPochInfPS_fifth_collapse_complex
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (∏ j : Fin 5, RamanujanQuintic.scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) *
      PowerSeries.expand 25 (by decide) (qPochInfPS ℂ) =
    (PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)) ^ 6 := by
  rw [prod_scaleX_qPochInfPS_fifth_collapse_AP_complex hζ]
  rw [expand_qPochInfPS_eq_qPochAPPS_complex 25 (by decide),
    expand_qPochInfPS_eq_qPochAPPS_complex 5 (by decide)]
  have hsplit := qPochAPPS_five_five_split_twentyfive_complex
  rw [hsplit]
  ring_nf

/-! ## Identification with the Chapter 16 denominator core -/

private theorem scaleX_of_isRes5 {R : Type*} [CommRing R] {c : R}
    (hc5 : c^5 = 1) {r : ℕ} (φ : R⟦X⟧) (hφ : IsRes5 r φ) :
    scaleX c φ = PowerSeries.C (c^r) * φ := by
  ext n
  rw [coeff_scaleX, PowerSeries.coeff_C_mul]
  by_cases hn : n % 5 = r
  · have hn_decomp : n = 5 * (n / 5) + r := by
      calc
        n = 5 * (n / 5) + n % 5 := by omega
        _ = 5 * (n / 5) + r := by rw [hn]
    have hpow : c ^ n = c ^ r := by
      rw [hn_decomp, pow_add, pow_mul, hc5, one_pow, one_mul]
    rw [hpow]
    ring_nf
  · rw [hφ n hn]
    ring_nf

private theorem scaleX_qPochInfPS_eq_E5_sum_complex
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (j : Fin 5) :
    scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ) =
      E5 ℂ 0 + (PowerSeries.C ζ : ℂ⟦X⟧) ^ (j : ℕ) * E5 ℂ 1 +
        (PowerSeries.C ζ : ℂ⟦X⟧) ^ (2 * (j : ℕ)) * E5 ℂ 2 := by
  have hc5 : (ζ ^ (j : ℕ)) ^ 5 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [qPochInfPS_five_dissection ℂ, map_add, map_add]
  rw [scaleX_of_isRes5 hc5 (E5 ℂ 0) (isRes5_E5 ℂ 0),
    scaleX_of_isRes5 hc5 (E5 ℂ 1) (isRes5_E5 ℂ 1),
    scaleX_of_isRes5 hc5 (E5 ℂ 2) (isRes5_E5 ℂ 2)]
  simp [map_pow, pow_mul, mul_comm]

private theorem quintic_dissection_factor_product {S : Type*} [CommRing S]
    {z : S} (hz4 : z^4 = -(1 + z + z^2 + z^3)) (hz5 : z^5 = 1)
    (A B D : S) (hAD : A * D = -B^2) :
    ∏ j : Fin 5, (A + z ^ (j : ℕ) * B + z ^ (2 * (j : ℕ)) * D) =
      A^5 + 11 * B^5 + D^5 := by
  have hzpow (a r : ℕ) : z ^ (5 * a + r) = z ^ r := by
    rw [pow_add, pow_mul, hz5, one_pow, one_mul]
  have hz6 : z^6 = z := by simpa using hzpow 1 1
  have hz7 : z^7 = z^2 := by simpa using hzpow 1 2
  have hz8 : z^8 = z^3 := by simpa using hzpow 1 3
  have hz9 : z^9 = z^4 := by simpa using hzpow 1 4
  have hz10 : z^10 = 1 := by simpa using hzpow 2 0
  have hz11 : z^11 = z := by simpa using hzpow 2 1
  have hz12 : z^12 = z^2 := by simpa using hzpow 2 2
  have hz13 : z^13 = z^3 := by simpa using hzpow 2 3
  have hz14 : z^14 = z^4 := by simpa using hzpow 2 4
  have hz15 : z^15 = 1 := by simpa using hzpow 3 0
  have hz16 : z^16 = z := by simpa using hzpow 3 1
  have hz17 : z^17 = z^2 := by simpa using hzpow 3 2
  have hz18 : z^18 = z^3 := by simpa using hzpow 3 3
  have hz19 : z^19 = z^4 := by simpa using hzpow 3 4
  have hz20 : z^20 = 1 := by simpa using hzpow 4 0
  have hfactor :
      ∏ j : Fin 5, (A + z ^ (j : ℕ) * B + z ^ (2 * (j : ℕ)) * D) =
        A^5 + 11 * B^5 + D^5 + (A * D + B^2) * (5 * A * B * D - 10 * B^3) := by
    norm_num [Fin.prod_univ_five]
    ring_nf
    simp only [hz20, hz19, hz18, hz17, hz16, hz15, hz14, hz13, hz12, hz11,
      hz10, hz9, hz8, hz7, hz6, hz5]
    rw [hz4]
    ring_nf
  rw [hfactor]
  have hrel : A * D + B^2 = 0 := by rw [hAD]; ring_nf
  rw [hrel]
  ring_nf

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

private theorem map_E5DenominatorCoreRat_complex :
    PowerSeries.map (algebraMap ℚ ℂ) E5DenominatorCoreRat =
      (E5 ℂ 0)^5 + (11 : ℂ⟦X⟧) * (E5 ℂ 1)^5 + (E5 ℂ 2)^5 := by
  have h11 :
      PowerSeries.map (algebraMap ℚ ℂ) (11 : ℚ⟦X⟧) = (11 : ℂ⟦X⟧) := by
    rw [show (11 : ℚ⟦X⟧) = PowerSeries.C (11 : ℚ) by
      exact (map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 11).symm]
    rw [PowerSeries.map_C]
    exact (map_natCast (PowerSeries.C : ℂ →+* ℂ⟦X⟧) 11).symm
  rw [E5DenominatorCoreRat, map_add, map_add, map_pow, map_mul, map_pow, map_pow,
    map_E5_rat_complex 0, map_E5_rat_complex 1, map_E5_rat_complex 2, h11]

private theorem E5_zero_mul_two_eq_neg_one_sq_complex :
    E5 ℂ 0 * E5 ℂ 2 = -(E5 ℂ 1)^2 := by
  have hmap := congrArg (PowerSeries.map (algebraMap ℚ ℂ))
    E5_zero_mul_two_eq_neg_one_sq_rat
  rw [map_mul, map_neg, map_pow, map_E5_rat_complex 0, map_E5_rat_complex 1,
    map_E5_rat_complex 2] at hmap
  exact hmap

theorem prod_scaleX_qPochInfPS_eq_E5DenominatorCore_complex
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (∏ j : Fin 5, RamanujanQuintic.scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) =
      PowerSeries.map (algebraMap ℚ ℂ) Ch16MBIProof.E5DenominatorCoreRat := by
  let Z : ℂ⟦X⟧ := PowerSeries.C ζ
  let A : ℂ⟦X⟧ := E5 ℂ 0
  let B : ℂ⟦X⟧ := E5 ℂ 1
  let D : ℂ⟦X⟧ := E5 ℂ 2
  have hsum : ∑ i ∈ Finset.range 5, ζ ^ i = 0 :=
    hζ.geom_sum_eq_zero (by norm_num)
  have hsum' : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    norm_num [Finset.sum_range_succ] at hsum ⊢
    simpa [add_assoc] using hsum
  have hζ4 : ζ ^ 4 = -(1 + ζ + ζ ^ 2 + ζ ^ 3) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_assoc, add_comm, add_left_comm] using hsum'
  have hZ4 : Z^4 = -(1 + Z + Z^2 + Z^3) := by
    subst Z
    simpa [map_add, map_neg, map_one, map_pow] using
      congrArg (PowerSeries.C : ℂ →+* ℂ⟦X⟧) hζ4
  have hZ5 : Z^5 = 1 := by
    subst Z
    simpa [map_one, map_pow] using
      congrArg (PowerSeries.C : ℂ →+* ℂ⟦X⟧) hζ.pow_eq_one
  have hAD : A * D = -B^2 := by
    simpa [A, B, D] using E5_zero_mul_two_eq_neg_one_sq_complex
  calc
    (∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ))
        = ∏ j : Fin 5, (A + Z ^ (j : ℕ) * B + Z ^ (2 * (j : ℕ)) * D) := by
          apply Finset.prod_congr rfl
          intro j _hj
          simp [A, B, D, Z, scaleX_qPochInfPS_eq_E5_sum_complex hζ j, pow_mul]
    _ = A^5 + (11 : ℂ⟦X⟧) * B^5 + D^5 := by
          simpa [A, B, D] using
            quintic_dissection_factor_product (z := Z) hZ4 hZ5 A B D hAD
    _ = PowerSeries.map (algebraMap ℚ ℂ) E5DenominatorCoreRat := by
          rw [map_E5DenominatorCoreRat_complex]

theorem E5DenominatorCoreRat_mul_expand_twentyfive_qPochInfPS :
    E5DenominatorCoreRat *
        PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) =
      (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)
  have hζ : IsPrimitiveRoot ζ 5 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp 5 (by norm_num : (5 : ℕ) ≠ 0)
  apply PowerSeries.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  rw [map_mul, map_pow]
  rw [map_E5DenominatorCoreRat_complex]
  rw [PowerSeries.map_expand, PowerSeries.map_expand]
  rw [map_qPochInfPS (algebraMap ℚ ℂ)]
  have hprodcore :
      (∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) =
        E5 ℂ 0 ^ 5 + 11 * E5 ℂ 1 ^ 5 + E5 ℂ 2 ^ 5 := by
    rw [prod_scaleX_qPochInfPS_eq_E5DenominatorCore_complex hζ,
      map_E5DenominatorCoreRat_complex]
  rw [← hprodcore]
  exact prod_scaleX_qPochInfPS_fifth_collapse_complex hζ

theorem most_beautiful_identity :
    (PowerSeries.mk
        (fun n : ℕ => (partitionGenFun ℚ).coeff (5 * n + 4)) : ℚ⟦X⟧)
      =
    5 •
      ((PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^5 *
        (partitionGenFun ℚ)^6) := by
  exact most_beautiful_identity_of_E5_denominator_identity
    E5DenominatorCoreRat_mul_expand_twentyfive_qPochInfPS

end RamanujanQuinticJTP
end Pending
end QseriesFormalization
