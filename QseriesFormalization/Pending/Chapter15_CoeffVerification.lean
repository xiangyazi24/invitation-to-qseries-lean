import QseriesFormalization.Pending.Chapter15_R_ODE
import QseriesFormalization.Chapter19

/-!
# Coefficient verification for Chan Theorem 11.7 / Eq. 15.8

This file verifies the multiplicative formal-power-series identity

`chan15LHSPS R * PowerSeries.expand 5 (qPochInfPS R) = (qPochInfPS R)^5`

coefficient-by-coefficient through degree `40`.

The raw Lambert-side coefficients of `chan15LHSPS` alone through degree `40` are
`[1, -5, 5, 10, -15, -5, -10, 30, 25, -35, 5, -60, 30, 60, -30, 10, -55, 80,
35, -100, -15, -60, 60, 110, -50, -5, -60, 100, 90, -150, -10, -160, 105,
120, -80, 30, -105, 180, 100, -120, 25]`.
After multiplication by
`expand 5 (qPochInfPS R) = 1 - X^5 - X^10 + ...`, both sides of the
multiplicative identity have coefficients
`[1, -5, 5, 10, -15, -6, -5, 25, 15, -20, 9, -45, -5, 25, 20, 10, 15, 20,
-50, -35, -30, 55, -50, 15, 80, 1, 50, -35, -45, -15, 5, -50, -25, -55,
85, 51, 50, 10, -40, 65, 10]`.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch15CoeffVerification

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch15RODE

/-- Low-degree coefficients of `qPochInfPS`, from Euler's pentagonal theorem. -/
private def qPochLowCoeff : Nat → Int
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | 6 => 0
  | 7 => 1
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | 11 => 0
  | 12 => -1
  | 13 => 0
  | 14 => 0
  | 15 => -1
  | 16 => 0
  | 17 => 0
  | 18 => 0
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 1
  | 23 => 0
  | 24 => 0
  | 25 => 0
  | 26 => 1
  | 27 => 0
  | 28 => 0
  | 29 => 0
  | 30 => 0
  | 31 => 0
  | 32 => 0
  | 33 => 0
  | 34 => 0
  | 35 => -1
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => -1
  | _ => 0

/-- Convolution coefficients for powers of the low-degree Euler series. -/
private def qPochPowLowCoeff : Nat → Nat → Int
  | 0 => fun n => if n = 0 then 1 else 0
  | e + 1 => fun n =>
      ∑ k ∈ Finset.range (n + 1), qPochPowLowCoeff e k * qPochLowCoeff (n - k)

/-- Low-degree coefficients of the Lambert-series side `chan15LHSPS` alone. -/
def chan15LambertCoeffLow : Nat → Int
  | 0 => 1
  | 1 => -5
  | 2 => 5
  | 3 => 10
  | 4 => -15
  | 5 => -5
  | 6 => -10
  | 7 => 30
  | 8 => 25
  | 9 => -35
  | 10 => 5
  | 11 => -60
  | 12 => 30
  | 13 => 60
  | 14 => -30
  | 15 => 10
  | 16 => -55
  | 17 => 80
  | 18 => 35
  | 19 => -100
  | 20 => -15
  | 21 => -60
  | 22 => 60
  | 23 => 110
  | 24 => -50
  | 25 => -5
  | 26 => -60
  | 27 => 100
  | 28 => 90
  | 29 => -150
  | 30 => -10
  | 31 => -160
  | 32 => 105
  | 33 => 120
  | 34 => -80
  | 35 => 30
  | 36 => -105
  | 37 => 180
  | 38 => 100
  | 39 => -120
  | 40 => 25
  | _ => 0

private def expandFiveQCoeff : Nat → Int :=
  fun n => if 5 ∣ n then qPochLowCoeff (n / 5) else 0

private def chan15ProductLowCoeff (n : Nat) : Int :=
  ∑ k ∈ Finset.range (n + 1), chan15LambertCoeffLow k * expandFiveQCoeff (n - k)

/-- Low-degree coefficients of both sides of the multiplicative Eq. 15.8. -/
def chan15CoeffVerified : Nat → Int
  | 0 => 1
  | 1 => -5
  | 2 => 5
  | 3 => 10
  | 4 => -15
  | 5 => -6
  | 6 => -5
  | 7 => 25
  | 8 => 15
  | 9 => -20
  | 10 => 9
  | 11 => -45
  | 12 => -5
  | 13 => 25
  | 14 => 20
  | 15 => 10
  | 16 => 15
  | 17 => 20
  | 18 => -50
  | 19 => -35
  | 20 => -30
  | 21 => 55
  | 22 => -50
  | 23 => 15
  | 24 => 80
  | 25 => 1
  | 26 => 50
  | 27 => -35
  | 28 => -45
  | 29 => -15
  | 30 => 5
  | 31 => -50
  | 32 => -25
  | 33 => -55
  | 34 => 85
  | 35 => 51
  | 36 => 50
  | 37 => 10
  | 38 => -40
  | 39 => 65
  | 40 => 10
  | _ => 0

private theorem pentagonalSign_eq_qPochLowCoeff (n : Nat) (hn : n ≤ 40) :
    QseriesFormalization.PartI.Ch05.pentagonalSign n = qPochLowCoeff n := by
  interval_cases n <;> decide

private theorem coeff_qPochInfPS_low (R : Type*) [CommRing R] (n : Nat) (hn : n ≤ 40) :
    (qPochInfPS R).coeff n = (qPochLowCoeff n : R) := by
  rw [coeff_qPochInfPS_eq_pentagonalSign, pentagonalSign_eq_qPochLowCoeff n hn]

private theorem coeff_qPochInfPS_pow_low (R : Type*) [CommRing R]
    (e n : Nat) (hn : n ≤ 40) :
    ((qPochInfPS R) ^ e).coeff n = (qPochPowLowCoeff e n : R) := by
  induction e generalizing n with
  | zero =>
      by_cases h : n = 0
      · simp [qPochPowLowCoeff, PowerSeries.coeff_one, h]
      · simp [qPochPowLowCoeff, PowerSeries.coeff_one, h]
  | succ e ih =>
      rw [pow_succ, PowerSeries.coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [qPochPowLowCoeff]
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk_le_n : k ≤ n := by
        simp only [Finset.mem_range] at hk
        omega
      have hk40 : k ≤ 40 := by omega
      have hnk40 : n - k ≤ 40 := by omega
      rw [ih k hk40, coeff_qPochInfPS_low R (n - k) hnk40]
      simp

private theorem chan15LHSCoeffInt_low (n : Nat) (hn : n ≤ 40) :
    chan15LHSCoeffInt n = chan15LambertCoeffLow n := by
  interval_cases n <;> decide

private theorem chan15ProductLowCoeff_eq_verified (n : Nat) (hn : n ≤ 40) :
    chan15ProductLowCoeff n = chan15CoeffVerified n := by
  interval_cases n <;> decide

set_option maxRecDepth 8192 in
private theorem qPochPowLowCoeff_five_eq_verified (n : Nat) (hn : n ≤ 40) :
    qPochPowLowCoeff 5 n = chan15CoeffVerified n := by
  interval_cases n <;> decide

/-- `chan15LHSPS` alone has the advertised Lambert-side coefficients for `n ≤ 40`. -/
theorem coeff_chan15LHSPS_low (R : Type*) [CommRing R] (n : Nat) (hn : n ≤ 40) :
    (chan15LHSPS R).coeff n = (chan15LambertCoeffLow n : R) := by
  rw [coeff_chan15LHSPS, chan15LHSCoeff, chan15LHSCoeffInt_low n hn]

private theorem coeff_expand_five_qPochInfPS_low (R : Type*) [CommRing R]
    (n : Nat) (hn : n ≤ 40) :
    (PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff n =
      (expandFiveQCoeff n : R) := by
  rw [PowerSeries.coeff_expand]
  unfold expandFiveQCoeff
  by_cases h : 5 ∣ n
  · rw [if_pos h, if_pos h]
    have hdiv : n / 5 ≤ 40 := by omega
    exact coeff_qPochInfPS_low R (n / 5) hdiv
  · rw [if_neg h, if_neg h]
    norm_num

private theorem coeff_chan15_product_raw_low (R : Type*) [CommRing R]
    (n : Nat) (hn : n ≤ 40) :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff n =
      (chan15ProductLowCoeff n : R) := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  unfold chan15ProductLowCoeff
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le_n : k ≤ n := by
    simp only [Finset.mem_range] at hk
    omega
  have hk40 : k ≤ 40 := by omega
  have hnk40 : n - k ≤ 40 := by omega
  rw [coeff_chan15LHSPS_low R k hk40, coeff_expand_five_qPochInfPS_low R (n - k) hnk40]
  simp

/-- The product side of Eq. 15.8 has coefficients `chan15CoeffVerified` for `n ≤ 40`. -/
theorem coeff_chan15_product_low (R : Type*) [CommRing R]
    (n : Nat) (hn : n ≤ 40) :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff n =
      (chan15CoeffVerified n : R) := by
  rw [coeff_chan15_product_raw_low R n hn, chan15ProductLowCoeff_eq_verified n hn]

/-- The Euler-product side `(qPochInfPS)^5` has coefficients `chan15CoeffVerified`
for `n ≤ 40`. -/
theorem coeff_qPochInfPS_pow_five_low (R : Type*) [CommRing R]
    (n : Nat) (hn : n ≤ 40) :
    ((qPochInfPS R) ^ 5).coeff n = (chan15CoeffVerified n : R) := by
  rw [coeff_qPochInfPS_pow_low R 5 n hn, qPochPowLowCoeff_five_eq_verified n hn]

/-- Chan Theorem 11.7 / Eq. 15.8 holds coefficient-by-coefficient through degree `40`. -/
theorem chan15_theorem_11_7_coeff_low (R : Type*) [CommRing R]
    (n : Nat) (hn : n ≤ 40) :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff n =
      (((qPochInfPS R) ^ 5).coeff n) := by
  rw [coeff_chan15_product_low R n hn, coeff_qPochInfPS_pow_five_low R n hn]

theorem chan15_theorem_11_7_coeffs_zero_to_forty (R : Type*) [CommRing R] :
    ∀ n, n ≤ 40 →
      (chan15LHSPS R *
          PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff n =
        (((qPochInfPS R) ^ 5).coeff n) := by
  intro n hn
  exact chan15_theorem_11_7_coeff_low R n hn

theorem chan15_theorem_11_7_coeffs_zero_to_thirty (R : Type*) [CommRing R] :
    ∀ n, n ≤ 30 →
      (chan15LHSPS R *
          PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff n =
        (((qPochInfPS R) ^ 5).coeff n) := by
  intro n hn
  exact chan15_theorem_11_7_coeff_low R n (by omega)

theorem chan15_theorem_11_7_coeffs_zero_to_twenty (R : Type*) [CommRing R] :
    ∀ n, n ≤ 20 →
      (chan15LHSPS R *
          PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff n =
        (((qPochInfPS R) ^ 5).coeff n) := by
  intro n hn
  exact chan15_theorem_11_7_coeff_low R n (by omega)

theorem chan15_theorem_11_7_coeffs_zero_to_ten (R : Type*) [CommRing R] :
    ∀ n, n ≤ 10 →
      (chan15LHSPS R *
          PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff n =
        (((qPochInfPS R) ^ 5).coeff n) := by
  intro n hn
  exact chan15_theorem_11_7_coeff_low R n (by omega)

theorem chan15_theorem_11_7_coeff_0 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 0 =
      (((qPochInfPS R) ^ 5).coeff 0) := by
  exact chan15_theorem_11_7_coeff_low R 0 (by norm_num)

theorem chan15_theorem_11_7_coeff_1 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 1 =
      (((qPochInfPS R) ^ 5).coeff 1) := by
  exact chan15_theorem_11_7_coeff_low R 1 (by norm_num)

theorem chan15_theorem_11_7_coeff_2 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 2 =
      (((qPochInfPS R) ^ 5).coeff 2) := by
  exact chan15_theorem_11_7_coeff_low R 2 (by norm_num)

theorem chan15_theorem_11_7_coeff_3 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 3 =
      (((qPochInfPS R) ^ 5).coeff 3) := by
  exact chan15_theorem_11_7_coeff_low R 3 (by norm_num)

theorem chan15_theorem_11_7_coeff_4 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 4 =
      (((qPochInfPS R) ^ 5).coeff 4) := by
  exact chan15_theorem_11_7_coeff_low R 4 (by norm_num)

theorem chan15_theorem_11_7_coeff_5 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 5 =
      (((qPochInfPS R) ^ 5).coeff 5) := by
  exact chan15_theorem_11_7_coeff_low R 5 (by norm_num)

theorem chan15_theorem_11_7_coeff_6 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 6 =
      (((qPochInfPS R) ^ 5).coeff 6) := by
  exact chan15_theorem_11_7_coeff_low R 6 (by norm_num)

theorem chan15_theorem_11_7_coeff_7 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 7 =
      (((qPochInfPS R) ^ 5).coeff 7) := by
  exact chan15_theorem_11_7_coeff_low R 7 (by norm_num)

theorem chan15_theorem_11_7_coeff_8 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 8 =
      (((qPochInfPS R) ^ 5).coeff 8) := by
  exact chan15_theorem_11_7_coeff_low R 8 (by norm_num)

theorem chan15_theorem_11_7_coeff_9 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 9 =
      (((qPochInfPS R) ^ 5).coeff 9) := by
  exact chan15_theorem_11_7_coeff_low R 9 (by norm_num)

theorem chan15_theorem_11_7_coeff_10 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 10 =
      (((qPochInfPS R) ^ 5).coeff 10) := by
  exact chan15_theorem_11_7_coeff_low R 10 (by norm_num)

theorem chan15_theorem_11_7_coeff_11 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 11 =
      (((qPochInfPS R) ^ 5).coeff 11) := by
  exact chan15_theorem_11_7_coeff_low R 11 (by norm_num)

theorem chan15_theorem_11_7_coeff_12 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 12 =
      (((qPochInfPS R) ^ 5).coeff 12) := by
  exact chan15_theorem_11_7_coeff_low R 12 (by norm_num)

theorem chan15_theorem_11_7_coeff_13 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 13 =
      (((qPochInfPS R) ^ 5).coeff 13) := by
  exact chan15_theorem_11_7_coeff_low R 13 (by norm_num)

theorem chan15_theorem_11_7_coeff_14 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 14 =
      (((qPochInfPS R) ^ 5).coeff 14) := by
  exact chan15_theorem_11_7_coeff_low R 14 (by norm_num)

theorem chan15_theorem_11_7_coeff_15 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 15 =
      (((qPochInfPS R) ^ 5).coeff 15) := by
  exact chan15_theorem_11_7_coeff_low R 15 (by norm_num)

theorem chan15_theorem_11_7_coeff_16 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 16 =
      (((qPochInfPS R) ^ 5).coeff 16) := by
  exact chan15_theorem_11_7_coeff_low R 16 (by norm_num)

theorem chan15_theorem_11_7_coeff_17 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 17 =
      (((qPochInfPS R) ^ 5).coeff 17) := by
  exact chan15_theorem_11_7_coeff_low R 17 (by norm_num)

theorem chan15_theorem_11_7_coeff_18 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 18 =
      (((qPochInfPS R) ^ 5).coeff 18) := by
  exact chan15_theorem_11_7_coeff_low R 18 (by norm_num)

theorem chan15_theorem_11_7_coeff_19 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 19 =
      (((qPochInfPS R) ^ 5).coeff 19) := by
  exact chan15_theorem_11_7_coeff_low R 19 (by norm_num)

theorem chan15_theorem_11_7_coeff_20 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 20 =
      (((qPochInfPS R) ^ 5).coeff 20) := by
  exact chan15_theorem_11_7_coeff_low R 20 (by norm_num)

theorem chan15_theorem_11_7_coeff_21 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 21 =
      (((qPochInfPS R) ^ 5).coeff 21) := by
  exact chan15_theorem_11_7_coeff_low R 21 (by norm_num)

theorem chan15_theorem_11_7_coeff_22 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 22 =
      (((qPochInfPS R) ^ 5).coeff 22) := by
  exact chan15_theorem_11_7_coeff_low R 22 (by norm_num)

theorem chan15_theorem_11_7_coeff_23 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 23 =
      (((qPochInfPS R) ^ 5).coeff 23) := by
  exact chan15_theorem_11_7_coeff_low R 23 (by norm_num)

theorem chan15_theorem_11_7_coeff_24 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 24 =
      (((qPochInfPS R) ^ 5).coeff 24) := by
  exact chan15_theorem_11_7_coeff_low R 24 (by norm_num)

theorem chan15_theorem_11_7_coeff_25 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 25 =
      (((qPochInfPS R) ^ 5).coeff 25) := by
  exact chan15_theorem_11_7_coeff_low R 25 (by norm_num)

theorem chan15_theorem_11_7_coeff_26 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 26 =
      (((qPochInfPS R) ^ 5).coeff 26) := by
  exact chan15_theorem_11_7_coeff_low R 26 (by norm_num)

theorem chan15_theorem_11_7_coeff_27 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 27 =
      (((qPochInfPS R) ^ 5).coeff 27) := by
  exact chan15_theorem_11_7_coeff_low R 27 (by norm_num)

theorem chan15_theorem_11_7_coeff_28 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 28 =
      (((qPochInfPS R) ^ 5).coeff 28) := by
  exact chan15_theorem_11_7_coeff_low R 28 (by norm_num)

theorem chan15_theorem_11_7_coeff_29 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 29 =
      (((qPochInfPS R) ^ 5).coeff 29) := by
  exact chan15_theorem_11_7_coeff_low R 29 (by norm_num)

theorem chan15_theorem_11_7_coeff_30 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 30 =
      (((qPochInfPS R) ^ 5).coeff 30) := by
  exact chan15_theorem_11_7_coeff_low R 30 (by norm_num)

theorem chan15_theorem_11_7_coeff_31 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 31 =
      (((qPochInfPS R) ^ 5).coeff 31) := by
  exact chan15_theorem_11_7_coeff_low R 31 (by norm_num)

theorem chan15_theorem_11_7_coeff_32 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 32 =
      (((qPochInfPS R) ^ 5).coeff 32) := by
  exact chan15_theorem_11_7_coeff_low R 32 (by norm_num)

theorem chan15_theorem_11_7_coeff_33 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 33 =
      (((qPochInfPS R) ^ 5).coeff 33) := by
  exact chan15_theorem_11_7_coeff_low R 33 (by norm_num)

theorem chan15_theorem_11_7_coeff_34 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 34 =
      (((qPochInfPS R) ^ 5).coeff 34) := by
  exact chan15_theorem_11_7_coeff_low R 34 (by norm_num)

theorem chan15_theorem_11_7_coeff_35 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 35 =
      (((qPochInfPS R) ^ 5).coeff 35) := by
  exact chan15_theorem_11_7_coeff_low R 35 (by norm_num)

theorem chan15_theorem_11_7_coeff_36 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 36 =
      (((qPochInfPS R) ^ 5).coeff 36) := by
  exact chan15_theorem_11_7_coeff_low R 36 (by norm_num)

theorem chan15_theorem_11_7_coeff_37 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 37 =
      (((qPochInfPS R) ^ 5).coeff 37) := by
  exact chan15_theorem_11_7_coeff_low R 37 (by norm_num)

theorem chan15_theorem_11_7_coeff_38 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 38 =
      (((qPochInfPS R) ^ 5).coeff 38) := by
  exact chan15_theorem_11_7_coeff_low R 38 (by norm_num)

theorem chan15_theorem_11_7_coeff_39 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 39 =
      (((qPochInfPS R) ^ 5).coeff 39) := by
  exact chan15_theorem_11_7_coeff_low R 39 (by norm_num)

theorem chan15_theorem_11_7_coeff_40 (R : Type*) [CommRing R] :
    (chan15LHSPS R *
        PowerSeries.expand 5 (by decide : (5 : Nat) ≠ 0) (qPochInfPS R)).coeff 40 =
      (((qPochInfPS R) ^ 5).coeff 40) := by
  exact chan15_theorem_11_7_coeff_low R 40 (by norm_num)

end Ch15CoeffVerification
end Pending
end QseriesFormalization
