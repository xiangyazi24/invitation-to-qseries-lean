import Mathlib.Tactic.Ring
import QseriesFormalization.Basic
import QseriesFormalization.Chapter09

open scoped QseriesFormalization
open Ch09
open Field

theorem BaileyTransform_seven_alpha_zero_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hQ6 : qPochhammer q 6 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0)
    (hA6 : qPoch (a * q) q 6 ≠ 0) :
    qPoch (a * q / (ρ₁ * ρ₂)) q 7 * qPoch (a * q) q 7 +
      qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 6 *
        (qPochhammer q 7 * qPoch (a * q) q 7 /
          (qPochhammer q 6 * qPochhammer q 1 * qPoch (a * q) q 1)) +
      qPoch ρ₁ q 2 * qPoch ρ₂ q 2 *
        (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5 *
        (qPochhammer q 7 * qPoch (a * q) q 7 /
          (qPochhammer q 5 * qPochhammer q 2 * qPoch (a * q) q 2)) +
      qPoch ρ₁ q 3 * qPoch ρ₂ q 3 *
        (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
        (qPochhammer q 7 * qPoch (a * q) q 7 /
          (qPochhammer q 4 * qPochhammer q 3 * qPoch (a * q) q 3)) +
      qPoch ρ₁ q 4 * qPoch ρ₂ q 4 *
        (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
        (qPochhammer q 7 * qPoch (a * q) q 7 /
          (qPochhammer q 3 * qPochhammer q 4 * qPoch (a * q) q 4)) +
      qPoch ρ₁ q 5 * qPoch ρ₂ q 5 *
        (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
        (qPochhammer q 7 * qPoch (a * q) q 7 /
          (qPochhammer q 2 * qPochhammer q 5 * qPoch (a * q) q 5)) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 *
        (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
        (qPochhammer q 7 * qPoch (a * q) q 7 /
          (qPochhammer q 1 * qPochhammer q 6 * qPoch (a * q) q 6)) +
      qPoch ρ₁ q 7 * qPoch ρ₂ q 7 *
        (a * q / (ρ₁ * ρ₂)) ^ 7 =
      qPoch (a * q / ρ₁) q 7 * qPoch (a * q / ρ₂) q 7 := by
  rw [BaileyTransform_seven_alpha_zero_first_ratio a q hQ1 hQ6 hA1,
    BaileyTransform_seven_alpha_zero_second_ratio a q hQ1 hQ2 hQ5 hA2,
    BaileyTransform_seven_alpha_zero_third_ratio a q hQ1 hQ2 hQ3 hQ4 hA3,
    BaileyTransform_seven_alpha_zero_fourth_ratio a q hQ1 hQ2 hQ3 hQ4 hA4,
    BaileyTransform_seven_alpha_zero_fifth_ratio a q hQ1 hQ2 hQ5 hA5,
    BaileyTransform_seven_alpha_zero_sixth_ratio a q hQ1 hQ6 hA6]
  have hρ1 : ρ₁ ≠ 0 := left_ne_zero_of_mul hρ
  have hρ2 : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ
  simp [qPoch]
  field_simp [hρ, hρ1, hρ2]
  ring

