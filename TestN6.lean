import Mathlib.Tactic.Ring
import QseriesFormalization.Basic
import QseriesFormalization.Chapter09

open scoped QseriesFormalization

variable (a q ρ₁ ρ₂ : ℂ)
theorem test_n6 :
    qPoch (a * q / (ρ₁ * ρ₂)) q 6 +
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5 *
          ((1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) *
            ((1 - a * q ^ 2) * (1 - a * q ^ 3) *
              (1 - a * q ^ 4) * (1 - a * q ^ 5) *
              (1 - a * q ^ 6)))) +
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
          (((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4)) *
            ((1 - a * q ^ 3) * (1 - a * q ^ 4) *
              (1 - a * q ^ 5) * (1 - a * q ^ 6)))) +
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
          (((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2) * (1 + q ^ 3)) *
            ((1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6)))) +
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
          (((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4)) *
            ((1 - a * q ^ 5) * (1 - a * q ^ 6)))) +
      (qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
          ((1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) * (1 - a * q ^ 6))) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 =
        qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 := by
  simp [qPoch]
  ring
