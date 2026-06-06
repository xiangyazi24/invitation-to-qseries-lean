import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Chapter 15 formal logarithmic derivative infrastructure

This file packages the formal derivative and Euler theta operator used in the
Chan §15 logarithmic-derivative route.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch15FormalDeriv

open PowerSeries
open scoped PowerSeries

variable {R : Type*}

/-- Formal derivative on one-variable formal power series.  This is Mathlib's
`PowerSeries.derivative`, exposed under the name used in the Chapter 15 notes. -/
noncomputable abbrev formalDeriv [CommSemiring R] (f : R⟦X⟧) : R⟦X⟧ :=
  d⁄dX R f

@[simp] theorem coeff_formalDeriv [CommSemiring R] (f : R⟦X⟧) (n : ℕ) :
    (formalDeriv f).coeff n = f.coeff (n + 1) * (n + 1 : R) := by
  exact PowerSeries.coeff_derivative f n

/-- Euler's theta operator `X d/dX`. -/
noncomputable def thetaOp [CommSemiring R] (f : R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.X * formalDeriv f

@[simp] theorem coeff_zero_thetaOp [CommSemiring R] (f : R⟦X⟧) :
    (thetaOp f).coeff 0 = 0 := by
  simp [thetaOp]

@[simp] theorem coeff_thetaOp [CommSemiring R] (f : R⟦X⟧) (n : ℕ) :
    (thetaOp f).coeff n = f.coeff n * (n : R) := by
  cases n with
  | zero =>
      simp
  | succ n =>
      simp [thetaOp, Nat.cast_add, Nat.cast_one]

@[simp] theorem thetaOp_zero [CommSemiring R] :
    thetaOp (0 : R⟦X⟧) = 0 := by
  simp [thetaOp, formalDeriv]

@[simp] theorem thetaOp_one [CommSemiring R] :
    thetaOp (1 : R⟦X⟧) = 0 := by
  simp [thetaOp, formalDeriv]

@[simp] theorem thetaOp_C [CommSemiring R] (r : R) :
    thetaOp (PowerSeries.C r) = 0 := by
  simp [thetaOp, formalDeriv]

@[simp] theorem thetaOp_X [CommSemiring R] :
    thetaOp (PowerSeries.X : R⟦X⟧) = PowerSeries.X := by
  simp [thetaOp, formalDeriv]

theorem thetaOp_add [CommSemiring R] (f g : R⟦X⟧) :
    thetaOp (f + g) = thetaOp f + thetaOp g := by
  unfold thetaOp formalDeriv
  rw [map_add]
  ring

theorem thetaOp_sub [CommRing R] (f g : R⟦X⟧) :
    thetaOp (f - g) = thetaOp f - thetaOp g := by
  unfold thetaOp formalDeriv
  rw [map_sub]
  ring

@[simp] theorem thetaOp_neg [CommRing R] (f : R⟦X⟧) :
    thetaOp (-f) = -thetaOp f := by
  unfold thetaOp formalDeriv
  rw [map_neg]
  ring

/-- Euler's theta operator is a derivation. -/
theorem thetaOp_mul [CommSemiring R] (f g : R⟦X⟧) :
    thetaOp (f * g) = f * thetaOp g + g * thetaOp f := by
  unfold thetaOp formalDeriv
  rw [Derivation.leibniz]
  simp [smul_eq_mul]
  ring

theorem thetaOp_C_mul [CommSemiring R] (r : R) (f : R⟦X⟧) :
    thetaOp (PowerSeries.C r * f) = PowerSeries.C r * thetaOp f := by
  rw [thetaOp_mul, thetaOp_C]
  ring

theorem thetaOp_X_mul [CommSemiring R] (f : R⟦X⟧) :
    thetaOp (PowerSeries.X * f) = PowerSeries.X * f + PowerSeries.X * thetaOp f := by
  rw [thetaOp_mul, thetaOp_X]
  ring

theorem thetaOp_pow [CommSemiring R] (f : R⟦X⟧) (n : ℕ) :
    thetaOp (f ^ n) = (n : R⟦X⟧) * f ^ (n - 1) * thetaOp f := by
  unfold thetaOp formalDeriv
  rw [Derivation.leibniz_pow]
  simp [nsmul_eq_mul, smul_eq_mul]
  ring

/-- Logarithmic theta derivative `Theta(f)/f` over a field. -/
noncomputable def thetaDlog {K : Type*} [Field K] (f : K⟦X⟧) : K⟦X⟧ :=
  thetaOp f * f⁻¹

theorem thetaDlog_mul {K : Type*} [Field K] (f g : K⟦X⟧)
    (hf : PowerSeries.constantCoeff f ≠ 0)
    (hg : PowerSeries.constantCoeff g ≠ 0) :
    thetaDlog (f * g) = thetaDlog f + thetaDlog g := by
  unfold thetaDlog
  rw [thetaOp_mul, PowerSeries.mul_inv_rev]
  calc
    (f * thetaOp g + g * thetaOp f) * (g⁻¹ * f⁻¹)
        = thetaOp g * g⁻¹ * (f * f⁻¹) +
          thetaOp f * f⁻¹ * (g * g⁻¹) := by ring
    _ = thetaOp g * g⁻¹ + thetaOp f * f⁻¹ := by
      rw [PowerSeries.mul_inv_cancel f hf, PowerSeries.mul_inv_cancel g hg]
      ring
    _ = thetaOp f * f⁻¹ + thetaOp g * g⁻¹ := by ring

theorem thetaDlog_pow {K : Type*} [Field K] (f : K⟦X⟧)
    (hf : PowerSeries.constantCoeff f ≠ 0) (n : ℕ) :
    thetaDlog (f ^ n) = (n : K⟦X⟧) * thetaDlog f := by
  unfold thetaDlog
  rw [thetaOp_pow]
  by_cases hn : n = 0
  · simp [hn]
  · have hpow : PowerSeries.constantCoeff (f ^ (n - 1)) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ hf
    have hcancel : f ^ (n - 1) * (f ^ n)⁻¹ = f⁻¹ := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      calc
        f ^ (n - 1) * (f ^ n)⁻¹
            = f ^ (n - 1) * (f ^ (n - 1) * f)⁻¹ := by
                rw [← pow_succ, Nat.sub_add_cancel hnpos]
        _ = f ^ (n - 1) * (f⁻¹ * (f ^ (n - 1))⁻¹) := by
                rw [PowerSeries.mul_inv_rev]
        _ = f⁻¹ * (f ^ (n - 1) * (f ^ (n - 1))⁻¹) := by ring
        _ = f⁻¹ := by
                rw [PowerSeries.mul_inv_cancel _ hpow]
                ring
    calc
      (n : K⟦X⟧) * f ^ (n - 1) * thetaOp f * (f ^ n)⁻¹
          = (n : K⟦X⟧) * thetaOp f * (f ^ (n - 1) * (f ^ n)⁻¹) := by ring
      _ = (n : K⟦X⟧) * thetaOp f * f⁻¹ := by rw [hcancel]
      _ = (n : K⟦X⟧) * (thetaOp f * f⁻¹) := by ring

end Ch15FormalDeriv
end Pending
end QseriesFormalization
