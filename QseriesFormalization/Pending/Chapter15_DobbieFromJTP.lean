import QseriesFormalization.Pending.Chapter15_FormalDeriv
import QseriesFormalization.Pending.Chapter15_R_ODE
import QseriesFormalization.Pending.RamanujanQuinticJTP

/-!
# Chapter 15 logarithmic-derivative consequences of the quintic JTP identities

This file records the formal `thetaOp = X d/dX` consequences of the two
Hirschhorn §8.3 quintic JTP identities and the fifth-root product collapse.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch15DobbieFromJTP

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch15FormalDeriv
open QseriesFormalization.Pending.Ch15RODE
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.RamanujanQuinticJTP

noncomputable abbrev expand5Qpoch (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (qPochInfPS R)

noncomputable abbrev expand25Qpoch (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 25 (by decide : (25 : ℕ) ≠ 0) (qPochInfPS R)

theorem thetaOp_section83_pair14
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    thetaOp (section83JTPProductPS ζ) =
      thetaOp (section83_rhs_pair14 ζ) := by
  exact congrArg thetaOp (section83JTPProductPS_eq_rhs_pair14 hζ)

theorem thetaOp_section83_pair23
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    thetaOp (section83JTPProductPS (ζ ^ 2)) =
      thetaOp (section83_rhs_pair23 ζ) := by
  exact congrArg thetaOp (section83JTPProductPS_eq_rhs_pair23 hζ)

theorem thetaOp_section83_rhs_pair14
    (ζ : ℂ) :
    thetaOp (section83_rhs_pair14 ζ) =
      thetaOp (section83A ℂ) +
        PowerSeries.C (quinticPeriodBeta ζ) *
          (PowerSeries.X * section83B ℂ +
            PowerSeries.X * thetaOp (section83B ℂ)) := by
  rw [section83_rhs_pair14, thetaOp_add]
  congr 1
  rw [show PowerSeries.C (quinticPeriodBeta ζ) * PowerSeries.X * section83B ℂ =
      PowerSeries.C (quinticPeriodBeta ζ) * (PowerSeries.X * section83B ℂ) by ring]
  rw [thetaOp_C_mul, thetaOp_X_mul]

theorem thetaOp_section83_rhs_pair23
    (ζ : ℂ) :
    thetaOp (section83_rhs_pair23 ζ) =
      thetaOp (section83A ℂ) +
        PowerSeries.C (quinticPeriodAlpha ζ) *
          (PowerSeries.X * section83B ℂ +
            PowerSeries.X * thetaOp (section83B ℂ)) := by
  rw [section83_rhs_pair23, thetaOp_add]
  congr 1
  rw [show PowerSeries.C (quinticPeriodAlpha ζ) * PowerSeries.X * section83B ℂ =
      PowerSeries.C (quinticPeriodAlpha ζ) * (PowerSeries.X * section83B ℂ) by ring]
  rw [thetaOp_C_mul, thetaOp_X_mul]

theorem thetaOp_fifth_root_collapse_complex
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    thetaOp
        ((∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) *
          expand25Qpoch ℂ) =
      thetaOp ((expand5Qpoch ℂ) ^ 6) := by
  exact congrArg thetaOp
    (prod_scaleX_qPochInfPS_fifth_collapse_complex hζ)

theorem thetaOp_fifth_root_collapse_complex_expanded
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) *
        thetaOp (expand25Qpoch ℂ) +
      expand25Qpoch ℂ *
        thetaOp (∏ j : Fin 5, scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) =
      (6 : ℂ⟦X⟧) * (expand5Qpoch ℂ) ^ 5 *
        thetaOp (expand5Qpoch ℂ) := by
  have h := thetaOp_fifth_root_collapse_complex hζ
  rw [thetaOp_mul, thetaOp_pow] at h
  simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h

/-- Current Chapter 15 endpoint with the same statement as `Ch15RODE`.

This theorem has no local proof placeholder; its unconditional status is
exactly the status of `Ch15RODE.chan_theorem_11_7`, namely it still depends on
the integer coefficient core in `Chapter15_R_ODE.lean`. -/
theorem chan_theorem_11_7_from_current_core
    (R : Type*) [CommRing R] :
    chan15LHSPS R * expand5Qpoch R = (qPochInfPS R) ^ 5 := by
  simpa [expand5Qpoch] using chan_theorem_11_7 R

end Ch15DobbieFromJTP
end Pending
end QseriesFormalization
