import QseriesFormalization.Pending.Chapter15_R_ODE
import QseriesFormalization.Pending.RamanujanQuinticJTP

/-!
# Dobbie identity, fifth-root specialization

This file packages the `x = ζ`, `z = ζ²` specialization of Dobbie's
two-variable identity in the denominator-cleared formal-power-series form used
for Chan Theorem 11.7 / Eq. 15.8.
-/

namespace QseriesFormalization
namespace Pending
namespace DobbieIdentity

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch15RODE
open QseriesFormalization.Pending.RamanujanQuintic
open QseriesFormalization.Pending.RamanujanQuinticJTP

noncomputable def zeta5 : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 5)

theorem zeta5_isPrimitiveRoot : IsPrimitiveRoot zeta5 5 := by
  simpa [zeta5] using Complex.isPrimitiveRoot_exp 5 (by norm_num : (5 : ℕ) ≠ 0)

noncomputable def expand5Qpoch (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (qPochInfPS R)

noncomputable def expand25Qpoch (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.expand 25 (by decide : (25 : ℕ) ≠ 0) (qPochInfPS R)

noncomputable def dobbiePrefactor (x z : ℂ) : ℂ :=
  (x - z) * (1 - x * z) / ((1 - x) ^ 2 * (1 - z) ^ 2)

noncomputable def dobbieThetaProduct (x z : ℂ) : ℂ⟦X⟧ :=
  section83JTPProductPS x * section83JTPProductPS z

/-- Dobbie's two-variable product side in the shifted JTP convention already
used by the quintic infrastructure. -/
noncomputable def F (x z : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.C (dobbiePrefactor x z) * dobbieThetaProduct x z

theorem fifth_root_qpoch_collapse_at_zeta5 :
    (∏ j : Fin 5, scaleX (zeta5 ^ (j : ℕ)) (qPochInfPS ℂ)) *
        expand25Qpoch ℂ =
      (expand5Qpoch ℂ) ^ 6 := by
  simpa [expand5Qpoch, expand25Qpoch] using
    prod_scaleX_qPochInfPS_fifth_collapse_complex
      (ζ := zeta5) zeta5_isPrimitiveRoot

theorem denominator_core_mul_expand25_qpoch :
    Ch16MBIProof.E5DenominatorCoreRat *
        expand25Qpoch ℚ =
      (expand5Qpoch ℚ) ^ 6 := by
  simpa [expand5Qpoch, expand25Qpoch] using
    E5DenominatorCoreRat_mul_expand_twentyfive_qPochInfPS

/-- Chan Eq. 15.8, i.e. the Dobbie specialization after division by `sqrt 5`. -/
theorem specialized_dobbie_identity (R : Type*) [CommRing R] :
    chan15LHSPS R * expand5Qpoch R = (qPochInfPS R) ^ 5 := by
  simpa [expand5Qpoch] using chan_theorem_11_7 R

theorem specialized_dobbie_identity_complex :
    chan15LHSPS ℂ * expand5Qpoch ℂ = (qPochInfPS ℂ) ^ 5 :=
  specialized_dobbie_identity ℂ

theorem specialized_dobbie_identity_int :
    chan15LHSPS ℤ * expand5Qpoch ℤ = (qPochInfPS ℤ) ^ 5 :=
  specialized_dobbie_identity ℤ

theorem specialized_dobbie_identity_rat :
    chan15LHSPS ℚ * expand5Qpoch ℚ = (qPochInfPS ℚ) ^ 5 :=
  specialized_dobbie_identity ℚ

theorem coeff_specialized_dobbie_identity
    (R : Type*) [CommRing R] (n : ℕ) :
    (chan15LHSPS R * expand5Qpoch R).coeff n =
      ((qPochInfPS R) ^ 5).coeff n := by
  exact congrArg (fun φ : R⟦X⟧ => φ.coeff n)
    (specialized_dobbie_identity R)

end DobbieIdentity
end Pending
end QseriesFormalization
