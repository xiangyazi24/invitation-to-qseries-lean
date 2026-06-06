import QseriesFormalization.Pending.Chapter20_Eisenstein
import QseriesFormalization.Pending.Chapter20_LiouvilleConvolution

/-!
# Chapter 20: assembly for the mod-691 tau route

This file collects the currently proved pieces of the Liouville/Eisenstein
approach.  The all-`n` `sigma_1 * sigma_3` Lahiri identity now gives the
formal `E4` Ramanujan theta equation.  The discriminant and mod-691 tau
congruence steps are exposed as thin conditional bridges, because the
independent `E6` theta equation and the weight-12 linear Eisenstein identity
are not proved in the imported files.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch20TauMod691Proof

open PowerSeries
open scoped PowerSeries

theorem liouville_lahiriSigma1Sigma3_all (n : Nat) :
    (240 : Int) * QseriesFormalization.Pending.Ch20LiouvilleConvolution.sigma1Sigma3ConvZ n =
      21 * QseriesFormalization.Pending.Ch20LiouvilleConvolution.sigmaPowZ 5 n + (10 - 30 * (n : Int)) * QseriesFormalization.Pending.Ch20LiouvilleConvolution.sigmaPowZ 3 n -
        QseriesFormalization.Pending.Ch20LiouvilleConvolution.sigmaPowZ 1 n :=
  QseriesFormalization.Pending.Ch20LiouvilleConvolution.twoforty_mul_sigma1Sigma3ConvZ_eq_lahiri n

theorem lahiriSigma1Sigma3IdentityAt_all (n : Nat) :
    QseriesFormalization.Pending.Ch20Eisenstein.lahiriSigma1Sigma3IdentityAt n :=
  QseriesFormalization.Pending.Ch20Eisenstein.lahiriSigma1Sigma3IdentityAt_all n

theorem ramanujanThetaE4ArithmeticIdentityAt_all (n : Nat) :
    QseriesFormalization.Pending.Ch20Eisenstein.ramanujanThetaE4ArithmeticIdentityAt n :=
  QseriesFormalization.Pending.Ch20Eisenstein.ramanujanThetaE4ArithmeticIdentityAt_all n

theorem RamanujanThetaE4_from_lahiri : QseriesFormalization.Pending.Ch20Eisenstein.RamanujanThetaE4 :=
  QseriesFormalization.Pending.Ch20Eisenstein.RamanujanThetaE4_all

theorem RamanujanThetaE6_from_liouville : QseriesFormalization.Pending.Ch20Eisenstein.RamanujanThetaE6 :=
  QseriesFormalization.Pending.Ch20Eisenstein.RamanujanThetaE6_all

theorem eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS
    (hE6 : QseriesFormalization.Pending.Ch20Eisenstein.RamanujanThetaE6) :
    QseriesFormalization.Pending.Ch20Eisenstein.eisensteinE4PS ^ 3 - QseriesFormalization.Pending.Ch20Eisenstein.eisensteinE6PS ^ 2 =
      (PowerSeries.C (1728 : ℚ)) * QseriesFormalization.PartIV.Ch20.discriminantPS ℚ :=
  QseriesFormalization.Pending.Ch20Eisenstein.eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS
    RamanujanThetaE4_from_lahiri hE6

theorem eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS_all :
    QseriesFormalization.Pending.Ch20Eisenstein.eisensteinE4PS ^ 3 - QseriesFormalization.Pending.Ch20Eisenstein.eisensteinE6PS ^ 2 =
      (PowerSeries.C (1728 : ℚ)) * QseriesFormalization.PartIV.Ch20.discriminantPS ℚ :=
  eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS
    RamanujanThetaE6_from_liouville

/-! ## Lightweight local mod-691 bridge

The current compiled `Chapter20` module in this workspace predates the generic
mod-691 bridge definitions now present in source, so this assembly file keeps a
local version using only the stable `discriminantPS`, `ramanujanTau`, and
`sigma11` interface.
-/

noncomputable def eisensteinE12PSMod691 : (ZMod 691)⟦X⟧ :=
  PowerSeries.mk fun n => (QseriesFormalization.PartIV.Ch20.sigma11 n : ZMod 691)

@[simp] theorem coeff_eisensteinE12PSMod691 (n : Nat) :
    eisensteinE12PSMod691.coeff n = (QseriesFormalization.PartIV.Ch20.sigma11 n : ZMod 691) := by
  simp [eisensteinE12PSMod691]

theorem ramanujanTau_congr_sigma11_mod_691_of_discriminant_eq_eisensteinE12
    (h : QseriesFormalization.PartIV.Ch20.discriminantPS (ZMod 691) = eisensteinE12PSMod691) (n : Nat) :
    (QseriesFormalization.PartIV.Ch20.ramanujanTau ℤ n : ZMod 691) = (QseriesFormalization.PartIV.Ch20.sigma11 n : ZMod 691) := by
  rw [QseriesFormalization.PartIV.Ch20.cast_ramanujanTau_int (ZMod 691) n]
  unfold QseriesFormalization.PartIV.Ch20.ramanujanTau
  simpa using congrArg (fun f : (ZMod 691)⟦X⟧ => f.coeff n) h

noncomputable def divisorSigmaPowerPS (R : Type*) [CommRing R] (r : Nat) : R⟦X⟧ :=
  PowerSeries.mk fun n => ((Nat.divisorSum n fun d => d ^ r : Nat) : R)

noncomputable def eisensteinE4PS (R : Type*) [CommRing R] : R⟦X⟧ :=
  1 + (240 : R⟦X⟧) * divisorSigmaPowerPS R 3

noncomputable def eisensteinE6PS (R : Type*) [CommRing R] : R⟦X⟧ :=
  1 - (504 : R⟦X⟧) * divisorSigmaPowerPS R 5

noncomputable def eisensteinS11PS (R : Type*) [CommRing R] : R⟦X⟧ :=
  divisorSigmaPowerPS R 11

@[simp] theorem coeff_eisensteinS11PS
    (R : Type*) [CommRing R] (n : Nat) :
    (eisensteinS11PS R).coeff n = (QseriesFormalization.PartIV.Ch20.sigma11 n : R) := by
  simp [eisensteinS11PS, divisorSigmaPowerPS, QseriesFormalization.PartIV.Ch20.sigma11]

theorem eisensteinE12PSMod691_eq_eisensteinS11PS :
    eisensteinE12PSMod691 = eisensteinS11PS (ZMod 691) := by
  ext n
  simp [eisensteinE12PSMod691]

def eisensteinDeltaIdentityMod691 : Prop :=
  eisensteinE4PS (ZMod 691) ^ 3 - eisensteinE6PS (ZMod 691) ^ 2 =
    (1728 : (ZMod 691)⟦X⟧) * QseriesFormalization.PartIV.Ch20.discriminantPS (ZMod 691)

def eisensteinWeight12LinearIdentityMod691 : Prop :=
  (441 : (ZMod 691)⟦X⟧) * eisensteinE4PS (ZMod 691) ^ 3 +
      (250 : (ZMod 691)⟦X⟧) * eisensteinE6PS (ZMod 691) ^ 2 =
    (691 : (ZMod 691)⟦X⟧) + (65520 : (ZMod 691)⟦X⟧) *
      eisensteinS11PS (ZMod 691)

private theorem zmod691_ps_natCast_691 :
    (691 : (ZMod 691)⟦X⟧) = 0 := by
  change PowerSeries.C (691 : ZMod 691) = 0
  have h : (691 : ZMod 691) = 0 := by native_decide
  rw [h]
  simp

private theorem zmod691_199_mul_65520 :
    (199 : ZMod 691) * (65520 : ZMod 691) = 1 := by
  native_decide

theorem eisensteinS11PS_eq_discriminantPS_mod_691_of_eisenstein_identities
    (hDelta : eisensteinDeltaIdentityMod691)
    (hLinear : eisensteinWeight12LinearIdentityMod691) :
    eisensteinS11PS (ZMod 691) = QseriesFormalization.PartIV.Ch20.discriminantPS (ZMod 691) := by
  let PS := (ZMod 691)⟦X⟧
  let E4 : PS := eisensteinE4PS (ZMod 691)
  let E6 : PS := eisensteinE6PS (ZMod 691)
  let S : PS := eisensteinS11PS (ZMod 691)
  let D : PS := QseriesFormalization.PartIV.Ch20.discriminantPS (ZMod 691)
  change E4 ^ 3 - E6 ^ 2 = (1728 : PS) * D at hDelta
  change (441 : PS) * E4 ^ 3 + (250 : PS) * E6 ^ 2 =
    (691 : PS) + (65520 : PS) * S at hLinear
  change S = D
  ext n
  have hDeltaCoeff := congrArg (fun f : PS => f.coeff n) hDelta
  change (E4 ^ 3 - E6 ^ 2).coeff n = ((1728 : PS) * D).coeff n at hDeltaCoeff
  rw [map_sub] at hDeltaCoeff
  change (E4 ^ 3).coeff n - (E6 ^ 2).coeff n =
    (PowerSeries.C (1728 : ZMod 691) * D).coeff n at hDeltaCoeff
  rw [PowerSeries.coeff_C_mul] at hDeltaCoeff
  have hLinearCoeff := congrArg (fun f : PS => f.coeff n) hLinear
  change
      ((441 : PS) * E4 ^ 3 + (250 : PS) * E6 ^ 2).coeff n =
        ((691 : PS) + (65520 : PS) * S).coeff n
    at hLinearCoeff
  rw [map_add, map_add] at hLinearCoeff
  rw [zmod691_ps_natCast_691] at hLinearCoeff
  change
      (PowerSeries.C (441 : ZMod 691) * E4 ^ 3).coeff n +
          (PowerSeries.C (250 : ZMod 691) * E6 ^ 2).coeff n =
        (0 : PS).coeff n + (PowerSeries.C (65520 : ZMod 691) * S).coeff n
    at hLinearCoeff
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul] at hLinearCoeff
  simp only [map_zero, zero_add] at hLinearCoeff
  have h691 : (691 : ZMod 691) = 0 := by native_decide
  have h4411728 : (441 : ZMod 691) * (1728 : ZMod 691) = (65520 : ZMod 691) := by
    native_decide
  have hcoeff : (65520 : ZMod 691) * S.coeff n =
      (65520 : ZMod 691) * D.coeff n := by
    calc
      (65520 : ZMod 691) * S.coeff n
          = (441 : ZMod 691) * (E4 ^ 3).coeff n +
              (250 : ZMod 691) * (E6 ^ 2).coeff n := by
              rw [hLinearCoeff]
      _ = (441 : ZMod 691) * ((E4 ^ 3).coeff n - (E6 ^ 2).coeff n) +
            (691 : ZMod 691) * (E6 ^ 2).coeff n := by ring
      _ = (441 : ZMod 691) * ((1728 : ZMod 691) * D.coeff n) +
            (691 : ZMod 691) * (E6 ^ 2).coeff n := by rw [hDeltaCoeff]
      _ = ((441 : ZMod 691) * (1728 : ZMod 691)) * D.coeff n +
            (0 : ZMod 691) * (E6 ^ 2).coeff n := by
            rw [h691]
            ring
      _ = (65520 : ZMod 691) * D.coeff n := by
            rw [h4411728]
            ring
  calc
    S.coeff n = 1 * S.coeff n := by ring
    _ = ((199 : ZMod 691) * (65520 : ZMod 691)) * S.coeff n := by
          rw [zmod691_199_mul_65520]
    _ = (199 : ZMod 691) * ((65520 : ZMod 691) * S.coeff n) := by ring
    _ = (199 : ZMod 691) * ((65520 : ZMod 691) * D.coeff n) := by rw [hcoeff]
    _ = ((199 : ZMod 691) * (65520 : ZMod 691)) * D.coeff n := by ring
    _ = 1 * D.coeff n := by rw [zmod691_199_mul_65520]
    _ = D.coeff n := by ring

theorem discriminantPS_eq_eisensteinE12PSMod691_of_eisenstein_identities
    (hDelta : eisensteinDeltaIdentityMod691)
    (hLinear : eisensteinWeight12LinearIdentityMod691) :
    QseriesFormalization.PartIV.Ch20.discriminantPS (ZMod 691) = eisensteinE12PSMod691 := by
  rw [eisensteinE12PSMod691_eq_eisensteinS11PS]
  exact (eisensteinS11PS_eq_discriminantPS_mod_691_of_eisenstein_identities
    hDelta hLinear).symm

theorem ramanujanTau_congr_sigma11_mod_691_of_eisenstein_identities
    (hDelta : eisensteinDeltaIdentityMod691)
    (hLinear : eisensteinWeight12LinearIdentityMod691) (n : Nat) :
    (QseriesFormalization.PartIV.Ch20.ramanujanTau ℤ n : ZMod 691) = (QseriesFormalization.PartIV.Ch20.sigma11 n : ZMod 691) :=
  ramanujanTau_congr_sigma11_mod_691_of_discriminant_eq_eisensteinE12
    (discriminantPS_eq_eisensteinE12PSMod691_of_eisenstein_identities
      hDelta hLinear) n

end Ch20TauMod691Proof
end Pending
end QseriesFormalization
