import QseriesFormalization.Pending.Chapter13_RRCF_RForm
import QseriesFormalization.Pending.Chapter13_Thm113
import QseriesFormalization.Pending.Chapter13_Eq1237
import QseriesFormalization.Pending.Chapter13_Watson_Algebraic

/-!
# Chapter 13 / §11.5 — Chan's "difficult and deep" identity (Theorem 11.5)

This file assembles the final Watson proof from the Chapter 13 prerequisites.

## The identity

Chan (cf. Hirschhorn, *The Power of q*, §9.2) calls the following the
"deep and difficult" identity of Ramanujan / Rogers-Ramanujan continued
fraction theory:

  `R(q)⁵ = R(q⁵) · (1 − 2·R(q⁵) + 4·R(q⁵)² − 3·R(q⁵)³ + R(q⁵)⁴)
                 / (1 + 3·R(q⁵) + 4·R(q⁵)² + 2·R(q⁵)³ + R(q⁵)⁴)`

where `R(q)` is the Rogers-Ramanujan continued fraction.  Since both sides
involve fractional `q`-powers (R(q) carries a `q^{1/5}` prefactor), we work
with the fractional-power-free variables defined in
`Pending/Chapter13_RRCF_RForm`:

  `r(q) := R(q)·q^{-1/5} = (q,q⁴,q⁵;q⁵)_∞ / (q²,q³,q⁵;q⁵)_∞`,
  `v := X · r(q⁵) = X · PowerSeries.expand 5 r(q)`.

Then the identity becomes the *formal-power-series* identity:

  `r(q)⁵ · (1 + 3v + 4v² + 2v³ + v⁴) = r(q⁵) · (1 − 2v + 4v² − 3v³ + v⁴)`.

Both denominators on the RHS / LHS are units in `ℚ⟦X⟧` (proved as
`Ch13RRCF.isUnit_rrcfDenomLHS` and `Ch13RRCF.isUnit_rrcfDenomRHS`), so the
quotient form `r(q)⁵ = r(q⁵)·N(v)/D(v)` is valid as a multiplicative
inverse identity in `ℚ⟦X⟧`; we state the **multiplicative form** below to
avoid any division.

## Numerical evidence

The identity has been verified term-by-term in `ℚ⟦X⟧` up to degree 60 by a
Sage/Python script; the residual difference at every degree is `0` (see
the Hirschhorn §9.2 derivation for the analytic reason).

The proof below follows Watson's algebraic route: Theorem 11.3 and Eq. 12.37
put `X * r(q)^5` and `v = X * r(q^5)` on the same quadratic branch, and
Watson's polynomial identities identify the branch.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch13DeepIdentity

open QseriesFormalization.Pending.Ch13RRCF
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.Ch16MBIProof

open PowerSeries

private theorem X_pow_mul_cancel {R : Type*} [CommSemiring R] (n : ℕ)
    {φ ψ : R⟦X⟧} (h : PowerSeries.X ^ n * φ = PowerSeries.X ^ n * ψ) :
    φ = ψ := by
  induction n with
  | zero =>
      simpa using h
  | succ n ih =>
    apply ih
    have h' :
        PowerSeries.X * (PowerSeries.X ^ n * φ) =
          PowerSeries.X * (PowerSeries.X ^ n * ψ) := by
      calc
        PowerSeries.X * (PowerSeries.X ^ n * φ) =
            PowerSeries.X ^ (n + 1) * φ := by ring
        _ = PowerSeries.X ^ (n + 1) * ψ := h
        _ = PowerSeries.X * (PowerSeries.X ^ n * ψ) := by ring
    exact PowerSeries.X_mul_cancel h'

private theorem isUnit_qPochInfPS_rat :
    IsUnit (qPochInfPS ℚ) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [coeff_zero_qPochInfPS]
  exact isUnit_one

private theorem isUnit_expand_qPochInfPS_rat (n : ℕ) (hn : n ≠ 0) :
    IsUnit (PowerSeries.expand n hn (qPochInfPS ℚ)) := by
  have hcoeff : (PowerSeries.expand n hn (qPochInfPS ℚ)).coeff 0 = 1 := by
    rw [PowerSeries.coeff_expand]
    simp [coeff_zero_qPochInfPS]
  rw [PowerSeries.isUnit_iff_constantCoeff,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff]
  exact isUnit_one

private theorem isUnit_expand_pentagonal023SeriesPS_rat (n : ℕ) (hn : n ≠ 0) :
    IsUnit (PowerSeries.expand n hn (pentagonal023SeriesPS ℚ)) := by
  have hcoeff :
      (PowerSeries.expand n hn (pentagonal023SeriesPS ℚ)).coeff 0 = 1 := by
    rw [PowerSeries.coeff_expand]
    simpa using coeff_zero_pentagonal023SeriesPS_rat
  rw [PowerSeries.isUnit_iff_constantCoeff,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff]
  exact isUnit_one

private theorem rrcf_expand_mul_pentagonal023 :
    (PowerSeries.expand 5 (by decide) rrcf_r) *
        PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ) =
      PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ) := by
  rw [← map_mul, rrcf_r_mul_pentagonal023SeriesPS_eq]

private theorem pentagonal014_mul_pentagonal023 :
    pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ =
      qPochInfPS ℚ * PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) :=
  pentagonal014Series_mul_pentagonal023Series_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat

private theorem expand_pentagonal014_mul_pentagonal023 :
    PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ) *
        PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ) =
      PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) *
        PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) := by
  have h := congrArg (PowerSeries.expand 5 (by decide)) pentagonal014_mul_pentagonal023
  rw [map_mul, map_mul] at h
  rw [← PowerSeries.expand_mul (p := 5) (hp := by decide) (q := 5)
    (hq := by decide) (qPochInfPS ℚ)] at h
  simpa using h

private theorem chan113_cleared_rrcf_v :
    let E : ℚ⟦X⟧ := qPochInfPS ℚ
    let F : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
    let G5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ)
    let C : ℚ⟦X⟧ := 1 - rrcf_v - rrcf_v ^ 2
    C * G5 ^ 2 = E * F := by
  dsimp
  have hvG := rrcf_v_mul_expand_pentagonal023SeriesPS_eq
  let G5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ)
  let H5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ)
  calc
    (1 - rrcf_v - rrcf_v ^ 2) *
        (PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ)) ^ 2 =
      G5 ^ 2 - (rrcf_v * G5) * G5 - (rrcf_v * G5) ^ 2 := by
        simp [G5]
        ring
    _ =
      G5 ^ 2 - (PowerSeries.X * H5) * G5 - (PowerSeries.X * H5) ^ 2 := by
        rw [hvG]
    _ =
      (PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ)) ^ 2 -
        PowerSeries.X *
          PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ) *
          PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ) -
        PowerSeries.X ^ 2 *
          (PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ)) ^ 2 := by
        simp [G5, H5]
        ring
    _ = qPochInfPS ℚ * PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) :=
        QseriesFormalization.Pending.Ch13Thm113.chan_theorem_11_3_formal_ps

private theorem chan113_ratio_cleared :
    let E : ℚ⟦X⟧ := qPochInfPS ℚ
    let W : ℚ⟦X⟧ := PowerSeries.expand 25 (by decide) (qPochInfPS ℚ)
    let C : ℚ⟦X⟧ := 1 - rrcf_v - rrcf_v ^ 2
    rrcf_v * E = PowerSeries.X * C * W := by
  dsimp
  let E : ℚ⟦X⟧ := qPochInfPS ℚ
  let F : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
  let W : ℚ⟦X⟧ := PowerSeries.expand 25 (by decide) (qPochInfPS ℚ)
  let H5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ)
  let G5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ)
  let C : ℚ⟦X⟧ := 1 - rrcf_v - rrcf_v ^ 2
  have h113 : C * G5 ^ 2 = E * F := by
    simpa [E, F, G5, C] using chan113_cleared_rrcf_v
  have hVG : rrcf_v * G5 = PowerSeries.X * H5 := by
    simpa [G5, H5] using rrcf_v_mul_expand_pentagonal023SeriesPS_eq
  have hHG : H5 * G5 = F * W := by
    simpa [H5, G5, F, W] using expand_pentagonal014_mul_pentagonal023
  have hmul :
      F * (rrcf_v * E) = F * (PowerSeries.X * C * W) := by
    calc
      F * (rrcf_v * E) = rrcf_v * (E * F) := by ring
      _ = rrcf_v * (C * G5 ^ 2) := by rw [h113]
      _ = C * ((rrcf_v * G5) * G5) := by ring
      _ = C * ((PowerSeries.X * H5) * G5) := by rw [hVG]
      _ = F * (PowerSeries.X * C * W) := by
        rw [show (PowerSeries.X * H5) * G5 = PowerSeries.X * (H5 * G5) by ring,
          hHG]
        ring
  exact (isUnit_expand_qPochInfPS_rat 5 (by decide)).mul_right_inj.mp hmul

private theorem rrcf_pow_five_mul_pentagonal023_pow_five :
    rrcf_r ^ 5 * (pentagonal023SeriesPS ℚ) ^ 5 =
      (pentagonal014SeriesPS ℚ) ^ 5 := by
  rw [← mul_pow, rrcf_r_mul_pentagonal023SeriesPS_eq]

private theorem X_rrcf_pow_five_mul_pentagonal023_pow_five :
    (PowerSeries.X * rrcf_r ^ 5) * (pentagonal023SeriesPS ℚ) ^ 5 =
      PowerSeries.X * (pentagonal014SeriesPS ℚ) ^ 5 := by
  rw [mul_assoc, rrcf_pow_five_mul_pentagonal023_pow_five]

private theorem rrcf_v_pow_five_mul_G5_pow_ten :
    let H5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ)
    let G5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ)
    rrcf_v ^ 5 * G5 ^ 10 =
      PowerSeries.X ^ 5 * H5 ^ 5 * G5 ^ 5 := by
  dsimp
  let H5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ)
  let G5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ)
  have hVG : rrcf_v * G5 = PowerSeries.X * H5 := by
    simpa [H5, G5] using rrcf_v_mul_expand_pentagonal023SeriesPS_eq
  calc
    rrcf_v ^ 5 * G5 ^ 10 = (rrcf_v * G5) ^ 5 * G5 ^ 5 := by ring
    _ = (PowerSeries.X * H5) ^ 5 * G5 ^ 5 := by rw [hVG]
    _ = PowerSeries.X ^ 5 * H5 ^ 5 * G5 ^ 5 := by ring

private theorem rrcf_v_pow_ten_mul_G5_pow_ten :
    let H5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ)
    let G5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ)
    rrcf_v ^ 10 * G5 ^ 10 = PowerSeries.X ^ 10 * H5 ^ 10 := by
  dsimp
  let H5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ)
  let G5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ)
  have hVG : rrcf_v * G5 = PowerSeries.X * H5 := by
    simpa [H5, G5] using rrcf_v_mul_expand_pentagonal023SeriesPS_eq
  calc
    rrcf_v ^ 10 * G5 ^ 10 = (rrcf_v * G5) ^ 10 := by ring
    _ = (PowerSeries.X * H5) ^ 10 := by rw [hVG]
    _ = PowerSeries.X ^ 10 * H5 ^ 10 := by ring

private theorem eq1237_original_branch :
    let E : ℚ⟦X⟧ := qPochInfPS ℚ
    let F : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
    let Y : ℚ⟦X⟧ := PowerSeries.X * rrcf_r ^ 5
    E ^ 6 * Y = PowerSeries.X * F ^ 6 * (1 - 11 * Y - Y ^ 2) := by
  dsimp
  let E : ℚ⟦X⟧ := qPochInfPS ℚ
  let F : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
  let H : ℚ⟦X⟧ := pentagonal014SeriesPS ℚ
  let G : ℚ⟦X⟧ := pentagonal023SeriesPS ℚ
  let Y : ℚ⟦X⟧ := PowerSeries.X * rrcf_r ^ 5
  have hYG : Y * G ^ 5 = PowerSeries.X * H ^ 5 := by
    simpa [Y, H, G] using X_rrcf_pow_five_mul_pentagonal023_pow_five
  have hYG10 : Y * G ^ 10 = PowerSeries.X * H ^ 5 * G ^ 5 := by
    calc
      Y * G ^ 10 = (Y * G ^ 5) * G ^ 5 := by ring
      _ = (PowerSeries.X * H ^ 5) * G ^ 5 := by rw [hYG]
      _ = PowerSeries.X * H ^ 5 * G ^ 5 := by ring
  have hY2G10 : Y ^ 2 * G ^ 10 = PowerSeries.X ^ 2 * H ^ 10 := by
    calc
      Y ^ 2 * G ^ 10 = (Y * G ^ 5) ^ 2 := by ring
      _ = (PowerSeries.X * H ^ 5) ^ 2 := by rw [hYG]
      _ = PowerSeries.X ^ 2 * H ^ 10 := by ring
  have hcore :
      (G ^ 10 -
          (11 : ℚ⟦X⟧) * PowerSeries.X * H ^ 5 * G ^ 5 -
          PowerSeries.X ^ 2 * H ^ 10) =
        G ^ 10 * (1 - 11 * Y - Y ^ 2) := by
    calc
      G ^ 10 -
          (11 : ℚ⟦X⟧) * PowerSeries.X * H ^ 5 * G ^ 5 -
          PowerSeries.X ^ 2 * H ^ 10 =
        G ^ 10 - (11 : ℚ⟦X⟧) * (Y * G ^ 10) - Y ^ 2 * G ^ 10 := by
          rw [hYG10, hY2G10]
          ring
      _ = G ^ 10 * (1 - 11 * Y - Y ^ 2) := by ring
  have hEq : E ^ 6 * H ^ 5 * G ^ 5 =
      F ^ 6 *
        (G ^ 10 -
          (11 : ℚ⟦X⟧) * PowerSeries.X * H ^ 5 * G ^ 5 -
          PowerSeries.X ^ 2 * H ^ 10) := by
    simpa [E, F, H, G] using
      QseriesFormalization.Pending.Ch13Eq1237.chan_eq_12_37_cleared
  have hmul :
      G ^ 10 * (E ^ 6 * Y) =
        G ^ 10 * (PowerSeries.X * F ^ 6 * (1 - 11 * Y - Y ^ 2)) := by
    calc
      G ^ 10 * (E ^ 6 * Y) = E ^ 6 * (Y * G ^ 10) := by ring
      _ = E ^ 6 * (PowerSeries.X * H ^ 5 * G ^ 5) := by rw [hYG10]
      _ = PowerSeries.X * (E ^ 6 * H ^ 5 * G ^ 5) := by ring
      _ = PowerSeries.X *
          (F ^ 6 *
            (G ^ 10 -
              (11 : ℚ⟦X⟧) * PowerSeries.X * H ^ 5 * G ^ 5 -
              PowerSeries.X ^ 2 * H ^ 10)) := by
        rw [hEq]
      _ = G ^ 10 * (PowerSeries.X * F ^ 6 * (1 - 11 * Y - Y ^ 2)) := by
        rw [hcore]
        ring
  exact ((isUnit_pentagonal023SeriesPS_rat.pow 10).mul_right_inj.mp hmul)

private theorem eq1237_expanded_ratio :
    let F : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
    let W : ℚ⟦X⟧ := PowerSeries.expand 25 (by decide) (qPochInfPS ℚ)
    let C : ℚ⟦X⟧ := 1 - rrcf_v - rrcf_v ^ 2
    let A : ℚ⟦X⟧ :=
      QseriesFormalization.Pending.WatsonAlgebraic.A rrcf_v
    let B : ℚ⟦X⟧ :=
      QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v
    F ^ 6 * rrcf_v ^ 5 = PowerSeries.X ^ 5 * W ^ 6 * C * A * B := by
  dsimp
  let F : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
  let W : ℚ⟦X⟧ := PowerSeries.expand 25 (by decide) (qPochInfPS ℚ)
  let H5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ)
  let G5 : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ)
  let C : ℚ⟦X⟧ := 1 - rrcf_v - rrcf_v ^ 2
  let A : ℚ⟦X⟧ := QseriesFormalization.Pending.WatsonAlgebraic.A rrcf_v
  let B : ℚ⟦X⟧ := QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v
  have hEq :
      F ^ 6 * H5 ^ 5 * G5 ^ 5 =
        W ^ 6 *
          (G5 ^ 10 -
            (11 : ℚ⟦X⟧) * PowerSeries.X ^ 5 * H5 ^ 5 * G5 ^ 5 -
            PowerSeries.X ^ 10 * H5 ^ 10) := by
    have hmap := congrArg (PowerSeries.expand 5 (by decide))
      QseriesFormalization.Pending.Ch13Eq1237.chan_eq_12_37_cleared
    rw [map_mul, map_mul, map_pow, map_pow, map_pow,
      map_mul, map_sub, map_sub, map_pow, map_mul, map_mul, map_mul,
      map_pow, map_pow, map_pow, PowerSeries.expand_X] at hmap
    rw [← PowerSeries.expand_mul (p := 5) (hp := by decide) (q := 5)
      (hq := by decide) (qPochInfPS ℚ)] at hmap
    have h11 :
        PowerSeries.expand 5 (by decide) (11 : ℚ⟦X⟧) = (11 : ℚ⟦X⟧) := by
      rw [show (11 : ℚ⟦X⟧) = PowerSeries.C (11 : ℚ) by
        exact (map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 11).symm]
      rw [PowerSeries.expand_C]
    have hXsq : (PowerSeries.X ^ 5 : ℚ⟦X⟧) ^ 2 = PowerSeries.X ^ 10 := by
      ring
    rw [map_mul, map_pow, map_pow, PowerSeries.expand_X] at hmap
    rw [h11, hXsq] at hmap
    simpa [F, W, H5, G5] using hmap
  have hV5 : rrcf_v ^ 5 * G5 ^ 10 =
      PowerSeries.X ^ 5 * H5 ^ 5 * G5 ^ 5 := by
    simpa [H5, G5] using rrcf_v_pow_five_mul_G5_pow_ten
  have hV10 : rrcf_v ^ 10 * G5 ^ 10 =
      PowerSeries.X ^ 10 * H5 ^ 10 := by
    simpa [H5, G5] using rrcf_v_pow_ten_mul_G5_pow_ten
  have hwatson :
      C * A * B = 1 - 11 * rrcf_v ^ 5 - rrcf_v ^ 10 := by
    simpa [C, A, B] using
      QseriesFormalization.Pending.WatsonAlgebraic.watson_core_identity
        (R := ℚ⟦X⟧) rrcf_v
  have hcore :
      (G5 ^ 10 -
          (11 : ℚ⟦X⟧) * PowerSeries.X ^ 5 * H5 ^ 5 * G5 ^ 5 -
          PowerSeries.X ^ 10 * H5 ^ 10) =
        G5 ^ 10 * (C * A * B) := by
    calc
      G5 ^ 10 -
          (11 : ℚ⟦X⟧) * PowerSeries.X ^ 5 * H5 ^ 5 * G5 ^ 5 -
          PowerSeries.X ^ 10 * H5 ^ 10 =
        G5 ^ 10 - (11 : ℚ⟦X⟧) * (rrcf_v ^ 5 * G5 ^ 10) -
          rrcf_v ^ 10 * G5 ^ 10 := by
          rw [hV5, hV10]
          ring
      _ = G5 ^ 10 * (1 - 11 * rrcf_v ^ 5 - rrcf_v ^ 10) := by ring
      _ = G5 ^ 10 * (C * A * B) := by rw [hwatson]
  have hmul :
      G5 ^ 10 * (F ^ 6 * rrcf_v ^ 5) =
        G5 ^ 10 * (PowerSeries.X ^ 5 * W ^ 6 * C * A * B) := by
    calc
      G5 ^ 10 * (F ^ 6 * rrcf_v ^ 5) =
          F ^ 6 * (rrcf_v ^ 5 * G5 ^ 10) := by ring
      _ = F ^ 6 * (PowerSeries.X ^ 5 * H5 ^ 5 * G5 ^ 5) := by rw [hV5]
      _ = PowerSeries.X ^ 5 * (F ^ 6 * H5 ^ 5 * G5 ^ 5) := by ring
      _ = PowerSeries.X ^ 5 *
          (W ^ 6 *
            (G5 ^ 10 -
              (11 : ℚ⟦X⟧) * PowerSeries.X ^ 5 * H5 ^ 5 * G5 ^ 5 -
              PowerSeries.X ^ 10 * H5 ^ 10)) := by
          rw [hEq]
      _ = G5 ^ 10 * (PowerSeries.X ^ 5 * W ^ 6 * C * A * B) := by
          rw [hcore]
          ring
  exact ((isUnit_expand_pentagonal023SeriesPS_rat 5 (by decide)).pow 10).mul_right_inj.mp hmul

private theorem isUnit_one_sub_rrcf_v_sub_sq :
    IsUnit (1 - rrcf_v - rrcf_v ^ 2) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have hv : PowerSeries.constantCoeff rrcf_v = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact coeff_zero_rrcf_v_eq_zero
  simp [map_sub, map_pow, hv]

private theorem y_satisfies_watson_branch :
    let C : ℚ⟦X⟧ := 1 - rrcf_v - rrcf_v ^ 2
    let A : ℚ⟦X⟧ :=
      QseriesFormalization.Pending.WatsonAlgebraic.A rrcf_v
    let B : ℚ⟦X⟧ :=
      QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v
    let Y : ℚ⟦X⟧ := PowerSeries.X * rrcf_r ^ 5
    rrcf_v * A * B * (1 - 11 * Y - Y ^ 2) = C ^ 5 * Y := by
  dsimp
  let E : ℚ⟦X⟧ := qPochInfPS ℚ
  let F : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
  let W : ℚ⟦X⟧ := PowerSeries.expand 25 (by decide) (qPochInfPS ℚ)
  let C : ℚ⟦X⟧ := 1 - rrcf_v - rrcf_v ^ 2
  let A : ℚ⟦X⟧ := QseriesFormalization.Pending.WatsonAlgebraic.A rrcf_v
  let B : ℚ⟦X⟧ := QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v
  let Y : ℚ⟦X⟧ := PowerSeries.X * rrcf_r ^ 5
  let Q : ℚ⟦X⟧ := 1 - 11 * Y - Y ^ 2
  have hCE : rrcf_v * E = PowerSeries.X * C * W := by
    simpa [E, W, C] using chan113_ratio_cleared
  have hratio : F ^ 6 * rrcf_v ^ 5 =
      PowerSeries.X ^ 5 * W ^ 6 * C * A * B := by
    simpa [F, W, C, A, B] using eq1237_expanded_ratio
  have hY : E ^ 6 * Y = PowerSeries.X * F ^ 6 * Q := by
    simpa [E, F, Y, Q] using eq1237_original_branch
  have hCE6 : rrcf_v ^ 6 * E ^ 6 = PowerSeries.X ^ 6 * C ^ 6 * W ^ 6 := by
    calc
      rrcf_v ^ 6 * E ^ 6 = (rrcf_v * E) ^ 6 := by ring
      _ = (PowerSeries.X * C * W) ^ 6 := by rw [hCE]
      _ = PowerSeries.X ^ 6 * C ^ 6 * W ^ 6 := by ring
  have hbig :
      PowerSeries.X ^ 6 * W ^ 6 * C * (rrcf_v * A * B * Q) =
        PowerSeries.X ^ 6 * W ^ 6 * C * (C ^ 5 * Y) := by
    calc
      PowerSeries.X ^ 6 * W ^ 6 * C * (rrcf_v * A * B * Q)
          =
        PowerSeries.X * rrcf_v *
          (PowerSeries.X ^ 5 * W ^ 6 * C * A * B) * Q := by ring
      _ = PowerSeries.X * rrcf_v * (F ^ 6 * rrcf_v ^ 5) * Q := by
        rw [hratio]
      _ = rrcf_v ^ 6 * (PowerSeries.X * F ^ 6 * Q) := by ring
      _ = rrcf_v ^ 6 * (E ^ 6 * Y) := by rw [hY]
      _ = (rrcf_v ^ 6 * E ^ 6) * Y := by ring
      _ = (PowerSeries.X ^ 6 * C ^ 6 * W ^ 6) * Y := by rw [hCE6]
      _ = PowerSeries.X ^ 6 * W ^ 6 * C * (C ^ 5 * Y) := by ring
  have hbig' :
      PowerSeries.X ^ 6 * (W ^ 6 * C * (rrcf_v * A * B * Q)) =
        PowerSeries.X ^ 6 * (W ^ 6 * C * (C ^ 5 * Y)) := by
    simpa [mul_assoc] using hbig
  have hnoX :
      W ^ 6 * C * (rrcf_v * A * B * Q) =
        W ^ 6 * C * (C ^ 5 * Y) :=
    X_pow_mul_cancel 6 hbig'
  have hunit : IsUnit (W ^ 6 * C) :=
    (isUnit_expand_qPochInfPS_rat 25 (by decide)).pow 6 |>.mul
      (by simpa [C] using isUnit_one_sub_rrcf_v_sub_sq)
  have hcancel :
      rrcf_v * A * B * Q = C ^ 5 * Y :=
    hunit.mul_right_inj.mp hnoX
  simpa [Q] using hcancel

private theorem isUnit_watson_B_rrcf_v :
    IsUnit (QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v) := by
  simpa [QseriesFormalization.Pending.WatsonAlgebraic.B] using isUnit_rrcfDenomLHS

private theorem constantCoeff_watson_B_rrcf_v_ne_zero :
    PowerSeries.constantCoeff
        (QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v) ≠ 0 := by
  have hv : PowerSeries.constantCoeff rrcf_v = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact coeff_zero_rrcf_v_eq_zero
  have hcc :
      PowerSeries.constantCoeff
          (QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v) = 1 := by
    simp [QseriesFormalization.Pending.WatsonAlgebraic.B, map_add, map_mul, map_pow, hv]
  rw [hcc]
  exact one_ne_zero

private theorem watson_Z_mul_B :
    let A : ℚ⟦X⟧ :=
      QseriesFormalization.Pending.WatsonAlgebraic.A rrcf_v
    let B : ℚ⟦X⟧ :=
      QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v
    let Z : ℚ⟦X⟧ := rrcf_v * A * B⁻¹
    Z * B = rrcf_v * A := by
  dsimp
  let A : ℚ⟦X⟧ := QseriesFormalization.Pending.WatsonAlgebraic.A rrcf_v
  let B : ℚ⟦X⟧ := QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v
  let Z : ℚ⟦X⟧ := rrcf_v * A * B⁻¹
  have hBinv : B⁻¹ * B = 1 := by
    simpa [B] using PowerSeries.inv_mul_cancel
      (QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v)
      constantCoeff_watson_B_rrcf_v_ne_zero
  calc
    Z * B = rrcf_v * A * (B⁻¹ * B) := by ring
    _ = rrcf_v * A := by rw [hBinv]; ring

private theorem z_satisfies_watson_branch :
    let C : ℚ⟦X⟧ := 1 - rrcf_v - rrcf_v ^ 2
    let A : ℚ⟦X⟧ :=
      QseriesFormalization.Pending.WatsonAlgebraic.A rrcf_v
    let B : ℚ⟦X⟧ :=
      QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v
    let Z : ℚ⟦X⟧ := rrcf_v * A * B⁻¹
    rrcf_v * A * B * (1 - 11 * Z - Z ^ 2) = C ^ 5 * Z := by
  dsimp
  let C : ℚ⟦X⟧ := 1 - rrcf_v - rrcf_v ^ 2
  let A : ℚ⟦X⟧ := QseriesFormalization.Pending.WatsonAlgebraic.A rrcf_v
  let B : ℚ⟦X⟧ := QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v
  let Z : ℚ⟦X⟧ := rrcf_v * A * B⁻¹
  have hZB : Z * B = rrcf_v * A := by
    simpa [A, B, Z] using watson_Z_mul_B
  have hquad :
      B ^ 2 - 11 * rrcf_v * A * B - rrcf_v ^ 2 * A ^ 2 = C ^ 5 := by
    simpa [C, A, B] using
      QseriesFormalization.Pending.WatsonAlgebraic.watson_quadratic_identity
        (R := ℚ⟦X⟧) rrcf_v
  have hmul :
      (rrcf_v * A * B * (1 - 11 * Z - Z ^ 2)) * B =
        (C ^ 5 * Z) * B := by
    calc
      (rrcf_v * A * B * (1 - 11 * Z - Z ^ 2)) * B =
          rrcf_v * A * (B ^ 2 - 11 * (Z * B) * B - (Z * B) ^ 2) := by
            ring
      _ = rrcf_v * A *
          (B ^ 2 - 11 * (rrcf_v * A) * B - (rrcf_v * A) ^ 2) := by
            rw [hZB]
      _ = rrcf_v * A *
          (B ^ 2 - 11 * rrcf_v * A * B - rrcf_v ^ 2 * A ^ 2) := by
            ring
      _ = rrcf_v * A * C ^ 5 := by rw [hquad]
      _ = (C ^ 5 * Z) * B := by
            rw [show (C ^ 5 * Z) * B = C ^ 5 * (Z * B) by ring, hZB]
            ring
  exact isUnit_watson_B_rrcf_v.mul_left_inj.mp hmul

private theorem y_eq_watson_Z :
    let A : ℚ⟦X⟧ :=
      QseriesFormalization.Pending.WatsonAlgebraic.A rrcf_v
    let B : ℚ⟦X⟧ :=
      QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v
    let Y : ℚ⟦X⟧ := PowerSeries.X * rrcf_r ^ 5
    let Z : ℚ⟦X⟧ := rrcf_v * A * B⁻¹
    Y = Z := by
  dsimp
  let C : ℚ⟦X⟧ := 1 - rrcf_v - rrcf_v ^ 2
  let A : ℚ⟦X⟧ := QseriesFormalization.Pending.WatsonAlgebraic.A rrcf_v
  let B : ℚ⟦X⟧ := QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v
  let Y : ℚ⟦X⟧ := PowerSeries.X * rrcf_r ^ 5
  let Z : ℚ⟦X⟧ := rrcf_v * A * B⁻¹
  let K : ℚ⟦X⟧ := rrcf_v * A * B * (11 + Y + Z) + C ^ 5
  have hY : rrcf_v * A * B * (1 - 11 * Y - Y ^ 2) = C ^ 5 * Y := by
    simpa [C, A, B, Y] using y_satisfies_watson_branch
  have hZ : rrcf_v * A * B * (1 - 11 * Z - Z ^ 2) = C ^ 5 * Z := by
    simpa [C, A, B, Z] using z_satisfies_watson_branch
  have heq :
      rrcf_v * A * B * (1 - 11 * Y - Y ^ 2) - C ^ 5 * Y =
        rrcf_v * A * B * (1 - 11 * Z - Z ^ 2) - C ^ 5 * Z := by
    rw [hY, hZ]
    ring
  have hfactor : (Y - Z) * K = 0 := by
    calc
      (Y - Z) * K =
          -((rrcf_v * A * B * (1 - 11 * Y - Y ^ 2) - C ^ 5 * Y) -
            (rrcf_v * A * B * (1 - 11 * Z - Z ^ 2) - C ^ 5 * Z)) := by
            simp [K]
            ring
      _ = 0 := by rw [heq]; ring
  have hKunit : IsUnit K := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have hv : PowerSeries.constantCoeff rrcf_v = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact coeff_zero_rrcf_v_eq_zero
    have hC : PowerSeries.constantCoeff C = 1 := by
      simp [C, map_sub, map_pow, hv]
    have hKcc : PowerSeries.constantCoeff K = 1 := by
      simp [K, hC, map_add, map_mul, map_pow, hv]
    rw [hKcc]
    exact isUnit_one
  have hsub : Y - Z = 0 := by
    have hfactor' : (Y - Z) * K = 0 * K := by
      simpa using hfactor
    exact hKunit.mul_left_inj.mp hfactor'
  exact sub_eq_zero.mp hsub

/-- **Chan's Theorem 11.5 ("difficult and deep" identity), formal-PS form
with cleared denominators.**

This is the precise Lean target for Ch13's chapter-main result.  Both
sides are formal power series in `ℚ⟦X⟧`; equality is in the sense of
`PowerSeries.ext` (coefficient-wise).

After closing this theorem, the standard form
`R(q)⁵ = R(q⁵) · (1−2R(q⁵)+4R(q⁵)²−3R(q⁵)³+R(q⁵)⁴) /
                 (1+3R(q⁵)+4R(q⁵)²+2R(q⁵)³+R(q⁵)⁴)`
follows by `mul_left_cancel₀ isUnit_rrcfDenomLHS.ne_zero` and by
re-attaching the `q^{1/5}` prefactor in the analytic interpretation
(`R(q) = q^{1/5}·r(q)` raises both sides to the 5th power, so the
fractional powers cancel: `R(q)⁵ = q·r(q)⁵`, and likewise on the RHS the
prefactors combine to `q`).

Proof strategy: Watson's algebraic branch argument, assembled above. -/
theorem chan_theorem_11_5 :
    rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4) =
      (PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4) := by
  let S : ℚ⟦X⟧ := PowerSeries.expand 5 (by decide) rrcf_r
  let A : ℚ⟦X⟧ := QseriesFormalization.Pending.WatsonAlgebraic.A rrcf_v
  let B : ℚ⟦X⟧ := QseriesFormalization.Pending.WatsonAlgebraic.B rrcf_v
  let Y : ℚ⟦X⟧ := PowerSeries.X * rrcf_r ^ 5
  let Z : ℚ⟦X⟧ := rrcf_v * A * B⁻¹
  have hYZ : Y = Z := by
    simpa [A, B, Y, Z] using y_eq_watson_Z
  have hZB : Z * B = rrcf_v * A := by
    simpa [A, B, Z] using watson_Z_mul_B
  have hX :
      PowerSeries.X * (rrcf_r ^ 5 * B) =
        PowerSeries.X * (S * A) := by
    calc
      PowerSeries.X * (rrcf_r ^ 5 * B) = Y * B := by
        simp [Y]
        ring
      _ = Z * B := by rw [hYZ]
      _ = rrcf_v * A := hZB
      _ = PowerSeries.X * (S * A) := by
        simp [rrcf_v, S]
        ring
  have hmain : rrcf_r ^ 5 * B = S * A :=
    PowerSeries.X_mul_cancel hX
  simpa [S, A, B, QseriesFormalization.Pending.WatsonAlgebraic.A,
    QseriesFormalization.Pending.WatsonAlgebraic.B] using hmain

end Ch13DeepIdentity
end Pending
end QseriesFormalization
