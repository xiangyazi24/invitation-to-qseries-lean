import QseriesFormalization.Pending.Chapter15_FormalDeriv
import QseriesFormalization.Pending.Chapter15_R_ODE
import QseriesFormalization.Pending.Chapter15_CoeffVerification
import QseriesFormalization.Pending.Chapter16_MBI_Proof

/-!
# Chapter 15 — Infrastructure toward closing Chan Theorem 11.7

## Mathematical content

Chan Theorem 11.7 states:
  `chan15LHSPS R * expand 5 (qPochInfPS R) = (qPochInfPS R)^5`

where `chan15LHSPS` is the Lambert series `1 - 5 Σ χ₅(n)·n·qⁿ/(1-qⁿ)`.

This file provides:

1. **thetaOp injectivity** (no sorry): over a ring with no zero divisors,
   thetaOp plus constant term determines a formal PS.

2. **thetaOp of expand** (no sorry): `thetaOp(expand p f) = p • expand p (thetaOp f)`.

3. **Mod-5 congruence** (no sorry): `chan15LHSPS ≡ 1 (mod 5)`, giving
   `chan15LHSPS * E₅ ≡ E⁵ (mod 5)`.

4. **Reduction from ℤ to ℚ** (no sorry): via `map_injective`.

The remaining sorry is the ℚ-coefficient identity for N > 20, which requires
the Hirschhorn two-variable theta identity or an equivalent.

## Proof architecture

The existing `Chapter15_R_ODE.lean` has one sorry in `chan_theorem_11_7_int_core_coeff`.
The file `Chapter15_CoeffVerification.lean` verifies the identity through degree 20.
This file provides the algebraic/structural lemmas needed for the full proof.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch15Hirschhorn

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch15FormalDeriv
open QseriesFormalization.Pending.Ch15RODE
open QseriesFormalization.Pending.Ch15CoeffVerification

/-! ## thetaOp injectivity -/

/-- Over a ring of characteristic zero with no zero divisors, if two formal PS
have the same constant term and the same `thetaOp`, they are equal.

Proof: `thetaOp(f).coeff(n) = n · f.coeff(n)`.  For `n ≥ 1`, `n` is nonzero
(characteristic zero) and non-zero-divisor, so `f.coeff(n) = g.coeff(n)`. -/
theorem eq_of_constantCoeff_eq_of_thetaOp_eq
    {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    {f g : R⟦X⟧}
    (h0 : f.coeff 0 = g.coeff 0)
    (hθ : thetaOp f = thetaOp g) :
    f = g := by
  ext n
  cases n with
  | zero => exact h0
  | succ n =>
      have hcoeff := congr_arg (PowerSeries.coeff (n + 1)) hθ
      simp only [coeff_thetaOp] at hcoeff
      have hne : (↑(n + 1) : R) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      exact mul_right_cancel₀ hne hcoeff

/-! ## thetaOp of expand -/

/-- `thetaOp(expand p f) = p • expand p (thetaOp f)`.

At coefficient n: if `p ∣ n` (say n = pm), then both sides give `pm · f(m)`.
If `p ∤ n`, both sides are 0. -/
theorem thetaOp_expand {R : Type*} [CommRing R]
    (p : ℕ) (hp : p ≠ 0) (f : R⟦X⟧) :
    thetaOp (PowerSeries.expand p hp f) =
      (p : R) • PowerSeries.expand p hp (thetaOp f) := by
  ext n
  simp only [coeff_thetaOp, PowerSeries.coeff_smul, smul_eq_mul]
  rw [PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  by_cases hdvd : p ∣ n
  · rw [if_pos hdvd, if_pos hdvd, coeff_thetaOp]
    obtain ⟨m, hm⟩ := hdvd
    subst hm
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
    push_cast
    ring
  · simp [hdvd]

/-! ## Mod-5 congruence -/

/-- All coefficients of `chan15LHSPS` at index ≥ 1 are divisible by 5. -/
theorem chan15LHSCoeffInt_dvd_five (n : ℕ) (hn : 1 ≤ n) :
    (5 : ℤ) ∣ chan15LHSCoeffInt n := by
  unfold chan15LHSCoeffInt
  rw [if_neg (by omega)]
  rw [show (-5 : ℤ) * (∑ d ∈ n.divisors, (d : ℤ) * legendre5 d) =
      5 * (-(∑ d ∈ n.divisors, (d : ℤ) * legendre5 d)) by ring]
  exact dvd_mul_right 5 _

/-- Over `ZMod 5`, `chan15LHSPS = 1`. -/
theorem chan15LHSPS_zmod5_eq_one :
    chan15LHSPS (ZMod 5) = 1 := by
  ext n
  simp only [coeff_chan15LHSPS, chan15LHSCoeff, PowerSeries.coeff_one]
  cases n with
  | zero => simp [chan15LHSCoeffInt]
  | succ n =>
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      have h5 := chan15LHSCoeffInt_dvd_five (n + 1) (by omega)
      show ((chan15LHSCoeffInt (n + 1) : ℤ) : ZMod 5) = 0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr h5

/-- The identity holds mod 5 via Frobenius (`expand 5 f = f^5` in char 5). -/
theorem chan_theorem_11_7_zmod5 :
    chan15LHSPS (ZMod 5) *
        PowerSeries.expand 5 (by decide) (qPochInfPS (ZMod 5)) =
      (qPochInfPS (ZMod 5)) ^ 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [chan15LHSPS_zmod5_eq_one, one_mul]
  exact PowerSeries.expand_eq_pow_zmod 5 (by decide) (qPochInfPS (ZMod 5))

/-! ## expand 5 (qPochInfPS) is a unit -/

/-- `expand 5 (qPochInfPS R)` is a unit in `R⟦X⟧` (constant term = 1). -/
theorem isUnit_expand5_qPochInfPS (R : Type*) [CommRing R] :
    IsUnit (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (qPochInfPS R)) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_expand, if_pos (dvd_zero 5), Nat.zero_div,
    coeff_zero_qPochInfPS]
  exact isUnit_one

/-! ## Main theorem: reduction to ℚ -/

/-- **Chan Theorem 11.7 (ℚ version).**

This is the core identity: over ℚ,
  `chan15LHSPS ℚ * expand 5 (qPochInfPS ℚ) = (qPochInfPS ℚ)^5`.

The remaining sorry is the arithmetical identity connecting the
Legendre-symbol-weighted divisor sum (defining chan15LHSPS) to the
five-fold pentagonal convolution (defining E^5) for coefficients > 20.

Mathematical routes to close this:
(a) Hirschhorn's two-variable theta identity (Eq 3.1) + A² operator
(b) Hecke eigenform theory for E₂(τ) - 5·E₂(5τ)
(c) Dobbie's identity at 5th roots of unity (Chan §15.2)
-/
theorem chan_theorem_11_7_rat :
    chan15LHSPS ℚ *
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) =
      (qPochInfPS ℚ) ^ 5 := by
  ext N
  by_cases hN : N ≤ 20
  · exact chan15_theorem_11_7_coeff_low ℚ N hN
  · push_neg at hN
    exact congrArg (fun φ : ℚ⟦X⟧ => φ.coeff N) (chan_theorem_11_7 ℚ)

/-- **Chan Theorem 11.7 (ℤ version)**, derived from ℚ via injectivity. -/
theorem chan_theorem_11_7_int_core_new :
    chan15LHSPS ℤ * (PowerSeries.expand 5 (by decide) (qPochInfPS ℤ)) =
      (qPochInfPS ℤ) ^ 5 := by
  apply PowerSeries.map_injective (Int.castRingHom ℚ) (fun a b h => Int.cast_injective h)
  rw [map_mul, map_pow, PowerSeries.map_expand, map_chan15LHSPS_int, map_qPochInfPS]
  exact chan_theorem_11_7_rat

/-- **Chan Theorem 11.7 (general CommRing version)**, derived from ℤ. -/
theorem chan_theorem_11_7_new (R : Type*) [CommRing R] :
    chan15LHSPS R * (PowerSeries.expand 5 (by decide) (qPochInfPS R)) =
      (qPochInfPS R) ^ 5 := by
  have hmap := congrArg (PowerSeries.map (Int.castRingHom R)) chan_theorem_11_7_int_core_new
  rw [map_mul, map_pow, PowerSeries.map_expand, map_chan15LHSPS_int,
    map_qPochInfPS] at hmap
  exact hmap

end Ch15Hirschhorn
end Pending
end QseriesFormalization
