import QseriesFormalization.Chapter19
import QseriesFormalization.Chapter20
import QseriesFormalization.Pending.Chapter15_WronskianIndependent

/-!
# Chapter 15 — Differential equation for `R(q)` (Chan §15 / Theorem 11.7)

⚠️ **Resolves MISLABELED status of Chan §15.** Adds the precise Chan §15 chapter-main
result statement, replacing the q-Taylor infrastructure (which remains useful as
*background* in `Chapter15.lean` but is not the actual §15 content).

Chan Theorem 11.7 (proved in §15) is the differential equation
  `5q · d/dq · ln R(q) = η⁵(τ) / η(5τ)`

which, by integrating term-by-term (Theorem 11.1), is equivalent to the
formal-power-series identity (Eq 15.8 in Chan):

  `1 − 5 · Σ_{n≥1} (n|5) · n · qⁿ / (1 − qⁿ) = η⁵(τ) / η(5τ)`

where `(n|5)` denotes the Legendre symbol modulo `5`:
  +1 if n ≡ ±1 (mod 5),
  -1 if n ≡ ±2 (mod 5),
   0 if n ≡  0 (mod 5).

In our formal-PS setting `etaPS R := qPochInfPS R` (no `q^{1/24}` prefactor),
so `η⁵/η(5τ)` translates to `(qPochInfPS R)⁵ / PowerSeries.expand 5 (qPochInfPS R)`.
The denominator has constant coefficient `1`, so the division is well-defined
in `R⟦X⟧` and we state the identity as a *multiplicative* equality below to
avoid `Inv` typeclass issues over a general `CommRing R`.

## Open closure path (Chan §15)

Chan's proof in §15.2 uses **Dobbie's identity (1955)**, Eq. 15.1:
  `(x-z)(1-xz) / ((1-x)²(1-z)²) · [JTP-products] = LHS as a 2-variable Laurent series`

Specializing to `x = e^{2πi/5}, z = x²` collapses by Gaussian-period algebra
(`θ := β + β⁻¹` for the Golden ratio β) to Eq. 15.5, and the `qPochInfPS`
prefactor cancels by Eq. 14.35 (the 5-th root JTP infinite-product identity).

Modern proof (Milas 2004): vertex operator algebra / Zhu's theorem; out of
scope for this formalization without a Mathlib VOA module.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch15RODE

open PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.PartIV.Ch20
open QseriesFormalization.Pending.Ch15FormalDeriv
open QseriesFormalization.Pending.Ch10TenthOrder
open QseriesFormalization.Pending.Ch15WronskianIndependent

/-- The Legendre symbol mod 5, valued in `ℤ`:
  +1 if n ≡ ±1 (mod 5), -1 if n ≡ ±2 (mod 5), 0 if n ≡ 0 (mod 5). -/
def legendre5 (n : ℕ) : ℤ :=
  match n % 5 with
  | 0 => 0
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => 1
  | _ => 0  -- unreachable

@[simp] theorem legendre5_zero : legendre5 0 = 0 := rfl
@[simp] theorem legendre5_one : legendre5 1 = 1 := rfl
@[simp] theorem legendre5_two : legendre5 2 = -1 := rfl
@[simp] theorem legendre5_three : legendre5 3 = -1 := rfl
@[simp] theorem legendre5_four : legendre5 4 = 1 := rfl
@[simp] theorem legendre5_five : legendre5 5 = 0 := rfl

/-- Closed-form coefficient at `X^N` of Chan's Eq 15.8 LHS:
  `[X^N] (1 - 5 · Σ_{n≥1} (n|5) · n · X^n / (1 - X^n))`
  = `[N=0 ? 1 : 0] - 5 · Σ_{d|N} d · legendre5(d)`.
This is the Lambert-series coefficient expansion: each `(n|5)·n·X^n / (1-X^n)`
contributes `n·(n|5)` to coefficients at `X^{nm}` for every `m≥1`, i.e. at
every multiple of `n`. Summing over `n ≤ N` divisors of `N` gives the formula. -/
def chan15LHSCoeffInt (N : ℕ) : ℤ :=
  if N = 0 then 1
  else -5 * (∑ d ∈ N.divisors, (d : ℤ) * legendre5 d)

/-- Coefficient at `X^N` of Chan's Eq 15.8 LHS, as a value in any commutative
ring `R`, via canonical ℤ→R coercion. -/
def chan15LHSCoeff (R : Type*) [CommRing R] (N : ℕ) : R :=
  ((chan15LHSCoeffInt N : ℤ) : R)

/-- Chan Eq 15.8 LHS as a formal power series. -/
noncomputable def chan15LHSPS (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk (chan15LHSCoeff R)

@[simp] theorem coeff_chan15LHSPS (R : Type*) [CommRing R] (N : ℕ) :
    (chan15LHSPS R).coeff N = chan15LHSCoeff R N := by
  unfold chan15LHSPS
  rw [PowerSeries.coeff_mk]

@[simp] theorem chan15LHSCoeffInt_zero : chan15LHSCoeffInt 0 = 1 := rfl

/-- Constant coefficient of Chan's LHS is `1` (only the leading `1` contributes
at `X^0`; the Lambert series starts at `X^1`). -/
@[simp] theorem coeff_zero_chan15LHSPS (R : Type*) [CommRing R] :
    (chan15LHSPS R).coeff 0 = 1 := by
  simp [chan15LHSPS, chan15LHSCoeff]

/-- **Chan Theorem 11.7 / Eq 15.8 (formal-power-series form).**

Multiplicative form (avoids `Inv`, valid in any `CommRing R`):

  `chan15LHSPS R · PowerSeries.expand 5 (qPochInfPS R) = (qPochInfPS R)⁵`

In words: the LHS Lambert series `1 - 5·Σ(n|5)·n·q^n/(1-q^n)`, when multiplied
by `(q⁵;q⁵)_∞ = η(5τ)/q^{5/24}` (the formal version), equals `(q;q)_∞⁵ = η⁵(τ)/q^{5/24}`.

The remaining mathematical core is the integral coefficient identity
`chan_theorem_11_7_int_core_coeff` below.  Once that is available, the statement
over an arbitrary `CommRing` is just coefficient-cast naturality:
`chan15LHSPS` is defined by integer coefficients, and `qPochInfPS` commutes with
`PowerSeries.map`.

**Exact blocker.**  The missing core is the Lambert/product identity over
`ℤ⟦X⟧`:

```
1 - 5 * Σ χ₅(n) n X^n / (1 - X^n) = (q;q)_∞^5 / (q^5;q^5)_∞.
```

The existing 5th-root JTP infrastructure supplies the product and Gaussian
period algebra behind Chan §15.2, but not Dobbie's specialized two-variable
Lambert identity (or an equivalent all-coefficients divisor-sum proof).  Closing
`chan_theorem_11_7_int_core_coeff` requires one of:
1. a formal specialized Dobbie identity at `x = ζ`, `z = ζ^2`, plus the
   Lambert residue-class collapse; or
2. a direct all-`N` coefficient theorem identifying the divisor-sum convolution
   with `[X^N] (qPochInfPS ℤ)^5`.
-/
theorem map_chan15LHSPS_int (R : Type*) [CommRing R] :
    PowerSeries.map (Int.castRingHom R) (chan15LHSPS ℤ) = chan15LHSPS R := by
  ext N
  simp [chan15LHSCoeff]

/-- Descent step for the proposed analytic route: once the identity is proved
over `ℂ`, coefficientwise injectivity of `ℤ → ℂ` gives the integral formal-PS
core. -/
theorem chan_theorem_11_7_int_core_of_complex
    (hC :
      chan15LHSPS ℂ * (PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)) =
        (qPochInfPS ℂ) ^ 5) :
    chan15LHSPS ℤ * (PowerSeries.expand 5 (by decide) (qPochInfPS ℤ)) =
      (qPochInfPS ℤ) ^ 5 := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ)
  · intro a b h
    exact Int.cast_injective h
  rw [map_mul, map_pow, PowerSeries.map_expand, map_chan15LHSPS_int,
    map_qPochInfPS]
  exact hC

/-- Pure integer left side of the coefficient core, after replacing
`qPochInfPS` coefficients by Euler's pentagonal-sign coefficients. -/
def chan15CoreCoeffLHSZ (N : ℕ) : ℤ :=
  ∑ ij ∈ Finset.antidiagonal N,
    (chan15LHSCoeffInt ij.1 : ℤ) *
      (if 5 ∣ ij.2 then
        QseriesFormalization.PartI.Ch05.pentagonalSign (ij.2 / 5)
      else 0)

/-- Computable coefficient model for powers of `(q;q)_∞`, using Euler's
pentagonal-sign coefficients and ordinary Cauchy convolution. -/
def qPochPowPentagonalCoeff : ℕ → ℕ → ℤ
  | 0 => fun n => if n = 0 then 1 else 0
  | e + 1 => fun n =>
      ∑ k ∈ Finset.range (n + 1), qPochPowPentagonalCoeff e k *
        QseriesFormalization.PartI.Ch05.pentagonalSign (n - k)

theorem coeff_qPochInfPS_pow_pentagonal (e n : ℕ) :
    ((qPochInfPS ℤ) ^ e).coeff n = qPochPowPentagonalCoeff e n := by
  induction e generalizing n with
  | zero =>
      by_cases h : n = 0
      · simp [qPochPowPentagonalCoeff, PowerSeries.coeff_one, h]
      · simp [qPochPowPentagonalCoeff, PowerSeries.coeff_one, h]
  | succ e ih =>
      rw [pow_succ, PowerSeries.coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [qPochPowPentagonalCoeff]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [ih k, coeff_qPochInfPS_int_eq_pentagonalSign]

theorem chan15CoreCoeffLHSZ_eq_original_lhs (N : ℕ) :
    chan15CoreCoeffLHSZ N =
      (∑ ij ∈ Finset.antidiagonal N,
        (chan15LHSCoeffInt ij.1 : ℤ) *
          (if 5 ∣ ij.2 then (qPochInfPS ℤ).coeff (ij.2 / 5) else 0)) := by
  unfold chan15CoreCoeffLHSZ
  apply Finset.sum_congr rfl
  intro ij _hij
  by_cases h : 5 ∣ ij.2
  · rw [if_pos h, if_pos h, coeff_qPochInfPS_int_eq_pentagonalSign]
  · rw [if_neg h, if_neg h]

/-- The original all-coefficient core follows from the pure integer
pentagonal convolution identity. -/
theorem chan_theorem_11_7_int_core_coeff_of_pentagonal_identity (N : ℕ)
    (h :
      chan15CoreCoeffLHSZ N = qPochPowPentagonalCoeff 5 N) :
    (∑ ij ∈ Finset.antidiagonal N,
        (chan15LHSCoeffInt ij.1 : ℤ) *
          (if 5 ∣ ij.2 then (qPochInfPS ℤ).coeff (ij.2 / 5) else 0)) =
      ((qPochInfPS ℤ) ^ 5).coeff N := by
  rw [← chan15CoreCoeffLHSZ_eq_original_lhs N, coeff_qPochInfPS_pow_pentagonal]
  exact h

set_option maxRecDepth 4096 in
theorem chan15CoreCoeff_pentagonal_identity_le_thirty :
    ∀ N, N ≤ 30 →
      chan15CoreCoeffLHSZ N = qPochPowPentagonalCoeff 5 N := by
  intro N hN
  interval_cases N <;> native_decide

/-- The original coefficient core, verified through degree 30 inside this file
without importing the downstream coefficient-verification module. -/
theorem chan_theorem_11_7_int_core_coeff_le_thirty :
    ∀ N, N ≤ 30 →
      (∑ ij ∈ Finset.antidiagonal N,
          (chan15LHSCoeffInt ij.1 : ℤ) *
            (if 5 ∣ ij.2 then (qPochInfPS ℤ).coeff (ij.2 / 5) else 0)) =
        ((qPochInfPS ℤ) ^ 5).coeff N := by
  intro N hN
  exact chan_theorem_11_7_int_core_coeff_of_pentagonal_identity N
    (chan15CoreCoeff_pentagonal_identity_le_thirty N hN)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem chan15CoreCoeff_pentagonal_identity_le_forty :
    ∀ N, N ≤ 40 →
      chan15CoreCoeffLHSZ N = qPochPowPentagonalCoeff 5 N := by
  intro N hN
  interval_cases N <;> native_decide

/-- The original coefficient core, verified through degree 40.  This keeps the
finite executable certificate in the source file that owns the remaining
all-`N` blocker, rather than relying on downstream verification modules. -/
theorem chan_theorem_11_7_int_core_coeff_le_forty :
    ∀ N, N ≤ 40 →
      (∑ ij ∈ Finset.antidiagonal N,
          (chan15LHSCoeffInt ij.1 : ℤ) *
            (if 5 ∣ ij.2 then (qPochInfPS ℤ).coeff (ij.2 / 5) else 0)) =
        ((qPochInfPS ℤ) ^ 5).coeff N := by
  intro N hN
  exact chan_theorem_11_7_int_core_coeff_of_pentagonal_identity N
    (chan15CoreCoeff_pentagonal_identity_le_forty N hN)

def sigma1CoeffZ (n : ℕ) : ℤ :=
  (Nat.divisorSum n id : ℤ)

/-- Residual of the theta-log recurrence for `(q;q)_∞^5`:
`n a_n + 5 * sum_{k=1}^n sigma_1(k) a_{n-k} = 0`. -/
def etaPowFiveThetaResidualZ (a : ℕ → ℤ) (N : ℕ) : ℤ :=
  (N : ℤ) * a N +
    5 * ∑ k ∈ Finset.Icc 1 N, sigma1CoeffZ k * a (N - k)

def chan15CoreCoeffRecurrenceResidualZ (N : ℕ) : ℤ :=
  etaPowFiveThetaResidualZ chan15CoreCoeffLHSZ N

def qPochPowFiveCoeffRecurrenceResidualZ (N : ℕ) : ℤ :=
  etaPowFiveThetaResidualZ (fun n => qPochPowPentagonalCoeff 5 n) N

/-- Coefficient form of the convolution against `sigma_1` that appears in the
theta-log recurrence for `(q;q)_∞^5`. -/
theorem coeff_qPochPowFive_mul_divisorSigmaPS (N : ℕ) :
    (((qPochInfPS ℤ) ^ 5) * divisorSigmaPS ℤ).coeff N =
      ∑ k ∈ Finset.Icc 1 N,
        sigma1CoeffZ k * qPochPowPentagonalCoeff 5 (N - k) := by
  rw [PowerSeries.coeff_mul]
  rw [← Finset.Nat.sum_antidiagonal_swap
    (f := fun ij : ℕ × ℕ =>
      ((qPochInfPS ℤ) ^ 5).coeff ij.1 * (divisorSigmaPS ℤ).coeff ij.2)]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k j => ((qPochInfPS ℤ) ^ 5).coeff j * (divisorSigmaPS ℤ).coeff k)]
  simp only [coeff_divisorSigmaPS, sigma1CoeffZ]
  have hsubset : Finset.Icc 1 N ⊆ Finset.range (N + 1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [coeff_qPochInfPS_pow_pentagonal]
    ring
  · intro k hkrange hknot
    rw [Finset.mem_range] at hkrange
    have hk0 : k = 0 := by
      have hk_le : k ≤ N := by omega
      have hnot_one_le : ¬ 1 ≤ k := by
        intro hk_one
        exact hknot (by
          rw [Finset.mem_Icc]
          exact ⟨hk_one, hk_le⟩)
      omega
    subst k
    simp [Nat.divisorSum]

/-- The product side satisfies the theta-log recurrence for `(q;q)_∞^5` for
all coefficients.  This is the recurrence side that follows from the existing
formal `thetaOp_etaPS` infrastructure. -/
theorem qPochPowPentagonalCoeff_five_theta_recurrence (N : ℕ) :
    (N : ℤ) * qPochPowPentagonalCoeff 5 N =
      -5 * ∑ k ∈ Finset.Icc 1 N,
        sigma1CoeffZ k * qPochPowPentagonalCoeff 5 (N - k) := by
  have htheta :
      thetaOp ((qPochInfPS ℤ) ^ 5) =
        (-5 : ℤ⟦X⟧) * (((qPochInfPS ℤ) ^ 5) * divisorSigmaPS ℤ) := by
    change thetaOp ((etaPS ℤ) ^ 5) =
      (-5 : ℤ⟦X⟧) * (((etaPS ℤ) ^ 5) * divisorSigmaPS ℤ)
    rw [thetaOp_pow, thetaOp_etaPS_eq_neg_etaPS_mul_divisorSigmaPS]
    norm_num
    ring
  have hcoeff := congrArg (fun f : ℤ⟦X⟧ => f.coeff N) htheta
  change (thetaOp ((qPochInfPS ℤ) ^ 5)).coeff N =
      ((-5 : ℤ⟦X⟧) * (((qPochInfPS ℤ) ^ 5) * divisorSigmaPS ℤ)).coeff N at hcoeff
  rw [coeff_thetaOp] at hcoeff
  change ((qPochInfPS ℤ) ^ 5).coeff N * (N : ℤ) =
      ((-5 : ℤ⟦X⟧) * (((qPochInfPS ℤ) ^ 5) * divisorSigmaPS ℤ)).coeff N at hcoeff
  rw [show (-5 : ℤ⟦X⟧) = PowerSeries.C (-5 : ℤ) by norm_num] at hcoeff
  rw [PowerSeries.coeff_C_mul, coeff_qPochPowFive_mul_divisorSigmaPS N,
    coeff_qPochInfPS_pow_pentagonal 5 N] at hcoeff
  calc
    (N : ℤ) * qPochPowPentagonalCoeff 5 N =
        qPochPowPentagonalCoeff 5 N * (N : ℤ) := by ring
    _ = -5 * ∑ k ∈ Finset.Icc 1 N,
          sigma1CoeffZ k * qPochPowPentagonalCoeff 5 (N - k) := hcoeff

theorem qPochPowFiveCoeffRecurrenceResidualZ_eq_zero (N : ℕ) :
    qPochPowFiveCoeffRecurrenceResidualZ N = 0 := by
  unfold qPochPowFiveCoeffRecurrenceResidualZ etaPowFiveThetaResidualZ
  change (N : ℤ) * qPochPowPentagonalCoeff 5 N +
      5 * (∑ k ∈ Finset.Icc 1 N,
        sigma1CoeffZ k * qPochPowPentagonalCoeff 5 (N - k)) = 0
  rw [qPochPowPentagonalCoeff_five_theta_recurrence N]
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem chan15CoreCoeffRecurrenceResidualZ_eq_zero_le_forty :
    ∀ N, N ≤ 40 → chan15CoreCoeffRecurrenceResidualZ N = 0 := by
  intro N hN
  interval_cases N <;> native_decide

/-- If the Lambert/product convolution coefficients satisfy the same theta-log
recurrence as `(q;q)_∞^5`, then the remaining Chan §15 core follows by
coefficient-recursion uniqueness.  The unreduced arithmetic task is exactly the
all-`N` proof of `chan15CoreCoeffRecurrenceResidualZ_eq_zero`. -/
theorem chan15CoreCoeff_pentagonal_identity_of_theta_recurrence
    (hrec : ∀ N, chan15CoreCoeffRecurrenceResidualZ N = 0) :
    ∀ N, chan15CoreCoeffLHSZ N = qPochPowPentagonalCoeff 5 N := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      cases N with
      | zero =>
          native_decide
      | succ M =>
          let S : ℤ :=
            ∑ k ∈ Finset.Icc 1 (M + 1),
              sigma1CoeffZ k * qPochPowPentagonalCoeff 5 (M + 1 - k)
          have hsum :
              (∑ k ∈ Finset.Icc 1 (M + 1),
                sigma1CoeffZ k * chan15CoreCoeffLHSZ (M + 1 - k)) = S := by
            unfold S
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mem_Icc] at hk
            have hlt : M + 1 - k < M + 1 := by omega
            rw [ih (M + 1 - k) hlt]
          have hL := hrec (M + 1)
          have hR := qPochPowFiveCoeffRecurrenceResidualZ_eq_zero (M + 1)
          unfold chan15CoreCoeffRecurrenceResidualZ etaPowFiveThetaResidualZ at hL
          unfold qPochPowFiveCoeffRecurrenceResidualZ etaPowFiveThetaResidualZ at hR
          rw [hsum] at hL
          change (M + 1 : ℤ) * chan15CoreCoeffLHSZ (M + 1) + 5 * S = 0 at hL
          change (M + 1 : ℤ) * qPochPowPentagonalCoeff 5 (M + 1) + 5 * S = 0 at hR
          have hmul :
              (M + 1 : ℤ) * chan15CoreCoeffLHSZ (M + 1) =
                (M + 1 : ℤ) * qPochPowPentagonalCoeff 5 (M + 1) := by
            calc
              (M + 1 : ℤ) * chan15CoreCoeffLHSZ (M + 1)
                  = (M + 1 : ℤ) * chan15CoreCoeffLHSZ (M + 1) + 5 * S - 5 * S := by
                    ring
              _ = (M + 1 : ℤ) * qPochPowPentagonalCoeff 5 (M + 1) + 5 * S - 5 * S := by
                    rw [show (M + 1 : ℤ) * chan15CoreCoeffLHSZ (M + 1) + 5 * S =
                        (M + 1 : ℤ) * qPochPowPentagonalCoeff 5 (M + 1) + 5 * S by
                      rw [hL, hR]]
              _ = (M + 1 : ℤ) * qPochPowPentagonalCoeff 5 (M + 1) := by
                    ring
          apply mul_left_cancel₀ (show (M + 1 : ℤ) ≠ 0 by omega)
          exact hmul

/-- Bounded version of the same recurrence-uniqueness bridge.  If the
Lambert-side coefficients satisfy the theta-log recurrence through degree
`B`, then the pentagonal convolution identity also holds through degree `B`.

This is the finite form used by the executable certificates below; the only
missing ingredient for the all-degree theorem is replacing the bounded
hypothesis by an all-`N` proof. -/
theorem chan15CoreCoeff_pentagonal_identity_of_theta_recurrence_le
    (B : ℕ)
    (hrec : ∀ N, N ≤ B → chan15CoreCoeffRecurrenceResidualZ N = 0) :
    ∀ N, N ≤ B → chan15CoreCoeffLHSZ N = qPochPowPentagonalCoeff 5 N := by
  intro N hNB
  induction N using Nat.strong_induction_on with
  | h N ih =>
      cases N with
      | zero =>
          native_decide
      | succ M =>
          let S : ℤ :=
            ∑ k ∈ Finset.Icc 1 (M + 1),
              sigma1CoeffZ k * qPochPowPentagonalCoeff 5 (M + 1 - k)
          have hsum :
              (∑ k ∈ Finset.Icc 1 (M + 1),
                sigma1CoeffZ k * chan15CoreCoeffLHSZ (M + 1 - k)) = S := by
            unfold S
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mem_Icc] at hk
            have hlt : M + 1 - k < M + 1 := by omega
            have hleB : M + 1 - k ≤ B := by omega
            rw [ih (M + 1 - k) hlt hleB]
          have hL := hrec (M + 1) hNB
          have hR := qPochPowFiveCoeffRecurrenceResidualZ_eq_zero (M + 1)
          unfold chan15CoreCoeffRecurrenceResidualZ etaPowFiveThetaResidualZ at hL
          unfold qPochPowFiveCoeffRecurrenceResidualZ etaPowFiveThetaResidualZ at hR
          rw [hsum] at hL
          change (M + 1 : ℤ) * chan15CoreCoeffLHSZ (M + 1) + 5 * S = 0 at hL
          change (M + 1 : ℤ) * qPochPowPentagonalCoeff 5 (M + 1) + 5 * S = 0 at hR
          have hmul :
              (M + 1 : ℤ) * chan15CoreCoeffLHSZ (M + 1) =
                (M + 1 : ℤ) * qPochPowPentagonalCoeff 5 (M + 1) := by
            calc
              (M + 1 : ℤ) * chan15CoreCoeffLHSZ (M + 1)
                  = (M + 1 : ℤ) * chan15CoreCoeffLHSZ (M + 1) + 5 * S - 5 * S := by
                    ring
              _ = (M + 1 : ℤ) * qPochPowPentagonalCoeff 5 (M + 1) + 5 * S - 5 * S := by
                    rw [show (M + 1 : ℤ) * chan15CoreCoeffLHSZ (M + 1) + 5 * S =
                        (M + 1 : ℤ) * qPochPowPentagonalCoeff 5 (M + 1) + 5 * S by
                      rw [hL, hR]]
              _ = (M + 1 : ℤ) * qPochPowPentagonalCoeff 5 (M + 1) := by
                    ring
          apply mul_left_cancel₀ (show (M + 1 : ℤ) ≠ 0 by omega)
          exact hmul

/-- The degree-`≤40` pentagonal convolution certificate can be recovered from
the bounded theta-log recurrence certificate, rather than by recomputing the
identity directly. -/
theorem chan15CoreCoeff_pentagonal_identity_le_forty_from_theta_recurrence :
    ∀ N, N ≤ 40 →
      chan15CoreCoeffLHSZ N = qPochPowPentagonalCoeff 5 N :=
  chan15CoreCoeff_pentagonal_identity_of_theta_recurrence_le 40
    chan15CoreCoeffRecurrenceResidualZ_eq_zero_le_forty

private noncomputable def residueDivisorSigmaCoeff (r n : ℕ) : ℚ :=
  ∑ d ∈ Finset.range (n + 1),
    if d ∣ n ∧ 0 < n ∧ d % 5 = r then (d : ℚ) else 0

private theorem apDivisorSigmaPS_coeff_eq_residue_range_rat
    {r n : ℕ} (_hr0 : 0 < r) (hr5 : r < 5) :
    (apDivisorSigmaPS ℚ r 5).coeff n =
      residueDivisorSigmaCoeff r n := by
  unfold residueDivisorSigmaCoeff
  rw [coeff_apDivisorSigmaPS]
  refine Finset.sum_bij_ne_zero
    (s := Finset.range (n + 1)) (t := Finset.range (n + 1))
    (f := fun k =>
      if r + 5 * k ∣ n ∧ 0 < n then ((r + 5 * k : ℕ) : ℚ) else 0)
    (g := fun d =>
      if d ∣ n ∧ 0 < n ∧ d % 5 = r then (d : ℚ) else 0)
    (fun k _ _ => r + 5 * k) ?_ ?_ ?_ ?_
  · intro k _hk hfk
    by_cases hcond : r + 5 * k ∣ n ∧ 0 < n
    · exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.le_of_dvd hcond.2 hcond.1))
    · exact False.elim (hfk (by simp [hcond]))
  · intro k₁ _hk₁ _hfk₁ k₂ _hk₂ _hfk₂ h
    have h' : 5 * k₁ = 5 * k₂ := Nat.add_left_cancel h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5) h'
  · intro d hd hgd
    by_cases hcond : d ∣ n ∧ 0 < n ∧ d % 5 = r
    · refine ⟨d / 5, ?_, ?_, ?_⟩
      · exact Finset.mem_range.mpr
          (lt_of_le_of_lt (Nat.div_le_self d 5) (Finset.mem_range.mp hd))
      · have hd_eq : r + 5 * (d / 5) = d := by
          have h := Nat.mod_add_div d 5
          rw [hcond.2.2] at h
          omega
        have hdne : d ≠ 0 :=
          Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hcond.1 hcond.2.1)
        simp [hd_eq, hcond.1, hcond.2.1, hdne]
      · have h := Nat.mod_add_div d 5
        rw [hcond.2.2] at h
        omega
    · exact False.elim (hgd (by simp [hcond]))
  · intro k _hk hfk
    by_cases hcond : r + 5 * k ∣ n ∧ 0 < n
    · have hmod : (r + 5 * k) % 5 = r := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr5]
      simp [hcond, hmod]
    · exact False.elim (hfk (by simp [hcond]))

private theorem chan15_divisor_sum_eq_range_rat (n : ℕ) (hn : 0 < n) :
    (((∑ d ∈ n.divisors, (d : ℤ) * legendre5 d) : ℤ) : ℚ) =
      ∑ d ∈ Finset.range (n + 1),
        if d ∣ n ∧ 0 < d then (d : ℚ) * ((legendre5 d : ℤ) : ℚ) else 0 := by
  let f : ℕ → ℚ := fun d =>
    if d ∣ n ∧ 0 < d then (d : ℚ) * ((legendre5 d : ℤ) : ℚ) else 0
  have hcast :
      (((∑ d ∈ n.divisors, (d : ℤ) * legendre5 d) : ℤ) : ℚ) =
        ∑ d ∈ n.divisors, (d : ℚ) * ((legendre5 d : ℤ) : ℚ) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro d _hd
    norm_num
  have hdiv_to_f :
      (∑ d ∈ n.divisors, (d : ℚ) * ((legendre5 d : ℤ) : ℚ)) =
        ∑ d ∈ n.divisors, f d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hmem := Nat.mem_divisors.mp hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    simp [f, hmem.1, hdpos]
  have hsubset : n.divisors ⊆ Finset.range (n + 1) := by
    intro d hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.divisor_le hd))
  have hsum :
      (∑ d ∈ n.divisors, f d) =
        ∑ d ∈ Finset.range (n + 1), f d := by
    refine Finset.sum_subset hsubset ?_
    intro d _hdr hnot
    have hnotcond : ¬ (d ∣ n ∧ 0 < d) := by
      intro hcond
      exact hnot (Nat.mem_divisors.mpr ⟨hcond.1, Nat.ne_of_gt hn⟩)
    simp [f, hnotcond]
  calc
    (((∑ d ∈ n.divisors, (d : ℤ) * legendre5 d) : ℤ) : ℚ)
        = ∑ d ∈ n.divisors, (d : ℚ) * ((legendre5 d : ℤ) : ℚ) := hcast
    _ = ∑ d ∈ n.divisors, f d := hdiv_to_f
    _ = ∑ d ∈ Finset.range (n + 1), f d := hsum

private theorem chan15_range_legendre_eq_residue_coeffs (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ Finset.range (n + 1),
        if d ∣ n ∧ 0 < d then (d : ℚ) * ((legendre5 d : ℤ) : ℚ) else 0) =
      residueDivisorSigmaCoeff 1 n - residueDivisorSigmaCoeff 2 n -
        residueDivisorSigmaCoeff 3 n + residueDivisorSigmaCoeff 4 n := by
  unfold residueDivisorSigmaCoeff
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hdivpos : d ∣ n ∧ 0 < d
  · have hdmodlt : d % 5 < 5 := Nat.mod_lt d (by norm_num)
    interval_cases hmod : d % 5 <;>
      simp [hdivpos, hn, hmod, legendre5]
  · have hnot1 : ¬ (d ∣ n ∧ 0 < n ∧ d % 5 = 1) := by
      intro h
      exact hdivpos ⟨h.1, Nat.pos_of_dvd_of_pos h.1 h.2.1⟩
    have hnot2 : ¬ (d ∣ n ∧ 0 < n ∧ d % 5 = 2) := by
      intro h
      exact hdivpos ⟨h.1, Nat.pos_of_dvd_of_pos h.1 h.2.1⟩
    have hnot3 : ¬ (d ∣ n ∧ 0 < n ∧ d % 5 = 3) := by
      intro h
      exact hdivpos ⟨h.1, Nat.pos_of_dvd_of_pos h.1 h.2.1⟩
    have hnot4 : ¬ (d ∣ n ∧ 0 < n ∧ d % 5 = 4) := by
      intro h
      exact hdivpos ⟨h.1, Nat.pos_of_dvd_of_pos h.1 h.2.1⟩
    simp [hdivpos, hnot1, hnot2, hnot3, hnot4]

theorem chan15LHSPS_eq_apSigmaLambertFactor_rat :
    chan15LHSPS ℚ = apSigmaLambertFactor := by
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp [apSigmaLambertFactor, chan15LHSPS, chan15LHSCoeff, chan15LHSCoeffInt]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hs1 := apDivisorSigmaPS_coeff_eq_residue_range_rat
      (r := 1) (n := n) (by norm_num) (by norm_num)
    have hs2 := apDivisorSigmaPS_coeff_eq_residue_range_rat
      (r := 2) (n := n) (by norm_num) (by norm_num)
    have hs3 := apDivisorSigmaPS_coeff_eq_residue_range_rat
      (r := 3) (n := n) (by norm_num) (by norm_num)
    have hs4 := apDivisorSigmaPS_coeff_eq_residue_range_rat
      (r := 4) (n := n) (by norm_num) (by norm_num)
    have hsum :
        (((∑ d ∈ n.divisors, (d : ℤ) * legendre5 d) : ℤ) : ℚ) =
          residueDivisorSigmaCoeff 1 n - residueDivisorSigmaCoeff 2 n -
            residueDivisorSigmaCoeff 3 n + residueDivisorSigmaCoeff 4 n := by
      rw [chan15_divisor_sum_eq_range_rat n hn,
        chan15_range_legendre_eq_residue_coeffs n hn]
    have hleft :
        (chan15LHSPS ℚ).coeff n =
          -5 * (residueDivisorSigmaCoeff 1 n - residueDivisorSigmaCoeff 2 n -
            residueDivisorSigmaCoeff 3 n + residueDivisorSigmaCoeff 4 n) := by
      rw [coeff_chan15LHSPS, chan15LHSCoeff, chan15LHSCoeffInt, if_neg hn0]
      rw [Int.cast_mul, hsum]
      norm_num
    have hright :
        apSigmaLambertFactor.coeff n =
          5 * ((residueDivisorSigmaCoeff 2 n + residueDivisorSigmaCoeff 3 n) -
            (residueDivisorSigmaCoeff 1 n + residueDivisorSigmaCoeff 4 n)) := by
      change
        (1 + PowerSeries.C (5 : ℚ) *
          ((apDivisorSigmaPS ℚ 2 5 + apDivisorSigmaPS ℚ 3 5) -
            (apDivisorSigmaPS ℚ 1 5 + apDivisorSigmaPS ℚ 4 5))).coeff n =
          5 * ((residueDivisorSigmaCoeff 2 n + residueDivisorSigmaCoeff 3 n) -
            (residueDivisorSigmaCoeff 1 n + residueDivisorSigmaCoeff 4 n))
      rw [map_add, PowerSeries.coeff_one, if_neg hn0, PowerSeries.coeff_C_mul]
      rw [map_sub, map_add, map_add, hs1, hs2, hs3, hs4]
      ring
    rw [hleft, hright]
    ring

private theorem chan_theorem_11_7_rat_from_wronskian_independent :
    chan15LHSPS ℚ *
        PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) =
      (qPochInfPS ℚ) ^ 5 := by
  have hap :
      apSigmaLambertFactor * expandFiveQpochRat = (qPochInfPS ℚ) ^ 5 := by
    exact apSigmaLambertFactor_eq_etaQuotient_iff_mul_expandFive.mp
      (quintupleLogFactor_eq_etaQuotient_iff_apSigmaLambertFactor.mp
        quintupleProduct_log_derivative_identity)
  rw [chan15LHSPS_eq_apSigmaLambertFactor_rat]
  simpa [expandFiveQpochRat] using hap

private theorem chan_theorem_11_7_int_core_from_wronskian_independent :
    chan15LHSPS ℤ * (PowerSeries.expand 5 (by decide) (qPochInfPS ℤ)) =
      (qPochInfPS ℤ) ^ 5 := by
  apply PowerSeries.map_injective (Int.castRingHom ℚ)
  · intro a b h
    exact Int.cast_injective h
  rw [map_mul, map_pow, PowerSeries.map_expand, map_chan15LHSPS_int,
    map_qPochInfPS]
  exact chan_theorem_11_7_rat_from_wronskian_independent

/-- The remaining arithmetic core of Chan Theorem 11.7, in executable
pentagonal-convolution form.  This is now the exact all-`N` blocker. -/
theorem chan15CoreCoeff_pentagonal_identity (N : ℕ) :
    chan15CoreCoeffLHSZ N = qPochPowPentagonalCoeff 5 N := by
  have hcoeff := congrArg (fun f : ℤ⟦X⟧ => f.coeff N)
    chan_theorem_11_7_int_core_from_wronskian_independent
  change (chan15LHSPS ℤ * PowerSeries.expand 5 (by decide) (qPochInfPS ℤ)).coeff N =
    ((qPochInfPS ℤ) ^ 5).coeff N at hcoeff
  rw [PowerSeries.coeff_mul, coeff_qPochInfPS_pow_pentagonal] at hcoeff
  simpa [chan15CoreCoeffLHSZ, chan15LHSCoeff, PowerSeries.coeff_expand,
    coeff_qPochInfPS_int_eq_pentagonalSign] using hcoeff

/-- Exact coefficient form of the remaining integral blocker.  The left side
is `[X^N] (chan15LHSPS ℤ * expand 5 (qPochInfPS ℤ))`, with both the
Lambert-side coefficients and the `expand 5` coefficients unfolded. -/
theorem chan_theorem_11_7_int_core_coeff (N : ℕ) :
    (∑ ij ∈ Finset.antidiagonal N,
        (chan15LHSCoeffInt ij.1 : ℤ) *
          (if 5 ∣ ij.2 then (qPochInfPS ℤ).coeff (ij.2 / 5) else 0)) =
      ((qPochInfPS ℤ) ^ 5).coeff N := by
  exact chan_theorem_11_7_int_core_coeff_of_pentagonal_identity N
    (chan15CoreCoeff_pentagonal_identity N)

theorem chan_theorem_11_7_int_core :
    chan15LHSPS ℤ * (PowerSeries.expand 5 (by decide) (qPochInfPS ℤ)) =
      (qPochInfPS ℤ) ^ 5 := by
  ext N
  rw [PowerSeries.coeff_mul]
  simpa [PowerSeries.coeff_expand, chan15LHSCoeff] using
    chan_theorem_11_7_int_core_coeff N

theorem chan_theorem_11_7 (R : Type*) [CommRing R] :
    chan15LHSPS R * (PowerSeries.expand 5 (by decide) (qPochInfPS R)) =
      (qPochInfPS R) ^ 5 := by
  have hmap := congrArg (PowerSeries.map (Int.castRingHom R)) chan_theorem_11_7_int_core
  rw [map_mul, map_pow, PowerSeries.map_expand, map_chan15LHSPS_int,
    map_qPochInfPS] at hmap
  exact hmap

end Ch15RODE
end Pending
end QseriesFormalization
