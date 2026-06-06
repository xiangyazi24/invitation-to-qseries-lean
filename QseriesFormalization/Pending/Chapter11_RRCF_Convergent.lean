import QseriesFormalization.Chapter11
import QseriesFormalization.Pending.Chapter13_RRCF_RForm

/-!
# Chapter 11 — Rogers-Ramanujan continued fraction: correct convergents

⚠️ **AUX-LEVEL SCAFFOLDING** for Ch11 (currently AUX).

`Chapter11.R_trunc` builds the RRCF "outside-in" with `q^k` on the *outer*
factor at step `k`, which makes `R_trunc q n → 1` trivially as `n → ∞`
(since `q^n → 0` for `|q| < 1`).  That truncation is NOT a convergent of
the true RRCF.

This file defines the **standard convergents** of

  `R(q) = q^{1/5} · 1 / (1 + q / (1 + q² / (1 + q³ / (⋯))))`

via the **backward recurrence** for continued-fraction convergents
`p_n = a_n·p_{n-1} + b_n·p_{n-2}` with `a_n = 1`, `b_n = q^n`, and the
"trivial 0-th convergent = 1" initial condition `(p_{-1}=1, p_0=1)`, giving

  `p_0 = 1,  p_1 = 1 + q,  p_{n+1} = p_n + q^{n+1}·p_{n-1}`
  `q_0 = 1,  q_1 = 1,      q_{n+1} = q_n + q^{n+1}·q_{n-1}`

The `n`-th convergent (stripped of the `q^{1/5}` prefactor) is
`T_n(q) := p_n(q) / q_n(q)`; numerically `T_n → r(q) = (q;q^5)(q^4;q^5)/((q^2;q^5)(q^3;q^5))`
(Chan Theorem 11.1).

## What this file contributes (corrected 2026-05-27)

Note: yesterday's commit of this file had a base-case bug (`rrcf_A 1 := 1`
instead of `1+q`, `rrcf_B 0 := 0` instead of `1`) that made the recurrence
compute a different CF. Today's version is the corrected one matching
Chan §11 / Theorem 11.1.

- `rrcf_A`, `rrcf_B` : ℕ → ℂ → ℂ definitions, scalar form, for the
  numerator / denominator convergent sequences.
- `rrcf_APS`, `rrcf_BPS` : ℕ → ℚ⟦X⟧ formal-PS lift.
- `rrcf_TPS n := rrcf_APS (n+1) * (rrcf_BPS (n+1))⁻¹` formal-PS convergent.
- Small explicit values + base-case lemmas.

The chapter-main result (X-adic convergence of `rrcf_TPS n` to the formal
power series `r(q)`, equivalent to Chan Theorem 11.1) remains open; this
file provides the correct combinatorial scaffolding.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch11RRCFConvergent

/-- Numerator sequence of the RRCF convergents (scalar):
`A_0 = 1, A_1 = 1+q, A_{n+2} = A_{n+1} + q^{n+2}·A_n`. -/
noncomputable def rrcf_A : ℕ → ℂ → ℂ
  | 0, _ => 1
  | 1, q => 1 + q
  | n + 2, q => rrcf_A (n + 1) q + q ^ (n + 2) * rrcf_A n q

/-- Denominator sequence of the RRCF convergents (scalar):
`B_0 = 1, B_1 = 1, B_{n+2} = B_{n+1} + q^{n+2}·B_n`. -/
noncomputable def rrcf_B : ℕ → ℂ → ℂ
  | 0, _ => 1
  | 1, _ => 1
  | n + 2, q => rrcf_B (n + 1) q + q ^ (n + 2) * rrcf_B n q

@[simp] theorem rrcf_A_zero (q : ℂ) : rrcf_A 0 q = 1 := rfl
@[simp] theorem rrcf_A_one (q : ℂ) : rrcf_A 1 q = 1 + q := rfl
@[simp] theorem rrcf_B_zero (q : ℂ) : rrcf_B 0 q = 1 := rfl
@[simp] theorem rrcf_B_one (q : ℂ) : rrcf_B 1 q = 1 := rfl

theorem rrcf_A_succ_succ (n : ℕ) (q : ℂ) :
    rrcf_A (n + 2) q = rrcf_A (n + 1) q + q ^ (n + 2) * rrcf_A n q := rfl

theorem rrcf_B_succ_succ (n : ℕ) (q : ℂ) :
    rrcf_B (n + 2) q = rrcf_B (n + 1) q + q ^ (n + 2) * rrcf_B n q := rfl

/-- `A_2(q) = 1 + q + q²`. -/
theorem rrcf_A_two (q : ℂ) : rrcf_A 2 q = 1 + q + q ^ 2 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, rrcf_A_succ_succ, rrcf_A_one, rrcf_A_zero]
  ring

/-- `B_2(q) = 1 + q²`. -/
theorem rrcf_B_two (q : ℂ) : rrcf_B 2 q = 1 + q ^ 2 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, rrcf_B_succ_succ, rrcf_B_one, rrcf_B_zero]
  ring

/-- `A_3(q) = 1 + q + q² + q³ + q⁴`. -/
theorem rrcf_A_three (q : ℂ) : rrcf_A 3 q = 1 + q + q ^ 2 + q ^ 3 + q ^ 4 := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, rrcf_A_succ_succ, rrcf_A_two, rrcf_A_one]
  ring

/-- `B_3(q) = 1 + q² + q³`. -/
theorem rrcf_B_three (q : ℂ) : rrcf_B 3 q = 1 + q ^ 2 + q ^ 3 := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, rrcf_B_succ_succ, rrcf_B_two, rrcf_B_one]
  ring

/-! ## Formal-power-series version of the RRCF convergents

To talk about convergence `T_n → r(q)` as `n → ∞`, we lift the recurrence
from `ℂ → ℂ` to `ℚ⟦X⟧` (where the `X`-adic topology makes "stabilization
at fixed degree" precise). Each `B_n` has constant coefficient `1`, hence
is a unit, hence `T_n := A_n · B_n⁻¹` is a genuine formal power series.
-/

open PowerSeries

/-- Numerator sequence of RRCF convergents, as formal power series over `ℚ`. -/
noncomputable def rrcf_APS : ℕ → ℚ⟦X⟧
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => rrcf_APS (n + 1) + X ^ (n + 2) * rrcf_APS n

/-- Denominator sequence of RRCF convergents, as formal power series over `ℚ`. -/
noncomputable def rrcf_BPS : ℕ → ℚ⟦X⟧
  | 0 => 1
  | 1 => 1
  | n + 2 => rrcf_BPS (n + 1) + X ^ (n + 2) * rrcf_BPS n

@[simp] theorem rrcf_APS_zero : rrcf_APS 0 = 1 := rfl
@[simp] theorem rrcf_APS_one : rrcf_APS 1 = 1 + X := rfl
@[simp] theorem rrcf_BPS_zero : rrcf_BPS 0 = 1 := rfl
@[simp] theorem rrcf_BPS_one : rrcf_BPS 1 = 1 := rfl

theorem rrcf_APS_succ_succ (n : ℕ) :
    rrcf_APS (n + 2) = rrcf_APS (n + 1) + X ^ (n + 2) * rrcf_APS n := rfl

theorem rrcf_BPS_succ_succ (n : ℕ) :
    rrcf_BPS (n + 2) = rrcf_BPS (n + 1) + X ^ (n + 2) * rrcf_BPS n := rfl

/-- The constant coefficient of `rrcf_APS n` is `1` for all `n`.

Proof by complete induction. Base cases `n=0,1` give 1 directly; the
inductive step uses `(X^{n+2}).coeff 0 = 0` to kill the correction term. -/
theorem constantCoeff_rrcf_APS : ∀ n : ℕ,
    PowerSeries.constantCoeff (rrcf_APS n) = 1
  | 0 => by simp
  | 1 => by simp [rrcf_APS_one, map_add, map_one, PowerSeries.constantCoeff_X]
  | n + 2 => by
      rw [rrcf_APS_succ_succ, map_add, map_mul, map_pow, PowerSeries.constantCoeff_X,
          zero_pow (Nat.succ_ne_zero _), zero_mul, add_zero,
          constantCoeff_rrcf_APS (n + 1)]

/-- The constant coefficient of `rrcf_BPS n` is `1` for all `n`. -/
theorem constantCoeff_rrcf_BPS : ∀ n : ℕ,
    PowerSeries.constantCoeff (rrcf_BPS n) = 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
      rw [rrcf_BPS_succ_succ, map_add, map_mul, map_pow, PowerSeries.constantCoeff_X,
          zero_pow (Nat.succ_ne_zero _), zero_mul, add_zero,
          constantCoeff_rrcf_BPS (n + 1)]

/-- `rrcf_BPS n` is a unit in `ℚ⟦X⟧` for all `n`. -/
theorem isUnit_rrcf_BPS (n : ℕ) : IsUnit (rrcf_BPS n) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_rrcf_BPS]
  exact isUnit_one

/-- The `n`-th formal-PS convergent of the reciprocal RRCF `1/r(q) =
1 + q/(1+q²/(1+q³/⋯))`. This converges to `1/r(q)`, NOT directly to `r(q)`:

`T_n(X) := A_n(X) · B_n(X)⁻¹` in `ℚ⟦X⟧`.

For the convergent of `r(q)` itself, use `rrcf_RPS` below. -/
noncomputable def rrcf_TPS (n : ℕ) : ℚ⟦X⟧ :=
  rrcf_APS n * (rrcf_BPS n)⁻¹

@[simp] theorem rrcf_TPS_zero : rrcf_TPS 0 = 1 := by
  unfold rrcf_TPS
  rw [rrcf_APS_zero, rrcf_BPS_zero, inv_one, mul_one]

/-! ## Convergence-toward-`r(q)` infrastructure: the CF cross-determinant

The standard structural identity for CF convergents:
  `A_{n+1}·B_n − A_n·B_{n+1} = (−1)^n · X^{(n+1)(n+2)/2}`

drives the convergence of `T_n = A_n/B_n` in the X-adic topology of `ℚ⟦X⟧`,
because the difference `T_{n+1} − T_n = (−1)^n · X^{(n+1)(n+2)/2}/(B_n·B_{n+1})`
has X-adic order ≥ `(n+1)(n+2)/2 → ∞`, hence the sequence is Cauchy and
converges to a limit (`r(q)`, Chan Theorem 11.1).

We prove the cross-determinant identity by induction. -/

private lemma triangular_step (k : ℕ) :
    k + 2 + (k + 1) * (k + 2) / 2 = (k + 2) * (k + 3) / 2 := by
  -- Both (k+1)(k+2) and (k+2)(k+3) are even (consecutive integers product);
  -- the identity then reduces to (k+2)(k+3) = 2(k+2) + (k+1)(k+2), pure ring.
  have h1 : 2 ∣ (k + 1) * (k + 2) := (Nat.even_mul_succ_self (k + 1)).two_dvd
  have h2 : 2 ∣ (k + 2) * (k + 3) := (Nat.even_mul_succ_self (k + 2)).two_dvd
  have heq : (k + 2) * (k + 3) = 2 * (k + 2) + (k + 1) * (k + 2) := by ring
  omega

/-- **CF cross-determinant identity** for the RRCF convergents:
  `A_{n+1}·B_n − A_n·B_{n+1} = (−1)^n · X^{(n+1)(n+2)/2}`.

This is the bridge to convergence: from this, `T_n` differences shrink in
X-adic order at the triangular-number rate, hence form a Cauchy sequence
in `ℚ⟦X⟧`. -/
theorem rrcf_cross_det_PS (n : ℕ) :
    rrcf_APS (n + 1) * rrcf_BPS n - rrcf_APS n * rrcf_BPS (n + 1)
      = ((-1) ^ n : ℚ⟦X⟧) * X ^ ((n + 1) * (n + 2) / 2) := by
  induction n with
  | zero =>
    rw [rrcf_APS_one, rrcf_APS_zero, rrcf_BPS_zero, rrcf_BPS_one]
    simp
  | succ k ih =>
    rw [rrcf_APS_succ_succ k, rrcf_BPS_succ_succ k]
    -- Expand: (A_{k+1} + X^{k+2}·A_k)·B_{k+1} - A_{k+1}·(B_{k+1} + X^{k+2}·B_k)
    -- = X^{k+2} · (A_k·B_{k+1} - A_{k+1}·B_k)
    -- = -X^{k+2} · (A_{k+1}·B_k - A_k·B_{k+1})
    -- = -X^{k+2} · (-1)^k · X^{(k+1)(k+2)/2}   [by IH]
    -- = (-1)^{k+1} · X^{k+2 + (k+1)(k+2)/2}
    -- = (-1)^{k+1} · X^{(k+2)(k+3)/2}
    have key : (rrcf_APS (k + 1) + X ^ (k + 2) * rrcf_APS k) * rrcf_BPS (k + 1)
        - rrcf_APS (k + 1) * (rrcf_BPS (k + 1) + X ^ (k + 2) * rrcf_BPS k)
        = -(X ^ (k + 2)) *
          (rrcf_APS (k + 1) * rrcf_BPS k - rrcf_APS k * rrcf_BPS (k + 1)) := by
      ring
    rw [key, ih]
    rw [show ((-1) ^ (k + 1) : ℚ⟦X⟧) = -((-1) ^ k) by ring]
    rw [show ((k + 1) + 1) * ((k + 1) + 2) / 2 = (k + 2) * (k + 3) / 2 from rfl]
    rw [← triangular_step k]
    rw [pow_add]
    ring

/-- **Successive-convergent difference in multiplicative form**:
  `(T_{n+1} − T_n) · B_n · B_{n+1} = (−1)^n · X^{(n+1)(n+2)/2}`.

Multiplying the cross-determinant identity through by `B_n·B_{n+1}` (both
units) gives the formal-PS version of the textbook
`T_{n+1} − T_n = (−1)^n · X^{(n+1)(n+2)/2}/(B_n·B_{n+1})`, avoiding division. -/
theorem rrcf_TPS_succ_diff_mul (n : ℕ) :
    (rrcf_TPS (n + 1) - rrcf_TPS n) * rrcf_BPS n * rrcf_BPS (n + 1)
      = ((-1) ^ n : ℚ⟦X⟧) * X ^ ((n + 1) * (n + 2) / 2) := by
  unfold rrcf_TPS
  have hBn : PowerSeries.constantCoeff (rrcf_BPS n) ≠ 0 := by
    rw [constantCoeff_rrcf_BPS]; exact one_ne_zero
  have hBn1 : PowerSeries.constantCoeff (rrcf_BPS (n + 1)) ≠ 0 := by
    rw [constantCoeff_rrcf_BPS]; exact one_ne_zero
  have eBn : (rrcf_BPS n)⁻¹ * rrcf_BPS n = 1 :=
    PowerSeries.inv_mul_cancel _ hBn
  have eBn1 : (rrcf_BPS (n + 1))⁻¹ * rrcf_BPS (n + 1) = 1 :=
    PowerSeries.inv_mul_cancel _ hBn1
  -- (A_{n+1}·B_{n+1}⁻¹ - A_n·B_n⁻¹)·B_n·B_{n+1}
  -- = A_{n+1}·(B_{n+1}⁻¹·B_{n+1})·B_n - A_n·(B_n⁻¹·B_n)·B_{n+1}
  -- = A_{n+1}·B_n - A_n·B_{n+1}
  calc (rrcf_APS (n + 1) * (rrcf_BPS (n + 1))⁻¹ - rrcf_APS n * (rrcf_BPS n)⁻¹)
          * rrcf_BPS n * rrcf_BPS (n + 1)
      = rrcf_APS (n + 1) * ((rrcf_BPS (n + 1))⁻¹ * rrcf_BPS (n + 1)) * rrcf_BPS n
        - rrcf_APS n * ((rrcf_BPS n)⁻¹ * rrcf_BPS n) * rrcf_BPS (n + 1) := by ring
    _ = rrcf_APS (n + 1) * rrcf_BPS n - rrcf_APS n * rrcf_BPS (n + 1) := by
        rw [eBn, eBn1]; ring
    _ = ((-1) ^ n : ℚ⟦X⟧) * X ^ ((n + 1) * (n + 2) / 2) := rrcf_cross_det_PS n

/-- The `n`-th formal-PS convergent of the RRCF `r(q) = 1/(1+q/(1+q²/⋯))`:

`R_n(X) := B_n(X) · A_n(X)⁻¹` in `ℚ⟦X⟧`.

(Indices swapped from `T_n` because `r(q) = 1/T(q)` and the convergent of a
reciprocal is the reciprocal of the convergent.) This converges to
`rrcf_r := pentagonal014SeriesPS · pentagonal023SeriesPS⁻¹` (Chan Theorem
11.1, the formal-PS version with `q^{1/5}` prefactor stripped). -/
noncomputable def rrcf_RPS (n : ℕ) : ℚ⟦X⟧ :=
  rrcf_BPS n * (rrcf_APS n)⁻¹

@[simp] theorem rrcf_RPS_zero : rrcf_RPS 0 = 1 := by
  unfold rrcf_RPS
  rw [rrcf_APS_zero, rrcf_BPS_zero, inv_one, mul_one]

@[simp] theorem rrcf_RPS_one : rrcf_RPS 1 = (1 + X : ℚ⟦X⟧)⁻¹ := by
  unfold rrcf_RPS
  rw [rrcf_BPS_one, rrcf_APS_one, one_mul]

/-- `A_2 = 1 + X + X²` in formal PS. -/
theorem rrcf_APS_two : (rrcf_APS 2 : ℚ⟦X⟧) = 1 + X + X ^ 2 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, rrcf_APS_succ_succ, rrcf_APS_one, rrcf_APS_zero]
  ring

/-- `B_2 = 1 + X²` in formal PS. -/
theorem rrcf_BPS_two : (rrcf_BPS 2 : ℚ⟦X⟧) = 1 + X ^ 2 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, rrcf_BPS_succ_succ, rrcf_BPS_one, rrcf_BPS_zero]
  ring

/-- `R_2 = (1+X²) · (1+X+X²)⁻¹` in formal PS. -/
theorem rrcf_RPS_two : rrcf_RPS 2 = (1 + X ^ 2 : ℚ⟦X⟧) * (1 + X + X ^ 2 : ℚ⟦X⟧)⁻¹ := by
  unfold rrcf_RPS
  rw [rrcf_BPS_two, rrcf_APS_two]

/-- `A_3 = 1 + X + X² + X³ + X⁴` in formal PS. -/
theorem rrcf_APS_three : (rrcf_APS 3 : ℚ⟦X⟧) = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, rrcf_APS_succ_succ, rrcf_APS_two, rrcf_APS_one]
  ring

/-- `B_3 = 1 + X² + X³` in formal PS. -/
theorem rrcf_BPS_three : (rrcf_BPS 3 : ℚ⟦X⟧) = 1 + X ^ 2 + X ^ 3 := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, rrcf_BPS_succ_succ, rrcf_BPS_two, rrcf_BPS_one]
  ring

/-- `R_3 = (1+X²+X³) · (1+X+X²+X³+X⁴)⁻¹` in formal PS. -/
theorem rrcf_RPS_three : rrcf_RPS 3 =
    (1 + X ^ 2 + X ^ 3 : ℚ⟦X⟧) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 : ℚ⟦X⟧)⁻¹ := by
  unfold rrcf_RPS
  rw [rrcf_BPS_three, rrcf_APS_three]

/-- **Successive R-convergent difference in multiplicative form**:
  `(R_{n+1} − R_n) · A_n · A_{n+1} = −(−1)^n · X^{(n+1)(n+2)/2}`.

Same X-adic rate as `rrcf_TPS_succ_diff_mul`, opposite sign (since
`R_n = 1/T_n` flips the difference). -/
theorem rrcf_RPS_succ_diff_mul (n : ℕ) :
    (rrcf_RPS (n + 1) - rrcf_RPS n) * rrcf_APS n * rrcf_APS (n + 1)
      = -(((-1) ^ n : ℚ⟦X⟧) * X ^ ((n + 1) * (n + 2) / 2)) := by
  unfold rrcf_RPS
  have hAn : PowerSeries.constantCoeff (rrcf_APS n) ≠ 0 := by
    rw [constantCoeff_rrcf_APS]; exact one_ne_zero
  have hAn1 : PowerSeries.constantCoeff (rrcf_APS (n + 1)) ≠ 0 := by
    rw [constantCoeff_rrcf_APS]; exact one_ne_zero
  have eAn : (rrcf_APS n)⁻¹ * rrcf_APS n = 1 :=
    PowerSeries.inv_mul_cancel _ hAn
  have eAn1 : (rrcf_APS (n + 1))⁻¹ * rrcf_APS (n + 1) = 1 :=
    PowerSeries.inv_mul_cancel _ hAn1
  calc (rrcf_BPS (n + 1) * (rrcf_APS (n + 1))⁻¹ - rrcf_BPS n * (rrcf_APS n)⁻¹)
          * rrcf_APS n * rrcf_APS (n + 1)
      = rrcf_BPS (n + 1) * ((rrcf_APS (n + 1))⁻¹ * rrcf_APS (n + 1)) * rrcf_APS n
        - rrcf_BPS n * ((rrcf_APS n)⁻¹ * rrcf_APS n) * rrcf_APS (n + 1) := by ring
    _ = rrcf_BPS (n + 1) * rrcf_APS n - rrcf_BPS n * rrcf_APS (n + 1) := by
        rw [eAn, eAn1]; ring
    _ = -(rrcf_APS (n + 1) * rrcf_BPS n - rrcf_APS n * rrcf_BPS (n + 1)) := by ring
    _ = -(((-1) ^ n : ℚ⟦X⟧) * X ^ ((n + 1) * (n + 2) / 2)) := by
        rw [rrcf_cross_det_PS n]

/-- **X-adic divisibility estimate for T-convergent differences**:
  `X^{(n+1)(n+2)/2} ∣ (T_{n+1} − T_n)` in `ℚ⟦X⟧`.

Since `B_n·B_{n+1}` is a unit, dividing the multiplicative succ-diff
formula `(T_{n+1}−T_n)·B_n·B_{n+1} = (−1)^n·X^N` by the unit gives
`T_{n+1}−T_n = (−1)^n·X^N·(B_n·B_{n+1})⁻¹`, exhibiting `X^N` as a divisor.

Direct consequence: the X-adic order of `T_{n+1}−T_n` is at least
`(n+1)(n+2)/2`, hence `T_n` is a Cauchy sequence in the X-adic topology
(the convergence rate is faster than any geometric). -/
theorem X_pow_triangular_dvd_rrcf_TPS_succ_diff (n : ℕ) :
    (X ^ ((n + 1) * (n + 2) / 2) : ℚ⟦X⟧) ∣ (rrcf_TPS (n + 1) - rrcf_TPS n) := by
  have hprod_ne : PowerSeries.constantCoeff (rrcf_BPS n * rrcf_BPS (n + 1)) ≠ 0 := by
    rw [map_mul, constantCoeff_rrcf_BPS, constantCoeff_rrcf_BPS]
    norm_num
  have e : (rrcf_BPS n * rrcf_BPS (n + 1)) * (rrcf_BPS n * rrcf_BPS (n + 1))⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hprod_ne
  refine ⟨((-1) ^ n : ℚ⟦X⟧) * (rrcf_BPS n * rrcf_BPS (n + 1))⁻¹, ?_⟩
  calc rrcf_TPS (n + 1) - rrcf_TPS n
      = (rrcf_TPS (n + 1) - rrcf_TPS n) *
        ((rrcf_BPS n * rrcf_BPS (n + 1)) * (rrcf_BPS n * rrcf_BPS (n + 1))⁻¹) := by
        rw [e, mul_one]
    _ = (rrcf_TPS (n + 1) - rrcf_TPS n) * rrcf_BPS n * rrcf_BPS (n + 1) *
        (rrcf_BPS n * rrcf_BPS (n + 1))⁻¹ := by ring
    _ = ((-1) ^ n : ℚ⟦X⟧) * X ^ ((n + 1) * (n + 2) / 2) *
        (rrcf_BPS n * rrcf_BPS (n + 1))⁻¹ := by rw [rrcf_TPS_succ_diff_mul n]
    _ = X ^ ((n + 1) * (n + 2) / 2) * (((-1) ^ n : ℚ⟦X⟧) *
        (rrcf_BPS n * rrcf_BPS (n + 1))⁻¹) := by ring

/-- **X-adic divisibility estimate for the R-convergent**, parallel to the
T-version. Used to derive convergence of `rrcf_RPS` to `rrcf_r`. -/
theorem X_pow_triangular_dvd_rrcf_RPS_succ_diff (n : ℕ) :
    (X ^ ((n + 1) * (n + 2) / 2) : ℚ⟦X⟧) ∣ (rrcf_RPS (n + 1) - rrcf_RPS n) := by
  have hprod_ne : PowerSeries.constantCoeff (rrcf_APS n * rrcf_APS (n + 1)) ≠ 0 := by
    rw [map_mul, constantCoeff_rrcf_APS, constantCoeff_rrcf_APS]
    norm_num
  have e : (rrcf_APS n * rrcf_APS (n + 1)) * (rrcf_APS n * rrcf_APS (n + 1))⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ hprod_ne
  refine ⟨-((-1) ^ n : ℚ⟦X⟧) * (rrcf_APS n * rrcf_APS (n + 1))⁻¹, ?_⟩
  calc rrcf_RPS (n + 1) - rrcf_RPS n
      = (rrcf_RPS (n + 1) - rrcf_RPS n) *
        ((rrcf_APS n * rrcf_APS (n + 1)) * (rrcf_APS n * rrcf_APS (n + 1))⁻¹) := by
        rw [e, mul_one]
    _ = (rrcf_RPS (n + 1) - rrcf_RPS n) * rrcf_APS n * rrcf_APS (n + 1) *
        (rrcf_APS n * rrcf_APS (n + 1))⁻¹ := by ring
    _ = -(((-1) ^ n : ℚ⟦X⟧) * X ^ ((n + 1) * (n + 2) / 2)) *
        (rrcf_APS n * rrcf_APS (n + 1))⁻¹ := by rw [rrcf_RPS_succ_diff_mul n]
    _ = X ^ ((n + 1) * (n + 2) / 2) * (-((-1) ^ n : ℚ⟦X⟧) *
        (rrcf_APS n * rrcf_APS (n + 1))⁻¹) := by ring

/-! ## Coefficient stabilization (X-adic Cauchy form)

The X^N divisibility theorems give a direct, no-topology form of the
Cauchy property: for fixed coefficient degree `k`, the sequence
`(rrcf_TPS n).coeff k` is **eventually constant** as `n → ∞`.

Specifically, for `n ≥ k`, `(rrcf_TPS (n+1)).coeff k = (rrcf_TPS n).coeff k`.
This is because `X^{(n+1)(n+2)/2} ∣ (T_{n+1}−T_n)` forces the `k`-th
coefficient to vanish whenever `k < (n+1)(n+2)/2`, which holds for `n ≥ k`
(since `(n+1)(n+2)/2 ≥ n+1 > k`).
-/

private lemma triangular_gt_of_le (n k : ℕ) (hk : k ≤ n) :
    k < (n + 1) * (n + 2) / 2 := by
  have h_even : 2 ∣ (n + 1) * (n + 2) := (Nat.even_mul_succ_self (n + 1)).two_dvd
  have h_ge : 2 * (n + 1) ≤ (n + 1) * (n + 2) := by
    have : (n + 1) * (n + 2) = (n + 1) * 2 + (n + 1) * n := by ring
    omega
  omega

/-- **Coefficient stabilization for the T-convergent**: for `n ≥ k`,
the `k`-th coefficient of `rrcf_TPS n` matches that of `rrcf_TPS (n+1)`. -/
theorem rrcf_TPS_succ_coeff_eq_of_le (n k : ℕ) (hk : k ≤ n) :
    (rrcf_TPS (n + 1)).coeff k = (rrcf_TPS n).coeff k := by
  have hk' : k < (n + 1) * (n + 2) / 2 := triangular_gt_of_le n k hk
  have hdvd := X_pow_triangular_dvd_rrcf_TPS_succ_diff n
  have hzero : (rrcf_TPS (n + 1) - rrcf_TPS n).coeff k = 0 := by
    rw [PowerSeries.X_pow_dvd_iff] at hdvd
    exact hdvd k hk'
  rw [map_sub] at hzero
  exact (sub_eq_zero.mp hzero)

/-- **Coefficient stabilization for the R-convergent**: same as for T,
for `n ≥ k` the `k`-th coefficient of `rrcf_RPS n` equals that of
`rrcf_RPS (n+1)`. -/
theorem rrcf_RPS_succ_coeff_eq_of_le (n k : ℕ) (hk : k ≤ n) :
    (rrcf_RPS (n + 1)).coeff k = (rrcf_RPS n).coeff k := by
  have hk' : k < (n + 1) * (n + 2) / 2 := triangular_gt_of_le n k hk
  have hdvd := X_pow_triangular_dvd_rrcf_RPS_succ_diff n
  have hzero : (rrcf_RPS (n + 1) - rrcf_RPS n).coeff k = 0 := by
    rw [PowerSeries.X_pow_dvd_iff] at hdvd
    exact hdvd k hk'
  rw [map_sub] at hzero
  exact (sub_eq_zero.mp hzero)

/-- **Coefficient stabilization across multiple steps**: for any `n ≥ k`,
the `k`-th coefficient of `rrcf_RPS n` equals `(rrcf_RPS k).coeff k`.
Induction on `n - k`. -/
theorem rrcf_RPS_coeff_eq_of_le (n k : ℕ) (hk : k ≤ n) :
    (rrcf_RPS n).coeff k = (rrcf_RPS k).coeff k := by
  induction n, hk using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [rrcf_RPS_succ_coeff_eq_of_le m k hm]; exact ih

/-- **Definition of `r(q)` via the CF limit**: the formal power series
whose `k`-th coefficient is `(rrcf_RPS k).coeff k`. Well-defined: any
convergent index `n ≥ k` gives the same `k`-th coefficient by
`rrcf_RPS_coeff_eq_of_le`. -/
noncomputable def rrcf_r_via_CF : ℚ⟦X⟧ :=
  PowerSeries.mk (fun k => (rrcf_RPS k).coeff k)

@[simp] theorem coeff_rrcf_r_via_CF (k : ℕ) :
    (rrcf_r_via_CF).coeff k = (rrcf_RPS k).coeff k := by
  unfold rrcf_r_via_CF
  rw [PowerSeries.coeff_mk]

/-- For any `n ≥ k`, the `k`-th coefficient of `rrcf_r_via_CF` matches
`(rrcf_RPS n).coeff k`. This is the "CF limit equals each tail" form of
the stabilization. -/
theorem coeff_rrcf_r_via_CF_of_le (n k : ℕ) (hk : k ≤ n) :
    (rrcf_r_via_CF).coeff k = (rrcf_RPS n).coeff k := by
  rw [coeff_rrcf_r_via_CF, rrcf_RPS_coeff_eq_of_le n k hk]

/-- Constant coefficient of `rrcf_r_via_CF` is `1`. -/
@[simp] theorem coeff_zero_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 0 = 1 := by
  rw [coeff_rrcf_r_via_CF, rrcf_RPS_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_one]

/-- `(1 + X)⁻¹.coeff 1 = −1` in `ℚ⟦X⟧`. -/
private theorem coeff_one_inv_one_add_X :
    ((1 + X : ℚ⟦X⟧)⁻¹).coeff 1 = -1 := by
  have h_const : PowerSeries.constantCoeff (1 + X : ℚ⟦X⟧) = 1 := by
    rw [map_add, map_one, PowerSeries.constantCoeff_X, add_zero]
  rw [PowerSeries.coeff_inv 1]
  simp only [if_neg (one_ne_zero (α := ℕ)), h_const, inv_one]
  -- antidiagonal 1 = {(0,1), (1,0)}; the filter `b < 1` keeps only (1, 0).
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  simp only [Finset.sum_insert (by decide : (0, 1) ∉ ({(1, 0)} : Finset (ℕ × ℕ))),
             Finset.sum_singleton]
  -- For (0, 1): b = 1, condition b < 1 is false.
  -- For (1, 0): b = 0, condition b < 1 is true; contributes coeff 1 (1+X) · coeff 0 (1+X)⁻¹.
  rw [if_neg (lt_irrefl 1), if_pos (zero_lt_one)]
  -- coeff 0 (1+X)⁻¹ = 1 (constantCoeff of inverse over a field at unit constant term)
  have h_inv0 : ((1 + X : ℚ⟦X⟧)⁻¹).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
        h_const, inv_one]
  rw [h_inv0]
  -- coeff 1 (1+X) = 1
  have h_coeff_X1 : (PowerSeries.coeff 1) ((1 + X : ℚ⟦X⟧)) = 1 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp
  rw [h_coeff_X1]
  ring

/-- `rrcf_r_via_CF.coeff 1 = −1`, matching the first non-trivial coefficient
of the product-form `rrcf_r` (also `−1`). -/
@[simp] theorem coeff_one_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 1 = -1 := by
  rw [coeff_rrcf_r_via_CF, rrcf_RPS_one]
  exact coeff_one_inv_one_add_X

/-! ## Match with product-form `rrcf_r` at small coefficient orders

These verify Chan §11 Theorem 11.1 unconditionally at small coefficient
indices: the CF-limit form `rrcf_r_via_CF` and the product form
`rrcf_r := pentagonal014SeriesPS · pentagonal023SeriesPS⁻¹` (from
`Ch13_RRCF_RForm`) agree at degrees 0 and 1.
-/

/-- **X⁰ coefficient match**: `rrcf_r_via_CF.coeff 0 = rrcf_r.coeff 0 = 1`. -/
theorem coeff_zero_rrcf_r_via_CF_eq_rrcf_r :
    (rrcf_r_via_CF).coeff 0 = (QseriesFormalization.Pending.Ch13RRCF.rrcf_r).coeff 0 := by
  rw [coeff_zero_rrcf_r_via_CF,
      QseriesFormalization.Pending.Ch13RRCF.coeff_zero_rrcf_r]

/-! ## Key identity: `rrcf_RPS n * rrcf_APS n = rrcf_BPS n`

This is the multiplicative form of `R_n = B_n · A_n⁻¹`: clearing the
denominator gives `R_n · A_n = B_n`, which makes coefficient extraction
a finite antidiagonal sum over known polynomial coefficients. -/

/-- `rrcf_RPS n * rrcf_APS n = rrcf_BPS n` — the denominator-cleared form. -/
theorem rrcf_RPS_mul_APS (n : ℕ) :
    rrcf_RPS n * rrcf_APS n = rrcf_BPS n := by
  unfold rrcf_RPS
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [constantCoeff_rrcf_APS]; exact one_ne_zero),
      mul_one]

/-! ## Higher-degree coefficient computations via the product identity

For degree `k`, `rrcf_r_via_CF.coeff k = (rrcf_RPS k).coeff k`. We compute
`(rrcf_RPS k).coeff k` by extracting degree `k` from `R_k · A_k = B_k`:

  `∑_{(i,j) ∈ antidiagonal k} R_k.coeff i · A_k.coeff j = B_k.coeff k`

Since `A_k.coeff 0 = 1`, this gives
`R_k.coeff k = B_k.coeff k − ∑_{i<k} R_k.coeff i · A_k.coeff (k−i)`,
a finite computation using the already-known lower coefficients. -/

/-- `A_4 = 1 + X + X² + X³ + 2X⁴ + X⁵ + X⁶` in formal PS. -/
theorem rrcf_APS_four : (rrcf_APS 4 : ℚ⟦X⟧) =
    1 + X + X ^ 2 + X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, rrcf_APS_succ_succ, rrcf_APS_three, rrcf_APS_two]
  ring

/-- `B_4 = 1 + X² + X³ + X⁴ + X⁶` in formal PS. -/
theorem rrcf_BPS_four : (rrcf_BPS 4 : ℚ⟦X⟧) =
    1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 6 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, rrcf_BPS_succ_succ, rrcf_BPS_three, rrcf_BPS_two]
  ring

/-- `A_5 = 1 + X + X² + X³ + 2X⁴ + 2X⁵ + 2X⁶ + X⁷ + X⁸ + X⁹` in formal PS. -/
theorem rrcf_APS_five : (rrcf_APS 5 : ℚ⟦X⟧) =
    1 + X + X ^ 2 + X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + 2 * X ^ 6 + X ^ 7 +
    X ^ 8 + X ^ 9 := by
  rw [show (5 : ℕ) = 3 + 2 from rfl, rrcf_APS_succ_succ, rrcf_APS_four, rrcf_APS_three]
  ring

/-- `B_5 = 1 + X² + X³ + X⁴ + X⁵ + X⁶ + X⁷ + X⁸` in formal PS. -/
theorem rrcf_BPS_five : (rrcf_BPS 5 : ℚ⟦X⟧) =
    1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 8 := by
  rw [show (5 : ℕ) = 3 + 2 from rfl, rrcf_BPS_succ_succ, rrcf_BPS_four, rrcf_BPS_three]
  ring

/-- `A_6 = 1 + X + X² + X³ + 2X⁴ + 2X⁵ + 3X⁶ + 2X⁷ + 2X⁸ + 2X⁹ + 2X¹⁰ + X¹¹ + X¹²`. -/
theorem rrcf_APS_six : (rrcf_APS 6 : ℚ⟦X⟧) =
    1 + X + X ^ 2 + X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + 3 * X ^ 6 + 2 * X ^ 7 +
    2 * X ^ 8 + 2 * X ^ 9 + 2 * X ^ 10 + X ^ 11 + X ^ 12 := by
  rw [show (6 : ℕ) = 4 + 2 from rfl, rrcf_APS_succ_succ, rrcf_APS_five, rrcf_APS_four]
  ring

/-- `B_6 = 1 + X² + X³ + X⁴ + X⁵ + 2X⁶ + X⁷ + 2X⁸ + X⁹ + X¹⁰ + X¹²`. -/
theorem rrcf_BPS_six : (rrcf_BPS 6 : ℚ⟦X⟧) =
    1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + 2 * X ^ 6 + X ^ 7 + 2 * X ^ 8 +
    X ^ 9 + X ^ 10 + X ^ 12 := by
  rw [show (6 : ℕ) = 4 + 2 from rfl, rrcf_BPS_succ_succ, rrcf_BPS_five, rrcf_BPS_four]
  ring

/-- `A_7` explicit polynomial. -/
theorem rrcf_APS_seven : (rrcf_APS 7 : ℚ⟦X⟧) =
    1 + X + X ^ 2 + X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + 3 * X ^ 6 + 3 * X ^ 7 +
    3 * X ^ 8 + 3 * X ^ 9 + 3 * X ^ 10 + 3 * X ^ 11 + 3 * X ^ 12 +
    2 * X ^ 13 + X ^ 14 + X ^ 15 + X ^ 16 := by
  rw [show (7 : ℕ) = 5 + 2 from rfl, rrcf_APS_succ_succ, rrcf_APS_six, rrcf_APS_five]
  ring

/-- `B_7` explicit polynomial. -/
theorem rrcf_BPS_seven : (rrcf_BPS 7 : ℚ⟦X⟧) =
    1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + 2 * X ^ 6 + 2 * X ^ 7 + 2 * X ^ 8 +
    2 * X ^ 9 + 2 * X ^ 10 + X ^ 11 + 2 * X ^ 12 + X ^ 13 + X ^ 14 + X ^ 15 := by
  rw [show (7 : ℕ) = 5 + 2 from rfl, rrcf_BPS_succ_succ, rrcf_BPS_six, rrcf_BPS_five]
  ring

/-- `A_8` explicit polynomial. -/
theorem rrcf_APS_eight : (rrcf_APS 8 : ℚ⟦X⟧) =
    1 + X + X ^ 2 + X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + 3 * X ^ 6 + 3 * X ^ 7 +
    4 * X ^ 8 + 4 * X ^ 9 + 4 * X ^ 10 + 4 * X ^ 11 + 5 * X ^ 12 +
    4 * X ^ 13 + 4 * X ^ 14 + 3 * X ^ 15 + 3 * X ^ 16 + 2 * X ^ 17 +
    2 * X ^ 18 + X ^ 19 + X ^ 20 := by
  rw [show (8 : ℕ) = 6 + 2 from rfl, rrcf_APS_succ_succ, rrcf_APS_seven, rrcf_APS_six]
  ring

/-- `B_8` explicit polynomial. -/
theorem rrcf_BPS_eight : (rrcf_BPS 8 : ℚ⟦X⟧) =
    1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + 2 * X ^ 6 + 2 * X ^ 7 + 3 * X ^ 8 +
    2 * X ^ 9 + 3 * X ^ 10 + 2 * X ^ 11 + 3 * X ^ 12 + 2 * X ^ 13 +
    3 * X ^ 14 + 2 * X ^ 15 + 2 * X ^ 16 + X ^ 17 + X ^ 18 + X ^ 20 := by
  rw [show (8 : ℕ) = 6 + 2 from rfl, rrcf_BPS_succ_succ, rrcf_BPS_seven, rrcf_BPS_six]
  ring

/-- `A_9` explicit polynomial. -/
theorem rrcf_APS_nine : (rrcf_APS 9 : ℚ⟦X⟧) =
    1 + X + X ^ 2 + X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + 3 * X ^ 6 + 3 * X ^ 7 +
    4 * X ^ 8 + 5 * X ^ 9 + 5 * X ^ 10 + 5 * X ^ 11 + 6 * X ^ 12 +
    6 * X ^ 13 + 6 * X ^ 14 + 6 * X ^ 15 + 6 * X ^ 16 + 5 * X ^ 17 +
    5 * X ^ 18 + 4 * X ^ 19 + 4 * X ^ 20 + 3 * X ^ 21 + 2 * X ^ 22 +
    X ^ 23 + X ^ 24 + X ^ 25 := by
  rw [show (9 : ℕ) = 7 + 2 from rfl, rrcf_APS_succ_succ, rrcf_APS_eight, rrcf_APS_seven]
  ring

/-- `B_9` explicit polynomial. -/
theorem rrcf_BPS_nine : (rrcf_BPS 9 : ℚ⟦X⟧) =
    1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + 2 * X ^ 6 + 2 * X ^ 7 + 3 * X ^ 8 +
    3 * X ^ 9 + 3 * X ^ 10 + 3 * X ^ 11 + 4 * X ^ 12 + 3 * X ^ 13 +
    4 * X ^ 14 + 4 * X ^ 15 + 4 * X ^ 16 + 3 * X ^ 17 + 3 * X ^ 18 +
    2 * X ^ 19 + 2 * X ^ 20 + 2 * X ^ 21 + X ^ 22 + X ^ 23 + X ^ 24 := by
  rw [show (9 : ℕ) = 7 + 2 from rfl, rrcf_BPS_succ_succ, rrcf_BPS_eight, rrcf_BPS_seven]
  ring

/-- `A_10` explicit polynomial. -/
theorem rrcf_APS_ten : (rrcf_APS 10 : ℚ⟦X⟧) =
    1 + X + X ^ 2 + X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + 3 * X ^ 6 + 3 * X ^ 7 +
    4 * X ^ 8 + 5 * X ^ 9 + 6 * X ^ 10 + 6 * X ^ 11 + 7 * X ^ 12 +
    7 * X ^ 13 + 8 * X ^ 14 + 8 * X ^ 15 + 9 * X ^ 16 + 8 * X ^ 17 +
    9 * X ^ 18 + 8 * X ^ 19 + 8 * X ^ 20 + 7 * X ^ 21 + 7 * X ^ 22 +
    5 * X ^ 23 + 5 * X ^ 24 + 4 * X ^ 25 + 3 * X ^ 26 + 2 * X ^ 27 +
    2 * X ^ 28 + X ^ 29 + X ^ 30 := by
  rw [show (10 : ℕ) = 8 + 2 from rfl, rrcf_APS_succ_succ, rrcf_APS_nine, rrcf_APS_eight]
  ring

/-- `B_10` explicit polynomial. -/
theorem rrcf_BPS_ten : (rrcf_BPS 10 : ℚ⟦X⟧) =
    1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + 2 * X ^ 6 + 2 * X ^ 7 + 3 * X ^ 8 +
    3 * X ^ 9 + 4 * X ^ 10 + 3 * X ^ 11 + 5 * X ^ 12 + 4 * X ^ 13 +
    5 * X ^ 14 + 5 * X ^ 15 + 6 * X ^ 16 + 5 * X ^ 17 + 6 * X ^ 18 +
    4 * X ^ 19 + 5 * X ^ 20 + 4 * X ^ 21 + 4 * X ^ 22 + 3 * X ^ 23 +
    4 * X ^ 24 + 2 * X ^ 25 + 2 * X ^ 26 + X ^ 27 + X ^ 28 + X ^ 30 := by
  rw [show (10 : ℕ) = 8 + 2 from rfl, rrcf_BPS_succ_succ, rrcf_BPS_nine, rrcf_BPS_eight]
  ring

/-- **Degree 2**: `rrcf_r_via_CF.coeff 2 = 1`.

By the product identity `R₂·A₂ = B₂`, extracting the degree-2 coefficient:
`R₂[0]·A₂[2] + R₂[1]·A₂[1] + R₂[2]·A₂[0] = B₂[2]`.
Substituting `R₂[0]=1, R₂[1]=−1, A₂[0..2]=[1,1,1], B₂[2]=1`:
`1·1 + (−1)·1 + R₂[2]·1 = 1`, hence `R₂[2] = 1`. -/
@[simp] theorem coeff_two_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 2 = 1 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 2
  have hcoeff : (rrcf_RPS 2 * rrcf_APS 2).coeff 2 = (rrcf_BPS 2).coeff 2 :=
    congr_arg (·.coeff 2) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) = {(0, 2), (1, 1), (2, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at hcoeff
  -- Substitute known coefficients of R₂, A₂, B₂
  have hR0 : (rrcf_RPS 2).coeff 0 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 2 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 2).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 2 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hA0 : (rrcf_APS 2).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
  have hA1 : (rrcf_APS 2).coeff 1 = 1 := by
    rw [rrcf_APS_two]; simp [PowerSeries.coeff_one, PowerSeries.coeff_X,
        PowerSeries.coeff_X_pow]
  have hA2 : (rrcf_APS 2).coeff 2 = 1 := by
    rw [rrcf_APS_two]; simp [PowerSeries.coeff_one, PowerSeries.coeff_X,
        PowerSeries.coeff_X_pow]
  have hB2 : (rrcf_BPS 2).coeff 2 = 1 := by
    rw [rrcf_BPS_two]; simp [PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  rw [hR0, hR1, hA0, hA1, hA2, hB2] at hcoeff
  linarith

/-- **Degree 3**: `rrcf_r_via_CF.coeff 3 = 0`. -/
@[simp] theorem coeff_three_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 3 = 0 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 3
  have hcoeff : (rrcf_RPS 3 * rrcf_APS 3).coeff 3 = (rrcf_BPS 3).coeff 3 :=
    congr_arg (·.coeff 3) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 3 : Finset (ℕ × ℕ)) =
    {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton] at hcoeff
  have hR0 : (rrcf_RPS 3).coeff 0 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 3 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 3).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 3 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 3).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 3 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hA0 : (rrcf_APS 3).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
  have hA1 : (rrcf_APS 3).coeff 1 = 1 := by
    rw [rrcf_APS_three]; simp [PowerSeries.coeff_one, PowerSeries.coeff_X,
        PowerSeries.coeff_X_pow]
  have hA2 : (rrcf_APS 3).coeff 2 = 1 := by
    rw [rrcf_APS_three]; simp [PowerSeries.coeff_one, PowerSeries.coeff_X,
        PowerSeries.coeff_X_pow]
  have hA3 : (rrcf_APS 3).coeff 3 = 1 := by
    rw [rrcf_APS_three]; simp [PowerSeries.coeff_one, PowerSeries.coeff_X,
        PowerSeries.coeff_X_pow]
  have hB3 : (rrcf_BPS 3).coeff 3 = 1 := by
    rw [rrcf_BPS_three]; simp [PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  rw [hR0, hR1, hR2, hA0, hA1, hA2, hA3, hB3] at hcoeff
  linarith

/-- **Degree 4**: `rrcf_r_via_CF.coeff 4 = -1`. -/
@[simp] theorem coeff_four_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 4 = -1 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 4
  have hcoeff : (rrcf_RPS 4 * rrcf_APS 4).coeff 4 = (rrcf_BPS 4).coeff 4 :=
    congr_arg (·.coeff 4) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
    {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at hcoeff
  have hR0 : (rrcf_RPS 4).coeff 0 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 4 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 4).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 4 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 4).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 4 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 4).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 4 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hA0 : (rrcf_APS 4).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
  -- Compute A₄ and B₄ coefficients from the recurrence:
  -- A₄ = A₃ + X⁴·A₂, B₄ = B₃ + X⁴·B₂
  have hA1 : (rrcf_APS 4).coeff 1 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, rrcf_APS_succ_succ, map_add,
        PowerSeries.coeff_X_pow_mul']
    rw [rrcf_APS_three]; simp [PowerSeries.coeff_one, PowerSeries.coeff_X,
        PowerSeries.coeff_X_pow]
  have hA2 : (rrcf_APS 4).coeff 2 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, rrcf_APS_succ_succ, map_add,
        PowerSeries.coeff_X_pow_mul']
    rw [rrcf_APS_three]; simp [PowerSeries.coeff_one, PowerSeries.coeff_X,
        PowerSeries.coeff_X_pow]
  have hA3 : (rrcf_APS 4).coeff 3 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, rrcf_APS_succ_succ, map_add,
        PowerSeries.coeff_X_pow_mul']
    rw [rrcf_APS_three]; simp [PowerSeries.coeff_one, PowerSeries.coeff_X,
        PowerSeries.coeff_X_pow]
  have hA4 : (rrcf_APS 4).coeff 4 = 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, rrcf_APS_succ_succ, map_add,
        PowerSeries.coeff_X_pow_mul']
    simp only [show ¬(4 < 4) from by omega, ↓reduceIte, show 4 - 4 = 0 from rfl]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hB4 : (rrcf_BPS 4).coeff 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, rrcf_BPS_succ_succ, map_add,
        PowerSeries.coeff_X_pow_mul']
    simp only [show ¬(4 < 4) from by omega, ↓reduceIte, show 4 - 4 = 0 from rfl]
    rw [rrcf_BPS_three, rrcf_BPS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  rw [hR0, hR1, hR2, hR3, hA0, hA1, hA2, hA3, hA4, hB4] at hcoeff
  linarith

/-- **Degree 5**: `rrcf_r_via_CF.coeff 5 = 1`. -/
@[simp] theorem coeff_five_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 5 = 1 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 5
  have hcoeff : (rrcf_RPS 5 * rrcf_APS 5).coeff 5 = (rrcf_BPS 5).coeff 5 :=
    congr_arg (·.coeff 5) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 5 : Finset (ℕ × ℕ)) =
    {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton] at hcoeff
  have hR0 : (rrcf_RPS 5).coeff 0 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 5 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 5).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 5 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 5).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 5 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 5).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 5 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 5).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 5 4 (by omega), coeff_four_rrcf_r_via_CF]
  -- Compute A₅ and B₅ coefficients via recurrence: A₅ = A₄ + X⁵·A₃
  -- Then A₄ = A₃ + X⁴·A₂. For k < 4: coeff k (A₅) = coeff k (A₃).
  have hA0 : (rrcf_APS 5).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
  -- For k = 1,2,3 < 5: coeff k (X⁵·A₃) = 0 and coeff k (X⁴·A₂) = 0,
  -- so coeff k A₅ = coeff k A₄ = coeff k A₃
  -- For k < 5: coeff k (A₅) = coeff k (A₃) (two steps of X^n·f vanishing)
  -- For k ≥ 4: need explicit computation via recurrence
  have hA1 : (rrcf_APS 5).coeff 1 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 1) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA2 : (rrcf_APS 5).coeff 2 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 2) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA3 : (rrcf_APS 5).coeff 3 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 3) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA4 : (rrcf_APS 5).coeff 4 = 2 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 4) from by omega), add_zero]
    -- coeff 4 A₄ = coeff 4 A₃ + coeff 0 A₂ = 1 + 1 = 2
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 4 from by omega), show 4 - (2 + 2) = 0 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X,
               PowerSeries.coeff_zero_eq_constantCoeff_apply, map_one]
    norm_num
  have hA5 : (rrcf_APS 5).coeff 5 = 2 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 5 from by omega), show 5 - (3 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    -- coeff 5 A₄ + 1
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 5 from by omega), show 5 - (2 + 2) = 1 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hB5 : (rrcf_BPS 5).coeff 5 = 1 := by
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 5 from by omega), show 5 - (3 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_BPS]
    -- coeff 5 B₄ + 1
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 5 from by omega), show 5 - (2 + 2) = 1 from by omega]
    rw [rrcf_BPS_three, rrcf_BPS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hA0, hA1, hA2, hA3, hA4, hA5, hB5] at hcoeff
  linarith

/-- **Degree 6**: `rrcf_r_via_CF.coeff 6 = -1`. -/
@[simp] theorem coeff_six_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 6 = -1 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 6
  have hcoeff : (rrcf_RPS 6 * rrcf_APS 6).coeff 6 = (rrcf_BPS 6).coeff 6 :=
    congr_arg (·.coeff 6) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 6 : Finset (ℕ × ℕ)) =
    {(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (6, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at hcoeff
  have hR0 : (rrcf_RPS 6).coeff 0 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 6 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 6).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 6 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 6).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 6 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 6).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 6 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 6).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 6 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 6).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 6 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hA0 : (rrcf_APS 6).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
  have hA1 : (rrcf_APS 6).coeff 1 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 1) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA2 : (rrcf_APS 6).coeff 2 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 2) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA3 : (rrcf_APS 6).coeff 3 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 3) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA4 : (rrcf_APS 6).coeff 4 = 2 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 4 from by omega), show 4 - (2 + 2) = 0 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X,
               PowerSeries.coeff_zero_eq_constantCoeff_apply, map_one]
    norm_num
  have hA5 : (rrcf_APS 6).coeff 5 = 2 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 5 from by omega), show 5 - (3 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 5 from by omega), show 5 - (2 + 2) = 1 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA6 : (rrcf_APS 6).coeff 6 = 3 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 6 from by omega), show 6 - (4 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 6 from by omega), show 6 - (3 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 6 from by omega), show 6 - (2 + 2) = 2 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hB6 : (rrcf_BPS 6).coeff 6 = 2 := by
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 6 from by omega), show 6 - (4 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_BPS]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 6 from by omega), show 6 - (3 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 6 from by omega), show 6 - (2 + 2) = 2 from by omega]
    rw [rrcf_BPS_three, rrcf_BPS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hB6] at hcoeff
  linarith

/-- **Degree 7**: `rrcf_r_via_CF.coeff 7 = 1`. -/
@[simp] theorem coeff_seven_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 7 = 1 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 7
  have hcoeff : (rrcf_RPS 7 * rrcf_APS 7).coeff 7 = (rrcf_BPS 7).coeff 7 :=
    congr_arg (·.coeff 7) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 7 : Finset (ℕ × ℕ)) =
    {(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1), (7, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton] at hcoeff
  have hR0 : (rrcf_RPS 7).coeff 0 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 7 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 7).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 7 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 7).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 7 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 7).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 7 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 7).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 7 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 7).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 7 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 7).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 7 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hA0 : (rrcf_APS 7).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
  -- A_7 coeff 1: peel 7=5+2, 6=4+2, 5=3+2, 4=2+2; all X^n terms vanish since n+2 > 1
  have hA1 : (rrcf_APS 7).coeff 1 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 1) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA2 : (rrcf_APS 7).coeff 2 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 2) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA3 : (rrcf_APS 7).coeff 3 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 3) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA4 : (rrcf_APS 7).coeff 4 = 2 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 4 from by omega), show 4 - (2 + 2) = 0 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X,
               PowerSeries.coeff_zero_eq_constantCoeff_apply, map_one]
    norm_num
  have hA5 : (rrcf_APS 7).coeff 5 = 2 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 5 from by omega), show 5 - (3 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 5 from by omega), show 5 - (2 + 2) = 1 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA6 : (rrcf_APS 7).coeff 6 = 3 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 6) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 6 from by omega), show 6 - (4 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 6 from by omega), show 6 - (3 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 6 from by omega), show 6 - (2 + 2) = 2 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA7 : (rrcf_APS 7).coeff 7 = 3 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 7 from by omega), show 7 - (5 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 7 from by omega), show 7 - (4 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 7 from by omega), show 7 - (3 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 7 from by omega), show 7 - (2 + 2) = 3 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hB7 : (rrcf_BPS 7).coeff 7 = 2 := by
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 7 from by omega), show 7 - (5 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_BPS]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 7 from by omega), show 7 - (4 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 7 from by omega), show 7 - (3 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 7 from by omega), show 7 - (2 + 2) = 3 from by omega]
    rw [rrcf_BPS_three, rrcf_BPS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hB7] at hcoeff
  linarith

/-- **Degree 8**: `rrcf_r_via_CF.coeff 8 = 0`. -/
@[simp] theorem coeff_eight_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 8 = 0 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 8
  have hcoeff : (rrcf_RPS 8 * rrcf_APS 8).coeff 8 = (rrcf_BPS 8).coeff 8 :=
    congr_arg (·.coeff 8) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 8 : Finset (ℕ × ℕ)) =
    {(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2), (7, 1), (8, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at hcoeff
  have hR0 : (rrcf_RPS 8).coeff 0 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 8 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 8).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 8 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 8).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 8 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 8).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 8 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 8).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 8 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 8).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 8 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 8).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 8 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 8).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 8 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hA0 : (rrcf_APS 8).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
  have hA1 : (rrcf_APS 8).coeff 1 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 1) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA2 : (rrcf_APS 8).coeff 2 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 2) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA3 : (rrcf_APS 8).coeff 3 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 3) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA4 : (rrcf_APS 8).coeff 4 = 2 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 4 from by omega), show 4 - (2 + 2) = 0 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X,
               PowerSeries.coeff_zero_eq_constantCoeff_apply, map_one]
    norm_num
  have hA5 : (rrcf_APS 8).coeff 5 = 2 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 5 from by omega), show 5 - (3 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 5 from by omega), show 5 - (2 + 2) = 1 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA6 : (rrcf_APS 8).coeff 6 = 3 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 6) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 6) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 6 from by omega), show 6 - (4 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 6 from by omega), show 6 - (3 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 6 from by omega), show 6 - (2 + 2) = 2 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA7 : (rrcf_APS 8).coeff 7 = 3 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 7) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 7 from by omega), show 7 - (5 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 7 from by omega), show 7 - (4 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 7 from by omega), show 7 - (3 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 7 from by omega), show 7 - (2 + 2) = 3 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA8 : (rrcf_APS 8).coeff 8 = 4 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 6 + 2 ≤ 8 from by omega), show 8 - (6 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 8 from by omega), show 8 - (5 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 8 from by omega), show 8 - (4 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 8 from by omega), show 8 - (3 + 2) = 3 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 8 from by omega), show 8 - (2 + 2) = 4 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hB8 : (rrcf_BPS 8).coeff 8 = 3 := by
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 6 + 2 ≤ 8 from by omega), show 8 - (6 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_BPS]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 8 from by omega), show 8 - (5 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 8 from by omega), show 8 - (4 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 8 from by omega), show 8 - (3 + 2) = 3 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 8 from by omega), show 8 - (2 + 2) = 4 from by omega]
    rw [rrcf_BPS_three, rrcf_BPS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hB8] at hcoeff
  linarith

/-- **Degree 9**: `rrcf_r_via_CF.coeff 9 = -1`. -/
@[simp] theorem coeff_nine_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 9 = -1 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 9
  have hcoeff : (rrcf_RPS 9 * rrcf_APS 9).coeff 9 = (rrcf_BPS 9).coeff 9 :=
    congr_arg (·.coeff 9) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 9 : Finset (ℕ × ℕ)) =
    {(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3), (7, 2), (8, 1),
     (9, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton] at hcoeff
  have hR0 : (rrcf_RPS 9).coeff 0 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 9 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 9).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 9 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 9).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 9 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 9).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 9 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 9).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 9 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 9).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 9 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 9).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 9 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 9).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 9 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hR8 : (rrcf_RPS 9).coeff 8 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 9 8 (by omega), coeff_eight_rrcf_r_via_CF]
  have hA0 : (rrcf_APS 9).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
  have hA1 : (rrcf_APS 9).coeff 1 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 1) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA2 : (rrcf_APS 9).coeff 2 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 2) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA3 : (rrcf_APS 9).coeff 3 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 3) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA4 : (rrcf_APS 9).coeff 4 = 2 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 4 from by omega), show 4 - (2 + 2) = 0 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X,
               PowerSeries.coeff_zero_eq_constantCoeff_apply, map_one]
    norm_num
  have hA5 : (rrcf_APS 9).coeff 5 = 2 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 5 from by omega), show 5 - (3 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 5 from by omega), show 5 - (2 + 2) = 1 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA6 : (rrcf_APS 9).coeff 6 = 3 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 6) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 6) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 6) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 6 from by omega), show 6 - (4 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 6 from by omega), show 6 - (3 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 6 from by omega), show 6 - (2 + 2) = 2 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA7 : (rrcf_APS 9).coeff 7 = 3 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 7) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 7) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 7 from by omega), show 7 - (5 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 7 from by omega), show 7 - (4 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 7 from by omega), show 7 - (3 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 7 from by omega), show 7 - (2 + 2) = 3 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA8 : (rrcf_APS 9).coeff 8 = 4 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 8) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 6 + 2 ≤ 8 from by omega), show 8 - (6 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 8 from by omega), show 8 - (5 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 8 from by omega), show 8 - (4 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 8 from by omega), show 8 - (3 + 2) = 3 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 8 from by omega), show 8 - (2 + 2) = 4 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA9 : (rrcf_APS 9).coeff 9 = 5 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 7 + 2 ≤ 9 from by omega), show 9 - (7 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 6 + 2 ≤ 9 from by omega), show 9 - (6 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 9 from by omega), show 9 - (5 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 9 from by omega), show 9 - (4 + 2) = 3 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 9 from by omega), show 9 - (3 + 2) = 4 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 9 from by omega), show 9 - (2 + 2) = 5 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hB9 : (rrcf_BPS 9).coeff 9 = 3 := by
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 7 + 2 ≤ 9 from by omega), show 9 - (7 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_BPS]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 6 + 2 ≤ 9 from by omega), show 9 - (6 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 9 from by omega), show 9 - (5 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 9 from by omega), show 9 - (4 + 2) = 3 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 9 from by omega), show 9 - (3 + 2) = 4 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 9 from by omega), show 9 - (2 + 2) = 5 from by omega]
    rw [rrcf_BPS_three, rrcf_BPS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hB9] at hcoeff
  linarith

/-- **Degree 10**: `rrcf_r_via_CF.coeff 10 = 2`. -/
@[simp] theorem coeff_ten_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 10 = 2 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 10
  have hcoeff : (rrcf_RPS 10 * rrcf_APS 10).coeff 10 = (rrcf_BPS 10).coeff 10 :=
    congr_arg (·.coeff 10) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 10 : Finset (ℕ × ℕ)) =
    {(0, 10), (1, 9), (2, 8), (3, 7), (4, 6), (5, 5), (6, 4), (7, 3), (8, 2),
     (9, 1), (10, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at hcoeff
  have hR0 : (rrcf_RPS 10).coeff 0 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 10 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 10).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 10 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 10).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 10 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 10).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 10 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 10).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 10 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 10).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 10 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 10).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 10 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 10).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 10 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hR8 : (rrcf_RPS 10).coeff 8 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 10 8 (by omega), coeff_eight_rrcf_r_via_CF]
  have hR9 : (rrcf_RPS 10).coeff 9 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 10 9 (by omega), coeff_nine_rrcf_r_via_CF]
  have hA0 : (rrcf_APS 10).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
  have hA1 : (rrcf_APS 10).coeff 1 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 8)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(8 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 1) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 1) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA2 : (rrcf_APS 10).coeff 2 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 8)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(8 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 2) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 2) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA3 : (rrcf_APS 10).coeff 3 = 1 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 8)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(8 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 3) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(2 + 2 ≤ 3) from by omega), add_zero]
    rw [rrcf_APS_three]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA4 : (rrcf_APS 10).coeff 4 = 2 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 8)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(8 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(3 + 2 ≤ 4) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 4 from by omega), show 4 - (2 + 2) = 0 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X,
               PowerSeries.coeff_zero_eq_constantCoeff_apply, map_one]
    norm_num
  have hA5 : (rrcf_APS 10).coeff 5 = 2 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 8)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(8 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(4 + 2 ≤ 5) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 5 from by omega), show 5 - (3 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 5 from by omega), show 5 - (2 + 2) = 1 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA6 : (rrcf_APS 10).coeff 6 = 3 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 8)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(8 + 2 ≤ 6) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 6) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 6) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(5 + 2 ≤ 6) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 6 from by omega), show 6 - (4 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 6 from by omega), show 6 - (3 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 6 from by omega), show 6 - (2 + 2) = 2 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA7 : (rrcf_APS 10).coeff 7 = 3 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 8)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(8 + 2 ≤ 7) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 7) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(6 + 2 ≤ 7) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 7 from by omega), show 7 - (5 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 7 from by omega), show 7 - (4 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 7 from by omega), show 7 - (3 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 7 from by omega), show 7 - (2 + 2) = 3 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA8 : (rrcf_APS 10).coeff 8 = 4 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 8)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(8 + 2 ≤ 8) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(7 + 2 ≤ 8) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 6 + 2 ≤ 8 from by omega), show 8 - (6 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 8 from by omega), show 8 - (5 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 8 from by omega), show 8 - (4 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 8 from by omega), show 8 - (3 + 2) = 3 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 8 from by omega), show 8 - (2 + 2) = 4 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA9 : (rrcf_APS 10).coeff 9 = 5 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 8)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (show ¬(8 + 2 ≤ 9) from by omega), add_zero]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 7 + 2 ≤ 9 from by omega), show 9 - (7 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 6 + 2 ≤ 9 from by omega), show 9 - (6 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 9 from by omega), show 9 - (5 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 9 from by omega), show 9 - (4 + 2) = 3 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 9 from by omega), show 9 - (3 + 2) = 4 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 9 from by omega), show 9 - (2 + 2) = 5 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hA10 : (rrcf_APS 10).coeff 10 = 6 := by
    conv_lhs => rw [rrcf_APS_succ_succ (n := 8)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 8 + 2 ≤ 10 from by omega), show 10 - (8 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_APS]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 7 + 2 ≤ 10 from by omega), show 10 - (7 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 6 + 2 ≤ 10 from by omega), show 10 - (6 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 10 from by omega), show 10 - (5 + 2) = 3 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 10 from by omega), show 10 - (4 + 2) = 4 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 10 from by omega), show 10 - (3 + 2) = 5 from by omega]
    conv_lhs => rw [rrcf_APS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 10 from by omega), show 10 - (2 + 2) = 6 from by omega]
    rw [rrcf_APS_three, rrcf_APS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one, PowerSeries.coeff_X,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  have hB10 : (rrcf_BPS 10).coeff 10 = 4 := by
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 8)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 8 + 2 ≤ 10 from by omega), show 10 - (8 + 2) = 0 from by omega]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rrcf_BPS]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 7)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 7 + 2 ≤ 10 from by omega), show 10 - (7 + 2) = 1 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 6)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 6 + 2 ≤ 10 from by omega), show 10 - (6 + 2) = 2 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 5)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 5 + 2 ≤ 10 from by omega), show 10 - (5 + 2) = 3 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 4)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 4 + 2 ≤ 10 from by omega), show 10 - (4 + 2) = 4 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 3)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 3 + 2 ≤ 10 from by omega), show 10 - (3 + 2) = 5 from by omega]
    conv_lhs => rw [rrcf_BPS_succ_succ (n := 2)]
    rw [map_add, PowerSeries.coeff_X_pow_mul',
        if_pos (show 2 + 2 ≤ 10 from by omega), show 10 - (2 + 2) = 6 from by omega]
    rw [rrcf_BPS_three, rrcf_BPS_two]
    simp only [map_add, map_mul, map_pow, PowerSeries.coeff_one,
               PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', constantCoeff_X]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hA0, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hB10] at hcoeff
  linarith

/-!
### Recurrence-backed coefficient calculators for larger CF checks

The next coefficient verifications continue to use `R_k * A_k = B_k`.
These private calculators package the same recurrence-peeling used above:
`A_{n+2}=A_{n+1}+X^{n+2} A_n` and `B_{n+2}=B_{n+1}+X^{n+2} B_n`,
with `PowerSeries.coeff_X_pow_mul'` handling the shifted term.
-/

private def rrcfAPSCoeffZ : Nat → Nat → Int
  | 0, j => if j = 0 then 1 else 0
  | 1, j => if j = 0 ∨ j = 1 then 1 else 0
  | n + 2, j =>
      rrcfAPSCoeffZ (n + 1) j + if n + 2 ≤ j then rrcfAPSCoeffZ n (j - (n + 2)) else 0

private def rrcfBPSCoeffZ : Nat → Nat → Int
  | 0, j => if j = 0 then 1 else 0
  | 1, j => if j = 0 then 1 else 0
  | n + 2, j =>
      rrcfBPSCoeffZ (n + 1) j + if n + 2 ≤ j then rrcfBPSCoeffZ n (j - (n + 2)) else 0

private theorem coeff_rrcf_APS_eq_calc :
    ∀ n j : Nat, (rrcf_APS n).coeff j = (rrcfAPSCoeffZ n j : ℚ)
  | 0, j => by
      unfold rrcfAPSCoeffZ
      by_cases h : j = 0
      · subst j
        simp [PowerSeries.coeff_one]
      · simp [PowerSeries.coeff_one, h]
  | 1, j => by
      unfold rrcfAPSCoeffZ
      rw [rrcf_APS_one, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
      by_cases h0 : j = 0
      · subst j
        simp
      · by_cases h1 : j = 1
        · subst j
          simp
        · simp [h0, h1]
  | n + 2, j => by
      rw [rrcf_APS_succ_succ, map_add, PowerSeries.coeff_X_pow_mul']
      rw [coeff_rrcf_APS_eq_calc (n + 1) j]
      by_cases h : n + 2 ≤ j
      · rw [if_pos h, coeff_rrcf_APS_eq_calc n (j - (n + 2))]
        simp [rrcfAPSCoeffZ, h]
      · rw [if_neg h]
        simp [rrcfAPSCoeffZ, h]

private theorem coeff_rrcf_BPS_eq_calc :
    ∀ n j : Nat, (rrcf_BPS n).coeff j = (rrcfBPSCoeffZ n j : ℚ)
  | 0, j => by
      unfold rrcfBPSCoeffZ
      by_cases h : j = 0
      · subst j
        simp [PowerSeries.coeff_one]
      · simp [PowerSeries.coeff_one, h]
  | 1, j => by
      unfold rrcfBPSCoeffZ
      by_cases h : j = 0
      · subst j
        simp [rrcf_BPS_one, PowerSeries.coeff_one]
      · simp [rrcf_BPS_one, PowerSeries.coeff_one, h]
  | n + 2, j => by
      rw [rrcf_BPS_succ_succ, map_add, PowerSeries.coeff_X_pow_mul']
      rw [coeff_rrcf_BPS_eq_calc (n + 1) j]
      by_cases h : n + 2 ≤ j
      · rw [if_pos h, coeff_rrcf_BPS_eq_calc n (j - (n + 2))]
        simp [rrcfBPSCoeffZ, h]
      · rw [if_neg h]
        simp [rrcfBPSCoeffZ, h]

/-- **Degree 11**: `rrcf_r_via_CF.coeff 11 = -3`. -/
@[simp] theorem coeff_eleven_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 11 = -3 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 11
  have hcoeff : (rrcf_RPS 11 * rrcf_APS 11).coeff 11 = (rrcf_BPS 11).coeff 11 :=
    congr_arg (·.coeff 11) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun a b => (rrcf_RPS 11).coeff a * (rrcf_APS 11).coeff b) 11] at hcoeff
  norm_num [Finset.sum_range_succ] at hcoeff
  have hR0 : PowerSeries.constantCoeff (rrcf_RPS 11) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← coeff_rrcf_r_via_CF_of_le 11 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 11).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 11 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 11).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 11 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 11).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 11 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 11).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 11 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 11).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 11 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 11).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 11 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 11).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 11 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hR8 : (rrcf_RPS 11).coeff 8 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 11 8 (by omega), coeff_eight_rrcf_r_via_CF]
  have hR9 : (rrcf_RPS 11).coeff 9 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 11 9 (by omega), coeff_nine_rrcf_r_via_CF]
  have hR10 : (rrcf_RPS 11).coeff 10 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 11 10 (by omega), coeff_ten_rrcf_r_via_CF]
  have hA1 : (rrcf_APS 11).coeff 1 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 11 1 = 1 := by decide
    rw [h]
    norm_num
  have hA2 : (rrcf_APS 11).coeff 2 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 11 2 = 1 := by decide
    rw [h]
    norm_num
  have hA3 : (rrcf_APS 11).coeff 3 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 11 3 = 1 := by decide
    rw [h]
    norm_num
  have hA4 : (rrcf_APS 11).coeff 4 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 11 4 = 2 := by decide
    rw [h]
    norm_num
  have hA5 : (rrcf_APS 11).coeff 5 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 11 5 = 2 := by decide
    rw [h]
    norm_num
  have hA6 : (rrcf_APS 11).coeff 6 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 11 6 = 3 := by decide
    rw [h]
    norm_num
  have hA7 : (rrcf_APS 11).coeff 7 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 11 7 = 3 := by decide
    rw [h]
    norm_num
  have hA8 : (rrcf_APS 11).coeff 8 = 4 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 11 8 = 4 := by decide
    rw [h]
    norm_num
  have hA9 : (rrcf_APS 11).coeff 9 = 5 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 11 9 = 5 := by decide
    rw [h]
    norm_num
  have hA10 : (rrcf_APS 11).coeff 10 = 6 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 11 10 = 6 := by decide
    rw [h]
    norm_num
  have hA11 : (rrcf_APS 11).coeff 11 = 7 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 11 11 = 7 := by decide
    rw [h]
    norm_num
  have hB11 : (rrcf_BPS 11).coeff 11 = 4 := by
    rw [coeff_rrcf_BPS_eq_calc]
    have h : rrcfBPSCoeffZ 11 11 = 4 := by decide
    rw [h]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hB11, constantCoeff_rrcf_APS] at hcoeff
  norm_num at hcoeff
  linarith

/-- **Degree 12**: `rrcf_r_via_CF.coeff 12 = 2`. -/
@[simp] theorem coeff_twelve_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 12 = 2 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 12
  have hcoeff : (rrcf_RPS 12 * rrcf_APS 12).coeff 12 = (rrcf_BPS 12).coeff 12 :=
    congr_arg (·.coeff 12) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun a b => (rrcf_RPS 12).coeff a * (rrcf_APS 12).coeff b) 12] at hcoeff
  norm_num [Finset.sum_range_succ] at hcoeff
  have hR0 : PowerSeries.constantCoeff (rrcf_RPS 12) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← coeff_rrcf_r_via_CF_of_le 12 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 12).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 12 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 12).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 12 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 12).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 12 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 12).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 12 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 12).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 12 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 12).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 12 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 12).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 12 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hR8 : (rrcf_RPS 12).coeff 8 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 12 8 (by omega), coeff_eight_rrcf_r_via_CF]
  have hR9 : (rrcf_RPS 12).coeff 9 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 12 9 (by omega), coeff_nine_rrcf_r_via_CF]
  have hR10 : (rrcf_RPS 12).coeff 10 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 12 10 (by omega), coeff_ten_rrcf_r_via_CF]
  have hR11 : (rrcf_RPS 12).coeff 11 = -3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 12 11 (by omega), coeff_eleven_rrcf_r_via_CF]
  have hA1 : (rrcf_APS 12).coeff 1 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 12 1 = 1 := by decide
    rw [h]
    norm_num
  have hA2 : (rrcf_APS 12).coeff 2 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 12 2 = 1 := by decide
    rw [h]
    norm_num
  have hA3 : (rrcf_APS 12).coeff 3 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 12 3 = 1 := by decide
    rw [h]
    norm_num
  have hA4 : (rrcf_APS 12).coeff 4 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 12 4 = 2 := by decide
    rw [h]
    norm_num
  have hA5 : (rrcf_APS 12).coeff 5 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 12 5 = 2 := by decide
    rw [h]
    norm_num
  have hA6 : (rrcf_APS 12).coeff 6 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 12 6 = 3 := by decide
    rw [h]
    norm_num
  have hA7 : (rrcf_APS 12).coeff 7 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 12 7 = 3 := by decide
    rw [h]
    norm_num
  have hA8 : (rrcf_APS 12).coeff 8 = 4 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 12 8 = 4 := by decide
    rw [h]
    norm_num
  have hA9 : (rrcf_APS 12).coeff 9 = 5 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 12 9 = 5 := by decide
    rw [h]
    norm_num
  have hA10 : (rrcf_APS 12).coeff 10 = 6 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 12 10 = 6 := by decide
    rw [h]
    norm_num
  have hA11 : (rrcf_APS 12).coeff 11 = 7 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 12 11 = 7 := by decide
    rw [h]
    norm_num
  have hA12 : (rrcf_APS 12).coeff 12 = 9 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 12 12 = 9 := by decide
    rw [h]
    norm_num
  have hB12 : (rrcf_BPS 12).coeff 12 = 6 := by
    rw [coeff_rrcf_BPS_eq_calc]
    have h : rrcfBPSCoeffZ 12 12 = 6 := by decide
    rw [h]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hB12, constantCoeff_rrcf_APS] at hcoeff
  norm_num at hcoeff
  linarith

/-- **Degree 13**: `rrcf_r_via_CF.coeff 13 = 0`. -/
@[simp] theorem coeff_thirteen_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 13 = 0 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 13
  have hcoeff : (rrcf_RPS 13 * rrcf_APS 13).coeff 13 = (rrcf_BPS 13).coeff 13 :=
    congr_arg (·.coeff 13) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun a b => (rrcf_RPS 13).coeff a * (rrcf_APS 13).coeff b) 13] at hcoeff
  norm_num [Finset.sum_range_succ] at hcoeff
  have hR0 : PowerSeries.constantCoeff (rrcf_RPS 13) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← coeff_rrcf_r_via_CF_of_le 13 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 13).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 13 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 13).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 13 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 13).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 13 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 13).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 13 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 13).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 13 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 13).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 13 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 13).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 13 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hR8 : (rrcf_RPS 13).coeff 8 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 13 8 (by omega), coeff_eight_rrcf_r_via_CF]
  have hR9 : (rrcf_RPS 13).coeff 9 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 13 9 (by omega), coeff_nine_rrcf_r_via_CF]
  have hR10 : (rrcf_RPS 13).coeff 10 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 13 10 (by omega), coeff_ten_rrcf_r_via_CF]
  have hR11 : (rrcf_RPS 13).coeff 11 = -3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 13 11 (by omega), coeff_eleven_rrcf_r_via_CF]
  have hR12 : (rrcf_RPS 13).coeff 12 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 13 12 (by omega), coeff_twelve_rrcf_r_via_CF]
  have hA1 : (rrcf_APS 13).coeff 1 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 1 = 1 := by decide
    rw [h]
    norm_num
  have hA2 : (rrcf_APS 13).coeff 2 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 2 = 1 := by decide
    rw [h]
    norm_num
  have hA3 : (rrcf_APS 13).coeff 3 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 3 = 1 := by decide
    rw [h]
    norm_num
  have hA4 : (rrcf_APS 13).coeff 4 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 4 = 2 := by decide
    rw [h]
    norm_num
  have hA5 : (rrcf_APS 13).coeff 5 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 5 = 2 := by decide
    rw [h]
    norm_num
  have hA6 : (rrcf_APS 13).coeff 6 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 6 = 3 := by decide
    rw [h]
    norm_num
  have hA7 : (rrcf_APS 13).coeff 7 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 7 = 3 := by decide
    rw [h]
    norm_num
  have hA8 : (rrcf_APS 13).coeff 8 = 4 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 8 = 4 := by decide
    rw [h]
    norm_num
  have hA9 : (rrcf_APS 13).coeff 9 = 5 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 9 = 5 := by decide
    rw [h]
    norm_num
  have hA10 : (rrcf_APS 13).coeff 10 = 6 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 10 = 6 := by decide
    rw [h]
    norm_num
  have hA11 : (rrcf_APS 13).coeff 11 = 7 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 11 = 7 := by decide
    rw [h]
    norm_num
  have hA12 : (rrcf_APS 13).coeff 12 = 9 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 12 = 9 := by decide
    rw [h]
    norm_num
  have hA13 : (rrcf_APS 13).coeff 13 = 10 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 13 13 = 10 := by decide
    rw [h]
    norm_num
  have hB13 : (rrcf_BPS 13).coeff 13 = 6 := by
    rw [coeff_rrcf_BPS_eq_calc]
    have h : rrcfBPSCoeffZ 13 13 = 6 := by decide
    rw [h]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hR12, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hB13, constantCoeff_rrcf_APS] at hcoeff
  norm_num at hcoeff
  linarith

/-- **Degree 14**: `rrcf_r_via_CF.coeff 14 = -2`. -/
@[simp] theorem coeff_fourteen_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 14 = -2 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 14
  have hcoeff : (rrcf_RPS 14 * rrcf_APS 14).coeff 14 = (rrcf_BPS 14).coeff 14 :=
    congr_arg (·.coeff 14) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun a b => (rrcf_RPS 14).coeff a * (rrcf_APS 14).coeff b) 14] at hcoeff
  norm_num [Finset.sum_range_succ] at hcoeff
  have hR0 : PowerSeries.constantCoeff (rrcf_RPS 14) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← coeff_rrcf_r_via_CF_of_le 14 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 14).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 14).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 14).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 14).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 14).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 14).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 14).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hR8 : (rrcf_RPS 14).coeff 8 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 8 (by omega), coeff_eight_rrcf_r_via_CF]
  have hR9 : (rrcf_RPS 14).coeff 9 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 9 (by omega), coeff_nine_rrcf_r_via_CF]
  have hR10 : (rrcf_RPS 14).coeff 10 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 10 (by omega), coeff_ten_rrcf_r_via_CF]
  have hR11 : (rrcf_RPS 14).coeff 11 = -3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 11 (by omega), coeff_eleven_rrcf_r_via_CF]
  have hR12 : (rrcf_RPS 14).coeff 12 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 12 (by omega), coeff_twelve_rrcf_r_via_CF]
  have hR13 : (rrcf_RPS 14).coeff 13 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 14 13 (by omega), coeff_thirteen_rrcf_r_via_CF]
  have hA1 : (rrcf_APS 14).coeff 1 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 1 = 1 := by decide
    rw [h]
    norm_num
  have hA2 : (rrcf_APS 14).coeff 2 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 2 = 1 := by decide
    rw [h]
    norm_num
  have hA3 : (rrcf_APS 14).coeff 3 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 3 = 1 := by decide
    rw [h]
    norm_num
  have hA4 : (rrcf_APS 14).coeff 4 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 4 = 2 := by decide
    rw [h]
    norm_num
  have hA5 : (rrcf_APS 14).coeff 5 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 5 = 2 := by decide
    rw [h]
    norm_num
  have hA6 : (rrcf_APS 14).coeff 6 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 6 = 3 := by decide
    rw [h]
    norm_num
  have hA7 : (rrcf_APS 14).coeff 7 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 7 = 3 := by decide
    rw [h]
    norm_num
  have hA8 : (rrcf_APS 14).coeff 8 = 4 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 8 = 4 := by decide
    rw [h]
    norm_num
  have hA9 : (rrcf_APS 14).coeff 9 = 5 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 9 = 5 := by decide
    rw [h]
    norm_num
  have hA10 : (rrcf_APS 14).coeff 10 = 6 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 10 = 6 := by decide
    rw [h]
    norm_num
  have hA11 : (rrcf_APS 14).coeff 11 = 7 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 11 = 7 := by decide
    rw [h]
    norm_num
  have hA12 : (rrcf_APS 14).coeff 12 = 9 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 12 = 9 := by decide
    rw [h]
    norm_num
  have hA13 : (rrcf_APS 14).coeff 13 = 10 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 13 = 10 := by decide
    rw [h]
    norm_num
  have hA14 : (rrcf_APS 14).coeff 14 = 12 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 14 14 = 12 := by decide
    rw [h]
    norm_num
  have hB14 : (rrcf_BPS 14).coeff 14 = 8 := by
    rw [coeff_rrcf_BPS_eq_calc]
    have h : rrcfBPSCoeffZ 14 14 = 8 := by decide
    rw [h]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hR12, hR13, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hB14, constantCoeff_rrcf_APS] at hcoeff
  norm_num at hcoeff
  linarith

/-- **Degree 15**: `rrcf_r_via_CF.coeff 15 = 4`. -/
@[simp] theorem coeff_fifteen_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 15 = 4 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 15
  have hcoeff : (rrcf_RPS 15 * rrcf_APS 15).coeff 15 = (rrcf_BPS 15).coeff 15 :=
    congr_arg (·.coeff 15) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun a b => (rrcf_RPS 15).coeff a * (rrcf_APS 15).coeff b) 15] at hcoeff
  norm_num [Finset.sum_range_succ] at hcoeff
  have hR0 : PowerSeries.constantCoeff (rrcf_RPS 15) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← coeff_rrcf_r_via_CF_of_le 15 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 15).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 15).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 15).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 15).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 15).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 15).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 15).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hR8 : (rrcf_RPS 15).coeff 8 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 8 (by omega), coeff_eight_rrcf_r_via_CF]
  have hR9 : (rrcf_RPS 15).coeff 9 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 9 (by omega), coeff_nine_rrcf_r_via_CF]
  have hR10 : (rrcf_RPS 15).coeff 10 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 10 (by omega), coeff_ten_rrcf_r_via_CF]
  have hR11 : (rrcf_RPS 15).coeff 11 = -3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 11 (by omega), coeff_eleven_rrcf_r_via_CF]
  have hR12 : (rrcf_RPS 15).coeff 12 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 12 (by omega), coeff_twelve_rrcf_r_via_CF]
  have hR13 : (rrcf_RPS 15).coeff 13 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 13 (by omega), coeff_thirteen_rrcf_r_via_CF]
  have hR14 : (rrcf_RPS 15).coeff 14 = -2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 15 14 (by omega), coeff_fourteen_rrcf_r_via_CF]
  have hA1 : (rrcf_APS 15).coeff 1 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 1 = 1 := by decide
    rw [h]
    norm_num
  have hA2 : (rrcf_APS 15).coeff 2 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 2 = 1 := by decide
    rw [h]
    norm_num
  have hA3 : (rrcf_APS 15).coeff 3 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 3 = 1 := by decide
    rw [h]
    norm_num
  have hA4 : (rrcf_APS 15).coeff 4 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 4 = 2 := by decide
    rw [h]
    norm_num
  have hA5 : (rrcf_APS 15).coeff 5 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 5 = 2 := by decide
    rw [h]
    norm_num
  have hA6 : (rrcf_APS 15).coeff 6 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 6 = 3 := by decide
    rw [h]
    norm_num
  have hA7 : (rrcf_APS 15).coeff 7 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 7 = 3 := by decide
    rw [h]
    norm_num
  have hA8 : (rrcf_APS 15).coeff 8 = 4 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 8 = 4 := by decide
    rw [h]
    norm_num
  have hA9 : (rrcf_APS 15).coeff 9 = 5 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 9 = 5 := by decide
    rw [h]
    norm_num
  have hA10 : (rrcf_APS 15).coeff 10 = 6 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 10 = 6 := by decide
    rw [h]
    norm_num
  have hA11 : (rrcf_APS 15).coeff 11 = 7 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 11 = 7 := by decide
    rw [h]
    norm_num
  have hA12 : (rrcf_APS 15).coeff 12 = 9 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 12 = 9 := by decide
    rw [h]
    norm_num
  have hA13 : (rrcf_APS 15).coeff 13 = 10 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 13 = 10 := by decide
    rw [h]
    norm_num
  have hA14 : (rrcf_APS 15).coeff 14 = 12 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 14 = 12 := by decide
    rw [h]
    norm_num
  have hA15 : (rrcf_APS 15).coeff 15 = 14 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 15 15 = 14 := by decide
    rw [h]
    norm_num
  have hB15 : (rrcf_BPS 15).coeff 15 = 9 := by
    rw [coeff_rrcf_BPS_eq_calc]
    have h : rrcfBPSCoeffZ 15 15 = 9 := by decide
    rw [h]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hR12, hR13, hR14, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hB15, constantCoeff_rrcf_APS] at hcoeff
  norm_num at hcoeff
  linarith

/-- **Degree 16**: `rrcf_r_via_CF.coeff 16 = -4`. -/
@[simp] theorem coeff_sixteen_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 16 = -4 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 16
  have hcoeff : (rrcf_RPS 16 * rrcf_APS 16).coeff 16 = (rrcf_BPS 16).coeff 16 :=
    congr_arg (·.coeff 16) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun a b => (rrcf_RPS 16).coeff a * (rrcf_APS 16).coeff b) 16] at hcoeff
  norm_num [Finset.sum_range_succ] at hcoeff
  have hR0 : PowerSeries.constantCoeff (rrcf_RPS 16) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← coeff_rrcf_r_via_CF_of_le 16 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 16).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 16).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 16).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 16).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 16).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 16).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 16).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hR8 : (rrcf_RPS 16).coeff 8 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 8 (by omega), coeff_eight_rrcf_r_via_CF]
  have hR9 : (rrcf_RPS 16).coeff 9 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 9 (by omega), coeff_nine_rrcf_r_via_CF]
  have hR10 : (rrcf_RPS 16).coeff 10 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 10 (by omega), coeff_ten_rrcf_r_via_CF]
  have hR11 : (rrcf_RPS 16).coeff 11 = -3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 11 (by omega), coeff_eleven_rrcf_r_via_CF]
  have hR12 : (rrcf_RPS 16).coeff 12 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 12 (by omega), coeff_twelve_rrcf_r_via_CF]
  have hR13 : (rrcf_RPS 16).coeff 13 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 13 (by omega), coeff_thirteen_rrcf_r_via_CF]
  have hR14 : (rrcf_RPS 16).coeff 14 = -2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 14 (by omega), coeff_fourteen_rrcf_r_via_CF]
  have hR15 : (rrcf_RPS 16).coeff 15 = 4 := by
    rw [← coeff_rrcf_r_via_CF_of_le 16 15 (by omega), coeff_fifteen_rrcf_r_via_CF]
  have hA1 : (rrcf_APS 16).coeff 1 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 1 = 1 := by decide
    rw [h]
    norm_num
  have hA2 : (rrcf_APS 16).coeff 2 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 2 = 1 := by decide
    rw [h]
    norm_num
  have hA3 : (rrcf_APS 16).coeff 3 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 3 = 1 := by decide
    rw [h]
    norm_num
  have hA4 : (rrcf_APS 16).coeff 4 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 4 = 2 := by decide
    rw [h]
    norm_num
  have hA5 : (rrcf_APS 16).coeff 5 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 5 = 2 := by decide
    rw [h]
    norm_num
  have hA6 : (rrcf_APS 16).coeff 6 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 6 = 3 := by decide
    rw [h]
    norm_num
  have hA7 : (rrcf_APS 16).coeff 7 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 7 = 3 := by decide
    rw [h]
    norm_num
  have hA8 : (rrcf_APS 16).coeff 8 = 4 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 8 = 4 := by decide
    rw [h]
    norm_num
  have hA9 : (rrcf_APS 16).coeff 9 = 5 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 9 = 5 := by decide
    rw [h]
    norm_num
  have hA10 : (rrcf_APS 16).coeff 10 = 6 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 10 = 6 := by decide
    rw [h]
    norm_num
  have hA11 : (rrcf_APS 16).coeff 11 = 7 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 11 = 7 := by decide
    rw [h]
    norm_num
  have hA12 : (rrcf_APS 16).coeff 12 = 9 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 12 = 9 := by decide
    rw [h]
    norm_num
  have hA13 : (rrcf_APS 16).coeff 13 = 10 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 13 = 10 := by decide
    rw [h]
    norm_num
  have hA14 : (rrcf_APS 16).coeff 14 = 12 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 14 = 12 := by decide
    rw [h]
    norm_num
  have hA15 : (rrcf_APS 16).coeff 15 = 14 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 15 = 14 := by decide
    rw [h]
    norm_num
  have hA16 : (rrcf_APS 16).coeff 16 = 17 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 16 16 = 17 := by decide
    rw [h]
    norm_num
  have hB16 : (rrcf_BPS 16).coeff 16 = 11 := by
    rw [coeff_rrcf_BPS_eq_calc]
    have h : rrcfBPSCoeffZ 16 16 = 11 := by decide
    rw [h]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hR12, hR13, hR14, hR15, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hB16, constantCoeff_rrcf_APS] at hcoeff
  norm_num at hcoeff
  linarith

/-- **Degree 17**: `rrcf_r_via_CF.coeff 17 = 3`. -/
@[simp] theorem coeff_seventeen_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 17 = 3 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 17
  have hcoeff : (rrcf_RPS 17 * rrcf_APS 17).coeff 17 = (rrcf_BPS 17).coeff 17 :=
    congr_arg (·.coeff 17) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun a b => (rrcf_RPS 17).coeff a * (rrcf_APS 17).coeff b) 17] at hcoeff
  norm_num [Finset.sum_range_succ] at hcoeff
  have hR0 : PowerSeries.constantCoeff (rrcf_RPS 17) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← coeff_rrcf_r_via_CF_of_le 17 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 17).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 17).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 17).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 17).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 17).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 17).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 17).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hR8 : (rrcf_RPS 17).coeff 8 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 8 (by omega), coeff_eight_rrcf_r_via_CF]
  have hR9 : (rrcf_RPS 17).coeff 9 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 9 (by omega), coeff_nine_rrcf_r_via_CF]
  have hR10 : (rrcf_RPS 17).coeff 10 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 10 (by omega), coeff_ten_rrcf_r_via_CF]
  have hR11 : (rrcf_RPS 17).coeff 11 = -3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 11 (by omega), coeff_eleven_rrcf_r_via_CF]
  have hR12 : (rrcf_RPS 17).coeff 12 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 12 (by omega), coeff_twelve_rrcf_r_via_CF]
  have hR13 : (rrcf_RPS 17).coeff 13 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 13 (by omega), coeff_thirteen_rrcf_r_via_CF]
  have hR14 : (rrcf_RPS 17).coeff 14 = -2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 14 (by omega), coeff_fourteen_rrcf_r_via_CF]
  have hR15 : (rrcf_RPS 17).coeff 15 = 4 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 15 (by omega), coeff_fifteen_rrcf_r_via_CF]
  have hR16 : (rrcf_RPS 17).coeff 16 = -4 := by
    rw [← coeff_rrcf_r_via_CF_of_le 17 16 (by omega), coeff_sixteen_rrcf_r_via_CF]
  have hA1 : (rrcf_APS 17).coeff 1 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 1 = 1 := by decide
    rw [h]
    norm_num
  have hA2 : (rrcf_APS 17).coeff 2 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 2 = 1 := by decide
    rw [h]
    norm_num
  have hA3 : (rrcf_APS 17).coeff 3 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 3 = 1 := by decide
    rw [h]
    norm_num
  have hA4 : (rrcf_APS 17).coeff 4 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 4 = 2 := by decide
    rw [h]
    norm_num
  have hA5 : (rrcf_APS 17).coeff 5 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 5 = 2 := by decide
    rw [h]
    norm_num
  have hA6 : (rrcf_APS 17).coeff 6 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 6 = 3 := by decide
    rw [h]
    norm_num
  have hA7 : (rrcf_APS 17).coeff 7 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 7 = 3 := by decide
    rw [h]
    norm_num
  have hA8 : (rrcf_APS 17).coeff 8 = 4 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 8 = 4 := by decide
    rw [h]
    norm_num
  have hA9 : (rrcf_APS 17).coeff 9 = 5 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 9 = 5 := by decide
    rw [h]
    norm_num
  have hA10 : (rrcf_APS 17).coeff 10 = 6 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 10 = 6 := by decide
    rw [h]
    norm_num
  have hA11 : (rrcf_APS 17).coeff 11 = 7 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 11 = 7 := by decide
    rw [h]
    norm_num
  have hA12 : (rrcf_APS 17).coeff 12 = 9 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 12 = 9 := by decide
    rw [h]
    norm_num
  have hA13 : (rrcf_APS 17).coeff 13 = 10 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 13 = 10 := by decide
    rw [h]
    norm_num
  have hA14 : (rrcf_APS 17).coeff 14 = 12 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 14 = 12 := by decide
    rw [h]
    norm_num
  have hA15 : (rrcf_APS 17).coeff 15 = 14 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 15 = 14 := by decide
    rw [h]
    norm_num
  have hA16 : (rrcf_APS 17).coeff 16 = 17 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 16 = 17 := by decide
    rw [h]
    norm_num
  have hA17 : (rrcf_APS 17).coeff 17 = 19 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 17 17 = 19 := by decide
    rw [h]
    norm_num
  have hB17 : (rrcf_BPS 17).coeff 17 = 12 := by
    rw [coeff_rrcf_BPS_eq_calc]
    have h : rrcfBPSCoeffZ 17 17 = 12 := by decide
    rw [h]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hR12, hR13, hR14, hR15, hR16, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hB17, constantCoeff_rrcf_APS] at hcoeff
  norm_num at hcoeff
  linarith

/-- **Degree 18**: `rrcf_r_via_CF.coeff 18 = -1`. -/
@[simp] theorem coeff_eighteen_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 18 = -1 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 18
  have hcoeff : (rrcf_RPS 18 * rrcf_APS 18).coeff 18 = (rrcf_BPS 18).coeff 18 :=
    congr_arg (·.coeff 18) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun a b => (rrcf_RPS 18).coeff a * (rrcf_APS 18).coeff b) 18] at hcoeff
  norm_num [Finset.sum_range_succ] at hcoeff
  have hR0 : PowerSeries.constantCoeff (rrcf_RPS 18) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← coeff_rrcf_r_via_CF_of_le 18 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 18).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 18).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 18).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 18).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 18).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 18).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 18).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hR8 : (rrcf_RPS 18).coeff 8 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 8 (by omega), coeff_eight_rrcf_r_via_CF]
  have hR9 : (rrcf_RPS 18).coeff 9 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 9 (by omega), coeff_nine_rrcf_r_via_CF]
  have hR10 : (rrcf_RPS 18).coeff 10 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 10 (by omega), coeff_ten_rrcf_r_via_CF]
  have hR11 : (rrcf_RPS 18).coeff 11 = -3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 11 (by omega), coeff_eleven_rrcf_r_via_CF]
  have hR12 : (rrcf_RPS 18).coeff 12 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 12 (by omega), coeff_twelve_rrcf_r_via_CF]
  have hR13 : (rrcf_RPS 18).coeff 13 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 13 (by omega), coeff_thirteen_rrcf_r_via_CF]
  have hR14 : (rrcf_RPS 18).coeff 14 = -2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 14 (by omega), coeff_fourteen_rrcf_r_via_CF]
  have hR15 : (rrcf_RPS 18).coeff 15 = 4 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 15 (by omega), coeff_fifteen_rrcf_r_via_CF]
  have hR16 : (rrcf_RPS 18).coeff 16 = -4 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 16 (by omega), coeff_sixteen_rrcf_r_via_CF]
  have hR17 : (rrcf_RPS 18).coeff 17 = 3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 18 17 (by omega), coeff_seventeen_rrcf_r_via_CF]
  have hA1 : (rrcf_APS 18).coeff 1 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 1 = 1 := by decide
    rw [h]
    norm_num
  have hA2 : (rrcf_APS 18).coeff 2 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 2 = 1 := by decide
    rw [h]
    norm_num
  have hA3 : (rrcf_APS 18).coeff 3 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 3 = 1 := by decide
    rw [h]
    norm_num
  have hA4 : (rrcf_APS 18).coeff 4 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 4 = 2 := by decide
    rw [h]
    norm_num
  have hA5 : (rrcf_APS 18).coeff 5 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 5 = 2 := by decide
    rw [h]
    norm_num
  have hA6 : (rrcf_APS 18).coeff 6 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 6 = 3 := by decide
    rw [h]
    norm_num
  have hA7 : (rrcf_APS 18).coeff 7 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 7 = 3 := by decide
    rw [h]
    norm_num
  have hA8 : (rrcf_APS 18).coeff 8 = 4 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 8 = 4 := by decide
    rw [h]
    norm_num
  have hA9 : (rrcf_APS 18).coeff 9 = 5 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 9 = 5 := by decide
    rw [h]
    norm_num
  have hA10 : (rrcf_APS 18).coeff 10 = 6 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 10 = 6 := by decide
    rw [h]
    norm_num
  have hA11 : (rrcf_APS 18).coeff 11 = 7 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 11 = 7 := by decide
    rw [h]
    norm_num
  have hA12 : (rrcf_APS 18).coeff 12 = 9 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 12 = 9 := by decide
    rw [h]
    norm_num
  have hA13 : (rrcf_APS 18).coeff 13 = 10 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 13 = 10 := by decide
    rw [h]
    norm_num
  have hA14 : (rrcf_APS 18).coeff 14 = 12 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 14 = 12 := by decide
    rw [h]
    norm_num
  have hA15 : (rrcf_APS 18).coeff 15 = 14 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 15 = 14 := by decide
    rw [h]
    norm_num
  have hA16 : (rrcf_APS 18).coeff 16 = 17 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 16 = 17 := by decide
    rw [h]
    norm_num
  have hA17 : (rrcf_APS 18).coeff 17 = 19 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 17 = 19 := by decide
    rw [h]
    norm_num
  have hA18 : (rrcf_APS 18).coeff 18 = 23 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 18 18 = 23 := by decide
    rw [h]
    norm_num
  have hB18 : (rrcf_BPS 18).coeff 18 = 15 := by
    rw [coeff_rrcf_BPS_eq_calc]
    have h : rrcfBPSCoeffZ 18 18 = 15 := by decide
    rw [h]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hR12, hR13, hR14, hR15, hR16, hR17, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hA18, hB18, constantCoeff_rrcf_APS] at hcoeff
  norm_num at hcoeff
  linarith

/-- **Degree 19**: `rrcf_r_via_CF.coeff 19 = -3`. -/
@[simp] theorem coeff_nineteen_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 19 = -3 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 19
  have hcoeff : (rrcf_RPS 19 * rrcf_APS 19).coeff 19 = (rrcf_BPS 19).coeff 19 :=
    congr_arg (·.coeff 19) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun a b => (rrcf_RPS 19).coeff a * (rrcf_APS 19).coeff b) 19] at hcoeff
  norm_num [Finset.sum_range_succ] at hcoeff
  have hR0 : PowerSeries.constantCoeff (rrcf_RPS 19) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← coeff_rrcf_r_via_CF_of_le 19 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 19).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 19).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 19).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 19).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 19).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 19).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 19).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hR8 : (rrcf_RPS 19).coeff 8 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 8 (by omega), coeff_eight_rrcf_r_via_CF]
  have hR9 : (rrcf_RPS 19).coeff 9 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 9 (by omega), coeff_nine_rrcf_r_via_CF]
  have hR10 : (rrcf_RPS 19).coeff 10 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 10 (by omega), coeff_ten_rrcf_r_via_CF]
  have hR11 : (rrcf_RPS 19).coeff 11 = -3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 11 (by omega), coeff_eleven_rrcf_r_via_CF]
  have hR12 : (rrcf_RPS 19).coeff 12 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 12 (by omega), coeff_twelve_rrcf_r_via_CF]
  have hR13 : (rrcf_RPS 19).coeff 13 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 13 (by omega), coeff_thirteen_rrcf_r_via_CF]
  have hR14 : (rrcf_RPS 19).coeff 14 = -2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 14 (by omega), coeff_fourteen_rrcf_r_via_CF]
  have hR15 : (rrcf_RPS 19).coeff 15 = 4 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 15 (by omega), coeff_fifteen_rrcf_r_via_CF]
  have hR16 : (rrcf_RPS 19).coeff 16 = -4 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 16 (by omega), coeff_sixteen_rrcf_r_via_CF]
  have hR17 : (rrcf_RPS 19).coeff 17 = 3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 17 (by omega), coeff_seventeen_rrcf_r_via_CF]
  have hR18 : (rrcf_RPS 19).coeff 18 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 19 18 (by omega), coeff_eighteen_rrcf_r_via_CF]
  have hA1 : (rrcf_APS 19).coeff 1 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 1 = 1 := by decide
    rw [h]
    norm_num
  have hA2 : (rrcf_APS 19).coeff 2 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 2 = 1 := by decide
    rw [h]
    norm_num
  have hA3 : (rrcf_APS 19).coeff 3 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 3 = 1 := by decide
    rw [h]
    norm_num
  have hA4 : (rrcf_APS 19).coeff 4 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 4 = 2 := by decide
    rw [h]
    norm_num
  have hA5 : (rrcf_APS 19).coeff 5 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 5 = 2 := by decide
    rw [h]
    norm_num
  have hA6 : (rrcf_APS 19).coeff 6 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 6 = 3 := by decide
    rw [h]
    norm_num
  have hA7 : (rrcf_APS 19).coeff 7 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 7 = 3 := by decide
    rw [h]
    norm_num
  have hA8 : (rrcf_APS 19).coeff 8 = 4 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 8 = 4 := by decide
    rw [h]
    norm_num
  have hA9 : (rrcf_APS 19).coeff 9 = 5 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 9 = 5 := by decide
    rw [h]
    norm_num
  have hA10 : (rrcf_APS 19).coeff 10 = 6 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 10 = 6 := by decide
    rw [h]
    norm_num
  have hA11 : (rrcf_APS 19).coeff 11 = 7 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 11 = 7 := by decide
    rw [h]
    norm_num
  have hA12 : (rrcf_APS 19).coeff 12 = 9 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 12 = 9 := by decide
    rw [h]
    norm_num
  have hA13 : (rrcf_APS 19).coeff 13 = 10 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 13 = 10 := by decide
    rw [h]
    norm_num
  have hA14 : (rrcf_APS 19).coeff 14 = 12 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 14 = 12 := by decide
    rw [h]
    norm_num
  have hA15 : (rrcf_APS 19).coeff 15 = 14 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 15 = 14 := by decide
    rw [h]
    norm_num
  have hA16 : (rrcf_APS 19).coeff 16 = 17 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 16 = 17 := by decide
    rw [h]
    norm_num
  have hA17 : (rrcf_APS 19).coeff 17 = 19 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 17 = 19 := by decide
    rw [h]
    norm_num
  have hA18 : (rrcf_APS 19).coeff 18 = 23 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 18 = 23 := by decide
    rw [h]
    norm_num
  have hA19 : (rrcf_APS 19).coeff 19 = 26 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 19 19 = 26 := by decide
    rw [h]
    norm_num
  have hB19 : (rrcf_BPS 19).coeff 19 = 16 := by
    rw [coeff_rrcf_BPS_eq_calc]
    have h : rrcfBPSCoeffZ 19 19 = 16 := by decide
    rw [h]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hR12, hR13, hR14, hR15, hR16, hR17, hR18, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hA18, hA19, hB19, constantCoeff_rrcf_APS] at hcoeff
  norm_num at hcoeff
  linarith

/-- **Degree 20**: `rrcf_r_via_CF.coeff 20 = 6`. -/
@[simp] theorem coeff_twenty_rrcf_r_via_CF :
    (rrcf_r_via_CF).coeff 20 = 6 := by
  rw [coeff_rrcf_r_via_CF]
  have hprod := rrcf_RPS_mul_APS 20
  have hcoeff : (rrcf_RPS 20 * rrcf_APS 20).coeff 20 = (rrcf_BPS 20).coeff 20 :=
    congr_arg (·.coeff 20) hprod
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun a b => (rrcf_RPS 20).coeff a * (rrcf_APS 20).coeff b) 20] at hcoeff
  norm_num [Finset.sum_range_succ] at hcoeff
  have hR0 : PowerSeries.constantCoeff (rrcf_RPS 20) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← coeff_rrcf_r_via_CF_of_le 20 0 (by omega), coeff_zero_rrcf_r_via_CF]
  have hR1 : (rrcf_RPS 20).coeff 1 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 1 (by omega), coeff_one_rrcf_r_via_CF]
  have hR2 : (rrcf_RPS 20).coeff 2 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 2 (by omega), coeff_two_rrcf_r_via_CF]
  have hR3 : (rrcf_RPS 20).coeff 3 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 3 (by omega), coeff_three_rrcf_r_via_CF]
  have hR4 : (rrcf_RPS 20).coeff 4 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 4 (by omega), coeff_four_rrcf_r_via_CF]
  have hR5 : (rrcf_RPS 20).coeff 5 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 5 (by omega), coeff_five_rrcf_r_via_CF]
  have hR6 : (rrcf_RPS 20).coeff 6 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 6 (by omega), coeff_six_rrcf_r_via_CF]
  have hR7 : (rrcf_RPS 20).coeff 7 = 1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 7 (by omega), coeff_seven_rrcf_r_via_CF]
  have hR8 : (rrcf_RPS 20).coeff 8 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 8 (by omega), coeff_eight_rrcf_r_via_CF]
  have hR9 : (rrcf_RPS 20).coeff 9 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 9 (by omega), coeff_nine_rrcf_r_via_CF]
  have hR10 : (rrcf_RPS 20).coeff 10 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 10 (by omega), coeff_ten_rrcf_r_via_CF]
  have hR11 : (rrcf_RPS 20).coeff 11 = -3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 11 (by omega), coeff_eleven_rrcf_r_via_CF]
  have hR12 : (rrcf_RPS 20).coeff 12 = 2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 12 (by omega), coeff_twelve_rrcf_r_via_CF]
  have hR13 : (rrcf_RPS 20).coeff 13 = 0 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 13 (by omega), coeff_thirteen_rrcf_r_via_CF]
  have hR14 : (rrcf_RPS 20).coeff 14 = -2 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 14 (by omega), coeff_fourteen_rrcf_r_via_CF]
  have hR15 : (rrcf_RPS 20).coeff 15 = 4 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 15 (by omega), coeff_fifteen_rrcf_r_via_CF]
  have hR16 : (rrcf_RPS 20).coeff 16 = -4 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 16 (by omega), coeff_sixteen_rrcf_r_via_CF]
  have hR17 : (rrcf_RPS 20).coeff 17 = 3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 17 (by omega), coeff_seventeen_rrcf_r_via_CF]
  have hR18 : (rrcf_RPS 20).coeff 18 = -1 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 18 (by omega), coeff_eighteen_rrcf_r_via_CF]
  have hR19 : (rrcf_RPS 20).coeff 19 = -3 := by
    rw [← coeff_rrcf_r_via_CF_of_le 20 19 (by omega), coeff_nineteen_rrcf_r_via_CF]
  have hA1 : (rrcf_APS 20).coeff 1 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 1 = 1 := by decide
    rw [h]
    norm_num
  have hA2 : (rrcf_APS 20).coeff 2 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 2 = 1 := by decide
    rw [h]
    norm_num
  have hA3 : (rrcf_APS 20).coeff 3 = 1 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 3 = 1 := by decide
    rw [h]
    norm_num
  have hA4 : (rrcf_APS 20).coeff 4 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 4 = 2 := by decide
    rw [h]
    norm_num
  have hA5 : (rrcf_APS 20).coeff 5 = 2 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 5 = 2 := by decide
    rw [h]
    norm_num
  have hA6 : (rrcf_APS 20).coeff 6 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 6 = 3 := by decide
    rw [h]
    norm_num
  have hA7 : (rrcf_APS 20).coeff 7 = 3 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 7 = 3 := by decide
    rw [h]
    norm_num
  have hA8 : (rrcf_APS 20).coeff 8 = 4 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 8 = 4 := by decide
    rw [h]
    norm_num
  have hA9 : (rrcf_APS 20).coeff 9 = 5 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 9 = 5 := by decide
    rw [h]
    norm_num
  have hA10 : (rrcf_APS 20).coeff 10 = 6 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 10 = 6 := by decide
    rw [h]
    norm_num
  have hA11 : (rrcf_APS 20).coeff 11 = 7 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 11 = 7 := by decide
    rw [h]
    norm_num
  have hA12 : (rrcf_APS 20).coeff 12 = 9 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 12 = 9 := by decide
    rw [h]
    norm_num
  have hA13 : (rrcf_APS 20).coeff 13 = 10 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 13 = 10 := by decide
    rw [h]
    norm_num
  have hA14 : (rrcf_APS 20).coeff 14 = 12 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 14 = 12 := by decide
    rw [h]
    norm_num
  have hA15 : (rrcf_APS 20).coeff 15 = 14 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 15 = 14 := by decide
    rw [h]
    norm_num
  have hA16 : (rrcf_APS 20).coeff 16 = 17 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 16 = 17 := by decide
    rw [h]
    norm_num
  have hA17 : (rrcf_APS 20).coeff 17 = 19 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 17 = 19 := by decide
    rw [h]
    norm_num
  have hA18 : (rrcf_APS 20).coeff 18 = 23 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 18 = 23 := by decide
    rw [h]
    norm_num
  have hA19 : (rrcf_APS 20).coeff 19 = 26 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 19 = 26 := by decide
    rw [h]
    norm_num
  have hA20 : (rrcf_APS 20).coeff 20 = 31 := by
    rw [coeff_rrcf_APS_eq_calc]
    have h : rrcfAPSCoeffZ 20 20 = 31 := by decide
    rw [h]
    norm_num
  have hB20 : (rrcf_BPS 20).coeff 20 = 20 := by
    rw [coeff_rrcf_BPS_eq_calc]
    have h : rrcfBPSCoeffZ 20 20 = 20 := by decide
    rw [h]
    norm_num
  rw [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hR12, hR13, hR14, hR15, hR16, hR17, hR18, hR19, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hA18, hA19, hA20, hB20, constantCoeff_rrcf_APS] at hcoeff
  norm_num at hcoeff
  linarith

end Ch11RRCFConvergent
end Pending
end QseriesFormalization
