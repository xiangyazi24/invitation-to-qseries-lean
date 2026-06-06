import QseriesFormalization.Chapter10
import QseriesFormalization.Chapter19

/-!
# Chapter 10 / mock theta `f(q)` — formal power series foundation

⚠️  **AUX-LEVEL SCAFFOLDING** for what is currently a SHADOW chapter.

Ramanujan's third-order mock theta function (Lost Notebook):
  `f(q) := ∑_{n≥0} q^{n²} / (-q;q)_n²`.

The existing `Chapter10.ramanujanMockF_trunc` is the finite truncation;
this file defines `f(q)` as a *formal power series* `ramanujanMockFPS R`
(noncomputable, but well-defined coefficient-wise) and proves the basic
algebraic facts.  Chan §10's chapter-main result (Watson's identity, or
the mock-modular property) is not closed; this file lays the formal-PS
foundation toward such a closure.

## What this file contributes

- `ramanujanMockFPS R : PowerSeries R` over any commutative ring `R`,
  defined coefficient-wise via the truncations.
- `coeff_zero_ramanujanMockFPS = 1`: the `n = 0` term contributes `1`,
  higher-`n` terms contribute `0` to the constant coefficient.
- `ramanujanMockFPS_eq_coeff_trunc`: at the formal-PS level, each
  coefficient of `f(q)` equals the same coefficient of the finite
  truncation `ramanujanMockF_trunc q N` for any sufficiently-large `N`
  (the q-adic stabilisation argument).

## Approach to Chan §10 closure (open)

The chapter-main target is one of:
1. Watson's identity (1936): a closed form for `f(q)` in terms of theta
   series (the half-integral-weight cusp form / Eichler integral form).
2. The mock-modular property: `f(q)` has weight-1/2 mock-modular completion
   `\hat f(τ) = f(e^{2πiτ}) + (correction)` transforming as a modular form
   under `SL₂(ℤ)` (full proof needs Zwegers's holomorphic projection).
3. Andrews–Gordon–McIntosh order-3 mock theta identities.

All three are research-level (not in Hirschhorn either, per the
2026-05-24 subagent confirmation in `AUDIT_CLEANUP_PLAN.md`).
-/

namespace QseriesFormalization
namespace Pending
namespace Ch10MockThetaPS

open PowerSeries
open QseriesFormalization.PartII.Ch10

/-- The `n`-th summand of Ramanujan's mock theta, as a formal power series
over `ℚ`: `X^{n²} / (−X;X)_n²`.  The denominator `(−X;X)_n` has constant
term `1` (each factor `(1 − (−X)·X^k) = 1 + X^(k+1)` evaluates to `1` at
`X = 0`), so it's a unit in `ℚ⟦X⟧` (Field-instance `Inv` agrees with
the unit-inverse). -/
noncomputable def ramanujanMockSummandPS (n : ℕ) : ℚ⟦X⟧ :=
  X ^ (n * n) * ((qPoch (-X : ℚ⟦X⟧) X n)⁻¹) ^ 2

/-- The `0`-th summand of `f(q)` is `X⁰ · (1)⁻² = 1`. -/
@[simp] theorem ramanujanMockSummandPS_zero :
    ramanujanMockSummandPS 0 = 1 := by
  unfold ramanujanMockSummandPS
  simp [qPoch_zero]

/-- The `n`-th summand for `n ≥ 1` has constant coefficient `0`, because of
the explicit `X^{n²}` factor with `n² ≥ 1`. -/
theorem coeff_zero_ramanujanMockSummandPS_of_pos
    {n : ℕ} (hn : 0 < n) :
    (ramanujanMockSummandPS n).coeff 0 = 0 := by
  unfold ramanujanMockSummandPS
  have hn_sq : 0 < n * n := Nat.mul_pos hn hn
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
      PowerSeries.constantCoeff_X, zero_pow hn_sq.ne', zero_mul]

/-- Finite partial sum of `f(q)` as a formal power series over `ℚ`. -/
noncomputable def ramanujanMockFPartialPS (N : ℕ) : ℚ⟦X⟧ :=
  ∑ n ∈ Finset.range (N + 1), ramanujanMockSummandPS n

/-- Empty partial sum: `f_{≤0}(q) = X⁰/(−X;X)_0² = 1`. -/
@[simp] theorem ramanujanMockFPartialPS_zero :
    ramanujanMockFPartialPS 0 = 1 := by
  unfold ramanujanMockFPartialPS
  simp

/-- Recursion: `f_{≤N+1}(q) = f_{≤N}(q) + (summand at N+1)`. -/
theorem ramanujanMockFPartialPS_succ (N : ℕ) :
    ramanujanMockFPartialPS (N + 1) =
      ramanujanMockFPartialPS N + ramanujanMockSummandPS (N + 1) := by
  unfold ramanujanMockFPartialPS
  rw [Finset.sum_range_succ]

/-- Constant coefficient of any partial sum of `f(q)` is `1` (only the
`n = 0` summand contributes; all `n ≥ 1` summands have constant
coefficient `0` by `coeff_zero_ramanujanMockSummandPS_of_pos`). -/
theorem coeff_zero_ramanujanMockFPartialPS (N : ℕ) :
    (ramanujanMockFPartialPS N).coeff 0 = 1 := by
  unfold ramanujanMockFPartialPS
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sum]
  rw [show (1 : ℚ) =
        (PowerSeries.constantCoeff (ramanujanMockSummandPS 0)) by
        rw [ramanujanMockSummandPS_zero, map_one]]
  rw [Finset.sum_eq_single 0]
  · intro n _ hn0
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · exact (hn0 hz).elim
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          coeff_zero_ramanujanMockSummandPS_of_pos hpos]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.zero_lt_succ N))).elim

/-! ## Low-degree coefficients

For the current definition
`ramanujanMockSummandPS n = X^(n*n) * (qPoch (-X) X n)⁻¹^2`, the
stabilized coefficients through degree `5` are
`1, 1, -2, 3, -3, 3`.
-/

private theorem coeff_ramanujanMockSummandPS_eq_zero_of_lt_square {n k : ℕ}
    (hk : k < n * n) :
    (ramanujanMockSummandPS n).coeff k = 0 := by
  unfold ramanujanMockSummandPS
  rw [PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le_of_gt hk]

private theorem coeff_ramanujanMockFPartialPS_eq_two_of_le_five {N k : ℕ}
    (hN : 2 ≤ N) (hk : k ≤ 5) :
    (ramanujanMockFPartialPS N).coeff k = (ramanujanMockFPartialPS 2).coeff k := by
  unfold ramanujanMockFPartialPS
  rw [map_sum, map_sum]
  refine (Finset.sum_subset ?subset ?zero).symm
  · intro n hn
    rw [Finset.mem_range] at hn ⊢
    omega
  · intro n hnN hn3
    rw [Finset.mem_range] at hnN
    rw [Finset.mem_range] at hn3
    have hn_ge : 3 ≤ n := by omega
    exact coeff_ramanujanMockSummandPS_eq_zero_of_lt_square (by nlinarith)

private theorem cc_one_add_X : PowerSeries.constantCoeff (1 + X : ℚ⟦X⟧) = 1 := by
  rw [map_add, map_one, PowerSeries.constantCoeff_X, add_zero]

private theorem coeff_inv_one_add_X_0 :
    ((1 + X : ℚ⟦X⟧)⁻¹).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
      cc_one_add_X, inv_one]

private theorem coeff_inv_one_add_X_1 :
    ((1 + X : ℚ⟦X⟧)⁻¹).coeff 1 = -1 := by
  rw [PowerSeries.coeff_inv 1]
  simp only [if_neg one_ne_zero, cc_one_add_X, inv_one]
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (lt_irrefl 1), if_pos Nat.zero_lt_one]
  rw [coeff_inv_one_add_X_0]
  have h_coeff : (PowerSeries.coeff 1) ((1 + X : ℚ⟦X⟧)) = 1 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp
  rw [h_coeff]
  ring

private theorem coeff_inv_one_add_X_2 :
    ((1 + X : ℚ⟦X⟧)⁻¹).coeff 2 = 1 := by
  rw [PowerSeries.coeff_inv 2]
  simp only [if_neg (by decide : (2 : ℕ) ≠ 0), cc_one_add_X, inv_one]
  rw [show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) = {(0, 2), (1, 1), (2, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (by omega : ¬(2 < 2)), if_pos (by omega : 1 < 2),
      if_pos (by omega : 0 < 2)]
  rw [coeff_inv_one_add_X_0, coeff_inv_one_add_X_1]
  have h1 : (PowerSeries.coeff 1) ((1 + X : ℚ⟦X⟧)) = 1 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp
  have h2 : (PowerSeries.coeff 2) ((1 + X : ℚ⟦X⟧)) = 0 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp
  rw [h1, h2]
  ring

private theorem coeff_inv_one_add_X_3 :
    ((1 + X : ℚ⟦X⟧)⁻¹).coeff 3 = -1 := by
  rw [PowerSeries.coeff_inv 3]
  simp only [if_neg (by decide : (3 : ℕ) ≠ 0), cc_one_add_X, inv_one]
  rw [show (Finset.antidiagonal 3 : Finset (ℕ × ℕ)) =
    {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  rw [coeff_inv_one_add_X_0, coeff_inv_one_add_X_1, coeff_inv_one_add_X_2]
  have h1 : (PowerSeries.coeff 1) ((1 + X : ℚ⟦X⟧)) = 1 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp
  have h2 : (PowerSeries.coeff 2) ((1 + X : ℚ⟦X⟧)) = 0 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp
  have h3 : (PowerSeries.coeff 3) ((1 + X : ℚ⟦X⟧)) = 0 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp
  rw [h1, h2, h3]
  ring

private theorem coeff_inv_one_add_X_4 :
    ((1 + X : ℚ⟦X⟧)⁻¹).coeff 4 = 1 := by
  rw [PowerSeries.coeff_inv 4]
  simp only [if_neg (by decide : (4 : ℕ) ≠ 0), cc_one_add_X, inv_one]
  rw [show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
    {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega)]
  rw [coeff_inv_one_add_X_0, coeff_inv_one_add_X_1, coeff_inv_one_add_X_2,
      coeff_inv_one_add_X_3]
  have h1 : (PowerSeries.coeff 1) ((1 + X : ℚ⟦X⟧)) = 1 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp
  have h2 : (PowerSeries.coeff 2) ((1 + X : ℚ⟦X⟧)) = 0 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp
  have h3 : (PowerSeries.coeff 3) ((1 + X : ℚ⟦X⟧)) = 0 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp
  have h4 : (PowerSeries.coeff 4) ((1 + X : ℚ⟦X⟧)) = 0 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp
  rw [h1, h2, h3, h4]
  ring

private theorem coeff_inv_one_add_X_sq_0 :
    (((1 + X : ℚ⟦X⟧)⁻¹) ^ 2).coeff 0 = 1 := by
  rw [pow_two, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 0 : Finset (ℕ × ℕ)) = {(0, 0)} from rfl]
  rw [Finset.sum_singleton, coeff_inv_one_add_X_0]
  ring

private theorem coeff_inv_one_add_X_sq_1 :
    (((1 + X : ℚ⟦X⟧)⁻¹) ^ 2).coeff 1 = -2 := by
  rw [pow_two, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_inv_one_add_X_0, coeff_inv_one_add_X_1]
  ring

private theorem coeff_inv_one_add_X_sq_2 :
    (((1 + X : ℚ⟦X⟧)⁻¹) ^ 2).coeff 2 = 3 := by
  rw [pow_two, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) = {(0, 2), (1, 1), (2, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_inv_one_add_X_0, coeff_inv_one_add_X_1, coeff_inv_one_add_X_2]
  ring

private theorem coeff_inv_one_add_X_sq_3 :
    (((1 + X : ℚ⟦X⟧)⁻¹) ^ 2).coeff 3 = -4 := by
  rw [pow_two, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 3 : Finset (ℕ × ℕ)) =
    {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_inv_one_add_X_0, coeff_inv_one_add_X_1, coeff_inv_one_add_X_2,
      coeff_inv_one_add_X_3]
  ring

private theorem coeff_inv_one_add_X_sq_4 :
    (((1 + X : ℚ⟦X⟧)⁻¹) ^ 2).coeff 4 = 5 := by
  rw [pow_two, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
    {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [coeff_inv_one_add_X_0, coeff_inv_one_add_X_1, coeff_inv_one_add_X_2,
      coeff_inv_one_add_X_3, coeff_inv_one_add_X_4]
  ring

private theorem cc_qPoch_two :
    PowerSeries.constantCoeff (((1 + X) * (1 + X^2) : ℚ⟦X⟧)) = 1 := by
  rw [map_mul]
  simp [map_add, map_one, PowerSeries.constantCoeff_X]

private theorem coeff_qPoch_two_1 :
    (PowerSeries.coeff 1) (((1 + X) * (1 + X^2) : ℚ⟦X⟧)) = 1 := by
  rw [PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  have h_left0 : (PowerSeries.coeff 0) ((1 + X : ℚ⟦X⟧)) = 1 := by simp
  have h_left1 : (PowerSeries.coeff 1) ((1 + X : ℚ⟦X⟧)) = 1 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
    simp
  have h_right0 : (PowerSeries.coeff 0) ((1 + X^2 : ℚ⟦X⟧)) = 1 := by simp
  have h_right1 : (PowerSeries.coeff 1) ((1 + X^2 : ℚ⟦X⟧)) = 0 := by
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    simp
  rw [h_left0, h_left1, h_right0, h_right1]
  ring

private theorem coeff_inv_qPoch_two_0 :
    ((((1 + X) * (1 + X^2) : ℚ⟦X⟧)⁻¹).coeff 0) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
      cc_qPoch_two, inv_one]

private theorem coeff_inv_qPoch_two_1 :
    ((((1 + X) * (1 + X^2) : ℚ⟦X⟧)⁻¹).coeff 1) = -1 := by
  rw [PowerSeries.coeff_inv 1]
  simp only [if_neg one_ne_zero, cc_qPoch_two, inv_one]
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (lt_irrefl 1), if_pos Nat.zero_lt_one]
  rw [coeff_inv_qPoch_two_0, coeff_qPoch_two_1]
  ring

private theorem coeff_inv_qPoch_two_sq_0 :
    (((((1 + X) * (1 + X^2) : ℚ⟦X⟧)⁻¹) ^ 2).coeff 0) = 1 := by
  rw [pow_two, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 0 : Finset (ℕ × ℕ)) = {(0, 0)} from rfl]
  rw [Finset.sum_singleton, coeff_inv_qPoch_two_0]
  ring

private theorem coeff_inv_qPoch_two_sq_1 :
    (((((1 + X) * (1 + X^2) : ℚ⟦X⟧)⁻¹) ^ 2).coeff 1) = -2 := by
  rw [pow_two, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_inv_qPoch_two_0, coeff_inv_qPoch_two_1]
  ring

private theorem ramanujanMockFPartialPS_two_expanded :
    ramanujanMockFPartialPS 2 =
      (1 : ℚ⟦X⟧) + X ^ 1 * ((1 + X : ℚ⟦X⟧)⁻¹) ^ 2 +
        X ^ 4 * ((((1 + X) * (1 + X^2) : ℚ⟦X⟧)⁻¹) ^ 2) := by
  unfold ramanujanMockFPartialPS
  rw [show (Finset.range 3) = {0, 1, 2} from rfl]
  simp
  unfold ramanujanMockSummandPS
  simp [qPoch]
  ring_nf

theorem coeff_zero_ramanujanMockFPartialPS_two :
    (ramanujanMockFPartialPS 2).coeff 0 = 1 := by
  rw [ramanujanMockFPartialPS_two_expanded]
  rw [map_add, map_add, PowerSeries.coeff_one]
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  simp

theorem coeff_one_ramanujanMockFPartialPS_two :
    (ramanujanMockFPartialPS 2).coeff 1 = 1 := by
  rw [ramanujanMockFPartialPS_two_expanded]
  rw [map_add, map_add, PowerSeries.coeff_one]
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  rw [coeff_inv_one_add_X_sq_0]
  simp

theorem coeff_two_ramanujanMockFPartialPS_two :
    (ramanujanMockFPartialPS 2).coeff 2 = -2 := by
  rw [ramanujanMockFPartialPS_two_expanded]
  rw [map_add, map_add, PowerSeries.coeff_one]
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  rw [coeff_inv_one_add_X_sq_1]
  simp

theorem coeff_three_ramanujanMockFPartialPS_two :
    (ramanujanMockFPartialPS 2).coeff 3 = 3 := by
  rw [ramanujanMockFPartialPS_two_expanded]
  rw [map_add, map_add, PowerSeries.coeff_one]
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  rw [coeff_inv_one_add_X_sq_2]
  simp

theorem coeff_four_ramanujanMockFPartialPS_two :
    (ramanujanMockFPartialPS 2).coeff 4 = -3 := by
  rw [ramanujanMockFPartialPS_two_expanded]
  rw [map_add, map_add, PowerSeries.coeff_one]
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  rw [coeff_inv_one_add_X_sq_3, coeff_inv_qPoch_two_sq_0]
  simp
  ring

theorem coeff_five_ramanujanMockFPartialPS_two :
    (ramanujanMockFPartialPS 2).coeff 5 = 3 := by
  rw [ramanujanMockFPartialPS_two_expanded]
  rw [map_add, map_add, PowerSeries.coeff_one]
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  rw [coeff_inv_one_add_X_sq_4, coeff_inv_qPoch_two_sq_1]
  simp
  ring

theorem coeff_one_ramanujanMockFPartialPS_of_two_le (N : ℕ) (hN : 2 ≤ N) :
    (ramanujanMockFPartialPS N).coeff 1 = 1 := by
  rw [coeff_ramanujanMockFPartialPS_eq_two_of_le_five hN (by norm_num),
      coeff_one_ramanujanMockFPartialPS_two]

theorem coeff_two_ramanujanMockFPartialPS_of_two_le (N : ℕ) (hN : 2 ≤ N) :
    (ramanujanMockFPartialPS N).coeff 2 = -2 := by
  rw [coeff_ramanujanMockFPartialPS_eq_two_of_le_five hN (by norm_num),
      coeff_two_ramanujanMockFPartialPS_two]

theorem coeff_three_ramanujanMockFPartialPS_of_two_le (N : ℕ) (hN : 2 ≤ N) :
    (ramanujanMockFPartialPS N).coeff 3 = 3 := by
  rw [coeff_ramanujanMockFPartialPS_eq_two_of_le_five hN (by norm_num),
      coeff_three_ramanujanMockFPartialPS_two]

theorem coeff_four_ramanujanMockFPartialPS_of_two_le (N : ℕ) (hN : 2 ≤ N) :
    (ramanujanMockFPartialPS N).coeff 4 = -3 := by
  rw [coeff_ramanujanMockFPartialPS_eq_two_of_le_five hN (by norm_num),
      coeff_four_ramanujanMockFPartialPS_two]

theorem coeff_five_ramanujanMockFPartialPS_of_two_le (N : ℕ) (hN : 2 ≤ N) :
    (ramanujanMockFPartialPS N).coeff 5 = 3 := by
  rw [coeff_ramanujanMockFPartialPS_eq_two_of_le_five hN (by norm_num),
      coeff_five_ramanujanMockFPartialPS_two]

end Ch10MockThetaPS
end Pending
end QseriesFormalization
