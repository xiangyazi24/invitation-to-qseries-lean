import QseriesFormalization.Pending.Chapter13_RRCF_RForm

/-!
# Coefficient-by-coefficient verification of Chan Theorem 11.5

Both sides of Chan's "difficult and deep" identity

  `r(q)⁵ · (1 + 3v + 4v² + 2v³ + v⁴) = r(q⁵) · (1 − 2v + 4v² − 3v³ + v⁴)`

are computable formal power series in `ℚ⟦X⟧`. This file establishes the
coefficient infrastructure needed to verify the identity degree by degree,
extending the degree-0 verification in `Chapter13_RRCF_RForm`.

## Verified coefficient values

| k | rrcf_r | rrcf_v |
|---|--------|--------|
| 0 | 1      | 0      |
| 1 | -1     | 1      |
| 2 | 1      | 0      |
| 3 | 0      | 0      |

## Numerically verified identity coefficients

Both sides match through degree 10:
`[1, -2, 4, -3, 1, -1, 4, -12, 12, -5, 1, ...]`
-/

namespace QseriesFormalization
namespace Pending
namespace Ch13CoeffVerification

open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.Ch13RRCF
open QseriesFormalization.Pending.Ch16MBIProof

/-- Left-hand side of Chan Theorem 11.5 in the fractional-power-free
formal-power-series form used in this file. -/
noncomputable def chanTheorem115LHS : PowerSeries ℚ :=
  rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)

/-- Right-hand side of Chan Theorem 11.5 in the fractional-power-free
formal-power-series form used in this file. -/
noncomputable def chanTheorem115RHS : PowerSeries ℚ :=
  (PowerSeries.expand 5 (by decide) rrcf_r) *
    (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)

/-- Formal-power-series residual `LHS - RHS` for Chan Theorem 11.5. -/
noncomputable def chanTheorem115ResidualPS : PowerSeries ℚ :=
  chanTheorem115LHS - chanTheorem115RHS

/-- Reverse formal-power-series residual `RHS - LHS` for Chan Theorem 11.5. -/
noncomputable def chanTheorem115ReverseResidualPS : PowerSeries ℚ :=
  chanTheorem115RHS - chanTheorem115LHS

/-! ## Computable coefficient model for higher-degree checks -/

/-- Kronecker delta at degree `0`, as an integer coefficient sequence. -/
private def deltaCoeffZ (n : ℕ) : ℤ :=
  if n = 0 then 1 else 0

/-- Coefficients of the inverse of a unit power series with constant coefficient `1`. -/
private def unitInvCoeffAuxZ (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => -∑ i : Fin (n + 1), a (i.1 + 1) * unitInvCoeffAuxZ a (n - i.1)
termination_by n => n

/-- Truncated Cauchy product coefficient for integer coefficient sequences. -/
private def convCoeffZ (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i : Fin (n + 1), a i.1 * b (n - i.1)

/-- Coefficients of a positive power, computed by repeated Cauchy products. -/
private def powCoeffZ (a : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0 => deltaCoeffZ
  | k + 1 => fun n => convCoeffZ (powCoeffZ a k) a n

/-- Low-degree integer coefficients of
`r(q) = (q,q⁴,q⁵;q⁵)_∞/(q²,q³,q⁵;q⁵)_∞`, through degree `30`.

These are the coefficients produced by the unit-inverse recurrence for the
pentagonal quotient. They are cached here so the higher-degree Chan 11.5
checks do not repeatedly unfold the bilateral pentagonal sums. -/
def rrcfRCoeffZ : ℕ → ℤ
  | 0 => 1
  | 1 => -1
  | 2 => 1
  | 3 => 0
  | 4 => -1
  | 5 => 1
  | 6 => -1
  | 7 => 1
  | 8 => 0
  | 9 => -1
  | 10 => 2
  | 11 => -3
  | 12 => 2
  | 13 => 0
  | 14 => -2
  | 15 => 4
  | 16 => -4
  | 17 => 3
  | 18 => -1
  | 19 => -3
  | 20 => 6
  | 21 => -7
  | 22 => 5
  | 23 => 0
  | 24 => -5
  | 25 => 9
  | 26 => -10
  | 27 => 7
  | 28 => -1
  | 29 => -7
  | 30 => 14
  | _ => 0

/-- Integer coefficients of `v = X * r(q⁵)`. -/
def rrcfVCoeffZ (n : ℕ) : ℤ :=
  if n = 0 then 0
  else if 5 ∣ n - 1 then rrcfRCoeffZ ((n - 1) / 5) else 0

/-- Coefficients of `PowerSeries.expand 5 rrcf_r` in the integer model. -/
def expandFiveRRCoeffZ (n : ℕ) : ℤ :=
  if 5 ∣ n then rrcfRCoeffZ (n / 5) else 0

/-- Coefficients of the left polynomial factor in Chan Theorem 11.5. -/
def chanTheorem115LHSFactorCoeffZ (n : ℕ) : ℤ :=
  deltaCoeffZ n
    + 3 * rrcfVCoeffZ n
    + 4 * powCoeffZ rrcfVCoeffZ 2 n
    + 2 * powCoeffZ rrcfVCoeffZ 3 n
    + powCoeffZ rrcfVCoeffZ 4 n

/-- Coefficients of the right polynomial factor in Chan Theorem 11.5. -/
def chanTheorem115RHSFactorCoeffZ (n : ℕ) : ℤ :=
  deltaCoeffZ n
    - 2 * rrcfVCoeffZ n
    + 4 * powCoeffZ rrcfVCoeffZ 2 n
    - 3 * powCoeffZ rrcfVCoeffZ 3 n
    + powCoeffZ rrcfVCoeffZ 4 n

/-- Computable integer coefficient of the left side of Chan Theorem 11.5. -/
def chanTheorem115LHSCoeffZ (n : ℕ) : ℤ :=
  convCoeffZ (powCoeffZ rrcfRCoeffZ 5) chanTheorem115LHSFactorCoeffZ n

/-- Computable integer coefficient of the right side of Chan Theorem 11.5. -/
def chanTheorem115RHSCoeffZ (n : ℕ) : ℤ :=
  convCoeffZ expandFiveRRCoeffZ chanTheorem115RHSFactorCoeffZ n

/-- Computable integer residual coefficient `LHS - RHS` for Chan Theorem 11.5. -/
def chanTheorem115ResidualCoeffZ (n : ℕ) : ℤ :=
  chanTheorem115LHSCoeffZ n - chanTheorem115RHSCoeffZ n

/-- Computable integer reverse residual coefficient `RHS - LHS` for Chan
Theorem 11.5. -/
def chanTheorem115ReverseResidualCoeffZ (n : ℕ) : ℤ :=
  chanTheorem115RHSCoeffZ n - chanTheorem115LHSCoeffZ n

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- Degree-11 coefficient check for Chan Theorem 11.5, by the computable model. -/
theorem chanTheorem115CoeffZ_eq_eleven :
    chanTheorem115LHSCoeffZ 11 = chanTheorem115RHSCoeffZ 11 := by
  native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- Degree-12 coefficient check for Chan Theorem 11.5, by the computable model. -/
theorem chanTheorem115CoeffZ_eq_twelve :
    chanTheorem115LHSCoeffZ 12 = chanTheorem115RHSCoeffZ 12 := by
  native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- Degree-13 coefficient check for Chan Theorem 11.5, by the computable model. -/
theorem chanTheorem115CoeffZ_eq_thirteen :
    chanTheorem115LHSCoeffZ 13 = chanTheorem115RHSCoeffZ 13 := by
  native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- Chan Theorem 11.5 in the computable coefficient model, checked through degree `30`. -/
theorem chanTheorem115CoeffZ_eq_of_le_thirty {n : ℕ} (hn : n ≤ 30) :
    chanTheorem115LHSCoeffZ n = chanTheorem115RHSCoeffZ n := by
  interval_cases n <;> native_decide

/-- Finite-index form of the computable coefficient check through degree `30`. -/
theorem chanTheorem115CoeffZ_eq_fin_thirtyone (n : Fin 31) :
    chanTheorem115LHSCoeffZ n.1 = chanTheorem115RHSCoeffZ n.1 :=
  chanTheorem115CoeffZ_eq_of_le_thirty (by omega)

/-- Strict-bound form of the computable coefficient check through degree `30`. -/
theorem chanTheorem115CoeffZ_eq_of_lt_thirtyone
    {n : ℕ} (hn : n < 31) :
    chanTheorem115LHSCoeffZ n = chanTheorem115RHSCoeffZ n :=
  chanTheorem115CoeffZ_eq_of_le_thirty (by omega)

/-- Complement-bound form of the computable coefficient check through degree
`30`. -/
theorem chanTheorem115CoeffZ_eq_of_not_thirtyone_le
    {n : ℕ} (hn : ¬ 31 ≤ n) :
    chanTheorem115LHSCoeffZ n = chanTheorem115RHSCoeffZ n :=
  chanTheorem115CoeffZ_eq_of_lt_thirtyone (by omega)

/-- Symmetric form of the computable coefficient check through degree `30`. -/
theorem chanTheorem115CoeffZ_eq_symm_of_le_thirty
    {n : ℕ} (hn : n ≤ 30) :
    chanTheorem115RHSCoeffZ n = chanTheorem115LHSCoeffZ n :=
  (chanTheorem115CoeffZ_eq_of_le_thirty hn).symm

/-- Symmetric strict-bound form of the computable coefficient check through
degree `30`. -/
theorem chanTheorem115CoeffZ_eq_symm_of_lt_thirtyone
    {n : ℕ} (hn : n < 31) :
    chanTheorem115RHSCoeffZ n = chanTheorem115LHSCoeffZ n :=
  (chanTheorem115CoeffZ_eq_of_lt_thirtyone hn).symm

/-- Symmetric complement-bound form of the computable coefficient check through
degree `30`. -/
theorem chanTheorem115CoeffZ_eq_symm_of_not_thirtyone_le
    {n : ℕ} (hn : ¬ 31 ≤ n) :
    chanTheorem115RHSCoeffZ n = chanTheorem115LHSCoeffZ n :=
  (chanTheorem115CoeffZ_eq_of_not_thirtyone_le hn).symm

/-- Symmetric finite-index form of the computable coefficient check through
degree `30`. -/
theorem chanTheorem115CoeffZ_eq_fin_thirtyone_symm (n : Fin 31) :
    chanTheorem115RHSCoeffZ n.1 = chanTheorem115LHSCoeffZ n.1 :=
  (chanTheorem115CoeffZ_eq_fin_thirtyone n).symm

/-- Endpoint degree-30 coefficient check for Chan Theorem 11.5. -/
theorem chanTheorem115CoeffZ_eq_thirty :
    chanTheorem115LHSCoeffZ 30 = chanTheorem115RHSCoeffZ 30 :=
  chanTheorem115CoeffZ_eq_of_le_thirty (by norm_num)

/-- Symmetric endpoint degree-30 coefficient check for Chan Theorem 11.5. -/
theorem chanTheorem115CoeffZ_eq_thirty_symm :
    chanTheorem115RHSCoeffZ 30 = chanTheorem115LHSCoeffZ 30 :=
  chanTheorem115CoeffZ_eq_thirty.symm

/-- Difference form of the computable coefficient check through degree `30`. -/
theorem chanTheorem115CoeffZ_sub_eq_zero_of_le_thirty
    {n : ℕ} (hn : n ≤ 30) :
    chanTheorem115LHSCoeffZ n - chanTheorem115RHSCoeffZ n = 0 := by
  rw [chanTheorem115CoeffZ_eq_of_le_thirty hn]
  ring

/-- Strict-bound difference form of the computable coefficient check through
degree `30`. -/
theorem chanTheorem115CoeffZ_sub_eq_zero_of_lt_thirtyone
    {n : ℕ} (hn : n < 31) :
    chanTheorem115LHSCoeffZ n - chanTheorem115RHSCoeffZ n = 0 :=
  chanTheorem115CoeffZ_sub_eq_zero_of_le_thirty (by omega)

/-- Finite-index difference form of the computable coefficient check through
degree `30`. -/
theorem chanTheorem115CoeffZ_sub_eq_zero_fin_thirtyone (n : Fin 31) :
    chanTheorem115LHSCoeffZ n.1 - chanTheorem115RHSCoeffZ n.1 = 0 :=
  chanTheorem115CoeffZ_sub_eq_zero_of_le_thirty (by omega)

/-- Complement-bound difference form of the computable coefficient check
through degree `30`. -/
theorem chanTheorem115CoeffZ_sub_eq_zero_of_not_thirtyone_le
    {n : ℕ} (hn : ¬ 31 ≤ n) :
    chanTheorem115LHSCoeffZ n - chanTheorem115RHSCoeffZ n = 0 :=
  chanTheorem115CoeffZ_sub_eq_zero_of_lt_thirtyone (by omega)

/-- Endpoint degree-30 difference check for Chan Theorem 11.5. -/
theorem chanTheorem115CoeffZ_sub_eq_zero_thirty :
    chanTheorem115LHSCoeffZ 30 - chanTheorem115RHSCoeffZ 30 = 0 :=
  chanTheorem115CoeffZ_sub_eq_zero_of_le_thirty (by norm_num)

/-- Reverse-difference form of the computable coefficient check through
degree `30`. -/
theorem chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_of_le_thirty
    {n : ℕ} (hn : n ≤ 30) :
    chanTheorem115RHSCoeffZ n - chanTheorem115LHSCoeffZ n = 0 := by
  rw [← chanTheorem115CoeffZ_eq_of_le_thirty hn]
  ring

/-- Strict-bound reverse-difference form of the computable coefficient check
through degree `30`. -/
theorem chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_of_lt_thirtyone
    {n : ℕ} (hn : n < 31) :
    chanTheorem115RHSCoeffZ n - chanTheorem115LHSCoeffZ n = 0 :=
  chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_of_le_thirty (by omega)

/-- Finite-index reverse-difference form of the computable coefficient check
through degree `30`. -/
theorem chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_fin_thirtyone (n : Fin 31) :
    chanTheorem115RHSCoeffZ n.1 - chanTheorem115LHSCoeffZ n.1 = 0 :=
  chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_of_le_thirty (by omega)

/-- Complement-bound reverse-difference form of the computable coefficient
check through degree `30`. -/
theorem chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_of_not_thirtyone_le
    {n : ℕ} (hn : ¬ 31 ≤ n) :
    chanTheorem115RHSCoeffZ n - chanTheorem115LHSCoeffZ n = 0 :=
  chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_of_lt_thirtyone (by omega)

/-- Endpoint degree-30 reverse-difference check for Chan Theorem 11.5. -/
theorem chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_thirty :
    chanTheorem115RHSCoeffZ 30 - chanTheorem115LHSCoeffZ 30 = 0 :=
  chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_of_le_thirty (by norm_num)

/-- Residual-coefficient form of the computable check through degree `30`. -/
theorem chanTheorem115ResidualCoeffZ_eq_zero_of_le_thirty
    {n : ℕ} (hn : n ≤ 30) :
    chanTheorem115ResidualCoeffZ n = 0 := by
  unfold chanTheorem115ResidualCoeffZ
  exact chanTheorem115CoeffZ_sub_eq_zero_of_le_thirty hn

/-- Strict-bound residual-coefficient form through degree `30`. -/
theorem chanTheorem115ResidualCoeffZ_eq_zero_of_lt_thirtyone
    {n : ℕ} (hn : n < 31) :
    chanTheorem115ResidualCoeffZ n = 0 :=
  chanTheorem115ResidualCoeffZ_eq_zero_of_le_thirty (by omega)

/-- Finite-index residual-coefficient form through degree `30`. -/
theorem chanTheorem115ResidualCoeffZ_eq_zero_fin_thirtyone (n : Fin 31) :
    chanTheorem115ResidualCoeffZ n.1 = 0 :=
  chanTheorem115ResidualCoeffZ_eq_zero_of_le_thirty (by omega)

/-- The computable residual coefficient vanishes exactly when the computable
left and right coefficients agree. -/
theorem chanTheorem115ResidualCoeffZ_eq_zero_iff_coeffZ_eq (n : ℕ) :
    chanTheorem115ResidualCoeffZ n = 0 ↔
      chanTheorem115LHSCoeffZ n = chanTheorem115RHSCoeffZ n := by
  unfold chanTheorem115ResidualCoeffZ
  exact sub_eq_zero

/-- The computable residual coefficient is nonzero exactly when the computable
left and right coefficients disagree. -/
theorem chanTheorem115ResidualCoeffZ_ne_zero_iff_coeffZ_ne (n : ℕ) :
    chanTheorem115ResidualCoeffZ n ≠ 0 ↔
      chanTheorem115LHSCoeffZ n ≠ chanTheorem115RHSCoeffZ n := by
  constructor
  · intro hres hEq
    exact hres ((chanTheorem115ResidualCoeffZ_eq_zero_iff_coeffZ_eq n).mpr hEq)
  · intro hne hzero
    exact hne ((chanTheorem115ResidualCoeffZ_eq_zero_iff_coeffZ_eq n).mp hzero)

/-- The computable left/right coefficient mismatch is equivalent to nonzero
computable residual coefficient. -/
theorem chanTheorem115CoeffZ_ne_iff_residualCoeffZ_ne_zero (n : ℕ) :
    chanTheorem115LHSCoeffZ n ≠ chanTheorem115RHSCoeffZ n ↔
      chanTheorem115ResidualCoeffZ n ≠ 0 :=
  (chanTheorem115ResidualCoeffZ_ne_zero_iff_coeffZ_ne n).symm

/-- Complement-bound residual-coefficient form through degree `30`. -/
theorem chanTheorem115ResidualCoeffZ_eq_zero_of_not_thirtyone_le
    {n : ℕ} (hn : ¬ 31 ≤ n) :
    chanTheorem115ResidualCoeffZ n = 0 :=
  chanTheorem115ResidualCoeffZ_eq_zero_of_lt_thirtyone (by omega)

/-- Endpoint degree-30 residual-coefficient check. -/
theorem chanTheorem115ResidualCoeffZ_eq_zero_thirty :
    chanTheorem115ResidualCoeffZ 30 = 0 :=
  chanTheorem115ResidualCoeffZ_eq_zero_of_le_thirty (by norm_num)

/-- The computable reverse residual is the negative of the computable residual. -/
theorem chanTheorem115ReverseResidualCoeffZ_eq_neg_residualCoeffZ (n : ℕ) :
    chanTheorem115ReverseResidualCoeffZ n = -chanTheorem115ResidualCoeffZ n := by
  unfold chanTheorem115ReverseResidualCoeffZ chanTheorem115ResidualCoeffZ
  ring

/-- The computable residual is the negative of the computable reverse residual. -/
theorem chanTheorem115ResidualCoeffZ_eq_neg_reverseResidualCoeffZ (n : ℕ) :
    chanTheorem115ResidualCoeffZ n = -chanTheorem115ReverseResidualCoeffZ n := by
  rw [chanTheorem115ReverseResidualCoeffZ_eq_neg_residualCoeffZ]
  simp

/-- Computable reverse-residual form of the check through degree `30`. -/
theorem chanTheorem115ReverseResidualCoeffZ_eq_zero_of_le_thirty
    {n : ℕ} (hn : n ≤ 30) :
    chanTheorem115ReverseResidualCoeffZ n = 0 := by
  unfold chanTheorem115ReverseResidualCoeffZ
  exact chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_of_le_thirty hn

/-- Strict-bound computable reverse-residual form through degree `30`. -/
theorem chanTheorem115ReverseResidualCoeffZ_eq_zero_of_lt_thirtyone
    {n : ℕ} (hn : n < 31) :
    chanTheorem115ReverseResidualCoeffZ n = 0 :=
  chanTheorem115ReverseResidualCoeffZ_eq_zero_of_le_thirty (by omega)

/-- Finite-index computable reverse-residual form through degree `30`. -/
theorem chanTheorem115ReverseResidualCoeffZ_eq_zero_fin_thirtyone (n : Fin 31) :
    chanTheorem115ReverseResidualCoeffZ n.1 = 0 :=
  chanTheorem115ReverseResidualCoeffZ_eq_zero_of_le_thirty (by omega)

/-- The computable reverse residual coefficient vanishes exactly when the
computable right and left coefficients agree. -/
theorem chanTheorem115ReverseResidualCoeffZ_eq_zero_iff_coeffZ_eq (n : ℕ) :
    chanTheorem115ReverseResidualCoeffZ n = 0 ↔
      chanTheorem115RHSCoeffZ n = chanTheorem115LHSCoeffZ n := by
  unfold chanTheorem115ReverseResidualCoeffZ
  exact sub_eq_zero

/-- The computable reverse residual coefficient is nonzero exactly when the
computable right and left coefficients disagree. -/
theorem chanTheorem115ReverseResidualCoeffZ_ne_zero_iff_coeffZ_ne (n : ℕ) :
    chanTheorem115ReverseResidualCoeffZ n ≠ 0 ↔
      chanTheorem115RHSCoeffZ n ≠ chanTheorem115LHSCoeffZ n := by
  constructor
  · intro hres hEq
    exact hres ((chanTheorem115ReverseResidualCoeffZ_eq_zero_iff_coeffZ_eq n).mpr hEq)
  · intro hne hzero
    exact hne ((chanTheorem115ReverseResidualCoeffZ_eq_zero_iff_coeffZ_eq n).mp hzero)

/-- The computable right/left coefficient mismatch is equivalent to nonzero
computable reverse residual coefficient. -/
theorem chanTheorem115CoeffZ_ne_symm_iff_reverseResidualCoeffZ_ne_zero (n : ℕ) :
    chanTheorem115RHSCoeffZ n ≠ chanTheorem115LHSCoeffZ n ↔
      chanTheorem115ReverseResidualCoeffZ n ≠ 0 :=
  (chanTheorem115ReverseResidualCoeffZ_ne_zero_iff_coeffZ_ne n).symm

/-- Complement-bound computable reverse-residual form through degree `30`. -/
theorem chanTheorem115ReverseResidualCoeffZ_eq_zero_of_not_thirtyone_le
    {n : ℕ} (hn : ¬ 31 ≤ n) :
    chanTheorem115ReverseResidualCoeffZ n = 0 :=
  chanTheorem115ReverseResidualCoeffZ_eq_zero_of_lt_thirtyone (by omega)

/-- Endpoint degree-30 reverse-residual coefficient check. -/
theorem chanTheorem115ReverseResidualCoeffZ_eq_zero_thirty :
    chanTheorem115ReverseResidualCoeffZ 30 = 0 :=
  chanTheorem115ReverseResidualCoeffZ_eq_zero_of_le_thirty (by norm_num)

/-- Coefficientwise vanishing of the computable residual is equivalent to
coefficientwise vanishing of the computable reverse residual. -/
theorem chanTheorem115ResidualCoeffZ_eq_zero_iff_reverseResidualCoeffZ_eq_zero
    (n : ℕ) :
    chanTheorem115ResidualCoeffZ n = 0 ↔
      chanTheorem115ReverseResidualCoeffZ n = 0 := by
  rw [chanTheorem115ReverseResidualCoeffZ_eq_neg_residualCoeffZ]
  simp

/-- Coefficientwise vanishing of the computable reverse residual is equivalent
to coefficientwise vanishing of the computable residual. -/
theorem chanTheorem115ReverseResidualCoeffZ_eq_zero_iff_residualCoeffZ_eq_zero
    (n : ℕ) :
    chanTheorem115ReverseResidualCoeffZ n = 0 ↔
      chanTheorem115ResidualCoeffZ n = 0 :=
  (chanTheorem115ResidualCoeffZ_eq_zero_iff_reverseResidualCoeffZ_eq_zero n).symm

/-- Coefficientwise nonvanishing of the computable residual is equivalent to
coefficientwise nonvanishing of the computable reverse residual. -/
theorem chanTheorem115ResidualCoeffZ_ne_zero_iff_reverseResidualCoeffZ_ne_zero
    (n : ℕ) :
    chanTheorem115ResidualCoeffZ n ≠ 0 ↔
      chanTheorem115ReverseResidualCoeffZ n ≠ 0 := by
  constructor
  · intro hres hrev
    exact hres ((chanTheorem115ResidualCoeffZ_eq_zero_iff_reverseResidualCoeffZ_eq_zero n).mpr hrev)
  · intro hrev hres
    exact hrev ((chanTheorem115ResidualCoeffZ_eq_zero_iff_reverseResidualCoeffZ_eq_zero n).mp hres)

/-- Coefficientwise nonvanishing of the computable reverse residual is
equivalent to coefficientwise nonvanishing of the computable residual. -/
theorem chanTheorem115ReverseResidualCoeffZ_ne_zero_iff_residualCoeffZ_ne_zero
    (n : ℕ) :
    chanTheorem115ReverseResidualCoeffZ n ≠ 0 ↔
      chanTheorem115ResidualCoeffZ n ≠ 0 :=
  (chanTheorem115ResidualCoeffZ_ne_zero_iff_reverseResidualCoeffZ_ne_zero n).symm

/-- The computable left/right coefficient equality is equivalent to vanishing
of the computable residual coefficient. -/
theorem chanTheorem115CoeffZ_eq_iff_residualCoeffZ_eq_zero (n : ℕ) :
    chanTheorem115LHSCoeffZ n = chanTheorem115RHSCoeffZ n ↔
      chanTheorem115ResidualCoeffZ n = 0 :=
  (chanTheorem115ResidualCoeffZ_eq_zero_iff_coeffZ_eq n).symm

/-- The computable right/left coefficient equality is equivalent to vanishing
of the computable reverse residual coefficient. -/
theorem chanTheorem115CoeffZ_eq_symm_iff_reverseResidualCoeffZ_eq_zero (n : ℕ) :
    chanTheorem115RHSCoeffZ n = chanTheorem115LHSCoeffZ n ↔
      chanTheorem115ReverseResidualCoeffZ n = 0 :=
  (chanTheorem115ReverseResidualCoeffZ_eq_zero_iff_coeffZ_eq n).symm

/-- A computable left/right coefficient mismatch is equivalent to nonvanishing
of the computable reverse residual coefficient. -/
theorem chanTheorem115CoeffZ_ne_iff_reverseResidualCoeffZ_ne_zero (n : ℕ) :
    chanTheorem115LHSCoeffZ n ≠ chanTheorem115RHSCoeffZ n ↔
      chanTheorem115ReverseResidualCoeffZ n ≠ 0 :=
  (chanTheorem115CoeffZ_ne_iff_residualCoeffZ_ne_zero n).trans
    (chanTheorem115ResidualCoeffZ_ne_zero_iff_reverseResidualCoeffZ_ne_zero n)

/-- A computable right/left coefficient mismatch is equivalent to nonvanishing
of the computable residual coefficient. -/
theorem chanTheorem115CoeffZ_ne_symm_iff_residualCoeffZ_ne_zero (n : ℕ) :
    chanTheorem115RHSCoeffZ n ≠ chanTheorem115LHSCoeffZ n ↔
      chanTheorem115ResidualCoeffZ n ≠ 0 :=
  (chanTheorem115CoeffZ_ne_symm_iff_reverseResidualCoeffZ_ne_zero n).trans
    (chanTheorem115ReverseResidualCoeffZ_ne_zero_iff_residualCoeffZ_ne_zero n)

/-- If the computable residual has a nonzero coefficient, it must occur at
degree at least `31`. -/
theorem thirtyone_le_of_chanTheorem115ResidualCoeffZ_ne_zero
    {n : ℕ} (hn : chanTheorem115ResidualCoeffZ n ≠ 0) :
    31 ≤ n := by
  by_contra hlt
  push_neg at hlt
  exact hn (chanTheorem115ResidualCoeffZ_eq_zero_of_lt_thirtyone hlt)

/-- If the computable reverse residual has a nonzero coefficient, it must occur
at degree at least `31`. -/
theorem thirtyone_le_of_chanTheorem115ReverseResidualCoeffZ_ne_zero
    {n : ℕ} (hn : chanTheorem115ReverseResidualCoeffZ n ≠ 0) :
    31 ≤ n := by
  by_contra hlt
  push_neg at hlt
  exact hn (chanTheorem115ReverseResidualCoeffZ_eq_zero_of_lt_thirtyone hlt)

/-- If the computable LHS and RHS coefficients first disagree, the degree is at
least `31`. -/
theorem thirtyone_le_of_chanTheorem115CoeffZ_ne
    {n : ℕ} (hn : chanTheorem115LHSCoeffZ n ≠ chanTheorem115RHSCoeffZ n) :
    31 ≤ n := by
  apply thirtyone_le_of_chanTheorem115ResidualCoeffZ_ne_zero
  unfold chanTheorem115ResidualCoeffZ
  exact sub_ne_zero.mpr hn

/-- Symmetric lower bound for a computable coefficient mismatch. -/
theorem thirtyone_le_of_chanTheorem115CoeffZ_ne_symm
    {n : ℕ} (hn : chanTheorem115RHSCoeffZ n ≠ chanTheorem115LHSCoeffZ n) :
    31 ≤ n := by
  apply thirtyone_le_of_chanTheorem115ReverseResidualCoeffZ_ne_zero
  unfold chanTheorem115ReverseResidualCoeffZ
  exact sub_ne_zero.mpr hn

/-- If the raw computable forward difference is nonzero, the degree is at
least `31`. -/
theorem thirtyone_le_of_chanTheorem115CoeffZ_sub_ne_zero
    {n : ℕ} (hn : chanTheorem115LHSCoeffZ n - chanTheorem115RHSCoeffZ n ≠ 0) :
    31 ≤ n := by
  by_contra hlt
  push_neg at hlt
  exact hn (chanTheorem115CoeffZ_sub_eq_zero_of_lt_thirtyone hlt)

/-- If the raw computable reverse difference is nonzero, the degree is at
least `31`. -/
theorem thirtyone_le_of_chanTheorem115CoeffZ_rhs_sub_lhs_ne_zero
    {n : ℕ} (hn : chanTheorem115RHSCoeffZ n - chanTheorem115LHSCoeffZ n ≠ 0) :
    31 ≤ n := by
  by_contra hlt
  push_neg at hlt
  exact hn (chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_of_lt_thirtyone hlt)

/-- There is no computable coefficient mismatch below degree `31`. -/
theorem not_exists_lt_thirtyone_chanTheorem115CoeffZ_ne :
    ¬ ∃ n : ℕ, n < 31 ∧
      chanTheorem115LHSCoeffZ n ≠ chanTheorem115RHSCoeffZ n := by
  rintro ⟨n, hn, hne⟩
  exact hne (chanTheorem115CoeffZ_eq_of_lt_thirtyone hn)

/-- There is no computable coefficient mismatch through degree `30`. -/
theorem not_exists_le_thirty_chanTheorem115CoeffZ_ne :
    ¬ ∃ n : ℕ, n ≤ 30 ∧
      chanTheorem115LHSCoeffZ n ≠ chanTheorem115RHSCoeffZ n := by
  rintro ⟨n, hn, hne⟩
  exact hne (chanTheorem115CoeffZ_eq_of_le_thirty hn)

/-- There is no reverse computable coefficient mismatch below degree `31`. -/
theorem not_exists_lt_thirtyone_chanTheorem115CoeffZ_ne_symm :
    ¬ ∃ n : ℕ, n < 31 ∧
      chanTheorem115RHSCoeffZ n ≠ chanTheorem115LHSCoeffZ n := by
  rintro ⟨n, hn, hne⟩
  exact hne ((chanTheorem115CoeffZ_eq_of_lt_thirtyone hn).symm)

/-- There is no reverse computable coefficient mismatch through degree `30`. -/
theorem not_exists_le_thirty_chanTheorem115CoeffZ_ne_symm :
    ¬ ∃ n : ℕ, n ≤ 30 ∧
      chanTheorem115RHSCoeffZ n ≠ chanTheorem115LHSCoeffZ n := by
  rintro ⟨n, hn, hne⟩
  exact hne ((chanTheorem115CoeffZ_eq_of_le_thirty hn).symm)

/-- There is no nonzero raw computable forward difference below degree `31`. -/
theorem not_exists_lt_thirtyone_chanTheorem115CoeffZ_sub_ne_zero :
    ¬ ∃ n : ℕ, n < 31 ∧
      chanTheorem115LHSCoeffZ n - chanTheorem115RHSCoeffZ n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (chanTheorem115CoeffZ_sub_eq_zero_of_lt_thirtyone hn)

/-- There is no nonzero raw computable forward difference through degree `30`. -/
theorem not_exists_le_thirty_chanTheorem115CoeffZ_sub_ne_zero :
    ¬ ∃ n : ℕ, n ≤ 30 ∧
      chanTheorem115LHSCoeffZ n - chanTheorem115RHSCoeffZ n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (chanTheorem115CoeffZ_sub_eq_zero_of_le_thirty hn)

/-- There is no nonzero raw computable reverse difference below degree `31`. -/
theorem not_exists_lt_thirtyone_chanTheorem115CoeffZ_rhs_sub_lhs_ne_zero :
    ¬ ∃ n : ℕ, n < 31 ∧
      chanTheorem115RHSCoeffZ n - chanTheorem115LHSCoeffZ n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_of_lt_thirtyone hn)

/-- There is no nonzero raw computable reverse difference through degree `30`. -/
theorem not_exists_le_thirty_chanTheorem115CoeffZ_rhs_sub_lhs_ne_zero :
    ¬ ∃ n : ℕ, n ≤ 30 ∧
      chanTheorem115RHSCoeffZ n - chanTheorem115LHSCoeffZ n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (chanTheorem115CoeffZ_rhs_sub_lhs_eq_zero_of_le_thirty hn)

/-- There is no nonzero computable residual coefficient below degree `31`. -/
theorem not_exists_lt_thirtyone_chanTheorem115ResidualCoeffZ_ne_zero :
    ¬ ∃ n : ℕ, n < 31 ∧ chanTheorem115ResidualCoeffZ n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (chanTheorem115ResidualCoeffZ_eq_zero_of_lt_thirtyone hn)

/-- There is no nonzero computable residual coefficient through degree `30`. -/
theorem not_exists_le_thirty_chanTheorem115ResidualCoeffZ_ne_zero :
    ¬ ∃ n : ℕ, n ≤ 30 ∧ chanTheorem115ResidualCoeffZ n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (chanTheorem115ResidualCoeffZ_eq_zero_of_le_thirty hn)

/-- There is no nonzero computable reverse-residual coefficient below degree
`31`. -/
theorem not_exists_lt_thirtyone_chanTheorem115ReverseResidualCoeffZ_ne_zero :
    ¬ ∃ n : ℕ, n < 31 ∧ chanTheorem115ReverseResidualCoeffZ n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (chanTheorem115ReverseResidualCoeffZ_eq_zero_of_lt_thirtyone hn)

/-- There is no nonzero computable reverse-residual coefficient through degree
`30`. -/
theorem not_exists_le_thirty_chanTheorem115ReverseResidualCoeffZ_ne_zero :
    ¬ ∃ n : ℕ, n ≤ 30 ∧ chanTheorem115ReverseResidualCoeffZ n ≠ 0 := by
  rintro ⟨n, hn, hne⟩
  exact hne (chanTheorem115ReverseResidualCoeffZ_eq_zero_of_le_thirty hn)

/-- Boolean audit for the integer coefficient model through degree `30`. -/
def chanTheorem115CoeffZMatchThroughThirtyCheck : Bool :=
  (List.range 31).all
    (fun n => chanTheorem115LHSCoeffZ n == chanTheorem115RHSCoeffZ n)

/-- Boolean audit for zero residual coefficients through degree `30`. -/
def chanTheorem115ResidualCoeffZZeroThroughThirtyCheck : Bool :=
  (List.range 31).all (fun n => chanTheorem115ResidualCoeffZ n == 0)

/-- Boolean audit for zero reverse-residual coefficients through degree `30`. -/
def chanTheorem115ReverseResidualCoeffZZeroThroughThirtyCheck : Bool :=
  (List.range 31).all (fun n => chanTheorem115ReverseResidualCoeffZ n == 0)

/-- Combined Boolean audit for all computable integer coefficient checks through
degree `30`. -/
def chanTheorem115CoeffZAuditThroughThirtyCheck : Bool :=
  chanTheorem115CoeffZMatchThroughThirtyCheck &&
    chanTheorem115ResidualCoeffZZeroThroughThirtyCheck &&
    chanTheorem115ReverseResidualCoeffZZeroThroughThirtyCheck

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- The Boolean audit for the integer coefficient model through degree `30`
evaluates to `true`. -/
theorem chanTheorem115CoeffZMatchThroughThirtyCheck_true :
    chanTheorem115CoeffZMatchThroughThirtyCheck = true := by
  native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- The Boolean audit for zero residual coefficients through degree `30`
evaluates to `true`. -/
theorem chanTheorem115ResidualCoeffZZeroThroughThirtyCheck_true :
    chanTheorem115ResidualCoeffZZeroThroughThirtyCheck = true := by
  native_decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- The Boolean audit for zero reverse-residual coefficients through degree
`30` evaluates to `true`. -/
theorem chanTheorem115ReverseResidualCoeffZZeroThroughThirtyCheck_true :
    chanTheorem115ReverseResidualCoeffZZeroThroughThirtyCheck = true := by
  native_decide

/-- The combined Boolean audit for the computable coefficient model through
degree `30` evaluates to `true`. -/
theorem chanTheorem115CoeffZAuditThroughThirtyCheck_true :
    chanTheorem115CoeffZAuditThroughThirtyCheck = true := by
  rw [chanTheorem115CoeffZAuditThroughThirtyCheck,
    chanTheorem115CoeffZMatchThroughThirtyCheck_true,
    chanTheorem115ResidualCoeffZZeroThroughThirtyCheck_true,
    chanTheorem115ReverseResidualCoeffZZeroThroughThirtyCheck_true]
  rfl

/-! ## Pentagonal series coefficient values

We use the product-to-series bridge and finite product stabilization. -/

theorem coeff_pentagonal014_0 :
    (pentagonal014SeriesPS ℚ).coeff 0 = 1 :=
  coeff_zero_pentagonal014SeriesPS_rat

theorem coeff_pentagonal014_1 :
    (pentagonal014SeriesPS ℚ).coeff 1 = -1 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal014_2 :
    (pentagonal014SeriesPS ℚ).coeff 2 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal014_3 :
    (pentagonal014SeriesPS ℚ).coeff 3 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal014_4 :
    (pentagonal014SeriesPS ℚ).coeff 4 = -1 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal014_5 :
    (pentagonal014SeriesPS ℚ).coeff 5 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal014_6 :
    (pentagonal014SeriesPS ℚ).coeff 6 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal014_7 :
    (pentagonal014SeriesPS ℚ).coeff 7 = 1 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal014_8 :
    (pentagonal014SeriesPS ℚ).coeff 8 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal014_9 :
    (pentagonal014SeriesPS ℚ).coeff 9 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal014_10 :
    (pentagonal014SeriesPS ℚ).coeff 10 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal023_0 :
    (pentagonal023SeriesPS ℚ).coeff 0 = 1 :=
  coeff_zero_pentagonal023SeriesPS_rat

theorem coeff_pentagonal023_1 :
    (pentagonal023SeriesPS ℚ).coeff 1 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal023_2 :
    (pentagonal023SeriesPS ℚ).coeff 2 = -1 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal023_3 :
    (pentagonal023SeriesPS ℚ).coeff 3 = -1 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal023_4 :
    (pentagonal023SeriesPS ℚ).coeff 4 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal023_5 :
    (pentagonal023SeriesPS ℚ).coeff 5 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal023_6 :
    (pentagonal023SeriesPS ℚ).coeff 6 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal023_7 :
    (pentagonal023SeriesPS ℚ).coeff 7 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal023_8 :
    (pentagonal023SeriesPS ℚ).coeff 8 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal023_9 :
    (pentagonal023SeriesPS ℚ).coeff 9 = 1 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_pentagonal023_10 :
    (pentagonal023SeriesPS ℚ).coeff 10 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

/-! ## Coefficients of `(pentagonal023SeriesPS ℚ)⁻¹` -/

private theorem inv_const : PowerSeries.constantCoeff (pentagonal023SeriesPS ℚ) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_pentagonal023_0]

theorem coeff_inv_pentagonal023_0 :
    (pentagonal023SeriesPS ℚ)⁻¹.coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_pentagonal023_0, inv_one]

theorem coeff_inv_pentagonal023_1 :
    (pentagonal023SeriesPS ℚ)⁻¹.coeff 1 = 0 := by
  rw [PowerSeries.coeff_inv 1]
  simp only [if_neg one_ne_zero, inv_const, inv_one]
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (lt_irrefl 1), if_pos Nat.zero_lt_one]
  rw [coeff_inv_pentagonal023_0, coeff_pentagonal023_1]
  ring

theorem coeff_inv_pentagonal023_2 :
    (pentagonal023SeriesPS ℚ)⁻¹.coeff 2 = 1 := by
  rw [PowerSeries.coeff_inv 2]
  simp only [if_neg (by decide : (2 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) = {(0, 2), (1, 1), (2, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (by omega : ¬(2 < 2)), if_pos (by omega : 1 < 2), if_pos (by omega : 0 < 2)]
  rw [coeff_inv_pentagonal023_0, coeff_inv_pentagonal023_1,
      coeff_pentagonal023_1, coeff_pentagonal023_2]
  ring

theorem coeff_inv_pentagonal023_3 :
    (pentagonal023SeriesPS ℚ)⁻¹.coeff 3 = 1 := by
  rw [PowerSeries.coeff_inv 3]
  simp only [if_neg (by decide : (3 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 3 : Finset (ℕ × ℕ)) =
    {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  rw [coeff_inv_pentagonal023_0, coeff_inv_pentagonal023_1, coeff_inv_pentagonal023_2,
      coeff_pentagonal023_1, coeff_pentagonal023_2, coeff_pentagonal023_3]
  ring

theorem coeff_inv_pentagonal023_4 :
    (pentagonal023SeriesPS ℚ)⁻¹.coeff 4 = 1 := by
  rw [PowerSeries.coeff_inv 4]
  simp only [if_neg (by decide : (4 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
    {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega)]
  rw [coeff_inv_pentagonal023_0, coeff_inv_pentagonal023_1,
      coeff_inv_pentagonal023_2, coeff_inv_pentagonal023_3,
      coeff_pentagonal023_1, coeff_pentagonal023_2, coeff_pentagonal023_3,
      coeff_pentagonal023_4]
  ring

theorem coeff_inv_pentagonal023_5 :
    (pentagonal023SeriesPS ℚ)⁻¹.coeff 5 = 2 := by
  rw [PowerSeries.coeff_inv 5]
  simp only [if_neg (by decide : (5 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 5 : Finset (ℕ × ℕ)) =
    {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  rw [coeff_inv_pentagonal023_0, coeff_inv_pentagonal023_1,
      coeff_inv_pentagonal023_2, coeff_inv_pentagonal023_3,
      coeff_inv_pentagonal023_4, coeff_pentagonal023_1,
      coeff_pentagonal023_2, coeff_pentagonal023_3, coeff_pentagonal023_4,
      coeff_pentagonal023_5]
  ring

/-! ## Coefficients of `rrcf_r`

`rrcf_r = pentagonal014SeriesPS ℚ * (pentagonal023SeriesPS ℚ)⁻¹`
Series: `1 - X + X² + 0·X³ - X⁴ + X⁵ - X⁶ + X⁷ + ...` -/

theorem rrcf_r_coeff_0 : rrcf_r.coeff 0 = 1 := coeff_zero_rrcf_r

theorem rrcf_r_coeff_1 : rrcf_r.coeff 1 = -1 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl,
      Finset.sum_pair (show (0, 1) ≠ (1, 0) from by decide)]
  rw [coeff_pentagonal014_0, coeff_inv_pentagonal023_1,
      coeff_pentagonal014_1, coeff_inv_pentagonal023_0]
  ring

/-- `rrcf_r.coeff 2 = 1`.

Proof: Cauchy product at degree 2:
`∑ f.coeff(i) · g⁻¹.coeff(2-i) for i=0..2`
= `1·1 + (-1)·0 + 0·1 = 1` -/
theorem rrcf_r_coeff_2 : rrcf_r.coeff 2 = 1 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) = {(0, 2), (1, 1), (2, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_pentagonal014_0, coeff_inv_pentagonal023_2,
      coeff_pentagonal014_1, coeff_inv_pentagonal023_1,
      coeff_pentagonal014_2, coeff_inv_pentagonal023_0]
  ring

/-- `rrcf_r.coeff 3 = 0`.

Proof: Cauchy product at degree 3:
`∑ f.coeff(i) · g⁻¹.coeff(3-i) for i=0..3`
= `1·1 + (-1)·1 + 0·0 + 0·1 = 0` -/
theorem rrcf_r_coeff_3 : rrcf_r.coeff 3 = 0 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 3 : Finset (ℕ × ℕ)) =
        {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_pentagonal014_0, coeff_inv_pentagonal023_3,
      coeff_pentagonal014_1, coeff_inv_pentagonal023_2,
      coeff_pentagonal014_2, coeff_inv_pentagonal023_1,
      coeff_pentagonal014_3, coeff_inv_pentagonal023_0]
  ring

theorem rrcf_r_coeff_4 : rrcf_r.coeff 4 = -1 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
        {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [coeff_pentagonal014_0, coeff_inv_pentagonal023_4,
      coeff_pentagonal014_1, coeff_inv_pentagonal023_3,
      coeff_pentagonal014_2, coeff_inv_pentagonal023_2,
      coeff_pentagonal014_3, coeff_inv_pentagonal023_1,
      coeff_pentagonal014_4, coeff_inv_pentagonal023_0]
  ring

theorem rrcf_r_coeff_5 : rrcf_r.coeff 5 = 1 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 5 : Finset (ℕ × ℕ)) =
        {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_pentagonal014_0, coeff_inv_pentagonal023_5,
      coeff_pentagonal014_1, coeff_inv_pentagonal023_4,
      coeff_pentagonal014_2, coeff_inv_pentagonal023_3,
      coeff_pentagonal014_3, coeff_inv_pentagonal023_2,
      coeff_pentagonal014_4, coeff_inv_pentagonal023_1,
      coeff_pentagonal014_5, coeff_inv_pentagonal023_0]
  ring

theorem rrcf_r_coeff_6 : rrcf_r.coeff 6 = -1 := by
  have hcoeff := congr_arg (fun f : PowerSeries ℚ => f.coeff 6) rrcf_r_mul_pentagonal023SeriesPS_eq
  change (rrcf_r * pentagonal023SeriesPS ℚ).coeff 6 =
    (pentagonal014SeriesPS ℚ).coeff 6 at hcoeff
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 6 : Finset (ℕ × ℕ)) =
      {(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (6, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at hcoeff
  rw [coeff_pentagonal014_6, coeff_pentagonal023_0, coeff_pentagonal023_1,
      coeff_pentagonal023_2, coeff_pentagonal023_3, coeff_pentagonal023_4,
      coeff_pentagonal023_5, coeff_pentagonal023_6, rrcf_r_coeff_0,
      rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5] at hcoeff
  linarith

theorem rrcf_r_coeff_7 : rrcf_r.coeff 7 = 1 := by
  have hcoeff := congr_arg (fun f : PowerSeries ℚ => f.coeff 7) rrcf_r_mul_pentagonal023SeriesPS_eq
  change (rrcf_r * pentagonal023SeriesPS ℚ).coeff 7 =
    (pentagonal014SeriesPS ℚ).coeff 7 at hcoeff
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 7 : Finset (ℕ × ℕ)) =
      {(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1), (7, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton] at hcoeff
  rw [coeff_pentagonal014_7, coeff_pentagonal023_0, coeff_pentagonal023_1,
      coeff_pentagonal023_2, coeff_pentagonal023_3, coeff_pentagonal023_4,
      coeff_pentagonal023_5, coeff_pentagonal023_6, coeff_pentagonal023_7,
      rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3,
      rrcf_r_coeff_4, rrcf_r_coeff_5, rrcf_r_coeff_6] at hcoeff
  linarith

theorem rrcf_r_coeff_8 : rrcf_r.coeff 8 = 0 := by
  have hcoeff := congr_arg (fun f : PowerSeries ℚ => f.coeff 8) rrcf_r_mul_pentagonal023SeriesPS_eq
  change (rrcf_r * pentagonal023SeriesPS ℚ).coeff 8 =
    (pentagonal014SeriesPS ℚ).coeff 8 at hcoeff
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 8 : Finset (ℕ × ℕ)) =
      {(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2), (7, 1), (8, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at hcoeff
  rw [coeff_pentagonal014_8, coeff_pentagonal023_0, coeff_pentagonal023_1,
      coeff_pentagonal023_2, coeff_pentagonal023_3, coeff_pentagonal023_4,
      coeff_pentagonal023_5, coeff_pentagonal023_6, coeff_pentagonal023_7,
      coeff_pentagonal023_8, rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2,
      rrcf_r_coeff_3, rrcf_r_coeff_4, rrcf_r_coeff_5, rrcf_r_coeff_6,
      rrcf_r_coeff_7] at hcoeff
  linarith

theorem rrcf_r_coeff_9 : rrcf_r.coeff 9 = -1 := by
  have hcoeff := congr_arg (fun f : PowerSeries ℚ => f.coeff 9) rrcf_r_mul_pentagonal023SeriesPS_eq
  change (rrcf_r * pentagonal023SeriesPS ℚ).coeff 9 =
    (pentagonal014SeriesPS ℚ).coeff 9 at hcoeff
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [show (Finset.antidiagonal 9 : Finset (ℕ × ℕ)) =
      {(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3), (7, 2), (8, 1), (9, 0)} from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton] at hcoeff
  rw [coeff_pentagonal014_9, coeff_pentagonal023_0, coeff_pentagonal023_1,
      coeff_pentagonal023_2, coeff_pentagonal023_3, coeff_pentagonal023_4,
      coeff_pentagonal023_5, coeff_pentagonal023_6, coeff_pentagonal023_7,
      coeff_pentagonal023_8, coeff_pentagonal023_9, rrcf_r_coeff_0,
      rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7,
      rrcf_r_coeff_8] at hcoeff
  linarith

theorem rrcf_r_coeff_10 : rrcf_r.coeff 10 = 2 := by
  have hcoeff := congr_arg (fun f : PowerSeries ℚ => f.coeff 10) rrcf_r_mul_pentagonal023SeriesPS_eq
  change (rrcf_r * pentagonal023SeriesPS ℚ).coeff 10 =
    (pentagonal014SeriesPS ℚ).coeff 10 at hcoeff
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
  rw [coeff_pentagonal014_10, coeff_pentagonal023_0, coeff_pentagonal023_1,
      coeff_pentagonal023_2, coeff_pentagonal023_3, coeff_pentagonal023_4,
      coeff_pentagonal023_5, coeff_pentagonal023_6, coeff_pentagonal023_7,
      coeff_pentagonal023_8, coeff_pentagonal023_9, coeff_pentagonal023_10,
      rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3,
      rrcf_r_coeff_4, rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7,
      rrcf_r_coeff_8, rrcf_r_coeff_9] at hcoeff
  linarith

/-! ## Coefficients of `rrcf_v`

`rrcf_v = X * (expand 5 rrcf_r)`:
- coeff 0 = 0 (factor of X)
- coeff (5k+1) = rrcf_r.coeff k (via expand 5 and X shift)
- coeff n = 0 when (n-1) is not divisible by 5 -/

theorem rrcf_v_coeff_0 : rrcf_v.coeff 0 = 0 := coeff_zero_rrcf_v_eq_zero

theorem rrcf_v_coeff_1 : rrcf_v.coeff 1 = 1 := by
  show rrcf_v.coeff (0 + 1) = 1
  unfold rrcf_v
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand]
  simp [rrcf_r_coeff_0]

theorem rrcf_v_coeff_2 : rrcf_v.coeff 2 = 0 := by
  show rrcf_v.coeff (1 + 1) = 0
  unfold rrcf_v
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand]
  simp

theorem rrcf_v_coeff_3 : rrcf_v.coeff 3 = 0 := by
  show rrcf_v.coeff (2 + 1) = 0
  unfold rrcf_v
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand]
  simp

theorem rrcf_v_coeff_4 : rrcf_v.coeff 4 = 0 := by
  show rrcf_v.coeff (3 + 1) = 0
  unfold rrcf_v
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand]
  simp

theorem rrcf_v_coeff_5 : rrcf_v.coeff 5 = 0 := by
  show rrcf_v.coeff (4 + 1) = 0
  unfold rrcf_v
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand]
  simp

theorem rrcf_v_coeff_6 : rrcf_v.coeff 6 = -1 := by
  show rrcf_v.coeff (5 + 1) = -1
  unfold rrcf_v
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand]
  simp [rrcf_r_coeff_1]

theorem rrcf_v_coeff_7 : rrcf_v.coeff 7 = 0 := by
  show rrcf_v.coeff (6 + 1) = 0
  unfold rrcf_v
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand]
  simp

theorem rrcf_v_coeff_8 : rrcf_v.coeff 8 = 0 := by
  show rrcf_v.coeff (7 + 1) = 0
  unfold rrcf_v
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand]
  simp

theorem rrcf_v_coeff_9 : rrcf_v.coeff 9 = 0 := by
  show rrcf_v.coeff (8 + 1) = 0
  unfold rrcf_v
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand]
  simp

theorem rrcf_v_coeff_10 : rrcf_v.coeff 10 = 0 := by
  show rrcf_v.coeff (9 + 1) = 0
  unfold rrcf_v
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand]
  simp

/-! ## Fixed Cauchy-product coefficient helpers -/

private theorem coeff_mul_zero (f g : PowerSeries ℚ) :
    (f * g).coeff 0 = f.coeff 0 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.antidiagonal_zero, Finset.sum_singleton]

private theorem coeff_mul_one (f g : PowerSeries ℚ) :
    (f * g).coeff 1 = f.coeff 0 * g.coeff 1
      + f.coeff 1 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

private theorem coeff_mul_two (f g : PowerSeries ℚ) :
    (f * g).coeff 2 = f.coeff 0 * g.coeff 2
      + f.coeff 1 * g.coeff 1
      + f.coeff 2 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) = {(0, 2), (1, 1), (2, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private theorem coeff_mul_three (f g : PowerSeries ℚ) :
    (f * g).coeff 3 = f.coeff 0 * g.coeff 3
      + f.coeff 1 * g.coeff 2
      + f.coeff 2 * g.coeff 1
      + f.coeff 3 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 3 : Finset (ℕ × ℕ)) =
        {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private theorem coeff_mul_four (f g : PowerSeries ℚ) :
    (f * g).coeff 4 = f.coeff 0 * g.coeff 4
      + f.coeff 1 * g.coeff 3
      + f.coeff 2 * g.coeff 2
      + f.coeff 3 * g.coeff 1
      + f.coeff 4 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
        {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  ring

private theorem coeff_mul_five (f g : PowerSeries ℚ) :
    (f * g).coeff 5 = f.coeff 0 * g.coeff 5
      + f.coeff 1 * g.coeff 4
      + f.coeff 2 * g.coeff 3
      + f.coeff 3 * g.coeff 2
      + f.coeff 4 * g.coeff 1
      + f.coeff 5 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 5 : Finset (ℕ × ℕ)) =
        {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private theorem coeff_mul_six (f g : PowerSeries ℚ) :
    (f * g).coeff 6 = f.coeff 0 * g.coeff 6
      + f.coeff 1 * g.coeff 5
      + f.coeff 2 * g.coeff 4
      + f.coeff 3 * g.coeff 3
      + f.coeff 4 * g.coeff 2
      + f.coeff 5 * g.coeff 1
      + f.coeff 6 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 6 : Finset (ℕ × ℕ)) =
        {(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (6, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  ring

private theorem coeff_mul_seven (f g : PowerSeries ℚ) :
    (f * g).coeff 7 = f.coeff 0 * g.coeff 7
      + f.coeff 1 * g.coeff 6
      + f.coeff 2 * g.coeff 5
      + f.coeff 3 * g.coeff 4
      + f.coeff 4 * g.coeff 3
      + f.coeff 5 * g.coeff 2
      + f.coeff 6 * g.coeff 1
      + f.coeff 7 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 7 : Finset (ℕ × ℕ)) =
        {(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1), (7, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private theorem coeff_mul_eight (f g : PowerSeries ℚ) :
    (f * g).coeff 8 = f.coeff 0 * g.coeff 8
      + f.coeff 1 * g.coeff 7
      + f.coeff 2 * g.coeff 6
      + f.coeff 3 * g.coeff 5
      + f.coeff 4 * g.coeff 4
      + f.coeff 5 * g.coeff 3
      + f.coeff 6 * g.coeff 2
      + f.coeff 7 * g.coeff 1
      + f.coeff 8 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 8 : Finset (ℕ × ℕ)) =
        {(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2), (7, 1), (8, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  ring

private theorem coeff_mul_nine (f g : PowerSeries ℚ) :
    (f * g).coeff 9 = f.coeff 0 * g.coeff 9
      + f.coeff 1 * g.coeff 8
      + f.coeff 2 * g.coeff 7
      + f.coeff 3 * g.coeff 6
      + f.coeff 4 * g.coeff 5
      + f.coeff 5 * g.coeff 4
      + f.coeff 6 * g.coeff 3
      + f.coeff 7 * g.coeff 2
      + f.coeff 8 * g.coeff 1
      + f.coeff 9 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 9 : Finset (ℕ × ℕ)) =
        {(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3), (7, 2), (8, 1), (9, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private theorem coeff_mul_ten (f g : PowerSeries ℚ) :
    (f * g).coeff 10 = f.coeff 0 * g.coeff 10
      + f.coeff 1 * g.coeff 9
      + f.coeff 2 * g.coeff 8
      + f.coeff 3 * g.coeff 7
      + f.coeff 4 * g.coeff 6
      + f.coeff 5 * g.coeff 5
      + f.coeff 6 * g.coeff 4
      + f.coeff 7 * g.coeff 3
      + f.coeff 8 * g.coeff 2
      + f.coeff 9 * g.coeff 1
      + f.coeff 10 * g.coeff 0 := by
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 10 : Finset (ℕ × ℕ)) =
        {(0, 10), (1, 9), (2, 8), (3, 7), (4, 6), (5, 5), (6, 4), (7, 3), (8, 2),
         (9, 1), (10, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  ring

/-! ## Low-degree coefficient helpers -/

private theorem coeff_one_pow_const_one_rat
    (f : PowerSeries ℚ) (hf : f.coeff 0 = 1) (k : Nat) :
    (f ^ k).coeff 1 = (k : ℚ) * f.coeff 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [show (Finset.antidiagonal 1 : Finset (Nat × Nat)) = {(0, 1), (1, 0)} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    have h_zero : (f ^ k).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, one_pow]
    rw [h_zero, ih, hf, mul_one]
    push_cast
    ring

private theorem coeff_two_pow_const_one_rat
    (f : PowerSeries ℚ) (hf : f.coeff 0 = 1) (k : Nat) :
    (f ^ k).coeff 2 =
      (k : ℚ) * f.coeff 2 + (k.choose 2 : ℚ) * (f.coeff 1) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [show (Finset.antidiagonal 2 : Finset (Nat × Nat)) =
        {(0, 2), (1, 1), (2, 0)} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
    have h_zero : (f ^ k).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, one_pow]
    have h_one : (f ^ k).coeff 1 = (k : ℚ) * f.coeff 1 :=
      coeff_one_pow_const_one_rat f hf k
    rw [h_zero, h_one, ih, hf]
    have h_succ_choose : ((k + 1).choose 2 : ℚ) = (k.choose 2 : ℚ) + k := by
      rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]
      push_cast
      ring
    rw [h_succ_choose]
    push_cast
    ring

private theorem coeff_three_pow_const_one_rat
    (f : PowerSeries ℚ) (hf : f.coeff 0 = 1) (k : Nat) :
    (f ^ k).coeff 3 =
      (k : ℚ) * f.coeff 3
        + 2 * (k.choose 2 : ℚ) * f.coeff 2 * f.coeff 1
        + (k.choose 3 : ℚ) * (f.coeff 1) ^ 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [show (Finset.antidiagonal 3 : Finset (Nat × Nat)) =
        {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_singleton]
    have h_zero : (f ^ k).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, one_pow]
    have h_one : (f ^ k).coeff 1 = (k : ℚ) * f.coeff 1 :=
      coeff_one_pow_const_one_rat f hf k
    have h_two : (f ^ k).coeff 2 =
        (k : ℚ) * f.coeff 2 + (k.choose 2 : ℚ) * (f.coeff 1) ^ 2 :=
      coeff_two_pow_const_one_rat f hf k
    rw [h_zero, h_one, h_two, ih, hf]
    have hC2 : ((k + 1).choose 2 : ℚ) = (k.choose 2 : ℚ) + k := by
      rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]
      push_cast
      ring
    have hC3 : ((k + 1).choose 3 : ℚ) = (k.choose 3 : ℚ) + (k.choose 2 : ℚ) := by
      rw [Nat.choose_succ_succ]
      push_cast
      ring
    rw [hC2, hC3]
    push_cast
    ring

private theorem coeff_four_pow_const_one_rat
    (f : PowerSeries ℚ) (hf : f.coeff 0 = 1) (k : Nat) :
    (f ^ k).coeff 4 =
      (k : ℚ) * f.coeff 4
        + 2 * (k.choose 2 : ℚ) * f.coeff 3 * f.coeff 1
        + 3 * (k.choose 3 : ℚ) * f.coeff 2 * (f.coeff 1) ^ 2
        + (k.choose 2 : ℚ) * (f.coeff 2) ^ 2
        + (k.choose 4 : ℚ) * (f.coeff 1) ^ 4 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [show (Finset.antidiagonal 4 : Finset (Nat × Nat)) =
        {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_singleton]
    have h_zero : (f ^ k).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, one_pow]
    have h_one : (f ^ k).coeff 1 = (k : ℚ) * f.coeff 1 :=
      coeff_one_pow_const_one_rat f hf k
    have h_two : (f ^ k).coeff 2 =
        (k : ℚ) * f.coeff 2 + (k.choose 2 : ℚ) * (f.coeff 1) ^ 2 :=
      coeff_two_pow_const_one_rat f hf k
    have h_three : (f ^ k).coeff 3 =
        (k : ℚ) * f.coeff 3
          + 2 * (k.choose 2 : ℚ) * f.coeff 2 * f.coeff 1
          + (k.choose 3 : ℚ) * (f.coeff 1) ^ 3 :=
      coeff_three_pow_const_one_rat f hf k
    rw [h_zero, h_one, h_two, h_three, ih, hf]
    have hC2 : ((k + 1).choose 2 : ℚ) = (k.choose 2 : ℚ) + k := by
      rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]
      push_cast
      ring
    have hC3 : ((k + 1).choose 3 : ℚ) = (k.choose 3 : ℚ) + (k.choose 2 : ℚ) := by
      rw [Nat.choose_succ_succ]
      push_cast
      ring
    have hC4 : ((k + 1).choose 4 : ℚ) = (k.choose 4 : ℚ) + (k.choose 3 : ℚ) := by
      rw [Nat.choose_succ_succ]
      push_cast
      ring
    rw [hC2, hC3, hC4]
    push_cast
    ring

private theorem coeff_five_pow_const_one_rat
    (f : PowerSeries ℚ) (hf : f.coeff 0 = 1) (k : Nat) :
    (f ^ k).coeff 5 =
      (k : ℚ) * f.coeff 5
        + 2 * (k.choose 2 : ℚ) * f.coeff 4 * f.coeff 1
        + 2 * (k.choose 2 : ℚ) * f.coeff 3 * f.coeff 2
        + 3 * (k.choose 3 : ℚ) * f.coeff 3 * (f.coeff 1) ^ 2
        + 3 * (k.choose 3 : ℚ) * (f.coeff 2) ^ 2 * f.coeff 1
        + 4 * (k.choose 4 : ℚ) * f.coeff 2 * (f.coeff 1) ^ 3
        + (k.choose 5 : ℚ) * (f.coeff 1) ^ 5 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [show (Finset.antidiagonal 5 : Finset (Nat × Nat)) =
        {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl]
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_singleton]
    have h_zero : (f ^ k).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, one_pow]
    have h_one : (f ^ k).coeff 1 = (k : ℚ) * f.coeff 1 :=
      coeff_one_pow_const_one_rat f hf k
    have h_two : (f ^ k).coeff 2 =
        (k : ℚ) * f.coeff 2 + (k.choose 2 : ℚ) * (f.coeff 1) ^ 2 :=
      coeff_two_pow_const_one_rat f hf k
    have h_three : (f ^ k).coeff 3 =
        (k : ℚ) * f.coeff 3
          + 2 * (k.choose 2 : ℚ) * f.coeff 2 * f.coeff 1
          + (k.choose 3 : ℚ) * (f.coeff 1) ^ 3 :=
      coeff_three_pow_const_one_rat f hf k
    have h_four : (f ^ k).coeff 4 =
        (k : ℚ) * f.coeff 4
          + 2 * (k.choose 2 : ℚ) * f.coeff 3 * f.coeff 1
          + 3 * (k.choose 3 : ℚ) * f.coeff 2 * (f.coeff 1) ^ 2
          + (k.choose 2 : ℚ) * (f.coeff 2) ^ 2
          + (k.choose 4 : ℚ) * (f.coeff 1) ^ 4 :=
      coeff_four_pow_const_one_rat f hf k
    rw [h_zero, h_one, h_two, h_three, h_four, ih, hf]
    have hC2 : ((k + 1).choose 2 : ℚ) = (k.choose 2 : ℚ) + k := by
      rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]
      push_cast
      ring
    have hC3 : ((k + 1).choose 3 : ℚ) = (k.choose 3 : ℚ) + (k.choose 2 : ℚ) := by
      rw [Nat.choose_succ_succ]
      push_cast
      ring
    have hC4 : ((k + 1).choose 4 : ℚ) = (k.choose 4 : ℚ) + (k.choose 3 : ℚ) := by
      rw [Nat.choose_succ_succ]
      push_cast
      ring
    have hC5 : ((k + 1).choose 5 : ℚ) = (k.choose 5 : ℚ) + (k.choose 4 : ℚ) := by
      rw [Nat.choose_succ_succ]
      push_cast
      ring
    rw [hC2, hC3, hC4, hC5]
    push_cast
    ring

private theorem rrcf_r_pow_five_coeff_zero : (rrcf_r ^ 5).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, rrcf_r_coeff_0]
  norm_num

private theorem rrcf_r_pow_five_coeff_one : (rrcf_r ^ 5).coeff 1 = -5 := by
  rw [coeff_one_pow_const_one_rat rrcf_r rrcf_r_coeff_0 5, rrcf_r_coeff_1]
  norm_num

private theorem rrcf_r_pow_five_coeff_two : (rrcf_r ^ 5).coeff 2 = 15 := by
  rw [coeff_two_pow_const_one_rat rrcf_r rrcf_r_coeff_0 5, rrcf_r_coeff_2,
      rrcf_r_coeff_1]
  norm_num [Nat.choose]

private theorem rrcf_r_pow_five_coeff_three : (rrcf_r ^ 5).coeff 3 = -30 := by
  rw [coeff_three_pow_const_one_rat rrcf_r rrcf_r_coeff_0 5, rrcf_r_coeff_3,
      rrcf_r_coeff_2, rrcf_r_coeff_1]
  norm_num [Nat.choose]

private theorem rrcf_r_pow_five_coeff_four : (rrcf_r ^ 5).coeff 4 = 40 := by
  rw [coeff_four_pow_const_one_rat rrcf_r rrcf_r_coeff_0 5, rrcf_r_coeff_4,
      rrcf_r_coeff_3, rrcf_r_coeff_2, rrcf_r_coeff_1]
  norm_num [Nat.choose]

private theorem rrcf_r_pow_five_coeff_five : (rrcf_r ^ 5).coeff 5 = -26 := by
  rw [coeff_five_pow_const_one_rat rrcf_r rrcf_r_coeff_0 5, rrcf_r_coeff_5,
      rrcf_r_coeff_4, rrcf_r_coeff_3, rrcf_r_coeff_2, rrcf_r_coeff_1]
  norm_num [Nat.choose]

private theorem rrcf_r_pow_two_coeff_zero : (rrcf_r ^ 2).coeff 0 = 1 := by
  rw [sq, coeff_mul_zero]
  rw [rrcf_r_coeff_0]
  norm_num

private theorem rrcf_r_pow_two_coeff_one : (rrcf_r ^ 2).coeff 1 = -2 := by
  rw [sq, coeff_mul_one]
  rw [rrcf_r_coeff_0, rrcf_r_coeff_1]
  norm_num

private theorem rrcf_r_pow_two_coeff_two : (rrcf_r ^ 2).coeff 2 = 3 := by
  rw [sq, coeff_mul_two]
  rw [rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2]
  norm_num

private theorem rrcf_r_pow_two_coeff_three : (rrcf_r ^ 2).coeff 3 = -2 := by
  rw [sq, coeff_mul_three]
  rw [rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3]
  norm_num

private theorem rrcf_r_pow_two_coeff_four : (rrcf_r ^ 2).coeff 4 = -1 := by
  rw [sq, coeff_mul_four]
  rw [rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4]
  norm_num

private theorem rrcf_r_pow_two_coeff_five : (rrcf_r ^ 2).coeff 5 = 4 := by
  rw [sq, coeff_mul_five]
  rw [rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5]
  norm_num

private theorem rrcf_r_pow_two_coeff_six : (rrcf_r ^ 2).coeff 6 = -6 := by
  rw [sq, coeff_mul_six]
  rw [rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5, rrcf_r_coeff_6]
  norm_num

private theorem rrcf_r_pow_two_coeff_seven : (rrcf_r ^ 2).coeff 7 = 6 := by
  rw [sq, coeff_mul_seven]
  rw [rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7]
  norm_num

private theorem rrcf_r_pow_two_coeff_eight : (rrcf_r ^ 2).coeff 8 = -3 := by
  rw [sq, coeff_mul_eight]
  rw [rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7, rrcf_r_coeff_8]
  norm_num

private theorem rrcf_r_pow_two_coeff_nine : (rrcf_r ^ 2).coeff 9 = -2 := by
  rw [sq, coeff_mul_nine]
  rw [rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7, rrcf_r_coeff_8,
      rrcf_r_coeff_9]
  norm_num

private theorem rrcf_r_pow_two_coeff_ten : (rrcf_r ^ 2).coeff 10 = 9 := by
  rw [sq, coeff_mul_ten]
  rw [rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7, rrcf_r_coeff_8,
      rrcf_r_coeff_9, rrcf_r_coeff_10]
  norm_num

private theorem rrcf_r_pow_three_coeff_zero : (rrcf_r ^ 3).coeff 0 = 1 := by
  change (rrcf_r ^ (2 + 1)).coeff 0 = 1
  rw [pow_succ, coeff_mul_zero]
  rw [rrcf_r_pow_two_coeff_zero, rrcf_r_coeff_0]
  norm_num

private theorem rrcf_r_pow_three_coeff_one : (rrcf_r ^ 3).coeff 1 = -3 := by
  change (rrcf_r ^ (2 + 1)).coeff 1 = -3
  rw [pow_succ, coeff_mul_one]
  rw [rrcf_r_pow_two_coeff_zero, rrcf_r_pow_two_coeff_one, rrcf_r_coeff_0, rrcf_r_coeff_1]
  norm_num

private theorem rrcf_r_pow_three_coeff_two : (rrcf_r ^ 3).coeff 2 = 6 := by
  change (rrcf_r ^ (2 + 1)).coeff 2 = 6
  rw [pow_succ, coeff_mul_two]
  rw [rrcf_r_pow_two_coeff_zero, rrcf_r_pow_two_coeff_one, rrcf_r_pow_two_coeff_two,
      rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2]
  norm_num

private theorem rrcf_r_pow_three_coeff_three : (rrcf_r ^ 3).coeff 3 = -7 := by
  change (rrcf_r ^ (2 + 1)).coeff 3 = -7
  rw [pow_succ, coeff_mul_three]
  rw [rrcf_r_pow_two_coeff_zero, rrcf_r_pow_two_coeff_one, rrcf_r_pow_two_coeff_two,
      rrcf_r_pow_two_coeff_three, rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2,
      rrcf_r_coeff_3]
  norm_num

private theorem rrcf_r_pow_three_coeff_four : (rrcf_r ^ 3).coeff 4 = 3 := by
  change (rrcf_r ^ (2 + 1)).coeff 4 = 3
  rw [pow_succ, coeff_mul_four]
  rw [rrcf_r_pow_two_coeff_zero, rrcf_r_pow_two_coeff_one, rrcf_r_pow_two_coeff_two,
      rrcf_r_pow_two_coeff_three, rrcf_r_pow_two_coeff_four, rrcf_r_coeff_0,
      rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4]
  norm_num

private theorem rrcf_r_pow_three_coeff_five : (rrcf_r ^ 3).coeff 5 = 6 := by
  change (rrcf_r ^ (2 + 1)).coeff 5 = 6
  rw [pow_succ, coeff_mul_five]
  rw [rrcf_r_pow_two_coeff_zero, rrcf_r_pow_two_coeff_one, rrcf_r_pow_two_coeff_two,
      rrcf_r_pow_two_coeff_three, rrcf_r_pow_two_coeff_four, rrcf_r_pow_two_coeff_five,
      rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3,
      rrcf_r_coeff_4, rrcf_r_coeff_5]
  norm_num

private theorem rrcf_r_pow_three_coeff_six : (rrcf_r ^ 3).coeff 6 = -17 := by
  change (rrcf_r ^ (2 + 1)).coeff 6 = -17
  rw [pow_succ, coeff_mul_six]
  rw [rrcf_r_pow_two_coeff_zero, rrcf_r_pow_two_coeff_one, rrcf_r_pow_two_coeff_two,
      rrcf_r_pow_two_coeff_three, rrcf_r_pow_two_coeff_four, rrcf_r_pow_two_coeff_five,
      rrcf_r_pow_two_coeff_six, rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2,
      rrcf_r_coeff_3, rrcf_r_coeff_4, rrcf_r_coeff_5, rrcf_r_coeff_6]
  norm_num

private theorem rrcf_r_pow_three_coeff_seven : (rrcf_r ^ 3).coeff 7 = 24 := by
  change (rrcf_r ^ (2 + 1)).coeff 7 = 24
  rw [pow_succ, coeff_mul_seven]
  rw [rrcf_r_pow_two_coeff_zero, rrcf_r_pow_two_coeff_one, rrcf_r_pow_two_coeff_two,
      rrcf_r_pow_two_coeff_three, rrcf_r_pow_two_coeff_four, rrcf_r_pow_two_coeff_five,
      rrcf_r_pow_two_coeff_six, rrcf_r_pow_two_coeff_seven, rrcf_r_coeff_0,
      rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7]
  norm_num

private theorem rrcf_r_pow_three_coeff_eight : (rrcf_r ^ 3).coeff 8 = -21 := by
  change (rrcf_r ^ (2 + 1)).coeff 8 = -21
  rw [pow_succ, coeff_mul_eight]
  rw [rrcf_r_pow_two_coeff_zero, rrcf_r_pow_two_coeff_one, rrcf_r_pow_two_coeff_two,
      rrcf_r_pow_two_coeff_three, rrcf_r_pow_two_coeff_four, rrcf_r_pow_two_coeff_five,
      rrcf_r_pow_two_coeff_six, rrcf_r_pow_two_coeff_seven, rrcf_r_pow_two_coeff_eight,
      rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3,
      rrcf_r_coeff_4, rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7,
      rrcf_r_coeff_8]
  norm_num

private theorem rrcf_r_pow_three_coeff_nine : (rrcf_r ^ 3).coeff 9 = 6 := by
  change (rrcf_r ^ (2 + 1)).coeff 9 = 6
  rw [pow_succ, coeff_mul_nine]
  rw [rrcf_r_pow_two_coeff_zero, rrcf_r_pow_two_coeff_one, rrcf_r_pow_two_coeff_two,
      rrcf_r_pow_two_coeff_three, rrcf_r_pow_two_coeff_four, rrcf_r_pow_two_coeff_five,
      rrcf_r_pow_two_coeff_six, rrcf_r_pow_two_coeff_seven, rrcf_r_pow_two_coeff_eight,
      rrcf_r_pow_two_coeff_nine, rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2,
      rrcf_r_coeff_3, rrcf_r_coeff_4, rrcf_r_coeff_5, rrcf_r_coeff_6,
      rrcf_r_coeff_7, rrcf_r_coeff_8, rrcf_r_coeff_9]
  norm_num

private theorem rrcf_r_pow_three_coeff_ten : (rrcf_r ^ 3).coeff 10 = 21 := by
  change (rrcf_r ^ (2 + 1)).coeff 10 = 21
  rw [pow_succ, coeff_mul_ten]
  rw [rrcf_r_pow_two_coeff_zero, rrcf_r_pow_two_coeff_one, rrcf_r_pow_two_coeff_two,
      rrcf_r_pow_two_coeff_three, rrcf_r_pow_two_coeff_four, rrcf_r_pow_two_coeff_five,
      rrcf_r_pow_two_coeff_six, rrcf_r_pow_two_coeff_seven, rrcf_r_pow_two_coeff_eight,
      rrcf_r_pow_two_coeff_nine, rrcf_r_pow_two_coeff_ten, rrcf_r_coeff_0,
      rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7, rrcf_r_coeff_8,
      rrcf_r_coeff_9, rrcf_r_coeff_10]
  norm_num

private theorem rrcf_r_pow_four_coeff_zero : (rrcf_r ^ 4).coeff 0 = 1 := by
  change (rrcf_r ^ (3 + 1)).coeff 0 = 1
  rw [pow_succ, coeff_mul_zero]
  rw [rrcf_r_pow_three_coeff_zero, rrcf_r_coeff_0]
  norm_num

private theorem rrcf_r_pow_four_coeff_one : (rrcf_r ^ 4).coeff 1 = -4 := by
  change (rrcf_r ^ (3 + 1)).coeff 1 = -4
  rw [pow_succ, coeff_mul_one]
  rw [rrcf_r_pow_three_coeff_zero, rrcf_r_pow_three_coeff_one, rrcf_r_coeff_0, rrcf_r_coeff_1]
  norm_num

private theorem rrcf_r_pow_four_coeff_two : (rrcf_r ^ 4).coeff 2 = 10 := by
  change (rrcf_r ^ (3 + 1)).coeff 2 = 10
  rw [pow_succ, coeff_mul_two]
  rw [rrcf_r_pow_three_coeff_zero, rrcf_r_pow_three_coeff_one, rrcf_r_pow_three_coeff_two,
      rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2]
  norm_num

private theorem rrcf_r_pow_four_coeff_three : (rrcf_r ^ 4).coeff 3 = -16 := by
  change (rrcf_r ^ (3 + 1)).coeff 3 = -16
  rw [pow_succ, coeff_mul_three]
  rw [rrcf_r_pow_three_coeff_zero, rrcf_r_pow_three_coeff_one, rrcf_r_pow_three_coeff_two,
      rrcf_r_pow_three_coeff_three, rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2,
      rrcf_r_coeff_3]
  norm_num

private theorem rrcf_r_pow_four_coeff_four : (rrcf_r ^ 4).coeff 4 = 15 := by
  change (rrcf_r ^ (3 + 1)).coeff 4 = 15
  rw [pow_succ, coeff_mul_four]
  rw [rrcf_r_pow_three_coeff_zero, rrcf_r_pow_three_coeff_one, rrcf_r_pow_three_coeff_two,
      rrcf_r_pow_three_coeff_three, rrcf_r_pow_three_coeff_four, rrcf_r_coeff_0,
      rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4]
  norm_num

private theorem rrcf_r_pow_four_coeff_five : (rrcf_r ^ 4).coeff 5 = 0 := by
  change (rrcf_r ^ (3 + 1)).coeff 5 = 0
  rw [pow_succ, coeff_mul_five]
  rw [rrcf_r_pow_three_coeff_zero, rrcf_r_pow_three_coeff_one, rrcf_r_pow_three_coeff_two,
      rrcf_r_pow_three_coeff_three, rrcf_r_pow_three_coeff_four, rrcf_r_pow_three_coeff_five,
      rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3,
      rrcf_r_coeff_4, rrcf_r_coeff_5]
  norm_num

private theorem rrcf_r_pow_four_coeff_six : (rrcf_r ^ 4).coeff 6 = -30 := by
  change (rrcf_r ^ (3 + 1)).coeff 6 = -30
  rw [pow_succ, coeff_mul_six]
  rw [rrcf_r_pow_three_coeff_zero, rrcf_r_pow_three_coeff_one, rrcf_r_pow_three_coeff_two,
      rrcf_r_pow_three_coeff_three, rrcf_r_pow_three_coeff_four, rrcf_r_pow_three_coeff_five,
      rrcf_r_pow_three_coeff_six, rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2,
      rrcf_r_coeff_3, rrcf_r_coeff_4, rrcf_r_coeff_5, rrcf_r_coeff_6]
  norm_num

private theorem rrcf_r_pow_four_coeff_seven : (rrcf_r ^ 4).coeff 7 = 64 := by
  change (rrcf_r ^ (3 + 1)).coeff 7 = 64
  rw [pow_succ, coeff_mul_seven]
  rw [rrcf_r_pow_three_coeff_zero, rrcf_r_pow_three_coeff_one, rrcf_r_pow_three_coeff_two,
      rrcf_r_pow_three_coeff_three, rrcf_r_pow_three_coeff_four, rrcf_r_pow_three_coeff_five,
      rrcf_r_pow_three_coeff_six, rrcf_r_pow_three_coeff_seven, rrcf_r_coeff_0,
      rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7]
  norm_num

private theorem rrcf_r_pow_four_coeff_eight : (rrcf_r ^ 4).coeff 8 = -81 := by
  change (rrcf_r ^ (3 + 1)).coeff 8 = -81
  rw [pow_succ, coeff_mul_eight]
  rw [rrcf_r_pow_three_coeff_zero, rrcf_r_pow_three_coeff_one, rrcf_r_pow_three_coeff_two,
      rrcf_r_pow_three_coeff_three, rrcf_r_pow_three_coeff_four, rrcf_r_pow_three_coeff_five,
      rrcf_r_pow_three_coeff_six, rrcf_r_pow_three_coeff_seven, rrcf_r_pow_three_coeff_eight,
      rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3,
      rrcf_r_coeff_4, rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7,
      rrcf_r_coeff_8]
  norm_num

private theorem rrcf_r_pow_four_coeff_nine : (rrcf_r ^ 4).coeff 9 = 60 := by
  change (rrcf_r ^ (3 + 1)).coeff 9 = 60
  rw [pow_succ, coeff_mul_nine]
  rw [rrcf_r_pow_three_coeff_zero, rrcf_r_pow_three_coeff_one, rrcf_r_pow_three_coeff_two,
      rrcf_r_pow_three_coeff_three, rrcf_r_pow_three_coeff_four, rrcf_r_pow_three_coeff_five,
      rrcf_r_pow_three_coeff_six, rrcf_r_pow_three_coeff_seven, rrcf_r_pow_three_coeff_eight,
      rrcf_r_pow_three_coeff_nine, rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2,
      rrcf_r_coeff_3, rrcf_r_coeff_4, rrcf_r_coeff_5, rrcf_r_coeff_6,
      rrcf_r_coeff_7, rrcf_r_coeff_8, rrcf_r_coeff_9]
  norm_num

private theorem rrcf_r_pow_four_coeff_ten : (rrcf_r ^ 4).coeff 10 = 12 := by
  change (rrcf_r ^ (3 + 1)).coeff 10 = 12
  rw [pow_succ, coeff_mul_ten]
  rw [rrcf_r_pow_three_coeff_zero, rrcf_r_pow_three_coeff_one, rrcf_r_pow_three_coeff_two,
      rrcf_r_pow_three_coeff_three, rrcf_r_pow_three_coeff_four, rrcf_r_pow_three_coeff_five,
      rrcf_r_pow_three_coeff_six, rrcf_r_pow_three_coeff_seven, rrcf_r_pow_three_coeff_eight,
      rrcf_r_pow_three_coeff_nine, rrcf_r_pow_three_coeff_ten, rrcf_r_coeff_0,
      rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7, rrcf_r_coeff_8,
      rrcf_r_coeff_9, rrcf_r_coeff_10]
  norm_num

private theorem rrcf_r_pow_five_coeff_six : (rrcf_r ^ 5).coeff 6 = -30 := by
  change (rrcf_r ^ (4 + 1)).coeff 6 = -30
  rw [pow_succ, coeff_mul_six]
  rw [rrcf_r_pow_four_coeff_zero, rrcf_r_pow_four_coeff_one, rrcf_r_pow_four_coeff_two,
      rrcf_r_pow_four_coeff_three, rrcf_r_pow_four_coeff_four, rrcf_r_pow_four_coeff_five,
      rrcf_r_pow_four_coeff_six, rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2,
      rrcf_r_coeff_3, rrcf_r_coeff_4, rrcf_r_coeff_5, rrcf_r_coeff_6]
  norm_num

private theorem rrcf_r_pow_five_coeff_seven : (rrcf_r ^ 5).coeff 7 = 125 := by
  change (rrcf_r ^ (4 + 1)).coeff 7 = 125
  rw [pow_succ, coeff_mul_seven]
  rw [rrcf_r_pow_four_coeff_zero, rrcf_r_pow_four_coeff_one, rrcf_r_pow_four_coeff_two,
      rrcf_r_pow_four_coeff_three, rrcf_r_pow_four_coeff_four, rrcf_r_pow_four_coeff_five,
      rrcf_r_pow_four_coeff_six, rrcf_r_pow_four_coeff_seven, rrcf_r_coeff_0,
      rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7]
  norm_num

private theorem rrcf_r_pow_five_coeff_eight : (rrcf_r ^ 5).coeff 8 = -220 := by
  change (rrcf_r ^ (4 + 1)).coeff 8 = -220
  rw [pow_succ, coeff_mul_eight]
  rw [rrcf_r_pow_four_coeff_zero, rrcf_r_pow_four_coeff_one, rrcf_r_pow_four_coeff_two,
      rrcf_r_pow_four_coeff_three, rrcf_r_pow_four_coeff_four, rrcf_r_pow_four_coeff_five,
      rrcf_r_pow_four_coeff_six, rrcf_r_pow_four_coeff_seven, rrcf_r_pow_four_coeff_eight,
      rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3,
      rrcf_r_coeff_4, rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7,
      rrcf_r_coeff_8]
  norm_num

private theorem rrcf_r_pow_five_coeff_nine : (rrcf_r ^ 5).coeff 9 = 245 := by
  change (rrcf_r ^ (4 + 1)).coeff 9 = 245
  rw [pow_succ, coeff_mul_nine]
  rw [rrcf_r_pow_four_coeff_zero, rrcf_r_pow_four_coeff_one, rrcf_r_pow_four_coeff_two,
      rrcf_r_pow_four_coeff_three, rrcf_r_pow_four_coeff_four, rrcf_r_pow_four_coeff_five,
      rrcf_r_pow_four_coeff_six, rrcf_r_pow_four_coeff_seven, rrcf_r_pow_four_coeff_eight,
      rrcf_r_pow_four_coeff_nine, rrcf_r_coeff_0, rrcf_r_coeff_1, rrcf_r_coeff_2,
      rrcf_r_coeff_3, rrcf_r_coeff_4, rrcf_r_coeff_5, rrcf_r_coeff_6,
      rrcf_r_coeff_7, rrcf_r_coeff_8, rrcf_r_coeff_9]
  norm_num

private theorem rrcf_r_pow_five_coeff_ten : (rrcf_r ^ 5).coeff 10 = -124 := by
  change (rrcf_r ^ (4 + 1)).coeff 10 = -124
  rw [pow_succ, coeff_mul_ten]
  rw [rrcf_r_pow_four_coeff_zero, rrcf_r_pow_four_coeff_one, rrcf_r_pow_four_coeff_two,
      rrcf_r_pow_four_coeff_three, rrcf_r_pow_four_coeff_four, rrcf_r_pow_four_coeff_five,
      rrcf_r_pow_four_coeff_six, rrcf_r_pow_four_coeff_seven, rrcf_r_pow_four_coeff_eight,
      rrcf_r_pow_four_coeff_nine, rrcf_r_pow_four_coeff_ten, rrcf_r_coeff_0,
      rrcf_r_coeff_1, rrcf_r_coeff_2, rrcf_r_coeff_3, rrcf_r_coeff_4,
      rrcf_r_coeff_5, rrcf_r_coeff_6, rrcf_r_coeff_7, rrcf_r_coeff_8,
      rrcf_r_coeff_9, rrcf_r_coeff_10]
  norm_num

private theorem expand_five_rrcf_r_coeff_zero :
    (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) rrcf_r).coeff 0 = 1 := by
  rw [PowerSeries.coeff_expand]
  simp [rrcf_r_coeff_0]

private theorem expand_five_rrcf_r_coeff_one :
    (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) rrcf_r).coeff 1 = 0 := by
  rw [PowerSeries.coeff_expand]
  simp

private theorem expand_five_rrcf_r_coeff_two :
    (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) rrcf_r).coeff 2 = 0 := by
  rw [PowerSeries.coeff_expand]
  simp

private theorem expand_five_rrcf_r_coeff_three :
    (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) rrcf_r).coeff 3 = 0 := by
  rw [PowerSeries.coeff_expand]
  simp

private theorem expand_five_rrcf_r_coeff_four :
    (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) rrcf_r).coeff 4 = 0 := by
  rw [PowerSeries.coeff_expand]
  simp

private theorem expand_five_rrcf_r_coeff_five :
    (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) rrcf_r).coeff 5 = -1 := by
  rw [PowerSeries.coeff_expand]
  simp [rrcf_r_coeff_1]

private theorem expand_five_rrcf_r_coeff_six :
    (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) rrcf_r).coeff 6 = 0 := by
  rw [PowerSeries.coeff_expand]
  simp

private theorem expand_five_rrcf_r_coeff_seven :
    (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) rrcf_r).coeff 7 = 0 := by
  rw [PowerSeries.coeff_expand]
  simp

private theorem expand_five_rrcf_r_coeff_eight :
    (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) rrcf_r).coeff 8 = 0 := by
  rw [PowerSeries.coeff_expand]
  simp

private theorem expand_five_rrcf_r_coeff_nine :
    (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) rrcf_r).coeff 9 = 0 := by
  rw [PowerSeries.coeff_expand]
  simp

private theorem expand_five_rrcf_r_coeff_ten :
    (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) rrcf_r).coeff 10 = 1 := by
  rw [PowerSeries.coeff_expand]
  simp [rrcf_r_coeff_2]

private theorem coeff_one_two_mul (f : PowerSeries ℚ) :
    (2 * f).coeff 1 = 2 * f.coeff 1 := by
  rw [show (2 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (2 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_one_three_mul (f : PowerSeries ℚ) :
    (3 * f).coeff 1 = 3 * f.coeff 1 := by
  rw [show (3 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (3 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_one_four_mul (f : PowerSeries ℚ) :
    (4 * f).coeff 1 = 4 * f.coeff 1 := by
  rw [show (4 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (4 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_two_two_mul (f : PowerSeries ℚ) :
    (2 * f).coeff 2 = 2 * f.coeff 2 := by
  rw [show (2 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (2 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_two_three_mul (f : PowerSeries ℚ) :
    (3 * f).coeff 2 = 3 * f.coeff 2 := by
  rw [show (3 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (3 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_two_four_mul (f : PowerSeries ℚ) :
    (4 * f).coeff 2 = 4 * f.coeff 2 := by
  rw [show (4 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (4 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_three_two_mul (f : PowerSeries ℚ) :
    (2 * f).coeff 3 = 2 * f.coeff 3 := by
  rw [show (2 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (2 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_three_three_mul (f : PowerSeries ℚ) :
    (3 * f).coeff 3 = 3 * f.coeff 3 := by
  rw [show (3 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (3 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_three_four_mul (f : PowerSeries ℚ) :
    (4 * f).coeff 3 = 4 * f.coeff 3 := by
  rw [show (4 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (4 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_four_two_mul (f : PowerSeries ℚ) :
    (2 * f).coeff 4 = 2 * f.coeff 4 := by
  rw [show (2 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (2 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_four_three_mul (f : PowerSeries ℚ) :
    (3 * f).coeff 4 = 3 * f.coeff 4 := by
  rw [show (3 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (3 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_four_four_mul (f : PowerSeries ℚ) :
    (4 * f).coeff 4 = 4 * f.coeff 4 := by
  rw [show (4 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (4 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_five_two_mul (f : PowerSeries ℚ) :
    (2 * f).coeff 5 = 2 * f.coeff 5 := by
  rw [show (2 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (2 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_five_three_mul (f : PowerSeries ℚ) :
    (3 * f).coeff 5 = 3 * f.coeff 5 := by
  rw [show (3 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (3 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_five_four_mul (f : PowerSeries ℚ) :
    (4 * f).coeff 5 = 4 * f.coeff 5 := by
  rw [show (4 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (4 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_six_two_mul (f : PowerSeries ℚ) :
    (2 * f).coeff 6 = 2 * f.coeff 6 := by
  rw [show (2 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (2 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_six_three_mul (f : PowerSeries ℚ) :
    (3 * f).coeff 6 = 3 * f.coeff 6 := by
  rw [show (3 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (3 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_six_four_mul (f : PowerSeries ℚ) :
    (4 * f).coeff 6 = 4 * f.coeff 6 := by
  rw [show (4 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (4 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_seven_two_mul (f : PowerSeries ℚ) :
    (2 * f).coeff 7 = 2 * f.coeff 7 := by
  rw [show (2 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (2 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_seven_three_mul (f : PowerSeries ℚ) :
    (3 * f).coeff 7 = 3 * f.coeff 7 := by
  rw [show (3 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (3 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_seven_four_mul (f : PowerSeries ℚ) :
    (4 * f).coeff 7 = 4 * f.coeff 7 := by
  rw [show (4 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (4 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_eight_two_mul (f : PowerSeries ℚ) :
    (2 * f).coeff 8 = 2 * f.coeff 8 := by
  rw [show (2 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (2 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_eight_three_mul (f : PowerSeries ℚ) :
    (3 * f).coeff 8 = 3 * f.coeff 8 := by
  rw [show (3 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (3 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_eight_four_mul (f : PowerSeries ℚ) :
    (4 * f).coeff 8 = 4 * f.coeff 8 := by
  rw [show (4 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (4 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_nine_two_mul (f : PowerSeries ℚ) :
    (2 * f).coeff 9 = 2 * f.coeff 9 := by
  rw [show (2 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (2 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_nine_three_mul (f : PowerSeries ℚ) :
    (3 * f).coeff 9 = 3 * f.coeff 9 := by
  rw [show (3 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (3 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_nine_four_mul (f : PowerSeries ℚ) :
    (4 * f).coeff 9 = 4 * f.coeff 9 := by
  rw [show (4 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (4 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_ten_two_mul (f : PowerSeries ℚ) :
    (2 * f).coeff 10 = 2 * f.coeff 10 := by
  rw [show (2 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (2 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_ten_three_mul (f : PowerSeries ℚ) :
    (3 * f).coeff 10 = 3 * f.coeff 10 := by
  rw [show (3 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (3 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem coeff_ten_four_mul (f : PowerSeries ℚ) :
    (4 * f).coeff 10 = 4 * f.coeff 10 := by
  rw [show (4 : PowerSeries ℚ) = (PowerSeries.C : ℚ →+* PowerSeries ℚ) (4 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4).symm]
  rw [PowerSeries.coeff_C_mul]

private theorem rrcf_v_pow_coeff_zero (n : ℕ) (hn : n ≠ 0) :
    (rrcf_v ^ n).coeff 0 = 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, rrcf_v_coeff_0]
  exact zero_pow hn

private theorem rrcf_v_sq_coeff_one : (rrcf_v ^ 2).coeff 1 = 0 := by
  rw [sq, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_v_coeff_0, rrcf_v_coeff_1]
  ring

private theorem rrcf_v_cube_coeff_one : (rrcf_v ^ 3).coeff 1 = 0 := by
  change (rrcf_v ^ (2 + 1)).coeff 1 = 0
  rw [pow_succ, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_v_pow_coeff_zero 2 (by decide), rrcf_v_coeff_1,
      rrcf_v_sq_coeff_one, rrcf_v_coeff_0]
  ring

private theorem rrcf_v_fourth_coeff_one : (rrcf_v ^ 4).coeff 1 = 0 := by
  change (rrcf_v ^ (3 + 1)).coeff 1 = 0
  rw [pow_succ, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_v_pow_coeff_zero 3 (by decide), rrcf_v_coeff_1,
      rrcf_v_cube_coeff_one, rrcf_v_coeff_0]
  ring

private theorem rrcf_v_sq_coeff_two : (rrcf_v ^ 2).coeff 2 = 1 := by
  rw [sq, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) = {(0, 2), (1, 1), (2, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2]
  ring

private theorem rrcf_v_cube_coeff_two : (rrcf_v ^ 3).coeff 2 = 0 := by
  change (rrcf_v ^ (2 + 1)).coeff 2 = 0
  rw [pow_succ, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) = {(0, 2), (1, 1), (2, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_v_pow_coeff_zero 2 (by decide), rrcf_v_coeff_2,
      rrcf_v_sq_coeff_one, rrcf_v_coeff_1, rrcf_v_sq_coeff_two, rrcf_v_coeff_0]
  ring

private theorem rrcf_v_fourth_coeff_two : (rrcf_v ^ 4).coeff 2 = 0 := by
  change (rrcf_v ^ (3 + 1)).coeff 2 = 0
  rw [pow_succ, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) = {(0, 2), (1, 1), (2, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_v_pow_coeff_zero 3 (by decide), rrcf_v_coeff_2,
      rrcf_v_cube_coeff_one, rrcf_v_coeff_1, rrcf_v_cube_coeff_two, rrcf_v_coeff_0]
  ring

private theorem rrcf_v_sq_coeff_three : (rrcf_v ^ 2).coeff 3 = 0 := by
  rw [sq, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 3 : Finset (ℕ × ℕ)) =
      {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3]
  ring

private theorem rrcf_v_cube_coeff_three : (rrcf_v ^ 3).coeff 3 = 1 := by
  change (rrcf_v ^ (2 + 1)).coeff 3 = 1
  rw [pow_succ, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 3 : Finset (ℕ × ℕ)) =
      {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_v_pow_coeff_zero 2 (by decide), rrcf_v_coeff_3,
      rrcf_v_sq_coeff_one, rrcf_v_coeff_2, rrcf_v_sq_coeff_two, rrcf_v_coeff_1,
      rrcf_v_sq_coeff_three, rrcf_v_coeff_0]
  ring

private theorem rrcf_v_fourth_coeff_three : (rrcf_v ^ 4).coeff 3 = 0 := by
  change (rrcf_v ^ (3 + 1)).coeff 3 = 0
  rw [pow_succ, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 3 : Finset (ℕ × ℕ)) =
      {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_v_pow_coeff_zero 3 (by decide), rrcf_v_coeff_3,
      rrcf_v_cube_coeff_one, rrcf_v_coeff_2, rrcf_v_cube_coeff_two, rrcf_v_coeff_1,
      rrcf_v_cube_coeff_three, rrcf_v_coeff_0]
  ring

private theorem rrcf_v_sq_coeff_four : (rrcf_v ^ 2).coeff 4 = 0 := by
  rw [sq, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
      {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3,
      rrcf_v_coeff_4]
  ring

private theorem rrcf_v_cube_coeff_four : (rrcf_v ^ 3).coeff 4 = 0 := by
  change (rrcf_v ^ (2 + 1)).coeff 4 = 0
  rw [pow_succ, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
      {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [rrcf_v_pow_coeff_zero 2 (by decide), rrcf_v_coeff_4,
      rrcf_v_sq_coeff_one, rrcf_v_coeff_3, rrcf_v_sq_coeff_two, rrcf_v_coeff_2,
      rrcf_v_sq_coeff_three, rrcf_v_coeff_1, rrcf_v_sq_coeff_four,
      rrcf_v_coeff_0]
  ring

private theorem rrcf_v_fourth_coeff_four : (rrcf_v ^ 4).coeff 4 = 1 := by
  change (rrcf_v ^ (3 + 1)).coeff 4 = 1
  rw [pow_succ, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
      {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [rrcf_v_pow_coeff_zero 3 (by decide), rrcf_v_coeff_4,
      rrcf_v_cube_coeff_one, rrcf_v_coeff_3, rrcf_v_cube_coeff_two,
      rrcf_v_coeff_2, rrcf_v_cube_coeff_three, rrcf_v_coeff_1,
      rrcf_v_cube_coeff_four, rrcf_v_coeff_0]
  ring

private theorem rrcf_v_sq_coeff_five : (rrcf_v ^ 2).coeff 5 = 0 := by
  rw [sq, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 5 : Finset (ℕ × ℕ)) =
      {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3,
      rrcf_v_coeff_4, rrcf_v_coeff_5]
  ring

private theorem rrcf_v_cube_coeff_five : (rrcf_v ^ 3).coeff 5 = 0 := by
  change (rrcf_v ^ (2 + 1)).coeff 5 = 0
  rw [pow_succ, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 5 : Finset (ℕ × ℕ)) =
      {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_v_pow_coeff_zero 2 (by decide), rrcf_v_coeff_5,
      rrcf_v_sq_coeff_one, rrcf_v_coeff_4, rrcf_v_sq_coeff_two, rrcf_v_coeff_3,
      rrcf_v_sq_coeff_three, rrcf_v_coeff_2, rrcf_v_sq_coeff_four,
      rrcf_v_coeff_1, rrcf_v_sq_coeff_five, rrcf_v_coeff_0]
  ring

private theorem rrcf_v_fourth_coeff_five : (rrcf_v ^ 4).coeff 5 = 0 := by
  change (rrcf_v ^ (3 + 1)).coeff 5 = 0
  rw [pow_succ, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 5 : Finset (ℕ × ℕ)) =
      {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_v_pow_coeff_zero 3 (by decide), rrcf_v_coeff_5,
      rrcf_v_cube_coeff_one, rrcf_v_coeff_4, rrcf_v_cube_coeff_two,
      rrcf_v_coeff_3, rrcf_v_cube_coeff_three, rrcf_v_coeff_2,
      rrcf_v_cube_coeff_four, rrcf_v_coeff_1, rrcf_v_cube_coeff_five,
      rrcf_v_coeff_0]
  ring

private theorem rrcf_v_sq_coeff_six : (rrcf_v ^ 2).coeff 6 = 0 := by
  rw [sq, coeff_mul_six]
  rw [rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3,
      rrcf_v_coeff_4, rrcf_v_coeff_5, rrcf_v_coeff_6]
  ring

private theorem rrcf_v_sq_coeff_seven : (rrcf_v ^ 2).coeff 7 = -2 := by
  rw [sq, coeff_mul_seven]
  rw [rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3,
      rrcf_v_coeff_4, rrcf_v_coeff_5, rrcf_v_coeff_6, rrcf_v_coeff_7]
  ring

private theorem rrcf_v_sq_coeff_eight : (rrcf_v ^ 2).coeff 8 = 0 := by
  rw [sq, coeff_mul_eight]
  rw [rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3,
      rrcf_v_coeff_4, rrcf_v_coeff_5, rrcf_v_coeff_6, rrcf_v_coeff_7,
      rrcf_v_coeff_8]
  ring

private theorem rrcf_v_sq_coeff_nine : (rrcf_v ^ 2).coeff 9 = 0 := by
  rw [sq, coeff_mul_nine]
  rw [rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3,
      rrcf_v_coeff_4, rrcf_v_coeff_5, rrcf_v_coeff_6, rrcf_v_coeff_7,
      rrcf_v_coeff_8, rrcf_v_coeff_9]
  ring

private theorem rrcf_v_sq_coeff_ten : (rrcf_v ^ 2).coeff 10 = 0 := by
  rw [sq, coeff_mul_ten]
  rw [rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3,
      rrcf_v_coeff_4, rrcf_v_coeff_5, rrcf_v_coeff_6, rrcf_v_coeff_7,
      rrcf_v_coeff_8, rrcf_v_coeff_9, rrcf_v_coeff_10]
  ring

private theorem rrcf_v_cube_coeff_six : (rrcf_v ^ 3).coeff 6 = 0 := by
  change (rrcf_v ^ (2 + 1)).coeff 6 = 0
  rw [pow_succ, coeff_mul_six]
  rw [rrcf_v_pow_coeff_zero 2 (by decide), rrcf_v_sq_coeff_one,
      rrcf_v_sq_coeff_two, rrcf_v_sq_coeff_three, rrcf_v_sq_coeff_four,
      rrcf_v_sq_coeff_five, rrcf_v_sq_coeff_six, rrcf_v_coeff_0,
      rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3, rrcf_v_coeff_4,
      rrcf_v_coeff_5, rrcf_v_coeff_6]
  ring

private theorem rrcf_v_cube_coeff_seven : (rrcf_v ^ 3).coeff 7 = 0 := by
  change (rrcf_v ^ (2 + 1)).coeff 7 = 0
  rw [pow_succ, coeff_mul_seven]
  rw [rrcf_v_pow_coeff_zero 2 (by decide), rrcf_v_sq_coeff_one,
      rrcf_v_sq_coeff_two, rrcf_v_sq_coeff_three, rrcf_v_sq_coeff_four,
      rrcf_v_sq_coeff_five, rrcf_v_sq_coeff_six, rrcf_v_sq_coeff_seven,
      rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3,
      rrcf_v_coeff_4, rrcf_v_coeff_5, rrcf_v_coeff_6, rrcf_v_coeff_7]
  ring

private theorem rrcf_v_cube_coeff_eight : (rrcf_v ^ 3).coeff 8 = -3 := by
  change (rrcf_v ^ (2 + 1)).coeff 8 = -3
  rw [pow_succ, coeff_mul_eight]
  rw [rrcf_v_pow_coeff_zero 2 (by decide), rrcf_v_sq_coeff_one,
      rrcf_v_sq_coeff_two, rrcf_v_sq_coeff_three, rrcf_v_sq_coeff_four,
      rrcf_v_sq_coeff_five, rrcf_v_sq_coeff_six, rrcf_v_sq_coeff_seven,
      rrcf_v_sq_coeff_eight, rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2,
      rrcf_v_coeff_3, rrcf_v_coeff_4, rrcf_v_coeff_5, rrcf_v_coeff_6,
      rrcf_v_coeff_7, rrcf_v_coeff_8]
  ring

private theorem rrcf_v_cube_coeff_nine : (rrcf_v ^ 3).coeff 9 = 0 := by
  change (rrcf_v ^ (2 + 1)).coeff 9 = 0
  rw [pow_succ, coeff_mul_nine]
  rw [rrcf_v_pow_coeff_zero 2 (by decide), rrcf_v_sq_coeff_one,
      rrcf_v_sq_coeff_two, rrcf_v_sq_coeff_three, rrcf_v_sq_coeff_four,
      rrcf_v_sq_coeff_five, rrcf_v_sq_coeff_six, rrcf_v_sq_coeff_seven,
      rrcf_v_sq_coeff_eight, rrcf_v_sq_coeff_nine, rrcf_v_coeff_0,
      rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3, rrcf_v_coeff_4,
      rrcf_v_coeff_5, rrcf_v_coeff_6, rrcf_v_coeff_7, rrcf_v_coeff_8,
      rrcf_v_coeff_9]
  ring

private theorem rrcf_v_cube_coeff_ten : (rrcf_v ^ 3).coeff 10 = 0 := by
  change (rrcf_v ^ (2 + 1)).coeff 10 = 0
  rw [pow_succ, coeff_mul_ten]
  rw [rrcf_v_pow_coeff_zero 2 (by decide), rrcf_v_sq_coeff_one,
      rrcf_v_sq_coeff_two, rrcf_v_sq_coeff_three, rrcf_v_sq_coeff_four,
      rrcf_v_sq_coeff_five, rrcf_v_sq_coeff_six, rrcf_v_sq_coeff_seven,
      rrcf_v_sq_coeff_eight, rrcf_v_sq_coeff_nine, rrcf_v_sq_coeff_ten,
      rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3,
      rrcf_v_coeff_4, rrcf_v_coeff_5, rrcf_v_coeff_6, rrcf_v_coeff_7,
      rrcf_v_coeff_8, rrcf_v_coeff_9, rrcf_v_coeff_10]
  ring

private theorem rrcf_v_fourth_coeff_six : (rrcf_v ^ 4).coeff 6 = 0 := by
  change (rrcf_v ^ (3 + 1)).coeff 6 = 0
  rw [pow_succ, coeff_mul_six]
  rw [rrcf_v_pow_coeff_zero 3 (by decide), rrcf_v_cube_coeff_one,
      rrcf_v_cube_coeff_two, rrcf_v_cube_coeff_three, rrcf_v_cube_coeff_four,
      rrcf_v_cube_coeff_five, rrcf_v_cube_coeff_six, rrcf_v_coeff_0,
      rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3, rrcf_v_coeff_4,
      rrcf_v_coeff_5, rrcf_v_coeff_6]
  ring

private theorem rrcf_v_fourth_coeff_seven : (rrcf_v ^ 4).coeff 7 = 0 := by
  change (rrcf_v ^ (3 + 1)).coeff 7 = 0
  rw [pow_succ, coeff_mul_seven]
  rw [rrcf_v_pow_coeff_zero 3 (by decide), rrcf_v_cube_coeff_one,
      rrcf_v_cube_coeff_two, rrcf_v_cube_coeff_three, rrcf_v_cube_coeff_four,
      rrcf_v_cube_coeff_five, rrcf_v_cube_coeff_six, rrcf_v_cube_coeff_seven,
      rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3,
      rrcf_v_coeff_4, rrcf_v_coeff_5, rrcf_v_coeff_6, rrcf_v_coeff_7]
  ring

private theorem rrcf_v_fourth_coeff_eight : (rrcf_v ^ 4).coeff 8 = 0 := by
  change (rrcf_v ^ (3 + 1)).coeff 8 = 0
  rw [pow_succ, coeff_mul_eight]
  rw [rrcf_v_pow_coeff_zero 3 (by decide), rrcf_v_cube_coeff_one,
      rrcf_v_cube_coeff_two, rrcf_v_cube_coeff_three, rrcf_v_cube_coeff_four,
      rrcf_v_cube_coeff_five, rrcf_v_cube_coeff_six, rrcf_v_cube_coeff_seven,
      rrcf_v_cube_coeff_eight, rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2,
      rrcf_v_coeff_3, rrcf_v_coeff_4, rrcf_v_coeff_5, rrcf_v_coeff_6,
      rrcf_v_coeff_7, rrcf_v_coeff_8]
  ring

private theorem rrcf_v_fourth_coeff_nine : (rrcf_v ^ 4).coeff 9 = -4 := by
  change (rrcf_v ^ (3 + 1)).coeff 9 = -4
  rw [pow_succ, coeff_mul_nine]
  rw [rrcf_v_pow_coeff_zero 3 (by decide), rrcf_v_cube_coeff_one,
      rrcf_v_cube_coeff_two, rrcf_v_cube_coeff_three, rrcf_v_cube_coeff_four,
      rrcf_v_cube_coeff_five, rrcf_v_cube_coeff_six, rrcf_v_cube_coeff_seven,
      rrcf_v_cube_coeff_eight, rrcf_v_cube_coeff_nine, rrcf_v_coeff_0,
      rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3, rrcf_v_coeff_4,
      rrcf_v_coeff_5, rrcf_v_coeff_6, rrcf_v_coeff_7, rrcf_v_coeff_8,
      rrcf_v_coeff_9]
  ring

private theorem rrcf_v_fourth_coeff_ten : (rrcf_v ^ 4).coeff 10 = 0 := by
  change (rrcf_v ^ (3 + 1)).coeff 10 = 0
  rw [pow_succ, coeff_mul_ten]
  rw [rrcf_v_pow_coeff_zero 3 (by decide), rrcf_v_cube_coeff_one,
      rrcf_v_cube_coeff_two, rrcf_v_cube_coeff_three, rrcf_v_cube_coeff_four,
      rrcf_v_cube_coeff_five, rrcf_v_cube_coeff_six, rrcf_v_cube_coeff_seven,
      rrcf_v_cube_coeff_eight, rrcf_v_cube_coeff_nine, rrcf_v_cube_coeff_ten,
      rrcf_v_coeff_0, rrcf_v_coeff_1, rrcf_v_coeff_2, rrcf_v_coeff_3,
      rrcf_v_coeff_4, rrcf_v_coeff_5, rrcf_v_coeff_6, rrcf_v_coeff_7,
      rrcf_v_coeff_8, rrcf_v_coeff_9, rrcf_v_coeff_10]
  ring

private theorem rrcf_lhs_factor_coeff_zero :
    (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hv : PowerSeries.constantCoeff rrcf_v = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact rrcf_v_coeff_0
  simp [map_add, map_mul, map_pow, map_ofNat, hv]

private theorem rrcf_lhs_factor_coeff_one :
    (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4).coeff 1 = 3 := by
  simp only [map_add]
  rw [PowerSeries.coeff_one]
  rw [coeff_one_three_mul, coeff_one_four_mul, coeff_one_two_mul]
  rw [rrcf_v_coeff_1, rrcf_v_sq_coeff_one, rrcf_v_cube_coeff_one,
      rrcf_v_fourth_coeff_one]
  norm_num

private theorem rrcf_lhs_factor_coeff_two :
    (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4).coeff 2 = 4 := by
  simp only [map_add]
  rw [PowerSeries.coeff_one]
  rw [coeff_two_three_mul, coeff_two_four_mul, coeff_two_two_mul]
  rw [rrcf_v_coeff_2, rrcf_v_sq_coeff_two, rrcf_v_cube_coeff_two,
      rrcf_v_fourth_coeff_two]
  norm_num

private theorem rrcf_lhs_factor_coeff_three :
    (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4).coeff 3 = 2 := by
  simp only [map_add]
  rw [PowerSeries.coeff_one]
  rw [coeff_three_three_mul, coeff_three_four_mul, coeff_three_two_mul]
  rw [rrcf_v_coeff_3, rrcf_v_sq_coeff_three, rrcf_v_cube_coeff_three,
      rrcf_v_fourth_coeff_three]
  norm_num

private theorem rrcf_lhs_factor_coeff_four :
    (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4).coeff 4 = 1 := by
  simp only [map_add]
  rw [PowerSeries.coeff_one]
  rw [coeff_four_three_mul, coeff_four_four_mul, coeff_four_two_mul]
  rw [rrcf_v_coeff_4, rrcf_v_sq_coeff_four, rrcf_v_cube_coeff_four,
      rrcf_v_fourth_coeff_four]
  norm_num

private theorem rrcf_lhs_factor_coeff_five :
    (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4).coeff 5 = 0 := by
  simp only [map_add]
  rw [PowerSeries.coeff_one]
  rw [coeff_five_three_mul, coeff_five_four_mul, coeff_five_two_mul]
  rw [rrcf_v_coeff_5, rrcf_v_sq_coeff_five, rrcf_v_cube_coeff_five,
      rrcf_v_fourth_coeff_five]
  norm_num

private theorem rrcf_lhs_factor_coeff_six :
    (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4).coeff 6 = -3 := by
  simp only [map_add]
  rw [PowerSeries.coeff_one]
  rw [coeff_six_three_mul, coeff_six_four_mul, coeff_six_two_mul]
  rw [rrcf_v_coeff_6, rrcf_v_sq_coeff_six, rrcf_v_cube_coeff_six,
      rrcf_v_fourth_coeff_six]
  norm_num

private theorem rrcf_lhs_factor_coeff_seven :
    (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4).coeff 7 = -8 := by
  simp only [map_add]
  rw [PowerSeries.coeff_one]
  rw [coeff_seven_three_mul, coeff_seven_four_mul, coeff_seven_two_mul]
  rw [rrcf_v_coeff_7, rrcf_v_sq_coeff_seven, rrcf_v_cube_coeff_seven,
      rrcf_v_fourth_coeff_seven]
  norm_num

private theorem rrcf_lhs_factor_coeff_eight :
    (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4).coeff 8 = -6 := by
  simp only [map_add]
  rw [PowerSeries.coeff_one]
  rw [coeff_eight_three_mul, coeff_eight_four_mul, coeff_eight_two_mul]
  rw [rrcf_v_coeff_8, rrcf_v_sq_coeff_eight, rrcf_v_cube_coeff_eight,
      rrcf_v_fourth_coeff_eight]
  norm_num

private theorem rrcf_lhs_factor_coeff_nine :
    (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4).coeff 9 = -4 := by
  simp only [map_add]
  rw [PowerSeries.coeff_one]
  rw [coeff_nine_three_mul, coeff_nine_four_mul, coeff_nine_two_mul]
  rw [rrcf_v_coeff_9, rrcf_v_sq_coeff_nine, rrcf_v_cube_coeff_nine,
      rrcf_v_fourth_coeff_nine]
  norm_num

private theorem rrcf_lhs_factor_coeff_ten :
    (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4).coeff 10 = 0 := by
  simp only [map_add]
  rw [PowerSeries.coeff_one]
  rw [coeff_ten_three_mul, coeff_ten_four_mul, coeff_ten_two_mul]
  rw [rrcf_v_coeff_10, rrcf_v_sq_coeff_ten, rrcf_v_cube_coeff_ten,
      rrcf_v_fourth_coeff_ten]
  norm_num

private theorem rrcf_rhs_factor_coeff_zero :
    (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hv : PowerSeries.constantCoeff rrcf_v = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact rrcf_v_coeff_0
  simp [map_add, map_sub, map_mul, map_pow, map_ofNat, hv]

private theorem rrcf_rhs_factor_coeff_one :
    (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4).coeff 1 = -2 := by
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_one]
  rw [coeff_one_two_mul, coeff_one_four_mul, coeff_one_three_mul]
  rw [rrcf_v_coeff_1, rrcf_v_sq_coeff_one, rrcf_v_cube_coeff_one,
      rrcf_v_fourth_coeff_one]
  norm_num

private theorem rrcf_rhs_factor_coeff_two :
    (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4).coeff 2 = 4 := by
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_one]
  rw [coeff_two_two_mul, coeff_two_four_mul, coeff_two_three_mul]
  rw [rrcf_v_coeff_2, rrcf_v_sq_coeff_two, rrcf_v_cube_coeff_two,
      rrcf_v_fourth_coeff_two]
  norm_num

private theorem rrcf_rhs_factor_coeff_three :
    (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4).coeff 3 = -3 := by
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_one]
  rw [coeff_three_two_mul, coeff_three_four_mul, coeff_three_three_mul]
  rw [rrcf_v_coeff_3, rrcf_v_sq_coeff_three, rrcf_v_cube_coeff_three,
      rrcf_v_fourth_coeff_three]
  norm_num

private theorem rrcf_rhs_factor_coeff_four :
    (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4).coeff 4 = 1 := by
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_one]
  rw [coeff_four_two_mul, coeff_four_four_mul, coeff_four_three_mul]
  rw [rrcf_v_coeff_4, rrcf_v_sq_coeff_four, rrcf_v_cube_coeff_four,
      rrcf_v_fourth_coeff_four]
  norm_num

private theorem rrcf_rhs_factor_coeff_five :
    (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4).coeff 5 = 0 := by
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_one]
  rw [coeff_five_two_mul, coeff_five_four_mul, coeff_five_three_mul]
  rw [rrcf_v_coeff_5, rrcf_v_sq_coeff_five, rrcf_v_cube_coeff_five,
      rrcf_v_fourth_coeff_five]
  norm_num

private theorem rrcf_rhs_factor_coeff_six :
    (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4).coeff 6 = 2 := by
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_one]
  rw [coeff_six_two_mul, coeff_six_four_mul, coeff_six_three_mul]
  rw [rrcf_v_coeff_6, rrcf_v_sq_coeff_six, rrcf_v_cube_coeff_six,
      rrcf_v_fourth_coeff_six]
  norm_num

private theorem rrcf_rhs_factor_coeff_seven :
    (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4).coeff 7 = -8 := by
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_one]
  rw [coeff_seven_two_mul, coeff_seven_four_mul, coeff_seven_three_mul]
  rw [rrcf_v_coeff_7, rrcf_v_sq_coeff_seven, rrcf_v_cube_coeff_seven,
      rrcf_v_fourth_coeff_seven]
  norm_num

private theorem rrcf_rhs_factor_coeff_eight :
    (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4).coeff 8 = 9 := by
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_one]
  rw [coeff_eight_two_mul, coeff_eight_four_mul, coeff_eight_three_mul]
  rw [rrcf_v_coeff_8, rrcf_v_sq_coeff_eight, rrcf_v_cube_coeff_eight,
      rrcf_v_fourth_coeff_eight]
  norm_num

private theorem rrcf_rhs_factor_coeff_nine :
    (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4).coeff 9 = -4 := by
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_one]
  rw [coeff_nine_two_mul, coeff_nine_four_mul, coeff_nine_three_mul]
  rw [rrcf_v_coeff_9, rrcf_v_sq_coeff_nine, rrcf_v_cube_coeff_nine,
      rrcf_v_fourth_coeff_nine]
  norm_num

private theorem rrcf_rhs_factor_coeff_ten :
    (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4).coeff 10 = 0 := by
  simp only [map_add, map_sub]
  rw [PowerSeries.coeff_one]
  rw [coeff_ten_two_mul, coeff_ten_four_mul, coeff_ten_three_mul]
  rw [rrcf_v_coeff_10, rrcf_v_sq_coeff_ten, rrcf_v_cube_coeff_ten,
      rrcf_v_fourth_coeff_ten]
  norm_num

/-! ## Degree-k verification stubs for Chan Theorem 11.5

Once all individual coefficient values above are proved, these degree-k
verifications reduce to arithmetic in `ℚ`. Both sides are numerically
confirmed to match through degree 10. -/

/-- Degree-1 coefficient match of Chan Theorem 11.5. -/
theorem coeff_one_chan_theorem_11_5_LHS_eq_RHS :
    (rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)).coeff 1 =
      ((PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)).coeff 1 := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_r_pow_five_coeff_zero, rrcf_lhs_factor_coeff_one,
      rrcf_r_pow_five_coeff_one, rrcf_lhs_factor_coeff_zero,
      expand_five_rrcf_r_coeff_zero, rrcf_rhs_factor_coeff_one,
      expand_five_rrcf_r_coeff_one, rrcf_rhs_factor_coeff_zero]
  norm_num

/-- Degree-2 coefficient match of Chan Theorem 11.5. -/
theorem coeff_two_chan_theorem_11_5_LHS_eq_RHS :
    (rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)).coeff 2 =
      ((PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)).coeff 2 := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) =
      {(0, 2), (1, 1), (2, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_r_pow_five_coeff_zero, rrcf_lhs_factor_coeff_two,
      rrcf_r_pow_five_coeff_one, rrcf_lhs_factor_coeff_one,
      rrcf_r_pow_five_coeff_two, rrcf_lhs_factor_coeff_zero,
      expand_five_rrcf_r_coeff_zero, rrcf_rhs_factor_coeff_two,
      expand_five_rrcf_r_coeff_one, rrcf_rhs_factor_coeff_one,
      expand_five_rrcf_r_coeff_two, rrcf_rhs_factor_coeff_zero]
  norm_num

/-- Degree-3 coefficient match of Chan Theorem 11.5. -/
theorem coeff_three_chan_theorem_11_5_LHS_eq_RHS :
    (rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)).coeff 3 =
      ((PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)).coeff 3 := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 3 : Finset (ℕ × ℕ)) =
      {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_r_pow_five_coeff_zero, rrcf_lhs_factor_coeff_three,
      rrcf_r_pow_five_coeff_one, rrcf_lhs_factor_coeff_two,
      rrcf_r_pow_five_coeff_two, rrcf_lhs_factor_coeff_one,
      rrcf_r_pow_five_coeff_three, rrcf_lhs_factor_coeff_zero,
      expand_five_rrcf_r_coeff_zero, rrcf_rhs_factor_coeff_three,
      expand_five_rrcf_r_coeff_one, rrcf_rhs_factor_coeff_two,
      expand_five_rrcf_r_coeff_two, rrcf_rhs_factor_coeff_one,
      expand_five_rrcf_r_coeff_three, rrcf_rhs_factor_coeff_zero]
  norm_num

/-- Degree-4 coefficient match of Chan Theorem 11.5. -/
theorem coeff_four_chan_theorem_11_5_LHS_eq_RHS :
    (rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)).coeff 4 =
      ((PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)).coeff 4 := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
      {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [rrcf_r_pow_five_coeff_zero, rrcf_lhs_factor_coeff_four,
      rrcf_r_pow_five_coeff_one, rrcf_lhs_factor_coeff_three,
      rrcf_r_pow_five_coeff_two, rrcf_lhs_factor_coeff_two,
      rrcf_r_pow_five_coeff_three, rrcf_lhs_factor_coeff_one,
      rrcf_r_pow_five_coeff_four, rrcf_lhs_factor_coeff_zero,
      expand_five_rrcf_r_coeff_zero, rrcf_rhs_factor_coeff_four,
      expand_five_rrcf_r_coeff_one, rrcf_rhs_factor_coeff_three,
      expand_five_rrcf_r_coeff_two, rrcf_rhs_factor_coeff_two,
      expand_five_rrcf_r_coeff_three, rrcf_rhs_factor_coeff_one,
      expand_five_rrcf_r_coeff_four, rrcf_rhs_factor_coeff_zero]
  norm_num

/-- Degree-5 coefficient match of Chan Theorem 11.5. -/
theorem coeff_five_chan_theorem_11_5_LHS_eq_RHS :
    (rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)).coeff 5 =
      ((PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)).coeff 5 := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  rw [show (Finset.antidiagonal 5 : Finset (ℕ × ℕ)) =
      {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [rrcf_r_pow_five_coeff_zero, rrcf_lhs_factor_coeff_five,
      rrcf_r_pow_five_coeff_one, rrcf_lhs_factor_coeff_four,
      rrcf_r_pow_five_coeff_two, rrcf_lhs_factor_coeff_three,
      rrcf_r_pow_five_coeff_three, rrcf_lhs_factor_coeff_two,
      rrcf_r_pow_five_coeff_four, rrcf_lhs_factor_coeff_one,
      rrcf_r_pow_five_coeff_five, rrcf_lhs_factor_coeff_zero,
      expand_five_rrcf_r_coeff_zero, rrcf_rhs_factor_coeff_five,
      expand_five_rrcf_r_coeff_one, rrcf_rhs_factor_coeff_four,
      expand_five_rrcf_r_coeff_two, rrcf_rhs_factor_coeff_three,
      expand_five_rrcf_r_coeff_three, rrcf_rhs_factor_coeff_two,
      expand_five_rrcf_r_coeff_four, rrcf_rhs_factor_coeff_one,
      expand_five_rrcf_r_coeff_five, rrcf_rhs_factor_coeff_zero]
  norm_num

/-- Degree-6 coefficient match of Chan Theorem 11.5. -/
theorem coeff_six_chan_theorem_11_5_LHS_eq_RHS :
    (rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)).coeff 6 =
      ((PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)).coeff 6 := by
  rw [coeff_mul_six, coeff_mul_six]
  rw [rrcf_r_pow_five_coeff_zero, rrcf_lhs_factor_coeff_six,
      rrcf_r_pow_five_coeff_one, rrcf_lhs_factor_coeff_five,
      rrcf_r_pow_five_coeff_two, rrcf_lhs_factor_coeff_four,
      rrcf_r_pow_five_coeff_three, rrcf_lhs_factor_coeff_three,
      rrcf_r_pow_five_coeff_four, rrcf_lhs_factor_coeff_two,
      rrcf_r_pow_five_coeff_five, rrcf_lhs_factor_coeff_one,
      rrcf_r_pow_five_coeff_six, rrcf_lhs_factor_coeff_zero,
      expand_five_rrcf_r_coeff_zero, rrcf_rhs_factor_coeff_six,
      expand_five_rrcf_r_coeff_one, rrcf_rhs_factor_coeff_five,
      expand_five_rrcf_r_coeff_two, rrcf_rhs_factor_coeff_four,
      expand_five_rrcf_r_coeff_three, rrcf_rhs_factor_coeff_three,
      expand_five_rrcf_r_coeff_four, rrcf_rhs_factor_coeff_two,
      expand_five_rrcf_r_coeff_five, rrcf_rhs_factor_coeff_one,
      expand_five_rrcf_r_coeff_six, rrcf_rhs_factor_coeff_zero]
  norm_num

/-- Degree-7 coefficient match of Chan Theorem 11.5. -/
theorem coeff_seven_chan_theorem_11_5_LHS_eq_RHS :
    (rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)).coeff 7 =
      ((PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)).coeff 7 := by
  rw [coeff_mul_seven, coeff_mul_seven]
  rw [rrcf_r_pow_five_coeff_zero, rrcf_lhs_factor_coeff_seven,
      rrcf_r_pow_five_coeff_one, rrcf_lhs_factor_coeff_six,
      rrcf_r_pow_five_coeff_two, rrcf_lhs_factor_coeff_five,
      rrcf_r_pow_five_coeff_three, rrcf_lhs_factor_coeff_four,
      rrcf_r_pow_five_coeff_four, rrcf_lhs_factor_coeff_three,
      rrcf_r_pow_five_coeff_five, rrcf_lhs_factor_coeff_two,
      rrcf_r_pow_five_coeff_six, rrcf_lhs_factor_coeff_one,
      rrcf_r_pow_five_coeff_seven, rrcf_lhs_factor_coeff_zero,
      expand_five_rrcf_r_coeff_zero, rrcf_rhs_factor_coeff_seven,
      expand_five_rrcf_r_coeff_one, rrcf_rhs_factor_coeff_six,
      expand_five_rrcf_r_coeff_two, rrcf_rhs_factor_coeff_five,
      expand_five_rrcf_r_coeff_three, rrcf_rhs_factor_coeff_four,
      expand_five_rrcf_r_coeff_four, rrcf_rhs_factor_coeff_three,
      expand_five_rrcf_r_coeff_five, rrcf_rhs_factor_coeff_two,
      expand_five_rrcf_r_coeff_six, rrcf_rhs_factor_coeff_one,
      expand_five_rrcf_r_coeff_seven, rrcf_rhs_factor_coeff_zero]
  norm_num

/-- Degree-8 coefficient match of Chan Theorem 11.5. -/
theorem coeff_eight_chan_theorem_11_5_LHS_eq_RHS :
    (rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)).coeff 8 =
      ((PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)).coeff 8 := by
  rw [coeff_mul_eight, coeff_mul_eight]
  rw [rrcf_r_pow_five_coeff_zero, rrcf_lhs_factor_coeff_eight,
      rrcf_r_pow_five_coeff_one, rrcf_lhs_factor_coeff_seven,
      rrcf_r_pow_five_coeff_two, rrcf_lhs_factor_coeff_six,
      rrcf_r_pow_five_coeff_three, rrcf_lhs_factor_coeff_five,
      rrcf_r_pow_five_coeff_four, rrcf_lhs_factor_coeff_four,
      rrcf_r_pow_five_coeff_five, rrcf_lhs_factor_coeff_three,
      rrcf_r_pow_five_coeff_six, rrcf_lhs_factor_coeff_two,
      rrcf_r_pow_five_coeff_seven, rrcf_lhs_factor_coeff_one,
      rrcf_r_pow_five_coeff_eight, rrcf_lhs_factor_coeff_zero,
      expand_five_rrcf_r_coeff_zero, rrcf_rhs_factor_coeff_eight,
      expand_five_rrcf_r_coeff_one, rrcf_rhs_factor_coeff_seven,
      expand_five_rrcf_r_coeff_two, rrcf_rhs_factor_coeff_six,
      expand_five_rrcf_r_coeff_three, rrcf_rhs_factor_coeff_five,
      expand_five_rrcf_r_coeff_four, rrcf_rhs_factor_coeff_four,
      expand_five_rrcf_r_coeff_five, rrcf_rhs_factor_coeff_three,
      expand_five_rrcf_r_coeff_six, rrcf_rhs_factor_coeff_two,
      expand_five_rrcf_r_coeff_seven, rrcf_rhs_factor_coeff_one,
      expand_five_rrcf_r_coeff_eight, rrcf_rhs_factor_coeff_zero]
  norm_num

/-- Degree-9 coefficient match of Chan Theorem 11.5. -/
theorem coeff_nine_chan_theorem_11_5_LHS_eq_RHS :
    (rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)).coeff 9 =
      ((PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)).coeff 9 := by
  rw [coeff_mul_nine, coeff_mul_nine]
  rw [rrcf_r_pow_five_coeff_zero, rrcf_lhs_factor_coeff_nine,
      rrcf_r_pow_five_coeff_one, rrcf_lhs_factor_coeff_eight,
      rrcf_r_pow_five_coeff_two, rrcf_lhs_factor_coeff_seven,
      rrcf_r_pow_five_coeff_three, rrcf_lhs_factor_coeff_six,
      rrcf_r_pow_five_coeff_four, rrcf_lhs_factor_coeff_five,
      rrcf_r_pow_five_coeff_five, rrcf_lhs_factor_coeff_four,
      rrcf_r_pow_five_coeff_six, rrcf_lhs_factor_coeff_three,
      rrcf_r_pow_five_coeff_seven, rrcf_lhs_factor_coeff_two,
      rrcf_r_pow_five_coeff_eight, rrcf_lhs_factor_coeff_one,
      rrcf_r_pow_five_coeff_nine, rrcf_lhs_factor_coeff_zero,
      expand_five_rrcf_r_coeff_zero, rrcf_rhs_factor_coeff_nine,
      expand_five_rrcf_r_coeff_one, rrcf_rhs_factor_coeff_eight,
      expand_five_rrcf_r_coeff_two, rrcf_rhs_factor_coeff_seven,
      expand_five_rrcf_r_coeff_three, rrcf_rhs_factor_coeff_six,
      expand_five_rrcf_r_coeff_four, rrcf_rhs_factor_coeff_five,
      expand_five_rrcf_r_coeff_five, rrcf_rhs_factor_coeff_four,
      expand_five_rrcf_r_coeff_six, rrcf_rhs_factor_coeff_three,
      expand_five_rrcf_r_coeff_seven, rrcf_rhs_factor_coeff_two,
      expand_five_rrcf_r_coeff_eight, rrcf_rhs_factor_coeff_one,
      expand_five_rrcf_r_coeff_nine, rrcf_rhs_factor_coeff_zero]
  norm_num

/-- Degree-10 coefficient match of Chan Theorem 11.5. -/
theorem coeff_ten_chan_theorem_11_5_LHS_eq_RHS :
    (rrcf_r ^ 5 * (1 + 3 * rrcf_v + 4 * rrcf_v^2 + 2 * rrcf_v^3 + rrcf_v^4)).coeff 10 =
      ((PowerSeries.expand 5 (by decide) rrcf_r) *
        (1 - 2 * rrcf_v + 4 * rrcf_v^2 - 3 * rrcf_v^3 + rrcf_v^4)).coeff 10 := by
  rw [coeff_mul_ten, coeff_mul_ten]
  rw [rrcf_r_pow_five_coeff_zero, rrcf_lhs_factor_coeff_ten,
      rrcf_r_pow_five_coeff_one, rrcf_lhs_factor_coeff_nine,
      rrcf_r_pow_five_coeff_two, rrcf_lhs_factor_coeff_eight,
      rrcf_r_pow_five_coeff_three, rrcf_lhs_factor_coeff_seven,
      rrcf_r_pow_five_coeff_four, rrcf_lhs_factor_coeff_six,
      rrcf_r_pow_five_coeff_five, rrcf_lhs_factor_coeff_five,
      rrcf_r_pow_five_coeff_six, rrcf_lhs_factor_coeff_four,
      rrcf_r_pow_five_coeff_seven, rrcf_lhs_factor_coeff_three,
      rrcf_r_pow_five_coeff_eight, rrcf_lhs_factor_coeff_two,
      rrcf_r_pow_five_coeff_nine, rrcf_lhs_factor_coeff_one,
      rrcf_r_pow_five_coeff_ten, rrcf_lhs_factor_coeff_zero,
      expand_five_rrcf_r_coeff_zero, rrcf_rhs_factor_coeff_ten,
      expand_five_rrcf_r_coeff_one, rrcf_rhs_factor_coeff_nine,
      expand_five_rrcf_r_coeff_two, rrcf_rhs_factor_coeff_eight,
      expand_five_rrcf_r_coeff_three, rrcf_rhs_factor_coeff_seven,
      expand_five_rrcf_r_coeff_four, rrcf_rhs_factor_coeff_six,
      expand_five_rrcf_r_coeff_five, rrcf_rhs_factor_coeff_five,
      expand_five_rrcf_r_coeff_six, rrcf_rhs_factor_coeff_four,
      expand_five_rrcf_r_coeff_seven, rrcf_rhs_factor_coeff_three,
      expand_five_rrcf_r_coeff_eight, rrcf_rhs_factor_coeff_two,
      expand_five_rrcf_r_coeff_nine, rrcf_rhs_factor_coeff_one,
      expand_five_rrcf_r_coeff_ten, rrcf_rhs_factor_coeff_zero]
  norm_num

/-! ## Consolidated coefficient-match interfaces for Chan Theorem 11.5 -/

/-- Chan Theorem 11.5, verified coefficientwise through degree `10`. -/
theorem coeff_chanTheorem115_eq_of_le_ten {k : ℕ} (hk : k ≤ 10) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k := by
  interval_cases k <;> simp [chanTheorem115LHS, chanTheorem115RHS,
    QseriesFormalization.Pending.Ch13RRCF.coeff_zero_chan_theorem_11_5_LHS_eq_RHS,
    coeff_one_chan_theorem_11_5_LHS_eq_RHS,
    coeff_two_chan_theorem_11_5_LHS_eq_RHS,
    coeff_three_chan_theorem_11_5_LHS_eq_RHS,
    coeff_four_chan_theorem_11_5_LHS_eq_RHS,
    coeff_five_chan_theorem_11_5_LHS_eq_RHS,
    coeff_six_chan_theorem_11_5_LHS_eq_RHS,
    coeff_seven_chan_theorem_11_5_LHS_eq_RHS,
    coeff_eight_chan_theorem_11_5_LHS_eq_RHS,
    coeff_nine_chan_theorem_11_5_LHS_eq_RHS,
    coeff_ten_chan_theorem_11_5_LHS_eq_RHS]

/-- Finite-index form of the degree-`0..10` coefficient verification. -/
theorem coeff_chanTheorem115_eq_fin_eleven (k : Fin 11) :
    chanTheorem115LHS.coeff k.1 = chanTheorem115RHS.coeff k.1 :=
  coeff_chanTheorem115_eq_of_le_ten (by omega)

/-- The formal residual is definitionally the difference of the two sides. -/
theorem chanTheorem115ResidualPS_eq_sub :
    chanTheorem115ResidualPS = chanTheorem115LHS - chanTheorem115RHS :=
  rfl

/-- Coefficient form of the named formal residual. -/
theorem coeff_chanTheorem115ResidualPS_eq_sub (k : ℕ) :
    chanTheorem115ResidualPS.coeff k =
      chanTheorem115LHS.coeff k - chanTheorem115RHS.coeff k := by
  rw [chanTheorem115ResidualPS_eq_sub, map_sub]

/-- Vanishing of a Chan 11.5 residual coefficient is exactly coefficient
agreement at that degree. -/
theorem coeff_chanTheorem115ResidualPS_eq_zero_iff_coeff_eq (k : ℕ) :
    chanTheorem115ResidualPS.coeff k = 0 ↔
      chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k := by
  rw [coeff_chanTheorem115ResidualPS_eq_sub, sub_eq_zero]

/-- A truncated Chan 11.5 residual is zero iff the two truncated sides agree. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_iff_eq (N : ℕ) :
    PowerSeries.trunc N chanTheorem115ResidualPS = 0 ↔
      PowerSeries.trunc N chanTheorem115LHS =
        PowerSeries.trunc N chanTheorem115RHS := by
  constructor
  · intro h
    ext k
    by_cases hk : k < N
    · have hres : chanTheorem115ResidualPS.coeff k = 0 := by
        have hcoeff := congrArg (fun p => p.coeff k) h
        simpa [PowerSeries.coeff_trunc, hk] using hcoeff
      have hcoeff :
          chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
        (coeff_chanTheorem115ResidualPS_eq_zero_iff_coeff_eq k).1 hres
      rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hk, if_pos hk]
      exact hcoeff
    · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hk, if_neg hk]
  · intro h
    ext k
    by_cases hk : k < N
    · have hcoeff :
          chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k := by
        have hcoeff' := congrArg (fun p => p.coeff k) h
        simpa [PowerSeries.coeff_trunc, hk] using hcoeff'
      have hres : chanTheorem115ResidualPS.coeff k = 0 :=
        (coeff_chanTheorem115ResidualPS_eq_zero_iff_coeff_eq k).2 hcoeff
      rw [PowerSeries.coeff_trunc, if_pos hk, hres]
      simp
    · rw [PowerSeries.coeff_trunc, if_neg hk]
      simp

/-- Truncated equality of the two Chan 11.5 sides is equivalent to
coefficientwise equality below the truncation length. -/
theorem trunc_chanTheorem115LHS_eq_RHS_iff_coeff_eq (N : ℕ) :
    PowerSeries.trunc N chanTheorem115LHS =
      PowerSeries.trunc N chanTheorem115RHS ↔
      ∀ k : ℕ, k < N →
        chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k := by
  constructor
  · intro h k hk
    have hcoeff := congrArg (fun p => p.coeff k) h
    simpa [PowerSeries.coeff_trunc, hk] using hcoeff
  · intro h
    ext k
    by_cases hk : k < N
    · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hk, if_pos hk]
      exact h k hk
    · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hk, if_neg hk]

/-- A truncated Chan 11.5 residual is zero iff the two sides agree
coefficientwise below the truncation length. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_iff_coeff_eq (N : ℕ) :
    PowerSeries.trunc N chanTheorem115ResidualPS = 0 ↔
      ∀ k : ℕ, k < N →
        chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k := by
  rw [trunc_chanTheorem115ResidualPS_eq_zero_iff_eq,
    trunc_chanTheorem115LHS_eq_RHS_iff_coeff_eq]

/-- Extract coefficient agreement below `N` from a zero truncated Chan 11.5
residual. -/
theorem coeff_chanTheorem115_eq_of_trunc_residualPS_eq_zero
    {N k : ℕ} (h : PowerSeries.trunc N chanTheorem115ResidualPS = 0)
    (hk : k < N) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
  (trunc_chanTheorem115ResidualPS_eq_zero_iff_coeff_eq N).1 h k hk

/-- Build a zero truncated Chan 11.5 residual from coefficient agreement below
the truncation length. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_of_coeff_eq
    {N : ℕ}
    (h : ∀ k : ℕ, k < N →
      chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k) :
    PowerSeries.trunc N chanTheorem115ResidualPS = 0 :=
  (trunc_chanTheorem115ResidualPS_eq_zero_iff_coeff_eq N).2 h

/-- A truncated Chan 11.5 residual is zero iff its coefficients vanish below
the truncation length. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_iff_coeff_zero (N : ℕ) :
    PowerSeries.trunc N chanTheorem115ResidualPS = 0 ↔
      ∀ k : ℕ, k < N → chanTheorem115ResidualPS.coeff k = 0 := by
  constructor
  · intro h k hk
    have hcoeff := congrArg (fun p => p.coeff k) h
    simpa [PowerSeries.coeff_trunc, hk] using hcoeff
  · intro h
    ext k
    by_cases hk : k < N
    · rw [PowerSeries.coeff_trunc, if_pos hk, h k hk]
      simp
    · rw [PowerSeries.coeff_trunc, if_neg hk]
      simp

/-- Extract Chan 11.5 residual coefficient vanishing below `N` from a zero
truncated residual. -/
theorem coeff_chanTheorem115ResidualPS_eq_zero_of_trunc_eq_zero
    {N k : ℕ} (h : PowerSeries.trunc N chanTheorem115ResidualPS = 0)
    (hk : k < N) :
    chanTheorem115ResidualPS.coeff k = 0 :=
  (trunc_chanTheorem115ResidualPS_eq_zero_iff_coeff_zero N).1 h k hk

/-- Build a zero truncated Chan 11.5 residual from residual coefficient
vanishing below the truncation length. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_of_coeff_zero
    {N : ℕ}
    (h : ∀ k : ℕ, k < N → chanTheorem115ResidualPS.coeff k = 0) :
    PowerSeries.trunc N chanTheorem115ResidualPS = 0 :=
  (trunc_chanTheorem115ResidualPS_eq_zero_iff_coeff_zero N).2 h

/-- Difference form of the Chan Theorem 11.5 coefficient verification through
degree `10`. -/
theorem coeff_chanTheorem115_sub_eq_zero_of_le_ten {k : ℕ} (hk : k ≤ 10) :
    (chanTheorem115LHS - chanTheorem115RHS).coeff k = 0 := by
  rw [map_sub, coeff_chanTheorem115_eq_of_le_ten hk]
  simp

/-- Residual-series coefficient form of the Chan Theorem 11.5 verification
through degree `10`. -/
theorem coeff_chanTheorem115ResidualPS_eq_zero_of_le_ten {k : ℕ} (hk : k ≤ 10) :
    chanTheorem115ResidualPS.coeff k = 0 := by
  rw [chanTheorem115ResidualPS_eq_sub]
  exact coeff_chanTheorem115_sub_eq_zero_of_le_ten hk

/-- Finite-index residual-series coefficient form through degree `10`. -/
theorem coeff_chanTheorem115ResidualPS_eq_zero_fin_eleven (k : Fin 11) :
    chanTheorem115ResidualPS.coeff k.1 = 0 :=
  coeff_chanTheorem115ResidualPS_eq_zero_of_le_ten (by omega)

/-- Strict-bound form of the Chan Theorem 11.5 coefficient verification
through degree `10`. -/
theorem coeff_chanTheorem115_eq_of_lt_eleven {k : ℕ} (hk : k < 11) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
  coeff_chanTheorem115_eq_of_le_ten (by omega)

/-- Symmetric strict-bound form of the Chan Theorem 11.5 coefficient
verification through degree `10`. -/
theorem coeff_chanTheorem115_eq_symm_of_lt_eleven {k : ℕ} (hk : k < 11) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
  (coeff_chanTheorem115_eq_of_lt_eleven hk).symm

/-- Uniform finite-index form for any truncation length at most `11`. -/
theorem coeff_chanTheorem115_eq_fin_of_le_eleven
    {N : ℕ} (hN : N ≤ 11) (k : Fin N) :
    chanTheorem115LHS.coeff k.1 = chanTheorem115RHS.coeff k.1 :=
  coeff_chanTheorem115_eq_of_lt_eleven (by omega)

/-- Symmetric uniform finite-index form for any truncation length at most
`11`. -/
theorem coeff_chanTheorem115_eq_fin_symm_of_le_eleven
    {N : ℕ} (hN : N ≤ 11) (k : Fin N) :
    chanTheorem115RHS.coeff k.1 = chanTheorem115LHS.coeff k.1 :=
  coeff_chanTheorem115_eq_symm_of_lt_eleven (by omega)

/-- Strict-bound residual-series coefficient form through degree `10`. -/
theorem coeff_chanTheorem115ResidualPS_eq_zero_of_lt_eleven
    {k : ℕ} (hk : k < 11) :
    chanTheorem115ResidualPS.coeff k = 0 :=
  coeff_chanTheorem115ResidualPS_eq_zero_of_le_ten (by omega)

/-- Uniform finite-index residual-series coefficient form for any truncation
length at most `11`. -/
theorem coeff_chanTheorem115ResidualPS_eq_zero_fin_of_le_eleven
    {N : ℕ} (hN : N ≤ 11) (k : Fin N) :
    chanTheorem115ResidualPS.coeff k.1 = 0 :=
  coeff_chanTheorem115ResidualPS_eq_zero_of_lt_eleven (by omega)

/-- Reverse-difference form of the Chan Theorem 11.5 coefficient verification
through degree `10`. -/
theorem coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_le_ten {k : ℕ} (hk : k ≤ 10) :
    (chanTheorem115RHS - chanTheorem115LHS).coeff k = 0 := by
  rw [map_sub, ← coeff_chanTheorem115_eq_of_le_ten hk]
  simp

/-- Chan Theorem 11.5 holds after truncating both sides through degree `10`. -/
theorem trunc_chanTheorem115LHS_eq_RHS_through_ten :
    PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS := by
  ext k
  by_cases hk : k < 11
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hk, if_pos hk]
    exact coeff_chanTheorem115_eq_of_le_ten (by omega)
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hk, if_neg hk]

/-- The truncated difference of the two sides of Chan Theorem 11.5 is zero
through degree `10`. -/
theorem trunc_chanTheorem115_sub_eq_zero_through_ten :
    PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0 := by
  ext k
  by_cases hk : k < 11
  · rw [PowerSeries.coeff_trunc, if_pos hk,
      coeff_chanTheorem115_sub_eq_zero_of_le_ten (by omega)]
    simp
  · rw [PowerSeries.coeff_trunc, if_neg hk]
    simp

/-- The named formal residual truncates to zero through degree `10`. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_through_ten :
    PowerSeries.trunc 11 chanTheorem115ResidualPS = 0 := by
  rw [chanTheorem115ResidualPS_eq_sub]
  exact trunc_chanTheorem115_sub_eq_zero_through_ten

/-- Every truncation of the named formal residual of length at most `11` is
zero. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_of_le_eleven
    (N : ℕ) (hN : N ≤ 11) :
    PowerSeries.trunc N chanTheorem115ResidualPS = 0 := by
  ext k
  by_cases hk : k < N
  · rw [PowerSeries.coeff_trunc, if_pos hk,
      coeff_chanTheorem115ResidualPS_eq_zero_of_lt_eleven (by omega)]
    simp
  · rw [PowerSeries.coeff_trunc, if_neg hk]
    simp

/-- Chan Theorem 11.5 holds after any truncation length at most `11`. -/
theorem trunc_chanTheorem115LHS_eq_RHS_of_le_eleven
    (N : ℕ) (hN : N ≤ 11) :
    PowerSeries.trunc N chanTheorem115LHS =
      PowerSeries.trunc N chanTheorem115RHS :=
  (trunc_chanTheorem115ResidualPS_eq_zero_iff_eq N).1
    (trunc_chanTheorem115ResidualPS_eq_zero_of_le_eleven N hN)

/-- X-adic form of the residual verification through degree `10`. -/
theorem X_pow_eleven_dvd_chanTheorem115ResidualPS :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  exact coeff_chanTheorem115ResidualPS_eq_zero_of_lt_eleven hk

/-- X-adic divisibility of the Chan 11.5 residual is equivalent to vanishing of
its coefficients below degree `11`. -/
theorem X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_coeff_zero :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS ↔
      ∀ k : ℕ, k < 11 → chanTheorem115ResidualPS.coeff k = 0 := by
  rw [PowerSeries.X_pow_dvd_iff]

/-- X-adic divisibility of the Chan 11.5 residual is equivalent to its
truncation through degree `10` being zero. -/
theorem X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_trunc_eq_zero :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS ↔
      PowerSeries.trunc 11 chanTheorem115ResidualPS = 0 := by
  rw [X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_coeff_zero,
    trunc_chanTheorem115ResidualPS_eq_zero_iff_coeff_zero 11]

/-- Extract low-degree coefficient vanishing from X-adic divisibility of the
Chan 11.5 residual. -/
theorem coeff_chanTheorem115ResidualPS_eq_zero_of_X_pow_eleven_dvd
    {k : ℕ}
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS)
    (hk : k < 11) :
    chanTheorem115ResidualPS.coeff k = 0 :=
  (X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_coeff_zero.1 h) k hk

/-- Build X-adic divisibility of the Chan 11.5 residual from low-degree
coefficient vanishing. -/
theorem X_pow_eleven_dvd_chanTheorem115ResidualPS_of_coeff_zero
    (h : ∀ k : ℕ, k < 11 → chanTheorem115ResidualPS.coeff k = 0) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS :=
  X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_coeff_zero.2 h

/-- A zero truncation through degree `10` gives the corresponding X-adic
divisibility of the Chan 11.5 residual. -/
theorem X_pow_eleven_dvd_chanTheorem115ResidualPS_of_trunc_eq_zero
    (h : PowerSeries.trunc 11 chanTheorem115ResidualPS = 0) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS :=
  X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_trunc_eq_zero.2 h

/-- X-adic divisibility of the Chan 11.5 residual gives zero truncation through
degree `10`. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_of_X_pow_eleven_dvd
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS) :
    PowerSeries.trunc 11 chanTheorem115ResidualPS = 0 :=
  X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_trunc_eq_zero.1 h

/-- X-adic divisibility of the Chan 11.5 residual gives coefficient agreement
below degree `11`. -/
theorem coeff_chanTheorem115_eq_of_X_pow_eleven_dvd_residualPS
    {k : ℕ}
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS)
    (hk : k < 11) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
  (coeff_chanTheorem115ResidualPS_eq_zero_iff_coeff_eq k).1
    (coeff_chanTheorem115ResidualPS_eq_zero_of_X_pow_eleven_dvd h hk)

/-- X-adic divisibility of the Chan 11.5 residual gives truncation equality
through degree `10`. -/
theorem trunc_chanTheorem115LHS_eq_RHS_of_X_pow_eleven_dvd_residualPS
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS) :
    PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS :=
  (trunc_chanTheorem115ResidualPS_eq_zero_iff_eq 11).1
    (trunc_chanTheorem115ResidualPS_eq_zero_of_X_pow_eleven_dvd h)

/-- Low-degree coefficient agreement gives X-adic divisibility of the Chan 11.5
residual. -/
theorem X_pow_eleven_dvd_chanTheorem115ResidualPS_of_coeff_eq
    (h : ∀ k : ℕ, k < 11 →
      chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS :=
  X_pow_eleven_dvd_chanTheorem115ResidualPS_of_coeff_zero
    (fun k hk => (coeff_chanTheorem115ResidualPS_eq_zero_iff_coeff_eq k).2 (h k hk))

/-- The proved X-adic residual divisibility recovers coefficient agreement
through degree `10`. -/
theorem coeff_chanTheorem115_eq_of_lt_eleven_via_X_pow_eleven_dvd
    {k : ℕ} (hk : k < 11) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
  coeff_chanTheorem115_eq_of_X_pow_eleven_dvd_residualPS
    X_pow_eleven_dvd_chanTheorem115ResidualPS hk

/-- The proved X-adic residual divisibility recovers truncation equality
through degree `10`. -/
theorem trunc_chanTheorem115LHS_eq_RHS_through_ten_via_X_pow_eleven_dvd :
    PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS :=
  trunc_chanTheorem115LHS_eq_RHS_of_X_pow_eleven_dvd_residualPS
    X_pow_eleven_dvd_chanTheorem115ResidualPS

/-- The proved X-adic residual divisibility recovers the through-degree-`10`
zero truncation. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_through_ten_via_X_pow_eleven_dvd :
    PowerSeries.trunc 11 chanTheorem115ResidualPS = 0 :=
  trunc_chanTheorem115ResidualPS_eq_zero_of_X_pow_eleven_dvd
    X_pow_eleven_dvd_chanTheorem115ResidualPS

/-- If the formal residual has a nonzero coefficient, it must occur at degree
at least `11`. -/
theorem eleven_le_of_coeff_chanTheorem115ResidualPS_ne_zero
    {k : ℕ} (hk : chanTheorem115ResidualPS.coeff k ≠ 0) :
    11 ≤ k := by
  by_contra hlt
  push_neg at hlt
  exact hk (coeff_chanTheorem115ResidualPS_eq_zero_of_lt_eleven hlt)

/-- The named formal residual vanishes iff the two sides of Chan Theorem 11.5
are equal as formal power series. -/
theorem chanTheorem115ResidualPS_eq_zero_iff :
    chanTheorem115ResidualPS = 0 ↔ chanTheorem115LHS = chanTheorem115RHS := by
  rw [chanTheorem115ResidualPS_eq_sub, sub_eq_zero]

/-- Vanishing of the named formal residual gives the formal-power-series
identity. -/
theorem chanTheorem115LHS_eq_RHS_of_residualPS_eq_zero
    (h : chanTheorem115ResidualPS = 0) :
    chanTheorem115LHS = chanTheorem115RHS :=
  chanTheorem115ResidualPS_eq_zero_iff.1 h

/-- Vanishing of the named formal residual also gives the identity with sides
swapped. -/
theorem chanTheorem115RHS_eq_LHS_of_residualPS_eq_zero
    (h : chanTheorem115ResidualPS = 0) :
    chanTheorem115RHS = chanTheorem115LHS :=
  (chanTheorem115ResidualPS_eq_zero_iff.1 h).symm

/-- Equality of the two Chan 11.5 sides gives vanishing of the named formal
residual. -/
theorem chanTheorem115ResidualPS_eq_zero_of_LHS_eq_RHS
    (h : chanTheorem115LHS = chanTheorem115RHS) :
    chanTheorem115ResidualPS = 0 :=
  chanTheorem115ResidualPS_eq_zero_iff.2 h

/-- Equality of the two Chan 11.5 sides in reverse order also gives vanishing
of the named formal residual. -/
theorem chanTheorem115ResidualPS_eq_zero_of_RHS_eq_LHS
    (h : chanTheorem115RHS = chanTheorem115LHS) :
    chanTheorem115ResidualPS = 0 :=
  chanTheorem115ResidualPS_eq_zero_of_LHS_eq_RHS h.symm

/-- Equality of the two sides of Chan Theorem 11.5 is equivalent to
coefficientwise equality. -/
theorem chanTheorem115LHS_eq_RHS_iff_coeff_eq :
    chanTheorem115LHS = chanTheorem115RHS ↔
      ∀ k : ℕ, chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k := by
  constructor
  · intro h k
    rw [h]
  · intro h
    ext k
    exact h k

/-- The named formal residual vanishes iff all coefficients of the two sides
agree. -/
theorem chanTheorem115ResidualPS_eq_zero_iff_coeff_eq :
    chanTheorem115ResidualPS = 0 ↔
      ∀ k : ℕ, chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k := by
  rw [chanTheorem115ResidualPS_eq_zero_iff,
    chanTheorem115LHS_eq_RHS_iff_coeff_eq]

/-- Coefficientwise equality of the two Chan 11.5 sides gives vanishing of the
named formal residual. -/
theorem chanTheorem115ResidualPS_eq_zero_of_coeff_eq
    (h : ∀ k : ℕ, chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k) :
    chanTheorem115ResidualPS = 0 :=
  chanTheorem115ResidualPS_eq_zero_iff_coeff_eq.2 h

/-- Vanishing of the named formal residual gives coefficientwise equality of
the two Chan 11.5 sides. -/
theorem coeff_chanTheorem115_eq_of_residualPS_eq_zero
    (h : chanTheorem115ResidualPS = 0) (k : ℕ) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
  chanTheorem115ResidualPS_eq_zero_iff_coeff_eq.1 h k

/-- Vanishing of the named formal residual gives coefficientwise equality in
reverse order. -/
theorem coeff_chanTheorem115RHS_eq_LHS_of_residualPS_eq_zero
    (h : chanTheorem115ResidualPS = 0) (k : ℕ) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
  (coeff_chanTheorem115_eq_of_residualPS_eq_zero h k).symm

/-- Coefficientwise equality in reverse order also gives vanishing of the named
formal residual. -/
theorem chanTheorem115ResidualPS_eq_zero_of_coeff_eq_symm
    (h : ∀ k : ℕ, chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k) :
    chanTheorem115ResidualPS = 0 :=
  chanTheorem115ResidualPS_eq_zero_of_coeff_eq (fun k => (h k).symm)

/-- The named reverse formal residual is definitionally the reverse
difference of the two sides. -/
theorem chanTheorem115ReverseResidualPS_eq_sub :
    chanTheorem115ReverseResidualPS = chanTheorem115RHS - chanTheorem115LHS :=
  rfl

/-- Coefficient form of the named reverse formal residual. -/
theorem coeff_chanTheorem115ReverseResidualPS_eq_sub (k : ℕ) :
    chanTheorem115ReverseResidualPS.coeff k =
      chanTheorem115RHS.coeff k - chanTheorem115LHS.coeff k := by
  rw [chanTheorem115ReverseResidualPS_eq_sub, map_sub]

/-- Vanishing of a Chan 11.5 reverse residual coefficient is exactly coefficient
agreement at that degree, with the sides swapped. -/
theorem coeff_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_eq (k : ℕ) :
    chanTheorem115ReverseResidualPS.coeff k = 0 ↔
      chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k := by
  rw [coeff_chanTheorem115ReverseResidualPS_eq_sub, sub_eq_zero]

/-- A truncated Chan 11.5 reverse residual is zero iff the two truncated sides
agree in reverse order. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_eq (N : ℕ) :
    PowerSeries.trunc N chanTheorem115ReverseResidualPS = 0 ↔
      PowerSeries.trunc N chanTheorem115RHS =
        PowerSeries.trunc N chanTheorem115LHS := by
  constructor
  · intro h
    ext k
    by_cases hk : k < N
    · have hres : chanTheorem115ReverseResidualPS.coeff k = 0 := by
        have hcoeff := congrArg (fun p => p.coeff k) h
        simpa [PowerSeries.coeff_trunc, hk] using hcoeff
      have hcoeff :
          chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
        (coeff_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_eq k).1 hres
      rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hk, if_pos hk]
      exact hcoeff
    · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hk, if_neg hk]
  · intro h
    ext k
    by_cases hk : k < N
    · have hcoeff :
          chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k := by
        have hcoeff' := congrArg (fun p => p.coeff k) h
        simpa [PowerSeries.coeff_trunc, hk] using hcoeff'
      have hres : chanTheorem115ReverseResidualPS.coeff k = 0 :=
        (coeff_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_eq k).2 hcoeff
      rw [PowerSeries.coeff_trunc, if_pos hk, hres]
      simp
    · rw [PowerSeries.coeff_trunc, if_neg hk]
      simp

/-- Truncated equality of the two Chan 11.5 sides in reverse order is
equivalent to coefficientwise equality below the truncation length. -/
theorem trunc_chanTheorem115RHS_eq_LHS_iff_coeff_eq (N : ℕ) :
    PowerSeries.trunc N chanTheorem115RHS =
      PowerSeries.trunc N chanTheorem115LHS ↔
      ∀ k : ℕ, k < N →
        chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k := by
  constructor
  · intro h k hk
    have hcoeff := congrArg (fun p => p.coeff k) h
    simpa [PowerSeries.coeff_trunc, hk] using hcoeff
  · intro h
    ext k
    by_cases hk : k < N
    · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hk, if_pos hk]
      exact h k hk
    · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hk, if_neg hk]

/-- A truncated Chan 11.5 reverse residual is zero iff the two sides agree
coefficientwise below the truncation length, with the sides swapped. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_eq (N : ℕ) :
    PowerSeries.trunc N chanTheorem115ReverseResidualPS = 0 ↔
      ∀ k : ℕ, k < N →
        chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k := by
  rw [trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_eq,
    trunc_chanTheorem115RHS_eq_LHS_iff_coeff_eq]

/-- Extract reverse coefficient agreement below `N` from a zero truncated Chan
11.5 reverse residual. -/
theorem coeff_chanTheorem115_symm_eq_of_trunc_reverseResidualPS_eq_zero
    {N k : ℕ} (h : PowerSeries.trunc N chanTheorem115ReverseResidualPS = 0)
    (hk : k < N) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
  (trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_eq N).1 h k hk

/-- Build a zero truncated Chan 11.5 reverse residual from reverse coefficient
agreement below the truncation length. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_of_coeff_eq
    {N : ℕ}
    (h : ∀ k : ℕ, k < N →
      chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k) :
    PowerSeries.trunc N chanTheorem115ReverseResidualPS = 0 :=
  (trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_eq N).2 h

/-- A truncated Chan 11.5 reverse residual is zero iff its coefficients vanish
below the truncation length. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_zero (N : ℕ) :
    PowerSeries.trunc N chanTheorem115ReverseResidualPS = 0 ↔
      ∀ k : ℕ, k < N → chanTheorem115ReverseResidualPS.coeff k = 0 := by
  constructor
  · intro h k hk
    have hcoeff := congrArg (fun p => p.coeff k) h
    simpa [PowerSeries.coeff_trunc, hk] using hcoeff
  · intro h
    ext k
    by_cases hk : k < N
    · rw [PowerSeries.coeff_trunc, if_pos hk, h k hk]
      simp
    · rw [PowerSeries.coeff_trunc, if_neg hk]
      simp

/-- Extract reverse residual coefficient vanishing below `N` from a zero
truncated Chan 11.5 reverse residual. -/
theorem coeff_chanTheorem115ReverseResidualPS_eq_zero_of_trunc_eq_zero
    {N k : ℕ} (h : PowerSeries.trunc N chanTheorem115ReverseResidualPS = 0)
    (hk : k < N) :
    chanTheorem115ReverseResidualPS.coeff k = 0 :=
  (trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_zero N).1 h k hk

/-- Build a zero truncated Chan 11.5 reverse residual from reverse residual
coefficient vanishing below the truncation length. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_of_coeff_zero
    {N : ℕ}
    (h : ∀ k : ℕ, k < N → chanTheorem115ReverseResidualPS.coeff k = 0) :
    PowerSeries.trunc N chanTheorem115ReverseResidualPS = 0 :=
  (trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_zero N).2 h

/-- The reverse residual is the negative of the forward residual. -/
theorem chanTheorem115ReverseResidualPS_eq_neg_residualPS :
    chanTheorem115ReverseResidualPS = -chanTheorem115ResidualPS := by
  rw [chanTheorem115ReverseResidualPS_eq_sub, chanTheorem115ResidualPS_eq_sub]
  ring

/-- The forward residual is the negative of the reverse residual. -/
theorem chanTheorem115ResidualPS_eq_neg_reverseResidualPS :
    chanTheorem115ResidualPS = -chanTheorem115ReverseResidualPS := by
  rw [chanTheorem115ReverseResidualPS_eq_neg_residualPS]
  simp

/-- The forward and reverse Chan 11.5 residuals add to zero. -/
theorem chanTheorem115ResidualPS_add_reverseResidualPS_eq_zero :
    chanTheorem115ResidualPS + chanTheorem115ReverseResidualPS = 0 := by
  rw [chanTheorem115ReverseResidualPS_eq_neg_residualPS]
  simp

/-- The reverse and forward Chan 11.5 residuals add to zero. -/
theorem chanTheorem115ReverseResidualPS_add_residualPS_eq_zero :
    chanTheorem115ReverseResidualPS + chanTheorem115ResidualPS = 0 := by
  rw [chanTheorem115ReverseResidualPS_eq_neg_residualPS]
  simp

/-- Coefficient relation between the reverse and forward Chan 11.5 residuals. -/
theorem coeff_chanTheorem115ReverseResidualPS_eq_neg_residualPS (k : ℕ) :
    chanTheorem115ReverseResidualPS.coeff k =
      -chanTheorem115ResidualPS.coeff k := by
  rw [chanTheorem115ReverseResidualPS_eq_neg_residualPS, map_neg]

/-- Coefficient relation between the forward and reverse Chan 11.5 residuals. -/
theorem coeff_chanTheorem115ResidualPS_eq_neg_reverseResidualPS (k : ℕ) :
    chanTheorem115ResidualPS.coeff k =
      -chanTheorem115ReverseResidualPS.coeff k := by
  rw [chanTheorem115ResidualPS_eq_neg_reverseResidualPS, map_neg]

/-- The named reverse formal residual vanishes iff the two sides of Chan
Theorem 11.5 are equal in the reverse order. -/
theorem chanTheorem115ReverseResidualPS_eq_zero_iff :
    chanTheorem115ReverseResidualPS = 0 ↔
      chanTheorem115RHS = chanTheorem115LHS := by
  rw [chanTheorem115ReverseResidualPS_eq_sub, sub_eq_zero]

/-- Vanishing of the named reverse formal residual gives the formal-power-series
identity. -/
theorem chanTheorem115LHS_eq_RHS_of_reverseResidualPS_eq_zero
    (h : chanTheorem115ReverseResidualPS = 0) :
    chanTheorem115LHS = chanTheorem115RHS :=
  (chanTheorem115ReverseResidualPS_eq_zero_iff.1 h).symm

/-- Vanishing of the named reverse formal residual gives the identity in
reverse order. -/
theorem chanTheorem115RHS_eq_LHS_of_reverseResidualPS_eq_zero
    (h : chanTheorem115ReverseResidualPS = 0) :
    chanTheorem115RHS = chanTheorem115LHS :=
  chanTheorem115ReverseResidualPS_eq_zero_iff.1 h

/-- Equality of the two Chan 11.5 sides in reverse order gives vanishing of
the named reverse formal residual. -/
theorem chanTheorem115ReverseResidualPS_eq_zero_of_RHS_eq_LHS
    (h : chanTheorem115RHS = chanTheorem115LHS) :
    chanTheorem115ReverseResidualPS = 0 :=
  chanTheorem115ReverseResidualPS_eq_zero_iff.2 h

/-- Equality of the two Chan 11.5 sides also gives vanishing of the named
reverse formal residual. -/
theorem chanTheorem115ReverseResidualPS_eq_zero_of_LHS_eq_RHS
    (h : chanTheorem115LHS = chanTheorem115RHS) :
    chanTheorem115ReverseResidualPS = 0 :=
  chanTheorem115ReverseResidualPS_eq_zero_of_RHS_eq_LHS h.symm

/-- Equality of the two sides of Chan Theorem 11.5 in reverse order is
equivalent to coefficientwise equality. -/
theorem chanTheorem115RHS_eq_LHS_iff_coeff_eq :
    chanTheorem115RHS = chanTheorem115LHS ↔
      ∀ k : ℕ, chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k := by
  constructor
  · intro h k
    rw [h]
  · intro h
    ext k
    exact h k

/-- The named reverse formal residual vanishes iff all coefficients of the two
sides agree in reverse order. -/
theorem chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_eq :
    chanTheorem115ReverseResidualPS = 0 ↔
      ∀ k : ℕ, chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k := by
  rw [chanTheorem115ReverseResidualPS_eq_zero_iff,
    chanTheorem115RHS_eq_LHS_iff_coeff_eq]

/-- Coefficientwise equality in reverse order gives vanishing of the named
reverse formal residual. -/
theorem chanTheorem115ReverseResidualPS_eq_zero_of_coeff_eq
    (h : ∀ k : ℕ, chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k) :
    chanTheorem115ReverseResidualPS = 0 :=
  chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_eq.2 h

/-- Vanishing of the named reverse formal residual gives coefficientwise
equality in reverse order. -/
theorem coeff_chanTheorem115RHS_eq_LHS_of_reverseResidualPS_eq_zero
    (h : chanTheorem115ReverseResidualPS = 0) (k : ℕ) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
  chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_eq.1 h k

/-- Vanishing of the named reverse formal residual gives coefficientwise
equality in the forward order. -/
theorem coeff_chanTheorem115_eq_of_reverseResidualPS_eq_zero
    (h : chanTheorem115ReverseResidualPS = 0) (k : ℕ) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
  (coeff_chanTheorem115RHS_eq_LHS_of_reverseResidualPS_eq_zero h k).symm

/-- Coefficientwise equality in the forward order also gives vanishing of the
named reverse formal residual. -/
theorem chanTheorem115ReverseResidualPS_eq_zero_of_coeff_eq_symm
    (h : ∀ k : ℕ, chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k) :
    chanTheorem115ReverseResidualPS = 0 :=
  chanTheorem115ReverseResidualPS_eq_zero_of_coeff_eq (fun k => (h k).symm)

/-- The forward residual vanishes iff the reverse residual vanishes. -/
theorem chanTheorem115ResidualPS_eq_zero_iff_reverseResidualPS_eq_zero :
    chanTheorem115ResidualPS = 0 ↔ chanTheorem115ReverseResidualPS = 0 := by
  rw [chanTheorem115ReverseResidualPS_eq_neg_residualPS]
  simp

/-- Forward residual vanishing gives reverse residual vanishing. -/
theorem chanTheorem115ReverseResidualPS_eq_zero_of_residualPS_eq_zero
    (h : chanTheorem115ResidualPS = 0) :
    chanTheorem115ReverseResidualPS = 0 :=
  chanTheorem115ResidualPS_eq_zero_iff_reverseResidualPS_eq_zero.1 h

/-- The reverse residual vanishes iff the forward residual vanishes. -/
theorem chanTheorem115ReverseResidualPS_eq_zero_iff_residualPS_eq_zero :
    chanTheorem115ReverseResidualPS = 0 ↔ chanTheorem115ResidualPS = 0 :=
  chanTheorem115ResidualPS_eq_zero_iff_reverseResidualPS_eq_zero.symm

/-- Reverse residual vanishing gives forward residual vanishing. -/
theorem chanTheorem115ResidualPS_eq_zero_of_reverseResidualPS_eq_zero
    (h : chanTheorem115ReverseResidualPS = 0) :
    chanTheorem115ResidualPS = 0 :=
  chanTheorem115ReverseResidualPS_eq_zero_iff_residualPS_eq_zero.1 h

/-- Coefficientwise vanishing of the forward residual is equivalent to
coefficientwise vanishing of the reverse residual. -/
theorem coeff_chanTheorem115ResidualPS_eq_zero_iff_reverseResidualPS_eq_zero
    (k : ℕ) :
    chanTheorem115ResidualPS.coeff k = 0 ↔
      chanTheorem115ReverseResidualPS.coeff k = 0 := by
  rw [coeff_chanTheorem115ReverseResidualPS_eq_neg_residualPS]
  simp

/-- Forward residual coefficient vanishing gives reverse residual coefficient
vanishing. -/
theorem coeff_chanTheorem115ReverseResidualPS_eq_zero_of_residualPS_eq_zero
    {k : ℕ} (h : chanTheorem115ResidualPS.coeff k = 0) :
    chanTheorem115ReverseResidualPS.coeff k = 0 :=
  (coeff_chanTheorem115ResidualPS_eq_zero_iff_reverseResidualPS_eq_zero k).1 h

/-- Coefficientwise vanishing of the reverse residual is equivalent to
coefficientwise vanishing of the forward residual. -/
theorem coeff_chanTheorem115ReverseResidualPS_eq_zero_iff_residualPS_eq_zero
    (k : ℕ) :
    chanTheorem115ReverseResidualPS.coeff k = 0 ↔
      chanTheorem115ResidualPS.coeff k = 0 :=
  (coeff_chanTheorem115ResidualPS_eq_zero_iff_reverseResidualPS_eq_zero k).symm

/-- Reverse residual coefficient vanishing gives forward residual coefficient
vanishing. -/
theorem coeff_chanTheorem115ResidualPS_eq_zero_of_reverseResidualPS_eq_zero
    {k : ℕ} (h : chanTheorem115ReverseResidualPS.coeff k = 0) :
    chanTheorem115ResidualPS.coeff k = 0 :=
  (coeff_chanTheorem115ReverseResidualPS_eq_zero_iff_residualPS_eq_zero k).1 h

/-- The named reverse formal residual has zero coefficients through degree
`10`. -/
theorem coeff_chanTheorem115ReverseResidualPS_eq_zero_of_lt_eleven
    {k : ℕ} (hk : k < 11) :
    chanTheorem115ReverseResidualPS.coeff k = 0 := by
  rw [coeff_chanTheorem115ReverseResidualPS_eq_neg_residualPS,
    coeff_chanTheorem115ResidualPS_eq_zero_of_lt_eleven hk]
  simp

/-- Finite-index reverse residual coefficient form through degree `10`. -/
theorem coeff_chanTheorem115ReverseResidualPS_eq_zero_fin_eleven
    (k : Fin 11) :
    chanTheorem115ReverseResidualPS.coeff k.1 = 0 :=
  coeff_chanTheorem115ReverseResidualPS_eq_zero_of_lt_eleven (by omega)

/-- Uniform finite-index reverse residual coefficient form for any truncation
length at most `11`. -/
theorem coeff_chanTheorem115ReverseResidualPS_eq_zero_fin_of_le_eleven
    {N : ℕ} (hN : N ≤ 11) (k : Fin N) :
    chanTheorem115ReverseResidualPS.coeff k.1 = 0 :=
  coeff_chanTheorem115ReverseResidualPS_eq_zero_of_lt_eleven (by omega)

/-- Every truncation of the named reverse formal residual of length at most
`11` is zero. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_of_le_eleven
    (N : ℕ) (hN : N ≤ 11) :
    PowerSeries.trunc N chanTheorem115ReverseResidualPS = 0 := by
  ext k
  by_cases hk : k < N
  · rw [PowerSeries.coeff_trunc, if_pos hk,
      coeff_chanTheorem115ReverseResidualPS_eq_zero_of_lt_eleven (by omega)]
    simp
  · rw [PowerSeries.coeff_trunc, if_neg hk]
    simp

/-- The named reverse formal residual truncates to zero through degree `10`. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_through_ten :
    PowerSeries.trunc 11 chanTheorem115ReverseResidualPS = 0 :=
  trunc_chanTheorem115ReverseResidualPS_eq_zero_of_le_eleven 11 (by omega)

/-- Reverse-order truncation equality for every truncation length at most
`11`. -/
theorem trunc_chanTheorem115RHS_eq_LHS_of_le_eleven
    (N : ℕ) (hN : N ≤ 11) :
    PowerSeries.trunc N chanTheorem115RHS =
      PowerSeries.trunc N chanTheorem115LHS :=
  (trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_eq N).1
    (trunc_chanTheorem115ReverseResidualPS_eq_zero_of_le_eleven N hN)

/-- X-adic form of the reverse residual verification through degree `10`. -/
theorem X_pow_eleven_dvd_chanTheorem115ReverseResidualPS :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  exact coeff_chanTheorem115ReverseResidualPS_eq_zero_of_lt_eleven hk

/-- X-adic divisibility of the Chan 11.5 reverse residual is equivalent to
vanishing of its coefficients below degree `11`. -/
theorem X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_iff_coeff_zero :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS ↔
      ∀ k : ℕ, k < 11 → chanTheorem115ReverseResidualPS.coeff k = 0 := by
  rw [PowerSeries.X_pow_dvd_iff]

/-- X-adic divisibility of the Chan 11.5 reverse residual is equivalent to its
truncation through degree `10` being zero. -/
theorem X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_iff_trunc_eq_zero :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS ↔
      PowerSeries.trunc 11 chanTheorem115ReverseResidualPS = 0 := by
  rw [X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_iff_coeff_zero,
    trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_zero 11]

/-- Extract low-degree coefficient vanishing from X-adic divisibility of the
Chan 11.5 reverse residual. -/
theorem coeff_chanTheorem115ReverseResidualPS_eq_zero_of_X_pow_eleven_dvd
    {k : ℕ}
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS)
    (hk : k < 11) :
    chanTheorem115ReverseResidualPS.coeff k = 0 :=
  (X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_iff_coeff_zero.1 h) k hk

/-- Build X-adic divisibility of the Chan 11.5 reverse residual from
low-degree coefficient vanishing. -/
theorem X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_of_coeff_zero
    (h : ∀ k : ℕ, k < 11 → chanTheorem115ReverseResidualPS.coeff k = 0) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS :=
  X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_iff_coeff_zero.2 h

/-- A zero truncation through degree `10` gives the corresponding X-adic
divisibility of the Chan 11.5 reverse residual. -/
theorem X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_of_trunc_eq_zero
    (h : PowerSeries.trunc 11 chanTheorem115ReverseResidualPS = 0) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS :=
  X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_iff_trunc_eq_zero.2 h

/-- X-adic divisibility of the Chan 11.5 reverse residual gives zero
truncation through degree `10`. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_of_X_pow_eleven_dvd
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS) :
    PowerSeries.trunc 11 chanTheorem115ReverseResidualPS = 0 :=
  X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_iff_trunc_eq_zero.1 h

/-- X-adic divisibility of the Chan 11.5 reverse residual gives coefficient
agreement below degree `11`, with the sides swapped. -/
theorem coeff_chanTheorem115RHS_eq_LHS_of_X_pow_eleven_dvd_reverseResidualPS
    {k : ℕ}
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS)
    (hk : k < 11) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
  (coeff_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_eq k).1
    (coeff_chanTheorem115ReverseResidualPS_eq_zero_of_X_pow_eleven_dvd h hk)

/-- X-adic divisibility of the Chan 11.5 reverse residual gives reverse
truncation equality through degree `10`. -/
theorem trunc_chanTheorem115RHS_eq_LHS_of_X_pow_eleven_dvd_reverseResidualPS
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS) :
    PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS :=
  (trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_eq 11).1
    (trunc_chanTheorem115ReverseResidualPS_eq_zero_of_X_pow_eleven_dvd h)

/-- Low-degree reverse coefficient agreement gives X-adic divisibility of the
Chan 11.5 reverse residual. -/
theorem X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_of_coeff_eq
    (h : ∀ k : ℕ, k < 11 →
      chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS :=
  X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_of_coeff_zero
    (fun k hk => (coeff_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_eq k).2 (h k hk))

/-- The proved reverse X-adic residual divisibility recovers reverse coefficient
agreement through degree `10`. -/
theorem coeff_chanTheorem115RHS_eq_LHS_of_lt_eleven_via_X_pow_eleven_dvd
    {k : ℕ} (hk : k < 11) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
  coeff_chanTheorem115RHS_eq_LHS_of_X_pow_eleven_dvd_reverseResidualPS
    X_pow_eleven_dvd_chanTheorem115ReverseResidualPS hk

/-- The proved reverse X-adic residual divisibility recovers reverse truncation
equality through degree `10`. -/
theorem trunc_chanTheorem115RHS_eq_LHS_through_ten_via_X_pow_eleven_dvd :
    PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS :=
  trunc_chanTheorem115RHS_eq_LHS_of_X_pow_eleven_dvd_reverseResidualPS
    X_pow_eleven_dvd_chanTheorem115ReverseResidualPS

/-- The proved reverse X-adic residual divisibility recovers the
through-degree-`10` zero truncation. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_through_ten_via_X_pow_eleven_dvd :
    PowerSeries.trunc 11 chanTheorem115ReverseResidualPS = 0 :=
  trunc_chanTheorem115ReverseResidualPS_eq_zero_of_X_pow_eleven_dvd
    X_pow_eleven_dvd_chanTheorem115ReverseResidualPS

/-- If the reverse formal residual has a nonzero coefficient, it must occur at
degree at least `11`. -/
theorem eleven_le_of_coeff_chanTheorem115ReverseResidualPS_ne_zero
    {k : ℕ} (hk : chanTheorem115ReverseResidualPS.coeff k ≠ 0) :
    11 ≤ k := by
  by_contra hlt
  push_neg at hlt
  exact hk (coeff_chanTheorem115ReverseResidualPS_eq_zero_of_lt_eleven hlt)

/-- There is no formal coefficient mismatch below degree `11`. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_ne :
    ¬ ∃ k : ℕ, k < 11 ∧
      chanTheorem115LHS.coeff k ≠ chanTheorem115RHS.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115_eq_of_lt_eleven hk)

/-- There is no formal coefficient mismatch through degree `10`. -/
theorem not_exists_le_ten_coeff_chanTheorem115_ne :
    ¬ ∃ k : ℕ, k ≤ 10 ∧
      chanTheorem115LHS.coeff k ≠ chanTheorem115RHS.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115_eq_of_le_ten hk)

/-- There is no reverse formal coefficient mismatch below degree `11`. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_ne_symm :
    ¬ ∃ k : ℕ, k < 11 ∧
      chanTheorem115RHS.coeff k ≠ chanTheorem115LHS.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115_eq_symm_of_lt_eleven hk)

/-- There is no reverse formal coefficient mismatch through degree `10`. -/
theorem not_exists_le_ten_coeff_chanTheorem115_ne_symm :
    ¬ ∃ k : ℕ, k ≤ 10 ∧
      chanTheorem115RHS.coeff k ≠ chanTheorem115LHS.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne ((coeff_chanTheorem115_eq_of_le_ten hk).symm)

/-- The raw formal forward difference has no nonzero coefficient below degree
`11`. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_sub_ne_zero :
    ¬ ∃ k : ℕ, k < 11 ∧
      (chanTheorem115LHS - chanTheorem115RHS).coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115_sub_eq_zero_of_le_ten (by omega))

/-- The raw formal forward difference has no nonzero coefficient through degree
`10`. -/
theorem not_exists_le_ten_coeff_chanTheorem115_sub_ne_zero :
    ¬ ∃ k : ℕ, k ≤ 10 ∧
      (chanTheorem115LHS - chanTheorem115RHS).coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115_sub_eq_zero_of_le_ten hk)

/-- The raw formal reverse difference has no nonzero coefficient below degree
`11`. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_rhs_sub_lhs_ne_zero :
    ¬ ∃ k : ℕ, k < 11 ∧
      (chanTheorem115RHS - chanTheorem115LHS).coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_le_ten (by omega))

/-- The raw formal reverse difference has no nonzero coefficient through degree
`10`. -/
theorem not_exists_le_ten_coeff_chanTheorem115_rhs_sub_lhs_ne_zero :
    ¬ ∃ k : ℕ, k ≤ 10 ∧
      (chanTheorem115RHS - chanTheorem115LHS).coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_le_ten hk)

/-- The named forward formal residual has no nonzero coefficient below degree
`11`. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115ResidualPS_ne_zero :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115ResidualPS.coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115ResidualPS_eq_zero_of_lt_eleven hk)

/-- The named forward formal residual has no nonzero coefficient through degree
`10`. -/
theorem not_exists_le_ten_coeff_chanTheorem115ResidualPS_ne_zero :
    ¬ ∃ k : ℕ, k ≤ 10 ∧ chanTheorem115ResidualPS.coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115ResidualPS_eq_zero_of_le_ten hk)

/-- The named reverse formal residual has no nonzero coefficient below degree
`11`. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115ReverseResidualPS_ne_zero :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115ReverseResidualPS.coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115ReverseResidualPS_eq_zero_of_lt_eleven hk)

/-- The named reverse formal residual has no nonzero coefficient through degree
`10`. -/
theorem not_exists_le_ten_coeff_chanTheorem115ReverseResidualPS_ne_zero :
    ¬ ∃ k : ℕ, k ≤ 10 ∧ chanTheorem115ReverseResidualPS.coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115ReverseResidualPS_eq_zero_of_lt_eleven (by omega))

/-- Every nonzero coefficient of the raw forward difference occurs at degree
at least `11`. -/
theorem coeff_chanTheorem115_sub_ne_zero_ge_eleven
    {k : ℕ} (hk : (chanTheorem115LHS - chanTheorem115RHS).coeff k ≠ 0) :
    11 ≤ k := by
  by_contra hlt
  push_neg at hlt
  exact hk (coeff_chanTheorem115_sub_eq_zero_of_le_ten (by omega))

/-- Every nonzero coefficient of the raw reverse difference occurs at degree
at least `11`. -/
theorem coeff_chanTheorem115_rhs_sub_lhs_ne_zero_ge_eleven
    {k : ℕ} (hk : (chanTheorem115RHS - chanTheorem115LHS).coeff k ≠ 0) :
    11 ≤ k := by
  by_contra hlt
  push_neg at hlt
  exact hk (coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_le_ten (by omega))

/-- Every nonzero coefficient of the named forward residual occurs at degree
at least `11`. -/
theorem coeff_chanTheorem115ResidualPS_ne_zero_ge_eleven
    {k : ℕ} (hk : chanTheorem115ResidualPS.coeff k ≠ 0) :
    11 ≤ k :=
  eleven_le_of_coeff_chanTheorem115ResidualPS_ne_zero hk

/-- Every nonzero coefficient of the named reverse residual occurs at degree
at least `11`. -/
theorem coeff_chanTheorem115ReverseResidualPS_ne_zero_ge_eleven
    {k : ℕ} (hk : chanTheorem115ReverseResidualPS.coeff k ≠ 0) :
    11 ≤ k :=
  eleven_le_of_coeff_chanTheorem115ReverseResidualPS_ne_zero hk

/-- Below degree `11`, the raw forward difference has zero coefficient, in
implication form. -/
theorem coeff_chanTheorem115_sub_eq_zero_of_not_eleven_le
    {k : ℕ} (hk : ¬ 11 ≤ k) :
    (chanTheorem115LHS - chanTheorem115RHS).coeff k = 0 :=
  coeff_chanTheorem115_sub_eq_zero_of_le_ten (by omega)

/-- Below degree `11`, the raw reverse difference has zero coefficient, in
implication form. -/
theorem coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_not_eleven_le
    {k : ℕ} (hk : ¬ 11 ≤ k) :
    (chanTheorem115RHS - chanTheorem115LHS).coeff k = 0 :=
  coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_le_ten (by omega)

/-- Below degree `11`, the named forward residual has zero coefficient, in
implication form. -/
theorem coeff_chanTheorem115ResidualPS_eq_zero_of_not_eleven_le
    {k : ℕ} (hk : ¬ 11 ≤ k) :
    chanTheorem115ResidualPS.coeff k = 0 :=
  coeff_chanTheorem115ResidualPS_eq_zero_of_lt_eleven (by omega)

/-- Below degree `11`, the named reverse residual has zero coefficient, in
implication form. -/
theorem coeff_chanTheorem115ReverseResidualPS_eq_zero_of_not_eleven_le
    {k : ℕ} (hk : ¬ 11 ≤ k) :
    chanTheorem115ReverseResidualPS.coeff k = 0 :=
  coeff_chanTheorem115ReverseResidualPS_eq_zero_of_lt_eleven (by omega)

/-- The reverse truncated difference of the two sides of Chan Theorem 11.5 is
zero through degree `10`. -/
theorem trunc_chanTheorem115_rhs_sub_lhs_eq_zero_through_ten :
    PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0 := by
  ext k
  by_cases hk : k < 11
  · rw [PowerSeries.coeff_trunc, if_pos hk,
      coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_le_ten (by omega)]
    simp
  · rw [PowerSeries.coeff_trunc, if_neg hk]
    simp

/-- Zero truncation of the forward formal residual is equivalent to zero
truncation of the reverse formal residual, at any truncation length. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_iff_reverseResidualPS_eq_zero
    (N : ℕ) :
    PowerSeries.trunc N chanTheorem115ResidualPS = 0 ↔
      PowerSeries.trunc N chanTheorem115ReverseResidualPS = 0 := by
  rw [trunc_chanTheorem115ResidualPS_eq_zero_iff_coeff_zero,
    trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_coeff_zero]
  constructor
  · intro h k hk
    exact coeff_chanTheorem115ReverseResidualPS_eq_zero_of_residualPS_eq_zero
      (h k hk)
  · intro h k hk
    exact coeff_chanTheorem115ResidualPS_eq_zero_of_reverseResidualPS_eq_zero
      (h k hk)

/-- Zero truncation of the reverse formal residual is equivalent to zero
truncation of the forward formal residual, at any truncation length. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_residualPS_eq_zero
    (N : ℕ) :
    PowerSeries.trunc N chanTheorem115ReverseResidualPS = 0 ↔
      PowerSeries.trunc N chanTheorem115ResidualPS = 0 :=
  (trunc_chanTheorem115ResidualPS_eq_zero_iff_reverseResidualPS_eq_zero N).symm

/-- Zero truncation of the forward formal residual gives zero truncation of the
reverse formal residual at the same length. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_of_residualPS
    {N : ℕ} (h : PowerSeries.trunc N chanTheorem115ResidualPS = 0) :
    PowerSeries.trunc N chanTheorem115ReverseResidualPS = 0 :=
  (trunc_chanTheorem115ResidualPS_eq_zero_iff_reverseResidualPS_eq_zero N).1 h

/-- Zero truncation of the reverse formal residual gives zero truncation of the
forward formal residual at the same length. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_of_reverseResidualPS
    {N : ℕ} (h : PowerSeries.trunc N chanTheorem115ReverseResidualPS = 0) :
    PowerSeries.trunc N chanTheorem115ResidualPS = 0 :=
  (trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_residualPS_eq_zero N).1 h

/-- `X^11` divisibility is the same for the forward and reverse formal
residuals. -/
theorem X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_reverseResidualPS :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS ↔
      (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS := by
  rw [X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_coeff_zero,
    X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_iff_coeff_zero]
  constructor
  · intro h k hk
    exact coeff_chanTheorem115ReverseResidualPS_eq_zero_of_residualPS_eq_zero (h k hk)
  · intro h k hk
    exact coeff_chanTheorem115ResidualPS_eq_zero_of_reverseResidualPS_eq_zero (h k hk)

/-- Forward residual `X^11` divisibility gives reverse residual `X^11`
divisibility. -/
theorem X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_of_residualPS
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS :=
  X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_reverseResidualPS.1 h

/-- Reverse residual `X^11` divisibility gives forward residual `X^11`
divisibility. -/
theorem X_pow_eleven_dvd_chanTheorem115ResidualPS_of_reverseResidualPS
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS :=
  X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_reverseResidualPS.2 h

/-- The forward and reverse formal residuals have equivalent zero truncations
through degree `10`. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_iff_reverseResidualPS_eq_zero_through_ten :
    PowerSeries.trunc 11 chanTheorem115ResidualPS = 0 ↔
      PowerSeries.trunc 11 chanTheorem115ReverseResidualPS = 0 := by
  rw [← X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_trunc_eq_zero,
    ← X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_iff_trunc_eq_zero]
  exact X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_reverseResidualPS

/-- The reverse formal residual truncates to zero through degree `10`, recovered
from the forward residual. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_through_ten_from_residualPS :
    PowerSeries.trunc 11 chanTheorem115ReverseResidualPS = 0 :=
  trunc_chanTheorem115ResidualPS_eq_zero_iff_reverseResidualPS_eq_zero_through_ten.1
    trunc_chanTheorem115ResidualPS_eq_zero_through_ten

/-- The reverse and forward formal residuals have equivalent zero truncations
through degree `10`. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_residualPS_eq_zero_through_ten :
    PowerSeries.trunc 11 chanTheorem115ReverseResidualPS = 0 ↔
      PowerSeries.trunc 11 chanTheorem115ResidualPS = 0 :=
  trunc_chanTheorem115ResidualPS_eq_zero_iff_reverseResidualPS_eq_zero_through_ten.symm

/-- The forward formal residual truncates to zero through degree `10`, recovered
from the reverse residual. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_through_ten_from_reverseResidualPS :
    PowerSeries.trunc 11 chanTheorem115ResidualPS = 0 :=
  trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_residualPS_eq_zero_through_ten.1
    trunc_chanTheorem115ReverseResidualPS_eq_zero_through_ten

/-- Reverse residual `X^11` divisibility, recovered from the forward residual
divisibility. -/
theorem X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_from_residualPS :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS :=
  X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_of_residualPS
    X_pow_eleven_dvd_chanTheorem115ResidualPS

/-- Forward residual `X^11` divisibility, recovered from the reverse residual
divisibility. -/
theorem X_pow_eleven_dvd_chanTheorem115ResidualPS_from_reverseResidualPS :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS :=
  X_pow_eleven_dvd_chanTheorem115ResidualPS_of_reverseResidualPS
    X_pow_eleven_dvd_chanTheorem115ReverseResidualPS

/-- A length-`11` truncation is zero iff there is no nonzero coefficient below
degree `11`. -/
theorem trunc_eleven_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero
    (p : PowerSeries ℚ) :
    PowerSeries.trunc 11 p = 0 ↔
      ¬ ∃ k : ℕ, k < 11 ∧ p.coeff k ≠ 0 := by
  constructor
  · intro h
    rintro ⟨k, hk, hne⟩
    have hcoeff := congrArg (fun q => q.coeff k) h
    exact hne (by simpa [PowerSeries.coeff_trunc, hk] using hcoeff)
  · intro h
    ext k
    by_cases hk : k < 11
    · rw [PowerSeries.coeff_trunc, if_pos hk]
      by_cases hzero : p.coeff k = 0
      · exact hzero
      · exact False.elim (h ⟨k, hk, hzero⟩)
    · rw [PowerSeries.coeff_trunc, if_neg hk]
      simp

/-- `X^11` divisibility is equivalent to having no nonzero coefficient below
degree `11`. -/
theorem X_pow_eleven_dvd_iff_not_exists_lt_eleven_coeff_ne_zero
    (p : PowerSeries ℚ) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ p ↔
      ¬ ∃ k : ℕ, k < 11 ∧ p.coeff k ≠ 0 := by
  rw [PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h
    rintro ⟨k, hk, hne⟩
    exact hne (h k hk)
  · intro h k hk
    by_cases hzero : p.coeff k = 0
    · exact hzero
    · exact False.elim (h ⟨k, hk, hzero⟩)

/-- A length-`11` zero truncation is equivalent to `X^11` divisibility. -/
theorem trunc_eleven_eq_zero_iff_X_pow_eleven_dvd
    (p : PowerSeries ℚ) :
    PowerSeries.trunc 11 p = 0 ↔
      (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ p := by
  rw [trunc_eleven_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero,
    X_pow_eleven_dvd_iff_not_exists_lt_eleven_coeff_ne_zero]

/-- `X^11` divisibility is equivalent to a length-`11` zero truncation. -/
theorem X_pow_eleven_dvd_iff_trunc_eleven_eq_zero
    (p : PowerSeries ℚ) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ p ↔ PowerSeries.trunc 11 p = 0 :=
  (trunc_eleven_eq_zero_iff_X_pow_eleven_dvd p).symm

/-- The forward residual truncates to zero through degree `10` iff it has no
nonzero coefficient below degree `11`. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero :
    PowerSeries.trunc 11 chanTheorem115ResidualPS = 0 ↔
      ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115ResidualPS.coeff k ≠ 0 :=
  trunc_eleven_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero
    chanTheorem115ResidualPS

/-- The reverse residual truncates to zero through degree `10` iff it has no
nonzero coefficient below degree `11`. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero :
    PowerSeries.trunc 11 chanTheorem115ReverseResidualPS = 0 ↔
      ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115ReverseResidualPS.coeff k ≠ 0 :=
  trunc_eleven_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero
    chanTheorem115ReverseResidualPS

/-- The forward residual truncates to zero through degree `10` iff it is
divisible by `X^11`. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_iff_X_pow_eleven_dvd :
    PowerSeries.trunc 11 chanTheorem115ResidualPS = 0 ↔
      (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS :=
  trunc_eleven_eq_zero_iff_X_pow_eleven_dvd chanTheorem115ResidualPS

/-- The reverse residual truncates to zero through degree `10` iff it is
divisible by `X^11`. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_X_pow_eleven_dvd :
    PowerSeries.trunc 11 chanTheorem115ReverseResidualPS = 0 ↔
      (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS :=
  trunc_eleven_eq_zero_iff_X_pow_eleven_dvd chanTheorem115ReverseResidualPS

/-- Forward residual `X^11` divisibility is equivalent to having no nonzero
coefficient below degree `11`. -/
theorem X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_not_exists_lt_eleven_coeff_ne_zero :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS ↔
      ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115ResidualPS.coeff k ≠ 0 :=
  X_pow_eleven_dvd_iff_not_exists_lt_eleven_coeff_ne_zero chanTheorem115ResidualPS

/-- Reverse residual `X^11` divisibility is equivalent to having no nonzero
coefficient below degree `11`. -/
theorem X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_iff_not_exists_lt_eleven_coeff_ne_zero :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS ↔
      ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115ReverseResidualPS.coeff k ≠ 0 :=
  X_pow_eleven_dvd_iff_not_exists_lt_eleven_coeff_ne_zero
    chanTheorem115ReverseResidualPS

/-- The raw forward difference truncates to zero through degree `10` iff it has
no nonzero coefficient below degree `11`. -/
theorem trunc_chanTheorem115_sub_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero :
    PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0 ↔
      ¬ ∃ k : ℕ, k < 11 ∧ (chanTheorem115LHS - chanTheorem115RHS).coeff k ≠ 0 :=
  trunc_eleven_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero
    (chanTheorem115LHS - chanTheorem115RHS)

/-- The raw reverse difference truncates to zero through degree `10` iff it has
no nonzero coefficient below degree `11`. -/
theorem trunc_chanTheorem115_rhs_sub_lhs_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero :
    PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0 ↔
      ¬ ∃ k : ℕ, k < 11 ∧ (chanTheorem115RHS - chanTheorem115LHS).coeff k ≠ 0 :=
  trunc_eleven_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero
    (chanTheorem115RHS - chanTheorem115LHS)

/-- The raw forward difference truncates to zero through degree `10` iff it is
divisible by `X^11`. -/
theorem trunc_chanTheorem115_sub_eq_zero_iff_X_pow_eleven_dvd :
    PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0 ↔
      (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
        (chanTheorem115LHS - chanTheorem115RHS) :=
  trunc_eleven_eq_zero_iff_X_pow_eleven_dvd
    (chanTheorem115LHS - chanTheorem115RHS)

/-- The raw reverse difference truncates to zero through degree `10` iff it is
divisible by `X^11`. -/
theorem trunc_chanTheorem115_rhs_sub_lhs_eq_zero_iff_X_pow_eleven_dvd :
    PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0 ↔
      (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
        (chanTheorem115RHS - chanTheorem115LHS) :=
  trunc_eleven_eq_zero_iff_X_pow_eleven_dvd
    (chanTheorem115RHS - chanTheorem115LHS)

/-- Raw forward `X^11` divisibility is equivalent to having no nonzero
coefficient below degree `11`. -/
theorem X_pow_eleven_dvd_chanTheorem115_sub_iff_not_exists_lt_eleven_coeff_ne_zero :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
        (chanTheorem115LHS - chanTheorem115RHS) ↔
      ¬ ∃ k : ℕ, k < 11 ∧ (chanTheorem115LHS - chanTheorem115RHS).coeff k ≠ 0 :=
  X_pow_eleven_dvd_iff_not_exists_lt_eleven_coeff_ne_zero
    (chanTheorem115LHS - chanTheorem115RHS)

/-- Raw reverse `X^11` divisibility is equivalent to having no nonzero
coefficient below degree `11`. -/
theorem X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_iff_not_exists_lt_eleven_coeff_ne_zero :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
        (chanTheorem115RHS - chanTheorem115LHS) ↔
      ¬ ∃ k : ℕ, k < 11 ∧ (chanTheorem115RHS - chanTheorem115LHS).coeff k ≠ 0 :=
  X_pow_eleven_dvd_iff_not_exists_lt_eleven_coeff_ne_zero
    (chanTheorem115RHS - chanTheorem115LHS)

/-- The raw forward difference zero truncation through degree `10`, recovered
from the no-low-degree-counterexample form. -/
theorem trunc_chanTheorem115_sub_eq_zero_through_ten_from_not_exists :
    PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0 :=
  trunc_chanTheorem115_sub_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero.2
    not_exists_lt_eleven_coeff_chanTheorem115_sub_ne_zero

/-- The raw reverse difference zero truncation through degree `10`, recovered
from the no-low-degree-counterexample form. -/
theorem trunc_chanTheorem115_rhs_sub_lhs_eq_zero_through_ten_from_not_exists :
    PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0 :=
  trunc_chanTheorem115_rhs_sub_lhs_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero.2
    not_exists_lt_eleven_coeff_chanTheorem115_rhs_sub_lhs_ne_zero

/-- The named forward residual zero truncation through degree `10`, recovered
from the no-low-degree-counterexample form. -/
theorem trunc_chanTheorem115ResidualPS_eq_zero_through_ten_from_not_exists :
    PowerSeries.trunc 11 chanTheorem115ResidualPS = 0 :=
  trunc_chanTheorem115ResidualPS_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero.2
    not_exists_lt_eleven_coeff_chanTheorem115ResidualPS_ne_zero

/-- The named reverse residual zero truncation through degree `10`, recovered
from the no-low-degree-counterexample form. -/
theorem trunc_chanTheorem115ReverseResidualPS_eq_zero_through_ten_from_not_exists :
    PowerSeries.trunc 11 chanTheorem115ReverseResidualPS = 0 :=
  trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero.2
    not_exists_lt_eleven_coeff_chanTheorem115ReverseResidualPS_ne_zero

/-- Raw forward `X^11` divisibility, recovered from the
no-low-degree-counterexample form. -/
theorem X_pow_eleven_dvd_chanTheorem115_sub_from_not_exists :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115LHS - chanTheorem115RHS) :=
  X_pow_eleven_dvd_chanTheorem115_sub_iff_not_exists_lt_eleven_coeff_ne_zero.2
    not_exists_lt_eleven_coeff_chanTheorem115_sub_ne_zero

/-- Raw reverse `X^11` divisibility, recovered from the
no-low-degree-counterexample form. -/
theorem X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_from_not_exists :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115RHS - chanTheorem115LHS) :=
  X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_iff_not_exists_lt_eleven_coeff_ne_zero.2
    not_exists_lt_eleven_coeff_chanTheorem115_rhs_sub_lhs_ne_zero

/-- Named forward residual `X^11` divisibility, recovered from the
no-low-degree-counterexample form. -/
theorem X_pow_eleven_dvd_chanTheorem115ResidualPS_from_not_exists :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS :=
  X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_not_exists_lt_eleven_coeff_ne_zero.2
    not_exists_lt_eleven_coeff_chanTheorem115ResidualPS_ne_zero

/-- Named reverse residual `X^11` divisibility, recovered from the
no-low-degree-counterexample form. -/
theorem X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_from_not_exists :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS :=
  X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_iff_not_exists_lt_eleven_coeff_ne_zero.2
    not_exists_lt_eleven_coeff_chanTheorem115ReverseResidualPS_ne_zero

/-- The raw forward difference has no nonzero coefficient below degree `11`,
recovered from `X^11` divisibility. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_sub_ne_zero_from_X_pow_eleven_dvd
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115LHS - chanTheorem115RHS)) :
    ¬ ∃ k : ℕ, k < 11 ∧
      (chanTheorem115LHS - chanTheorem115RHS).coeff k ≠ 0 :=
  X_pow_eleven_dvd_chanTheorem115_sub_iff_not_exists_lt_eleven_coeff_ne_zero.1 h

/-- The raw reverse difference has no nonzero coefficient below degree `11`,
recovered from `X^11` divisibility. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_rhs_sub_lhs_ne_zero_from_X_pow_eleven_dvd
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115RHS - chanTheorem115LHS)) :
    ¬ ∃ k : ℕ, k < 11 ∧
      (chanTheorem115RHS - chanTheorem115LHS).coeff k ≠ 0 :=
  X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_iff_not_exists_lt_eleven_coeff_ne_zero.1 h

/-- The named forward residual has no nonzero coefficient below degree `11`,
recovered from `X^11` divisibility. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115ResidualPS_ne_zero_from_X_pow_eleven_dvd
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ResidualPS) :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115ResidualPS.coeff k ≠ 0 :=
  X_pow_eleven_dvd_chanTheorem115ResidualPS_iff_not_exists_lt_eleven_coeff_ne_zero.1 h

/-- The named reverse residual has no nonzero coefficient below degree `11`,
recovered from `X^11` divisibility. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115ReverseResidualPS_ne_zero_from_X_pow_eleven_dvd
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣ chanTheorem115ReverseResidualPS) :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115ReverseResidualPS.coeff k ≠ 0 :=
  X_pow_eleven_dvd_chanTheorem115ReverseResidualPS_iff_not_exists_lt_eleven_coeff_ne_zero.1 h

/-- The raw forward difference has no nonzero coefficient below degree `11`,
recovered from zero truncation through degree `10`. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_sub_ne_zero_from_trunc_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0) :
    ¬ ∃ k : ℕ, k < 11 ∧
      (chanTheorem115LHS - chanTheorem115RHS).coeff k ≠ 0 :=
  trunc_chanTheorem115_sub_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero.1 h

/-- The raw reverse difference has no nonzero coefficient below degree `11`,
recovered from zero truncation through degree `10`. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_rhs_sub_lhs_ne_zero_from_trunc_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0) :
    ¬ ∃ k : ℕ, k < 11 ∧
      (chanTheorem115RHS - chanTheorem115LHS).coeff k ≠ 0 :=
  trunc_chanTheorem115_rhs_sub_lhs_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero.1 h

/-- The named forward residual has no nonzero coefficient below degree `11`,
recovered from zero truncation through degree `10`. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115ResidualPS_ne_zero_from_trunc_eq_zero
    (h : PowerSeries.trunc 11 chanTheorem115ResidualPS = 0) :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115ResidualPS.coeff k ≠ 0 :=
  trunc_chanTheorem115ResidualPS_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero.1 h

/-- The named reverse residual has no nonzero coefficient below degree `11`,
recovered from zero truncation through degree `10`. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115ReverseResidualPS_ne_zero_from_trunc_eq_zero
    (h : PowerSeries.trunc 11 chanTheorem115ReverseResidualPS = 0) :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115ReverseResidualPS.coeff k ≠ 0 :=
  trunc_chanTheorem115ReverseResidualPS_eq_zero_iff_not_exists_lt_eleven_coeff_ne_zero.1 h

/-- Extract raw forward-difference coefficient vanishing below degree `11`
from `X^11` divisibility. -/
theorem coeff_chanTheorem115_sub_eq_zero_of_X_pow_eleven_dvd
    {k : ℕ}
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115LHS - chanTheorem115RHS))
    (hk : k < 11) :
    (chanTheorem115LHS - chanTheorem115RHS).coeff k = 0 :=
  (PowerSeries.X_pow_dvd_iff.mp h) k hk

/-- Extract raw reverse-difference coefficient vanishing below degree `11`
from `X^11` divisibility. -/
theorem coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_X_pow_eleven_dvd
    {k : ℕ}
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115RHS - chanTheorem115LHS))
    (hk : k < 11) :
    (chanTheorem115RHS - chanTheorem115LHS).coeff k = 0 :=
  (PowerSeries.X_pow_dvd_iff.mp h) k hk

/-- Build raw forward zero truncation through degree `10` from raw
coefficient vanishing below degree `11`. -/
theorem trunc_chanTheorem115_sub_eq_zero_of_coeff_zero
    (h : ∀ k : ℕ, k < 11 →
      (chanTheorem115LHS - chanTheorem115RHS).coeff k = 0) :
    PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0 := by
  ext k
  by_cases hk : k < 11
  · rw [PowerSeries.coeff_trunc, if_pos hk, h k hk]
    simp
  · rw [PowerSeries.coeff_trunc, if_neg hk]
    simp

/-- Build raw reverse zero truncation through degree `10` from raw
coefficient vanishing below degree `11`. -/
theorem trunc_chanTheorem115_rhs_sub_lhs_eq_zero_of_coeff_zero
    (h : ∀ k : ℕ, k < 11 →
      (chanTheorem115RHS - chanTheorem115LHS).coeff k = 0) :
    PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0 := by
  ext k
  by_cases hk : k < 11
  · rw [PowerSeries.coeff_trunc, if_pos hk, h k hk]
    simp
  · rw [PowerSeries.coeff_trunc, if_neg hk]
    simp

/-- Build raw forward `X^11` divisibility from raw coefficient vanishing below
degree `11`. -/
theorem X_pow_eleven_dvd_chanTheorem115_sub_of_coeff_zero
    (h : ∀ k : ℕ, k < 11 →
      (chanTheorem115LHS - chanTheorem115RHS).coeff k = 0) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115LHS - chanTheorem115RHS) := by
  rw [PowerSeries.X_pow_dvd_iff]
  exact h

/-- Build raw reverse `X^11` divisibility from raw coefficient vanishing below
degree `11`. -/
theorem X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_of_coeff_zero
    (h : ∀ k : ℕ, k < 11 →
      (chanTheorem115RHS - chanTheorem115LHS).coeff k = 0) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115RHS - chanTheorem115LHS) := by
  rw [PowerSeries.X_pow_dvd_iff]
  exact h

/-- Raw forward zero truncation through degree `10`, recovered from raw
`X^11` divisibility. -/
theorem trunc_chanTheorem115_sub_eq_zero_of_X_pow_eleven_dvd
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115LHS - chanTheorem115RHS)) :
    PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0 :=
  trunc_chanTheorem115_sub_eq_zero_iff_X_pow_eleven_dvd.2 h

/-- Raw reverse zero truncation through degree `10`, recovered from raw
`X^11` divisibility. -/
theorem trunc_chanTheorem115_rhs_sub_lhs_eq_zero_of_X_pow_eleven_dvd
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115RHS - chanTheorem115LHS)) :
    PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0 :=
  trunc_chanTheorem115_rhs_sub_lhs_eq_zero_iff_X_pow_eleven_dvd.2 h

/-- Raw forward `X^11` divisibility, recovered from zero truncation through
degree `10`. -/
theorem X_pow_eleven_dvd_chanTheorem115_sub_of_trunc_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115LHS - chanTheorem115RHS) :=
  trunc_chanTheorem115_sub_eq_zero_iff_X_pow_eleven_dvd.1 h

/-- Raw reverse `X^11` divisibility, recovered from zero truncation through
degree `10`. -/
theorem X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_of_trunc_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115RHS - chanTheorem115LHS) :=
  trunc_chanTheorem115_rhs_sub_lhs_eq_zero_iff_X_pow_eleven_dvd.1 h

/-- Raw forward `X^11` divisibility gives coefficient agreement below degree
`11`. -/
theorem coeff_chanTheorem115_eq_of_X_pow_eleven_dvd_sub
    {k : ℕ}
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115LHS - chanTheorem115RHS))
    (hk : k < 11) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k := by
  have hzero : (chanTheorem115LHS - chanTheorem115RHS).coeff k = 0 :=
    (PowerSeries.X_pow_dvd_iff.mp h) k hk
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- Raw reverse `X^11` divisibility gives reverse coefficient agreement below
degree `11`. -/
theorem coeff_chanTheorem115RHS_eq_LHS_of_X_pow_eleven_dvd_rhs_sub_lhs
    {k : ℕ}
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115RHS - chanTheorem115LHS))
    (hk : k < 11) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k := by
  have hzero : (chanTheorem115RHS - chanTheorem115LHS).coeff k = 0 :=
    (PowerSeries.X_pow_dvd_iff.mp h) k hk
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- Raw forward `X^11` divisibility gives truncated equality through degree
`10`. -/
theorem trunc_chanTheorem115LHS_eq_RHS_of_X_pow_eleven_dvd_sub
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115LHS - chanTheorem115RHS)) :
    PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS := by
  ext k
  by_cases hk : k < 11
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hk, if_pos hk]
    exact coeff_chanTheorem115_eq_of_X_pow_eleven_dvd_sub h hk
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hk, if_neg hk]

/-- Raw reverse `X^11` divisibility gives reverse truncated equality through
degree `10`. -/
theorem trunc_chanTheorem115RHS_eq_LHS_of_X_pow_eleven_dvd_rhs_sub_lhs
    (h : (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115RHS - chanTheorem115LHS)) :
    PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS := by
  ext k
  by_cases hk : k < 11
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hk, if_pos hk]
    exact coeff_chanTheorem115RHS_eq_LHS_of_X_pow_eleven_dvd_rhs_sub_lhs h hk
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hk, if_neg hk]

/-- The proved raw forward `X^11` divisibility recovers coefficient agreement
below degree `11`. -/
theorem coeff_chanTheorem115_eq_of_lt_eleven_via_raw_X_pow_eleven_dvd
    {k : ℕ} (hk : k < 11) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
  coeff_chanTheorem115_eq_of_X_pow_eleven_dvd_sub
    X_pow_eleven_dvd_chanTheorem115_sub_from_not_exists hk

/-- The proved raw reverse `X^11` divisibility recovers reverse coefficient
agreement below degree `11`. -/
theorem coeff_chanTheorem115RHS_eq_LHS_of_lt_eleven_via_raw_X_pow_eleven_dvd
    {k : ℕ} (hk : k < 11) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
  coeff_chanTheorem115RHS_eq_LHS_of_X_pow_eleven_dvd_rhs_sub_lhs
    X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_from_not_exists hk

/-- The proved raw forward `X^11` divisibility recovers truncated equality
through degree `10`. -/
theorem trunc_chanTheorem115LHS_eq_RHS_through_ten_via_raw_X_pow_eleven_dvd :
    PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS :=
  trunc_chanTheorem115LHS_eq_RHS_of_X_pow_eleven_dvd_sub
    X_pow_eleven_dvd_chanTheorem115_sub_from_not_exists

/-- The proved raw reverse `X^11` divisibility recovers reverse truncated
equality through degree `10`. -/
theorem trunc_chanTheorem115RHS_eq_LHS_through_ten_via_raw_X_pow_eleven_dvd :
    PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS :=
  trunc_chanTheorem115RHS_eq_LHS_of_X_pow_eleven_dvd_rhs_sub_lhs
    X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_from_not_exists

/-- Extract coefficient agreement below `N` directly from truncated equality of
the two Chan 11.5 sides. -/
theorem coeff_chanTheorem115_eq_of_trunc_LHS_eq_RHS
    {N k : ℕ}
    (h : PowerSeries.trunc N chanTheorem115LHS =
      PowerSeries.trunc N chanTheorem115RHS)
    (hk : k < N) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
  (trunc_chanTheorem115LHS_eq_RHS_iff_coeff_eq N).1 h k hk

/-- Extract reverse coefficient agreement below `N` directly from reverse
truncated equality of the two Chan 11.5 sides. -/
theorem coeff_chanTheorem115RHS_eq_LHS_of_trunc_RHS_eq_LHS
    {N k : ℕ}
    (h : PowerSeries.trunc N chanTheorem115RHS =
      PowerSeries.trunc N chanTheorem115LHS)
    (hk : k < N) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
  (trunc_chanTheorem115RHS_eq_LHS_iff_coeff_eq N).1 h k hk

/-- Extract coefficient agreement below `N` from reverse truncated equality,
with the coefficient equality put in forward order. -/
theorem coeff_chanTheorem115_eq_of_trunc_RHS_eq_LHS
    {N k : ℕ}
    (h : PowerSeries.trunc N chanTheorem115RHS =
      PowerSeries.trunc N chanTheorem115LHS)
    (hk : k < N) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
  (coeff_chanTheorem115RHS_eq_LHS_of_trunc_RHS_eq_LHS h hk).symm

/-- Extract reverse coefficient agreement below `N` from forward truncated
equality. -/
theorem coeff_chanTheorem115RHS_eq_LHS_of_trunc_LHS_eq_RHS
    {N k : ℕ}
    (h : PowerSeries.trunc N chanTheorem115LHS =
      PowerSeries.trunc N chanTheorem115RHS)
    (hk : k < N) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
  (coeff_chanTheorem115_eq_of_trunc_LHS_eq_RHS h hk).symm

/-- The through-degree-`10` truncated equality gives coefficient agreement
below degree `11`. -/
theorem coeff_chanTheorem115_eq_of_lt_eleven_via_trunc_LHS_eq_RHS
    {k : ℕ} (hk : k < 11) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
  coeff_chanTheorem115_eq_of_trunc_LHS_eq_RHS
    trunc_chanTheorem115LHS_eq_RHS_through_ten hk

/-- The reverse through-degree-`10` truncated equality gives reverse
coefficient agreement below degree `11`. -/
theorem coeff_chanTheorem115RHS_eq_LHS_of_lt_eleven_via_trunc_RHS_eq_LHS
    {k : ℕ} (hk : k < 11) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
  coeff_chanTheorem115RHS_eq_LHS_of_trunc_RHS_eq_LHS
    trunc_chanTheorem115RHS_eq_LHS_through_ten_via_X_pow_eleven_dvd hk

/-- The reverse through-degree-`10` truncated equality also gives coefficient
agreement in forward order below degree `11`. -/
theorem coeff_chanTheorem115_eq_of_lt_eleven_via_trunc_RHS_eq_LHS
    {k : ℕ} (hk : k < 11) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
  coeff_chanTheorem115_eq_of_trunc_RHS_eq_LHS
    trunc_chanTheorem115RHS_eq_LHS_through_ten_via_X_pow_eleven_dvd hk

/-- The forward through-degree-`10` truncated equality also gives reverse
coefficient agreement below degree `11`. -/
theorem coeff_chanTheorem115RHS_eq_LHS_of_lt_eleven_via_trunc_LHS_eq_RHS
    {k : ℕ} (hk : k < 11) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
  coeff_chanTheorem115RHS_eq_LHS_of_trunc_LHS_eq_RHS
    trunc_chanTheorem115LHS_eq_RHS_through_ten hk

/-- Strict-bound raw forward-difference coefficient form through degree `10`. -/
theorem coeff_chanTheorem115_sub_eq_zero_of_lt_eleven
    {k : ℕ} (hk : k < 11) :
    (chanTheorem115LHS - chanTheorem115RHS).coeff k = 0 :=
  coeff_chanTheorem115_sub_eq_zero_of_le_ten (by omega)

/-- Strict-bound raw reverse-difference coefficient form through degree `10`. -/
theorem coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_lt_eleven
    {k : ℕ} (hk : k < 11) :
    (chanTheorem115RHS - chanTheorem115LHS).coeff k = 0 :=
  coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_le_ten (by omega)

/-- Finite-index raw forward-difference coefficient form through degree `10`. -/
theorem coeff_chanTheorem115_sub_eq_zero_fin_eleven (k : Fin 11) :
    (chanTheorem115LHS - chanTheorem115RHS).coeff k.1 = 0 :=
  coeff_chanTheorem115_sub_eq_zero_of_lt_eleven (by omega)

/-- Finite-index raw reverse-difference coefficient form through degree `10`. -/
theorem coeff_chanTheorem115_rhs_sub_lhs_eq_zero_fin_eleven (k : Fin 11) :
    (chanTheorem115RHS - chanTheorem115LHS).coeff k.1 = 0 :=
  coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_lt_eleven (by omega)

/-- Uniform finite-index raw forward-difference coefficient form for any
truncation length at most `11`. -/
theorem coeff_chanTheorem115_sub_eq_zero_fin_of_le_eleven
    {N : ℕ} (hN : N ≤ 11) (k : Fin N) :
    (chanTheorem115LHS - chanTheorem115RHS).coeff k.1 = 0 :=
  coeff_chanTheorem115_sub_eq_zero_of_lt_eleven (by omega)

/-- Uniform finite-index raw reverse-difference coefficient form for any
truncation length at most `11`. -/
theorem coeff_chanTheorem115_rhs_sub_lhs_eq_zero_fin_of_le_eleven
    {N : ℕ} (hN : N ≤ 11) (k : Fin N) :
    (chanTheorem115RHS - chanTheorem115LHS).coeff k.1 = 0 :=
  coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_lt_eleven (by omega)

/-- Extract raw forward-difference coefficient vanishing below degree `11`
from raw zero truncation. -/
theorem coeff_chanTheorem115_sub_eq_zero_of_trunc_sub_eq_zero
    {k : ℕ}
    (h : PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0)
    (hk : k < 11) :
    (chanTheorem115LHS - chanTheorem115RHS).coeff k = 0 := by
  have hcoeff := congrArg (fun p => p.coeff k) h
  simpa [PowerSeries.coeff_trunc, hk] using hcoeff

/-- Extract raw reverse-difference coefficient vanishing below degree `11`
from raw zero truncation. -/
theorem coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_trunc_rhs_sub_lhs_eq_zero
    {k : ℕ}
    (h : PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0)
    (hk : k < 11) :
    (chanTheorem115RHS - chanTheorem115LHS).coeff k = 0 := by
  have hcoeff := congrArg (fun p => p.coeff k) h
  simpa [PowerSeries.coeff_trunc, hk] using hcoeff

/-- Raw forward zero truncation gives coefficient agreement below degree
`11`. -/
theorem coeff_chanTheorem115_eq_of_trunc_sub_eq_zero
    {k : ℕ}
    (h : PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0)
    (hk : k < 11) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k := by
  have hzero := coeff_chanTheorem115_sub_eq_zero_of_trunc_sub_eq_zero h hk
  have hsub : chanTheorem115LHS.coeff k - chanTheorem115RHS.coeff k = 0 := by
    simpa [map_sub] using hzero
  exact sub_eq_zero.1 hsub

/-- Raw reverse zero truncation gives reverse coefficient agreement below
degree `11`. -/
theorem coeff_chanTheorem115RHS_eq_LHS_of_trunc_rhs_sub_lhs_eq_zero
    {k : ℕ}
    (h : PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0)
    (hk : k < 11) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k := by
  have hzero :=
    coeff_chanTheorem115_rhs_sub_lhs_eq_zero_of_trunc_rhs_sub_lhs_eq_zero h hk
  have hsub : chanTheorem115RHS.coeff k - chanTheorem115LHS.coeff k = 0 := by
    simpa [map_sub] using hzero
  exact sub_eq_zero.1 hsub

/-- Raw forward zero truncation gives truncated equality through degree `10`. -/
theorem trunc_chanTheorem115LHS_eq_RHS_of_trunc_sub_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0) :
    PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS :=
  (trunc_chanTheorem115LHS_eq_RHS_iff_coeff_eq 11).2
    (fun _ hk => coeff_chanTheorem115_eq_of_trunc_sub_eq_zero h hk)

/-- Raw reverse zero truncation gives reverse truncated equality through
degree `10`. -/
theorem trunc_chanTheorem115RHS_eq_LHS_of_trunc_rhs_sub_lhs_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0) :
    PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS :=
  (trunc_chanTheorem115RHS_eq_LHS_iff_coeff_eq 11).2
    (fun _ hk => coeff_chanTheorem115RHS_eq_LHS_of_trunc_rhs_sub_lhs_eq_zero h hk)

/-- Truncated equality through degree `10` gives raw forward zero truncation. -/
theorem trunc_chanTheorem115_sub_eq_zero_of_trunc_LHS_eq_RHS
    (h : PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS) :
    PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0 :=
  trunc_chanTheorem115_sub_eq_zero_of_coeff_zero
    (fun _ hk => by
      rw [map_sub, coeff_chanTheorem115_eq_of_trunc_LHS_eq_RHS h hk]
      simp)

/-- Reverse truncated equality through degree `10` gives raw reverse zero
truncation. -/
theorem trunc_chanTheorem115_rhs_sub_lhs_eq_zero_of_trunc_RHS_eq_LHS
    (h : PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS) :
    PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0 :=
  trunc_chanTheorem115_rhs_sub_lhs_eq_zero_of_coeff_zero
    (fun _ hk => by
      rw [map_sub, coeff_chanTheorem115RHS_eq_LHS_of_trunc_RHS_eq_LHS h hk]
      simp)

/-- Truncated equality through degree `10` gives raw forward `X^11`
divisibility. -/
theorem X_pow_eleven_dvd_chanTheorem115_sub_of_trunc_LHS_eq_RHS
    (h : PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115LHS - chanTheorem115RHS) :=
  X_pow_eleven_dvd_chanTheorem115_sub_of_trunc_eq_zero
    (trunc_chanTheorem115_sub_eq_zero_of_trunc_LHS_eq_RHS h)

/-- Reverse truncated equality through degree `10` gives raw reverse `X^11`
divisibility. -/
theorem X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_of_trunc_RHS_eq_LHS
    (h : PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115RHS - chanTheorem115LHS) :=
  X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_of_trunc_eq_zero
    (trunc_chanTheorem115_rhs_sub_lhs_eq_zero_of_trunc_RHS_eq_LHS h)

/-- Raw forward zero truncation also gives reverse coefficient agreement below
degree `11`. -/
theorem coeff_chanTheorem115RHS_eq_LHS_of_trunc_sub_eq_zero
    {k : ℕ}
    (h : PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0)
    (hk : k < 11) :
    chanTheorem115RHS.coeff k = chanTheorem115LHS.coeff k :=
  (coeff_chanTheorem115_eq_of_trunc_sub_eq_zero h hk).symm

/-- Raw reverse zero truncation also gives coefficient agreement below degree
`11` in forward order. -/
theorem coeff_chanTheorem115_eq_of_trunc_rhs_sub_lhs_eq_zero
    {k : ℕ}
    (h : PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0)
    (hk : k < 11) :
    chanTheorem115LHS.coeff k = chanTheorem115RHS.coeff k :=
  (coeff_chanTheorem115RHS_eq_LHS_of_trunc_rhs_sub_lhs_eq_zero h hk).symm

/-- Raw forward zero truncation also gives reverse truncated equality through
degree `10`. -/
theorem trunc_chanTheorem115RHS_eq_LHS_of_trunc_sub_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0) :
    PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS :=
  (trunc_chanTheorem115LHS_eq_RHS_of_trunc_sub_eq_zero h).symm

/-- Raw reverse zero truncation also gives forward truncated equality through
degree `10`. -/
theorem trunc_chanTheorem115LHS_eq_RHS_of_trunc_rhs_sub_lhs_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0) :
    PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS :=
  (trunc_chanTheorem115RHS_eq_LHS_of_trunc_rhs_sub_lhs_eq_zero h).symm

/-- Forward truncated equality through degree `10` also gives raw reverse zero
truncation. -/
theorem trunc_chanTheorem115_rhs_sub_lhs_eq_zero_of_trunc_LHS_eq_RHS
    (h : PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS) :
    PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0 :=
  trunc_chanTheorem115_rhs_sub_lhs_eq_zero_of_trunc_RHS_eq_LHS h.symm

/-- Reverse truncated equality through degree `10` also gives raw forward zero
truncation. -/
theorem trunc_chanTheorem115_sub_eq_zero_of_trunc_RHS_eq_LHS
    (h : PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS) :
    PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0 :=
  trunc_chanTheorem115_sub_eq_zero_of_trunc_LHS_eq_RHS h.symm

/-- Forward truncated equality through degree `10` also gives raw reverse
`X^11` divisibility. -/
theorem X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_of_trunc_LHS_eq_RHS
    (h : PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115RHS - chanTheorem115LHS) :=
  X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_of_trunc_RHS_eq_LHS h.symm

/-- Reverse truncated equality through degree `10` also gives raw forward
`X^11` divisibility. -/
theorem X_pow_eleven_dvd_chanTheorem115_sub_of_trunc_RHS_eq_LHS
    (h : PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115LHS - chanTheorem115RHS) :=
  X_pow_eleven_dvd_chanTheorem115_sub_of_trunc_LHS_eq_RHS h.symm

/-- Raw forward zero truncation gives raw reverse `X^11` divisibility. -/
theorem X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_of_trunc_sub_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115RHS - chanTheorem115LHS) :=
  X_pow_eleven_dvd_chanTheorem115_rhs_sub_lhs_of_trunc_RHS_eq_LHS
    (trunc_chanTheorem115RHS_eq_LHS_of_trunc_sub_eq_zero h)

/-- Raw reverse zero truncation gives raw forward `X^11` divisibility. -/
theorem X_pow_eleven_dvd_chanTheorem115_sub_of_trunc_rhs_sub_lhs_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0) :
    (PowerSeries.X ^ 11 : PowerSeries ℚ) ∣
      (chanTheorem115LHS - chanTheorem115RHS) :=
  X_pow_eleven_dvd_chanTheorem115_sub_of_trunc_LHS_eq_RHS
    (trunc_chanTheorem115LHS_eq_RHS_of_trunc_rhs_sub_lhs_eq_zero h)

/-- Forward truncated equality rules out low-degree coefficient mismatches. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_ne_from_trunc_LHS_eq_RHS
    (h : PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS) :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115LHS.coeff k ≠ chanTheorem115RHS.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115_eq_of_trunc_LHS_eq_RHS h hk)

/-- Forward truncated equality rules out low-degree coefficient mismatches in
the reverse order. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_ne_symm_from_trunc_LHS_eq_RHS
    (h : PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS) :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115RHS.coeff k ≠ chanTheorem115LHS.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115RHS_eq_LHS_of_trunc_LHS_eq_RHS h hk)

/-- Reverse truncated equality rules out low-degree coefficient mismatches. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_ne_from_trunc_RHS_eq_LHS
    (h : PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS) :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115LHS.coeff k ≠ chanTheorem115RHS.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115_eq_of_trunc_RHS_eq_LHS h hk)

/-- Reverse truncated equality rules out low-degree coefficient mismatches in
the reverse order. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_ne_symm_from_trunc_RHS_eq_LHS
    (h : PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS) :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115RHS.coeff k ≠ chanTheorem115LHS.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115RHS_eq_LHS_of_trunc_RHS_eq_LHS h hk)

/-- Forward truncated equality rules out low-degree nonzero raw forward
difference coefficients. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_sub_ne_zero_from_trunc_LHS_eq_RHS
    (h : PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS) :
    ¬ ∃ k : ℕ, k < 11 ∧ (chanTheorem115LHS - chanTheorem115RHS).coeff k ≠ 0 :=
  not_exists_lt_eleven_coeff_chanTheorem115_sub_ne_zero_from_trunc_eq_zero
    (trunc_chanTheorem115_sub_eq_zero_of_trunc_LHS_eq_RHS h)

/-- Forward truncated equality rules out low-degree nonzero raw reverse
difference coefficients. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_rhs_sub_lhs_ne_zero_from_trunc_LHS_eq_RHS
    (h : PowerSeries.trunc 11 chanTheorem115LHS =
      PowerSeries.trunc 11 chanTheorem115RHS) :
    ¬ ∃ k : ℕ, k < 11 ∧ (chanTheorem115RHS - chanTheorem115LHS).coeff k ≠ 0 :=
  not_exists_lt_eleven_coeff_chanTheorem115_rhs_sub_lhs_ne_zero_from_trunc_eq_zero
    (trunc_chanTheorem115_rhs_sub_lhs_eq_zero_of_trunc_LHS_eq_RHS h)

/-- Reverse truncated equality rules out low-degree nonzero raw forward
difference coefficients. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_sub_ne_zero_from_trunc_RHS_eq_LHS
    (h : PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS) :
    ¬ ∃ k : ℕ, k < 11 ∧ (chanTheorem115LHS - chanTheorem115RHS).coeff k ≠ 0 :=
  not_exists_lt_eleven_coeff_chanTheorem115_sub_ne_zero_from_trunc_eq_zero
    (trunc_chanTheorem115_sub_eq_zero_of_trunc_RHS_eq_LHS h)

/-- Reverse truncated equality rules out low-degree nonzero raw reverse
difference coefficients. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_rhs_sub_lhs_ne_zero_from_trunc_RHS_eq_LHS
    (h : PowerSeries.trunc 11 chanTheorem115RHS =
      PowerSeries.trunc 11 chanTheorem115LHS) :
    ¬ ∃ k : ℕ, k < 11 ∧ (chanTheorem115RHS - chanTheorem115LHS).coeff k ≠ 0 :=
  not_exists_lt_eleven_coeff_chanTheorem115_rhs_sub_lhs_ne_zero_from_trunc_eq_zero
    (trunc_chanTheorem115_rhs_sub_lhs_eq_zero_of_trunc_RHS_eq_LHS h)

/-- Raw forward zero truncation gives raw reverse zero truncation. -/
theorem trunc_chanTheorem115_rhs_sub_lhs_eq_zero_of_trunc_sub_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0) :
    PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0 :=
  trunc_chanTheorem115_rhs_sub_lhs_eq_zero_of_trunc_RHS_eq_LHS
    (trunc_chanTheorem115RHS_eq_LHS_of_trunc_sub_eq_zero h)

/-- Raw reverse zero truncation gives raw forward zero truncation. -/
theorem trunc_chanTheorem115_sub_eq_zero_of_trunc_rhs_sub_lhs_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0) :
    PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0 :=
  trunc_chanTheorem115_sub_eq_zero_of_trunc_LHS_eq_RHS
    (trunc_chanTheorem115LHS_eq_RHS_of_trunc_rhs_sub_lhs_eq_zero h)

/-- Raw forward zero truncation rules out low-degree coefficient mismatches. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_ne_from_trunc_sub_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0) :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115LHS.coeff k ≠ chanTheorem115RHS.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115_eq_of_trunc_sub_eq_zero h hk)

/-- Raw forward zero truncation rules out low-degree coefficient mismatches in
the reverse order. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_ne_symm_from_trunc_sub_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0) :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115RHS.coeff k ≠ chanTheorem115LHS.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115RHS_eq_LHS_of_trunc_sub_eq_zero h hk)

/-- Raw reverse zero truncation rules out low-degree coefficient mismatches. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_ne_from_trunc_rhs_sub_lhs_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0) :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115LHS.coeff k ≠ chanTheorem115RHS.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115_eq_of_trunc_rhs_sub_lhs_eq_zero h hk)

/-- Raw reverse zero truncation rules out low-degree coefficient mismatches in
the reverse order. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_ne_symm_from_trunc_rhs_sub_lhs_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0) :
    ¬ ∃ k : ℕ, k < 11 ∧ chanTheorem115RHS.coeff k ≠ chanTheorem115LHS.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_chanTheorem115RHS_eq_LHS_of_trunc_rhs_sub_lhs_eq_zero h hk)

/-- Raw forward zero truncation rules out low-degree nonzero raw reverse
difference coefficients. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_rhs_sub_lhs_ne_zero_from_trunc_sub_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115LHS - chanTheorem115RHS) = 0) :
    ¬ ∃ k : ℕ, k < 11 ∧ (chanTheorem115RHS - chanTheorem115LHS).coeff k ≠ 0 :=
  not_exists_lt_eleven_coeff_chanTheorem115_rhs_sub_lhs_ne_zero_from_trunc_eq_zero
    (trunc_chanTheorem115_rhs_sub_lhs_eq_zero_of_trunc_sub_eq_zero h)

/-- Raw reverse zero truncation rules out low-degree nonzero raw forward
difference coefficients. -/
theorem not_exists_lt_eleven_coeff_chanTheorem115_sub_ne_zero_from_trunc_rhs_sub_lhs_eq_zero
    (h : PowerSeries.trunc 11 (chanTheorem115RHS - chanTheorem115LHS) = 0) :
    ¬ ∃ k : ℕ, k < 11 ∧ (chanTheorem115LHS - chanTheorem115RHS).coeff k ≠ 0 :=
  not_exists_lt_eleven_coeff_chanTheorem115_sub_ne_zero_from_trunc_eq_zero
    (trunc_chanTheorem115_sub_eq_zero_of_trunc_rhs_sub_lhs_eq_zero h)

end Ch13CoeffVerification
end Pending
end QseriesFormalization
