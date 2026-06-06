import QseriesFormalization.Basic
import QseriesFormalization.Chapter11
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Chapter 12 — Evaluation of the Rogers-Ramanujan continued fraction

⚠️  **SHADOW CHAPTER**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22): a previous `ramanujanRRCFValue := α⁻¹+β`
placeholder definition (which collapsed to 0) was removed; see the in-line
notice below.  What remains in this file is the catalog of `R_trunc q N`
closed-form unfoldings for N up to ~36 — these are mechanical and do not
constitute a Ch 12 main result.

**Chan's Ch 12 main result — the explicit evaluation of the Rogers-Ramanujan
continued fraction at `q = e^{-2π}` (and related special points) using the
golden-ratio formula — is NOT formalized here.**  Tracked as Tier 5 #17 in
`TODO_THEOREMS.md`.
-/

namespace QseriesFormalization
namespace PartIII
namespace Ch12

open QseriesFormalization.PartIII.Ch11 (α β)

/-- Local fallback for the golden-ratio inverse identity.  This can be replaced
by the Chapter 11 theorem once it is available upstream. -/
private theorem α_inv : α⁻¹ = α - 1 := by
  have hsq : α ^ 2 = α + 1 := QseriesFormalization.PartIII.Ch11.α_sq
  have hα_ne_zero : α ≠ 0 := by
    intro hα
    simp [hα] at hsq
  have hmul : α * (α - 1) = 1 := by
    nlinarith
  calc
    α⁻¹ = α⁻¹ * 1 := by ring
    _ = α⁻¹ * (α * (α - 1)) := by rw [hmul]
    _ = (α⁻¹ * α) * (α - 1) := by ring
    _ = 1 * (α - 1) := by rw [inv_mul_cancel₀ hα_ne_zero]
    _ = α - 1 := by ring

/-
  ⚠️  REMOVED placeholder (2026-05-22).

  The previous block here defined

    noncomputable def ramanujanRRCFValue : ℝ := α⁻¹ + β
    theorem ramanujanRRCFValue_eq : ramanujanRRCFValue = α⁻¹ + β := rfl
    theorem ramanujanRRCFValue_eq_simple : ramanujanRRCFValue = (α - 1) + β
    theorem ramanujanRRCFValue_placeholder_zero : ramanujanRRCFValue = 0

  This was a placeholder, not the Rogers-Ramanujan continued-fraction value.
  Chan's identity for the RRCF at `q = e^{-2π}` evaluates to a specific
  algebraic number involving the golden ratio (NOT `α⁻¹ + β = 0`).  Keeping
  the placeholder hidden behind a definition with name `ramanujanRRCFValue`
  amounts to a violation of playbook point 4 (no trivially-true conclusions)
  and point 11 (honest conditional/unconditional classification).

  TODO: a real Ch12 result needs either
    (a) the analytic limit `Tendsto (R_trunc q) atTop (RR_value_of q)` for
        suitable `q`, plus the closed-form evaluation at `q = e^{-2π}`; or
    (b) restrict to the truncations as a formal-power-series object and
        prove the truncation-level identity at the formal level.
  Neither is currently in this repository.

  Until then, Ch12 is **explicitly incomplete** at the chapter-main-result
  level; only the `R_trunc_N_eq` truncation identities below are real.
-/

/-- R_trunc q 1 expressed as a ratio matching H_trunc/G_trunc pattern at N=0. -/
theorem R_trunc_one_eq_inv_one_plus_q (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 1 = 1 / (1 + q) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_one q

/-- R_trunc at N=2 matches the nested continued fraction. -/
theorem R_trunc_two_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 2 =
      1 / (1 + q ^ 2 / (1 + q)) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_two q

/-- R_trunc at N=3. -/
theorem R_trunc_three_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 3 =
      1 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_three q

/-- R_trunc at N=4. -/
theorem R_trunc_four_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 4 =
      1 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q)))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_four q

/-- R_trunc at N=5. -/
theorem R_trunc_five_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 5 =
      1 / (1 + q ^ 5 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q))))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_five q

/-- R_trunc at N=6. -/
theorem R_trunc_six_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 6 =
      1 / (1 + q ^ 6 / (1 + q ^ 5 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q)))))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_six q

/-- R_trunc at N=7. -/
theorem R_trunc_seven_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 7 =
      1 / (1 + q ^ 7 / (1 + q ^ 6 / (1 + q ^ 5 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q))))))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_seven q

/-- R_trunc at N=8. -/
theorem R_trunc_eight_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 8 =
      1 / (1 + q ^ 8 / (1 + q ^ 7 / (1 + q ^ 6 / (1 + q ^ 5 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q)))))))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_eight q

/-- R_trunc at N=9. -/
theorem R_trunc_nine_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 9 =
      1 / (1 + q ^ 9 / (1 + q ^ 8 / (1 + q ^ 7 / (1 + q ^ 6 / (1 + q ^ 5 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q))))))))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_nine q

/-- R_trunc at N=10. -/
theorem R_trunc_ten_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 10 =
      1 / (1 + q ^ 10 / (1 + q ^ 9 / (1 + q ^ 8 / (1 + q ^ 7 / (1 + q ^ 6 / (1 + q ^ 5 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q)))))))))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_ten q

/-- R_trunc at N=11. -/
theorem R_trunc_eleven_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 11 =
      1 / (1 + q ^ 11 / (1 + q ^ 10 / (1 + q ^ 9 / (1 + q ^ 8 / (1 + q ^ 7 / (1 + q ^ 6 / (1 + q ^ 5 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q))))))))))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_eleven q

/-- R_trunc at N=12. -/
theorem R_trunc_twelve_eq (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 12 =
      1 / (1 + q ^ 12 / (1 + q ^ 11 / (1 + q ^ 10 / (1 + q ^ 9 / (1 + q ^ 8 / (1 + q ^ 7 / (1 + q ^ 6 / (1 + q ^ 5 / (1 + q ^ 4 / (1 + q ^ 3 / (1 + q ^ 2 / (1 + q)))))))))))) :=
  QseriesFormalization.PartIII.Ch11.R_trunc_twelve q

theorem R_trunc_eq_thirteen (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 13 = 1 / (1 + q ^ 13 * QseriesFormalization.PartIII.Ch11.R_trunc q 12) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fourteen (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 14 = 1 / (1 + q ^ 14 * QseriesFormalization.PartIII.Ch11.R_trunc q 13) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fifteen (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 15 = 1 / (1 + q ^ 15 * QseriesFormalization.PartIII.Ch11.R_trunc q 14) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_sixteen (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 16 = 1 / (1 + q ^ 16 * QseriesFormalization.PartIII.Ch11.R_trunc q 15) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_seventeen (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 17 = 1 / (1 + q ^ 17 * QseriesFormalization.PartIII.Ch11.R_trunc q 16) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_eighteen (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 18 = 1 / (1 + q ^ 18 * QseriesFormalization.PartIII.Ch11.R_trunc q 17) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_nineteen (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 19 = 1 / (1 + q ^ 19 * QseriesFormalization.PartIII.Ch11.R_trunc q 18) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_twenty (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 20 = 1 / (1 + q ^ 20 * QseriesFormalization.PartIII.Ch11.R_trunc q 19) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_twentyone (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 21 = 1 / (1 + q ^ 21 * QseriesFormalization.PartIII.Ch11.R_trunc q 20) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_twentytwo (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 22 = 1 / (1 + q ^ 22 * QseriesFormalization.PartIII.Ch11.R_trunc q 21) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_twentythree (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 23 = 1 / (1 + q ^ 23 * QseriesFormalization.PartIII.Ch11.R_trunc q 22) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_twentyfour (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 24 = 1 / (1 + q ^ 24 * QseriesFormalization.PartIII.Ch11.R_trunc q 23) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_twentyfive (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 25 = 1 / (1 + q ^ 25 * QseriesFormalization.PartIII.Ch11.R_trunc q 24) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_twentysix (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 26 = 1 / (1 + q ^ 26 * QseriesFormalization.PartIII.Ch11.R_trunc q 25) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_twentyseven (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 27 = 1 / (1 + q ^ 27 * QseriesFormalization.PartIII.Ch11.R_trunc q 26) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_twentyeight (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 28 = 1 / (1 + q ^ 28 * QseriesFormalization.PartIII.Ch11.R_trunc q 27) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_twentynine (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 29 = 1 / (1 + q ^ 29 * QseriesFormalization.PartIII.Ch11.R_trunc q 28) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_thirty (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 30 = 1 / (1 + q ^ 30 * QseriesFormalization.PartIII.Ch11.R_trunc q 29) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_thirtyone (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 31 = 1 / (1 + q ^ 31 * QseriesFormalization.PartIII.Ch11.R_trunc q 30) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_thirtytwo (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 32 = 1 / (1 + q ^ 32 * QseriesFormalization.PartIII.Ch11.R_trunc q 31) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_thirtythree (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 33 = 1 / (1 + q ^ 33 * QseriesFormalization.PartIII.Ch11.R_trunc q 32) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_thirtyfour (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 34 = 1 / (1 + q ^ 34 * QseriesFormalization.PartIII.Ch11.R_trunc q 33) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_thirtyfive (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 35 = 1 / (1 + q ^ 35 * QseriesFormalization.PartIII.Ch11.R_trunc q 34) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_thirtysix (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 36 = 1 / (1 + q ^ 36 * QseriesFormalization.PartIII.Ch11.R_trunc q 35) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_thirtyseven (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 37 = 1 / (1 + q ^ 37 * QseriesFormalization.PartIII.Ch11.R_trunc q 36) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_thirtyeight (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 38 = 1 / (1 + q ^ 38 * QseriesFormalization.PartIII.Ch11.R_trunc q 37) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_thirtynine (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 39 = 1 / (1 + q ^ 39 * QseriesFormalization.PartIII.Ch11.R_trunc q 38) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_forty (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 40 = 1 / (1 + q ^ 40 * QseriesFormalization.PartIII.Ch11.R_trunc q 39) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fortyone (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 41 = 1 / (1 + q ^ 41 * QseriesFormalization.PartIII.Ch11.R_trunc q 40) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fortytwo (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 42 = 1 / (1 + q ^ 42 * QseriesFormalization.PartIII.Ch11.R_trunc q 41) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fortythree (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 43 = 1 / (1 + q ^ 43 * QseriesFormalization.PartIII.Ch11.R_trunc q 42) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fortyfour (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 44 = 1 / (1 + q ^ 44 * QseriesFormalization.PartIII.Ch11.R_trunc q 43) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fortyfive (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 45 = 1 / (1 + q ^ 45 * QseriesFormalization.PartIII.Ch11.R_trunc q 44) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fortysix (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 46 = 1 / (1 + q ^ 46 * QseriesFormalization.PartIII.Ch11.R_trunc q 45) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fortyseven (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 47 = 1 / (1 + q ^ 47 * QseriesFormalization.PartIII.Ch11.R_trunc q 46) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fortyeight (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 48 = 1 / (1 + q ^ 48 * QseriesFormalization.PartIII.Ch11.R_trunc q 47) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fortynine (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 49 = 1 / (1 + q ^ 49 * QseriesFormalization.PartIII.Ch11.R_trunc q 48) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fifty (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 50 = 1 / (1 + q ^ 50 * QseriesFormalization.PartIII.Ch11.R_trunc q 49) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fiftyone (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 51 = 1 / (1 + q ^ 51 * QseriesFormalization.PartIII.Ch11.R_trunc q 50) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fiftytwo (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 52 = 1 / (1 + q ^ 52 * QseriesFormalization.PartIII.Ch11.R_trunc q 51) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fiftythree (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 53 = 1 / (1 + q ^ 53 * QseriesFormalization.PartIII.Ch11.R_trunc q 52) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fiftyfour (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 54 = 1 / (1 + q ^ 54 * QseriesFormalization.PartIII.Ch11.R_trunc q 53) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fiftyfive (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 55 = 1 / (1 + q ^ 55 * QseriesFormalization.PartIII.Ch11.R_trunc q 54) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fiftysix (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 56 = 1 / (1 + q ^ 56 * QseriesFormalization.PartIII.Ch11.R_trunc q 55) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fiftyseven (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 57 = 1 / (1 + q ^ 57 * QseriesFormalization.PartIII.Ch11.R_trunc q 56) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fiftyeight (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 58 = 1 / (1 + q ^ 58 * QseriesFormalization.PartIII.Ch11.R_trunc q 57) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_fiftynine (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 59 = 1 / (1 + q ^ 59 * QseriesFormalization.PartIII.Ch11.R_trunc q 58) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_sixty (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 60 = 1 / (1 + q ^ 60 * QseriesFormalization.PartIII.Ch11.R_trunc q 59) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_sixtyone (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 61 = 1 / (1 + q ^ 61 * QseriesFormalization.PartIII.Ch11.R_trunc q 60) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_sixtytwo (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 62 = 1 / (1 + q ^ 62 * QseriesFormalization.PartIII.Ch11.R_trunc q 61) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_sixtythree (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 63 = 1 / (1 + q ^ 63 * QseriesFormalization.PartIII.Ch11.R_trunc q 62) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_sixtyfour (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 64 = 1 / (1 + q ^ 64 * QseriesFormalization.PartIII.Ch11.R_trunc q 63) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_sixtyfive (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 65 = 1 / (1 + q ^ 65 * QseriesFormalization.PartIII.Ch11.R_trunc q 64) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_sixtysix (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 66 = 1 / (1 + q ^ 66 * QseriesFormalization.PartIII.Ch11.R_trunc q 65) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_sixtyseven (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 67 = 1 / (1 + q ^ 67 * QseriesFormalization.PartIII.Ch11.R_trunc q 66) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

theorem R_trunc_eq_sixtyeight (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 68 = 1 / (1 + q ^ 68 * QseriesFormalization.PartIII.Ch11.R_trunc q 67) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_sixtynine (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 69 = 1 / (1 + q ^ 69 * QseriesFormalization.PartIII.Ch11.R_trunc q 68) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_seventy (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 70 = 1 / (1 + q ^ 70 * QseriesFormalization.PartIII.Ch11.R_trunc q 69) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_seventyone (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 71 = 1 / (1 + q ^ 71 * QseriesFormalization.PartIII.Ch11.R_trunc q 70) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_seventytwo (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 72 = 1 / (1 + q ^ 72 * QseriesFormalization.PartIII.Ch11.R_trunc q 71) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_seventythree (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 73 = 1 / (1 + q ^ 73 * QseriesFormalization.PartIII.Ch11.R_trunc q 72) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_seventyfour (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 74 = 1 / (1 + q ^ 74 * QseriesFormalization.PartIII.Ch11.R_trunc q 73) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_seventyfive (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 75 = 1 / (1 + q ^ 75 * QseriesFormalization.PartIII.Ch11.R_trunc q 74) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_seventysix (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 76 = 1 / (1 + q ^ 76 * QseriesFormalization.PartIII.Ch11.R_trunc q 75) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_seventyseven (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 77 = 1 / (1 + q ^ 77 * QseriesFormalization.PartIII.Ch11.R_trunc q 76) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_seventyeight (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 78 = 1 / (1 + q ^ 78 * QseriesFormalization.PartIII.Ch11.R_trunc q 77) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_seventynine (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 79 = 1 / (1 + q ^ 79 * QseriesFormalization.PartIII.Ch11.R_trunc q 78) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_eighty (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 80 = 1 / (1 + q ^ 80 * QseriesFormalization.PartIII.Ch11.R_trunc q 79) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_eightyone (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 81 = 1 / (1 + q ^ 81 * QseriesFormalization.PartIII.Ch11.R_trunc q 80) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_eightytwo (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 82 = 1 / (1 + q ^ 82 * QseriesFormalization.PartIII.Ch11.R_trunc q 81) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_eightythree (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 83 = 1 / (1 + q ^ 83 * QseriesFormalization.PartIII.Ch11.R_trunc q 82) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_eightyfour (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 84 = 1 / (1 + q ^ 84 * QseriesFormalization.PartIII.Ch11.R_trunc q 83) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_eightyfive (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 85 = 1 / (1 + q ^ 85 * QseriesFormalization.PartIII.Ch11.R_trunc q 84) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_eightysix (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 86 = 1 / (1 + q ^ 86 * QseriesFormalization.PartIII.Ch11.R_trunc q 85) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_eightyseven (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 87 = 1 / (1 + q ^ 87 * QseriesFormalization.PartIII.Ch11.R_trunc q 86) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_eightyeight (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 88 = 1 / (1 + q ^ 88 * QseriesFormalization.PartIII.Ch11.R_trunc q 87) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_eightynine (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 89 = 1 / (1 + q ^ 89 * QseriesFormalization.PartIII.Ch11.R_trunc q 88) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_ninety (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 90 = 1 / (1 + q ^ 90 * QseriesFormalization.PartIII.Ch11.R_trunc q 89) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_ninetyone (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 91 = 1 / (1 + q ^ 91 * QseriesFormalization.PartIII.Ch11.R_trunc q 90) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_ninetytwo (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 92 = 1 / (1 + q ^ 92 * QseriesFormalization.PartIII.Ch11.R_trunc q 91) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_ninetythree (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 93 = 1 / (1 + q ^ 93 * QseriesFormalization.PartIII.Ch11.R_trunc q 92) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_ninetyfour (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 94 = 1 / (1 + q ^ 94 * QseriesFormalization.PartIII.Ch11.R_trunc q 93) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_ninetyfive (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 95 = 1 / (1 + q ^ 95 * QseriesFormalization.PartIII.Ch11.R_trunc q 94) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_ninetysix (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 96 = 1 / (1 + q ^ 96 * QseriesFormalization.PartIII.Ch11.R_trunc q 95) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_ninetyseven (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 97 = 1 / (1 + q ^ 97 * QseriesFormalization.PartIII.Ch11.R_trunc q 96) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_ninetyeight (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 98 = 1 / (1 + q ^ 98 * QseriesFormalization.PartIII.Ch11.R_trunc q 97) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_ninetynine (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 99 = 1 / (1 + q ^ 99 * QseriesFormalization.PartIII.Ch11.R_trunc q 98) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_onehundred (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 100 = 1 / (1 + q ^ 100 * QseriesFormalization.PartIII.Ch11.R_trunc q 99) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_onehundredone (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 101 = 1 / (1 + q ^ 101 * QseriesFormalization.PartIII.Ch11.R_trunc q 100) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_onehundredtwo (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 102 = 1 / (1 + q ^ 102 * QseriesFormalization.PartIII.Ch11.R_trunc q 101) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_onehundredthree (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 103 = 1 / (1 + q ^ 103 * QseriesFormalization.PartIII.Ch11.R_trunc q 102) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_onehundredfour (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 104 = 1 / (1 + q ^ 104 * QseriesFormalization.PartIII.Ch11.R_trunc q 103) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_onehundredfive (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 105 = 1 / (1 + q ^ 105 * QseriesFormalization.PartIII.Ch11.R_trunc q 104) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_onehundredsix (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 106 = 1 / (1 + q ^ 106 * QseriesFormalization.PartIII.Ch11.R_trunc q 105) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_onehundredseven (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 107 = 1 / (1 + q ^ 107 * QseriesFormalization.PartIII.Ch11.R_trunc q 106) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_onehundredeight (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 108 = 1 / (1 + q ^ 108 * QseriesFormalization.PartIII.Ch11.R_trunc q 107) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_onehundrednine (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 109 = 1 / (1 + q ^ 109 * QseriesFormalization.PartIII.Ch11.R_trunc q 108) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]

set_option maxRecDepth 2000 in
theorem R_trunc_eq_onehundredten (q : ℂ) :
    QseriesFormalization.PartIII.Ch11.R_trunc q 110 = 1 / (1 + q ^ 110 * QseriesFormalization.PartIII.Ch11.R_trunc q 109) := by
  simp [QseriesFormalization.PartIII.Ch11.R_trunc]


end Ch12
end PartIII
end QseriesFormalization

