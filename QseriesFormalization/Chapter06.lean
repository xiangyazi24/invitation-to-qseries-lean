import QseriesFormalization.Basic
import QseriesFormalization.Chapter04

/-!
# Chapter 6 — Macdonald's identities (Chan §6) — **MISLABELED**

⚠️  **MISLABELED CHAPTER**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22), after cross-checking Chan's TOC and
Chapter 6 text:

**Chan §6 is "Macdonald's identities".**  Its main result is
**Theorem 6.1**:

    η(q)^{t²-1}  =  c_0 · ∑_{(v_0,…,v_{t-1}) ∈ ℤ^t, v_i ≡ i (mod t),
                              v_0+…+v_{t-1}=0}
                     ∏_{i<j} (v_i − v_j) · q^{(v_0² + … + v_{t-1}²)/(2t)}

    where η(q) := q^{1/24} · ∏_{m≥1} (1 − q^m)  is the Dedekind η-function
    and t is an odd positive integer.  This is the Weyl-Macdonald-Kac
    denominator formula for the affine Lie algebra ŝl(2,ℂ).

**What this file actually contains** is just the polynomial truncation
`dedekindEtaTrunc q N := (q;q)_N` (without the `q^{1/24}` prefactor) and
its `_succ`/`_one` recursion.  That is **not** Chan §6 — it is just the
plain finite product `(q;q)_N`, which already lives in `Basic.lean`.

So Chan §6's Macdonald's identity (Theorem 6.1) was originally **completely
absent from this repository**.  The plain `dedekindEtaTrunc q N := (q;q)_N`
content below is unrelated finite-product scaffolding.

**Update (2026-05-24)**: the foundational `t = 2` (affine `A₁`, `ŝl(2,ℂ)`)
case of Macdonald's identity — i.e. **Jacobi's identity**
`(q;q)_∞³ = ∑_{k≥0} (-1)^k (2k+1) q^{k(k+1)/2}` — is now formalized and
proven **unconditionally** in `Pending/Chapter06_Macdonald_A1.lean`
(`macdonald_A1_identity`), as a corollary of the formal-PS Jacobi cube
identity B2.  The general odd-`t` Macdonald denominator formula (needing
affine Lie theory) remains open.
-/

namespace QseriesFormalization
namespace PartI
namespace Ch06

section Field

variable {R : Type*} [Field R]

/-- Truncated Dedekind-η-style product `q^{1/24} ∏_{m=1}^N (1 - q^m)`.
We omit the q^{1/24} prefactor here (it requires fractional powers);
this defines the polynomial part `η_red q N := (q;q)_N`. -/
noncomputable def dedekindEtaTrunc (q : R) (N : Nat) : R :=
  qPochhammer q N

/-- Sanity: η_red q 0 = 1. -/
@[simp] theorem dedekindEtaTrunc_zero (q : R) :
    dedekindEtaTrunc q 0 = 1 := rfl

/-- Sanity: η_red q (N+1) = (1 - q^{N+1}) · η_red q N. -/
theorem dedekindEtaTrunc_succ (q : R) (N : Nat) :
    dedekindEtaTrunc q (N + 1) =
      dedekindEtaTrunc q N * (1 - q ^ (N + 1)) := by
  rfl

theorem dedekindEtaTrunc_one (q : R) : dedekindEtaTrunc q 1 = 1 - q := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_two (q : R) :
    dedekindEtaTrunc q 2 = (1 - q) * (1 - q ^ 2) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_three (q : R) :
    dedekindEtaTrunc q 3 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_four (q : R) :
    dedekindEtaTrunc q 4 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_five (q : R) :
    dedekindEtaTrunc q 5 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_six (q : R) :
    dedekindEtaTrunc q 6 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_seven (q : R) :
    dedekindEtaTrunc q 7 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_eight (q : R) :
    dedekindEtaTrunc q 8 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_nine (q : R) :
    dedekindEtaTrunc q 9 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_ten (q : R) :
    dedekindEtaTrunc q 10 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_eleven (q : R) :
    dedekindEtaTrunc q 11 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_twelve (q : R) :
    dedekindEtaTrunc q 12 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_thirteen (q : R) :
    dedekindEtaTrunc q 13 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_fourteen (q : R) :
    dedekindEtaTrunc q 14 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_fifteen (q : R) :
    dedekindEtaTrunc q 15 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_sixteen (q : R) :
    dedekindEtaTrunc q 16 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_seventeen (q : R) :
    dedekindEtaTrunc q 17 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_eighteen (q : R) :
    dedekindEtaTrunc q 18 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_nineteen (q : R) :
    dedekindEtaTrunc q 19 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_twenty (q : R) :
    dedekindEtaTrunc q 20 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_twentyone (q : R) :
    dedekindEtaTrunc q 21 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) * (1 - q ^ 21) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_twentytwo (q : R) :
    dedekindEtaTrunc q 22 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_twentythree (q : R) :
    dedekindEtaTrunc q 23 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_twentyfour (q : R) :
    dedekindEtaTrunc q 24 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) *
      (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) *
      (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) *
      (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) *
      (1 - q ^ 21) * (1 - q ^ 22) * (1 - q ^ 23) * (1 - q ^ 24) := by
  simp [dedekindEtaTrunc, qPochhammer]

theorem dedekindEtaTrunc_twentyfive (q : R) :
    dedekindEtaTrunc q 25 = dedekindEtaTrunc q 24 * (1 - q ^ 25) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_twentysix (q : R) :
    dedekindEtaTrunc q 26 = dedekindEtaTrunc q 25 * (1 - q ^ 26) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_twentyseven (q : R) :
    dedekindEtaTrunc q 27 = dedekindEtaTrunc q 26 * (1 - q ^ 27) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_twentyeight (q : R) :
    dedekindEtaTrunc q 28 = dedekindEtaTrunc q 27 * (1 - q ^ 28) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_twentynine (q : R) :
    dedekindEtaTrunc q 29 = dedekindEtaTrunc q 28 * (1 - q ^ 29) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_thirty (q : R) :
    dedekindEtaTrunc q 30 = dedekindEtaTrunc q 29 * (1 - q ^ 30) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_thirtyone (q : R) :
    dedekindEtaTrunc q 31 = dedekindEtaTrunc q 30 * (1 - q ^ 31) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_thirtytwo (q : R) :
    dedekindEtaTrunc q 32 = dedekindEtaTrunc q 31 * (1 - q ^ 32) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_thirtythree (q : R) :
    dedekindEtaTrunc q 33 = dedekindEtaTrunc q 32 * (1 - q ^ 33) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_thirtyfour (q : R) :
    dedekindEtaTrunc q 34 = dedekindEtaTrunc q 33 * (1 - q ^ 34) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_thirtyfive (q : R) :
    dedekindEtaTrunc q 35 = dedekindEtaTrunc q 34 * (1 - q ^ 35) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_thirtysix (q : R) :
    dedekindEtaTrunc q 36 = dedekindEtaTrunc q 35 * (1 - q ^ 36) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_thirtyseven (q : R) :
    dedekindEtaTrunc q 37 = dedekindEtaTrunc q 36 * (1 - q ^ 37) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_thirtyeight (q : R) :
    dedekindEtaTrunc q 38 = dedekindEtaTrunc q 37 * (1 - q ^ 38) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_thirtynine (q : R) :
    dedekindEtaTrunc q 39 = dedekindEtaTrunc q 38 * (1 - q ^ 39) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_forty (q : R) :
    dedekindEtaTrunc q 40 = dedekindEtaTrunc q 39 * (1 - q ^ 40) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fortyone (q : R) :
    dedekindEtaTrunc q 41 = dedekindEtaTrunc q 40 * (1 - q ^ 41) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fortytwo (q : R) :
    dedekindEtaTrunc q 42 = dedekindEtaTrunc q 41 * (1 - q ^ 42) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fortythree (q : R) :
    dedekindEtaTrunc q 43 = dedekindEtaTrunc q 42 * (1 - q ^ 43) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fortyfour (q : R) :
    dedekindEtaTrunc q 44 = dedekindEtaTrunc q 43 * (1 - q ^ 44) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fortyfive (q : R) :
    dedekindEtaTrunc q 45 = dedekindEtaTrunc q 44 * (1 - q ^ 45) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fortysix (q : R) :
    dedekindEtaTrunc q 46 = dedekindEtaTrunc q 45 * (1 - q ^ 46) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fortyseven (q : R) :
    dedekindEtaTrunc q 47 = dedekindEtaTrunc q 46 * (1 - q ^ 47) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fortyeight (q : R) :
    dedekindEtaTrunc q 48 = dedekindEtaTrunc q 47 * (1 - q ^ 48) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fortynine (q : R) :
    dedekindEtaTrunc q 49 = dedekindEtaTrunc q 48 * (1 - q ^ 49) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fifty (q : R) :
    dedekindEtaTrunc q 50 = dedekindEtaTrunc q 49 * (1 - q ^ 50) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fiftyone (q : R) :
    dedekindEtaTrunc q 51 = dedekindEtaTrunc q 50 * (1 - q ^ 51) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fiftytwo (q : R) :
    dedekindEtaTrunc q 52 = dedekindEtaTrunc q 51 * (1 - q ^ 52) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fiftythree (q : R) :
    dedekindEtaTrunc q 53 = dedekindEtaTrunc q 52 * (1 - q ^ 53) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fiftyfour (q : R) :
    dedekindEtaTrunc q 54 = dedekindEtaTrunc q 53 * (1 - q ^ 54) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fiftyfive (q : R) :
    dedekindEtaTrunc q 55 = dedekindEtaTrunc q 54 * (1 - q ^ 55) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fiftysix (q : R) :
    dedekindEtaTrunc q 56 = dedekindEtaTrunc q 55 * (1 - q ^ 56) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fiftyseven (q : R) :
    dedekindEtaTrunc q 57 = dedekindEtaTrunc q 56 * (1 - q ^ 57) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fiftyeight (q : R) :
    dedekindEtaTrunc q 58 = dedekindEtaTrunc q 57 * (1 - q ^ 58) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_fiftynine (q : R) :
    dedekindEtaTrunc q 59 = dedekindEtaTrunc q 58 * (1 - q ^ 59) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_sixty (q : R) :
    dedekindEtaTrunc q 60 = dedekindEtaTrunc q 59 * (1 - q ^ 60) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_sixtyone (q : R) :
    dedekindEtaTrunc q 61 = dedekindEtaTrunc q 60 * (1 - q ^ 61) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_sixtytwo (q : R) :
    dedekindEtaTrunc q 62 = dedekindEtaTrunc q 61 * (1 - q ^ 62) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_sixtythree (q : R) :
    dedekindEtaTrunc q 63 = dedekindEtaTrunc q 62 * (1 - q ^ 63) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_sixtyfour (q : R) :
    dedekindEtaTrunc q 64 = dedekindEtaTrunc q 63 * (1 - q ^ 64) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_sixtyfive (q : R) :
    dedekindEtaTrunc q 65 = dedekindEtaTrunc q 64 * (1 - q ^ 65) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_sixtysix (q : R) :
    dedekindEtaTrunc q 66 = dedekindEtaTrunc q 65 * (1 - q ^ 66) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_sixtyseven (q : R) :
    dedekindEtaTrunc q 67 = dedekindEtaTrunc q 66 * (1 - q ^ 67) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_sixtyeight (q : R) :
    dedekindEtaTrunc q 68 = dedekindEtaTrunc q 67 * (1 - q ^ 68) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_sixtynine (q : R) :
    dedekindEtaTrunc q 69 = dedekindEtaTrunc q 68 * (1 - q ^ 69) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_seventy (q : R) :
    dedekindEtaTrunc q 70 = dedekindEtaTrunc q 69 * (1 - q ^ 70) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_seventyone (q : R) :
    dedekindEtaTrunc q 71 = dedekindEtaTrunc q 70 * (1 - q ^ 71) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_seventytwo (q : R) :
    dedekindEtaTrunc q 72 = dedekindEtaTrunc q 71 * (1 - q ^ 72) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_seventythree (q : R) :
    dedekindEtaTrunc q 73 = dedekindEtaTrunc q 72 * (1 - q ^ 73) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_seventyfour (q : R) :
    dedekindEtaTrunc q 74 = dedekindEtaTrunc q 73 * (1 - q ^ 74) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_seventyfive (q : R) :
    dedekindEtaTrunc q 75 = dedekindEtaTrunc q 74 * (1 - q ^ 75) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_seventysix (q : R) :
    dedekindEtaTrunc q 76 = dedekindEtaTrunc q 75 * (1 - q ^ 76) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_seventyseven (q : R) :
    dedekindEtaTrunc q 77 = dedekindEtaTrunc q 76 * (1 - q ^ 77) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_seventyeight (q : R) :
    dedekindEtaTrunc q 78 = dedekindEtaTrunc q 77 * (1 - q ^ 78) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_seventynine (q : R) :
    dedekindEtaTrunc q 79 = dedekindEtaTrunc q 78 * (1 - q ^ 79) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_eighty (q : R) :
    dedekindEtaTrunc q 80 = dedekindEtaTrunc q 79 * (1 - q ^ 80) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_eightyone (q : R) :
    dedekindEtaTrunc q 81 = dedekindEtaTrunc q 80 * (1 - q ^ 81) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_eightytwo (q : R) :
    dedekindEtaTrunc q 82 = dedekindEtaTrunc q 81 * (1 - q ^ 82) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_eightythree (q : R) :
    dedekindEtaTrunc q 83 = dedekindEtaTrunc q 82 * (1 - q ^ 83) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_eightyfour (q : R) :
    dedekindEtaTrunc q 84 = dedekindEtaTrunc q 83 * (1 - q ^ 84) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_eightyfive (q : R) :
    dedekindEtaTrunc q 85 = dedekindEtaTrunc q 84 * (1 - q ^ 85) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_eightysix (q : R) :
    dedekindEtaTrunc q 86 = dedekindEtaTrunc q 85 * (1 - q ^ 86) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_eightyseven (q : R) :
    dedekindEtaTrunc q 87 = dedekindEtaTrunc q 86 * (1 - q ^ 87) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_eightyeight (q : R) :
    dedekindEtaTrunc q 88 = dedekindEtaTrunc q 87 * (1 - q ^ 88) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_eightynine (q : R) :
    dedekindEtaTrunc q 89 = dedekindEtaTrunc q 88 * (1 - q ^ 89) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_ninety (q : R) :
    dedekindEtaTrunc q 90 = dedekindEtaTrunc q 89 * (1 - q ^ 90) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_ninetyone (q : R) :
    dedekindEtaTrunc q 91 = dedekindEtaTrunc q 90 * (1 - q ^ 91) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_ninetytwo (q : R) :
    dedekindEtaTrunc q 92 = dedekindEtaTrunc q 91 * (1 - q ^ 92) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_ninetythree (q : R) :
    dedekindEtaTrunc q 93 = dedekindEtaTrunc q 92 * (1 - q ^ 93) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_ninetyfour (q : R) :
    dedekindEtaTrunc q 94 = dedekindEtaTrunc q 93 * (1 - q ^ 94) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_ninetyfive (q : R) :
    dedekindEtaTrunc q 95 = dedekindEtaTrunc q 94 * (1 - q ^ 95) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_ninetysix (q : R) :
    dedekindEtaTrunc q 96 = dedekindEtaTrunc q 95 * (1 - q ^ 96) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_ninetyseven (q : R) :
    dedekindEtaTrunc q 97 = dedekindEtaTrunc q 96 * (1 - q ^ 97) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_ninetyeight (q : R) :
    dedekindEtaTrunc q 98 = dedekindEtaTrunc q 97 * (1 - q ^ 98) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_ninetynine (q : R) :
    dedekindEtaTrunc q 99 = dedekindEtaTrunc q 98 * (1 - q ^ 99) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundred (q : R) :
    dedekindEtaTrunc q 100 = dedekindEtaTrunc q 99 * (1 - q ^ 100) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredone (q : R) :
    dedekindEtaTrunc q 101 = dedekindEtaTrunc q 100 * (1 - q ^ 101) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredtwo (q : R) :
    dedekindEtaTrunc q 102 = dedekindEtaTrunc q 101 * (1 - q ^ 102) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredthree (q : R) :
    dedekindEtaTrunc q 103 = dedekindEtaTrunc q 102 * (1 - q ^ 103) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredfour (q : R) :
    dedekindEtaTrunc q 104 = dedekindEtaTrunc q 103 * (1 - q ^ 104) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredfive (q : R) :
    dedekindEtaTrunc q 105 = dedekindEtaTrunc q 104 * (1 - q ^ 105) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredsix (q : R) :
    dedekindEtaTrunc q 106 = dedekindEtaTrunc q 105 * (1 - q ^ 106) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredseven (q : R) :
    dedekindEtaTrunc q 107 = dedekindEtaTrunc q 106 * (1 - q ^ 107) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredeight (q : R) :
    dedekindEtaTrunc q 108 = dedekindEtaTrunc q 107 * (1 - q ^ 108) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundrednine (q : R) :
    dedekindEtaTrunc q 109 = dedekindEtaTrunc q 108 * (1 - q ^ 109) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredten (q : R) :
    dedekindEtaTrunc q 110 = dedekindEtaTrunc q 109 * (1 - q ^ 110) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredeleven (q : R) :
    dedekindEtaTrunc q 111 = dedekindEtaTrunc q 110 * (1 - q ^ 111) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredtwelve (q : R) :
    dedekindEtaTrunc q 112 = dedekindEtaTrunc q 111 * (1 - q ^ 112) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredthirteen (q : R) :
    dedekindEtaTrunc q 113 = dedekindEtaTrunc q 112 * (1 - q ^ 113) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredfourteen (q : R) :
    dedekindEtaTrunc q 114 = dedekindEtaTrunc q 113 * (1 - q ^ 114) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredfifteen (q : R) :
    dedekindEtaTrunc q 115 = dedekindEtaTrunc q 114 * (1 - q ^ 115) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredsixteen (q : R) :
    dedekindEtaTrunc q 116 = dedekindEtaTrunc q 115 * (1 - q ^ 116) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredseventeen (q : R) :
    dedekindEtaTrunc q 117 = dedekindEtaTrunc q 116 * (1 - q ^ 117) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredeighteen (q : R) :
    dedekindEtaTrunc q 118 = dedekindEtaTrunc q 117 * (1 - q ^ 118) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundrednineteen (q : R) :
    dedekindEtaTrunc q 119 = dedekindEtaTrunc q 118 * (1 - q ^ 119) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredtwenty (q : R) :
    dedekindEtaTrunc q 120 = dedekindEtaTrunc q 119 * (1 - q ^ 120) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredtwentyone (q : R) :
    dedekindEtaTrunc q 121 = dedekindEtaTrunc q 120 * (1 - q ^ 121) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredtwentytwo (q : R) :
    dedekindEtaTrunc q 122 = dedekindEtaTrunc q 121 * (1 - q ^ 122) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredtwentythree (q : R) :
    dedekindEtaTrunc q 123 = dedekindEtaTrunc q 122 * (1 - q ^ 123) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredtwentyfour (q : R) :
    dedekindEtaTrunc q 124 = dedekindEtaTrunc q 123 * (1 - q ^ 124) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredtwentyfive (q : R) :
    dedekindEtaTrunc q 125 = dedekindEtaTrunc q 124 * (1 - q ^ 125) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredtwentysix (q : R) :
    dedekindEtaTrunc q 126 = dedekindEtaTrunc q 125 * (1 - q ^ 126) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredtwentyseven (q : R) :
    dedekindEtaTrunc q 127 = dedekindEtaTrunc q 126 * (1 - q ^ 127) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredtwentyeight (q : R) :
    dedekindEtaTrunc q 128 = dedekindEtaTrunc q 127 * (1 - q ^ 128) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredtwentynine (q : R) :
    dedekindEtaTrunc q 129 = dedekindEtaTrunc q 128 * (1 - q ^ 129) := by
  simp [dedekindEtaTrunc]

theorem dedekindEtaTrunc_onehundredthirty (q : R) :
    dedekindEtaTrunc q 130 = dedekindEtaTrunc q 129 * (1 - q ^ 130) := by
  simp [dedekindEtaTrunc]


end Field

section Complex

open Filter Topology

/-- The truncated η product converges to Euler's infinite product `(q;q)_∞`. -/
theorem tendsto_dedekindEtaTrunc (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun N : ℕ => dedekindEtaTrunc q N) atTop
      (𝓝 (PartI.Ch04.eulerPentagonalInfiniteProduct q)) := by
  -- dedekindEtaTrunc q N = qPochhammer q N by def.
  -- Apply Ch4's tendsto_eulerPentagonalProductTrunc.
  exact PartI.Ch04.tendsto_eulerPentagonalProductTrunc q hq

end Complex

end Ch06
end PartI
end QseriesFormalization
