import QseriesFormalization.Basic

/-!
# Chapter 14 — Dyson-Garvan crank

⚠️  **AUX CHAPTER — chapter-main result OPEN**.

Per `PLAYBOOK_AUDIT.md` (2026-05-22): this file contains the formal
definition of the crank statistic (`crank`, `crankOnes`, `crankMu`,
`crankLargest`) and the trivial-shape calculations:

  • `crank_singleton`  : the partition `[n]` has crank `n` (n ≥ 2)
  • `crank_allOnes`    : the partition `[1,1,…,1]` of `n` has crank `-n` (n ≥ 1)

These give two of the five mod-5 residue classes for partitions of 4
(cranks 4 ≡ 4 and -4 ≡ 1 mod 5).  The truncations
`crankGenNumeratorTrunc_N`, `crankGenDenominatorTrunc_N`, etc. are
mechanical scaffold.

**Chan's Ch 14 main result — the Dyson-Garvan theorem that the crank
distributes evenly mod 5 / mod 7 / mod 11 over partitions of `5n+4` /
`7n+5` / `11n+6` respectively, thereby explaining the Ramanujan
congruences combinatorially — is NOT formalized here.**  Even the n=4
special case (`crankDistMod5OfFour` hits all 5 residues mod 5) is only
asserted at the level of definition, not proved.
-/

namespace QseriesFormalization
namespace PartIII
namespace Ch14

section Field

variable {R : Type*} [Field R]

/-- Truncated crank generating function numerator: `(q; q)_N`. -/
noncomputable def crankGenNumeratorTrunc (q : R) (N : Nat) : R :=
  qPochhammer q N

/-- Truncated crank generating function denominator for parameter z:
`(zq; q)_N · (z⁻¹q; q)_N`. -/
noncomputable def crankGenDenominatorTrunc (z q : R) (N : Nat) : R :=
  qPoch (z * q) q N * qPoch (z⁻¹ * q) q N

/-- Truncated crank generating function:
`C_N(z, q) = (q; q)_N / ((zq; q)_N · (z⁻¹q; q)_N)`. -/
noncomputable def crankGenTrunc (z q : R) (N : Nat) : R :=
  crankGenNumeratorTrunc q N / crankGenDenominatorTrunc z q N

@[simp] theorem crankGenNumeratorTrunc_zero (q : R) :
    crankGenNumeratorTrunc q 0 = 1 := rfl

@[simp] theorem crankGenDenominatorTrunc_zero (z q : R) :
    crankGenDenominatorTrunc z q 0 = 1 := by
  simp [crankGenDenominatorTrunc, qPoch]

theorem crankGenTrunc_zero (z q : R) :
    crankGenTrunc z q 0 = 1 := by
  simp [crankGenTrunc, crankGenNumeratorTrunc, crankGenDenominatorTrunc, qPoch]

/-- Recursion for the truncated crank numerator
`(q; q)_(N+1) = (q; q)_N · (1 − q^(N+1))`. -/
theorem crankGenNumeratorTrunc_succ (q : R) (N : Nat) :
    crankGenNumeratorTrunc q (N + 1) =
      crankGenNumeratorTrunc q N * (1 - q ^ (N + 1)) := by
  simp [crankGenNumeratorTrunc, qPochhammer_succ]

/-- Recursion for the truncated crank denominator
`(zq; q)_(N+1) · (z⁻¹q; q)_(N+1)
  = (zq; q)_N · (z⁻¹q; q)_N · (1 − zq^(N+1)) · (1 − z⁻¹q^(N+1))`. -/
theorem crankGenDenominatorTrunc_succ (z q : R) (N : Nat) :
    crankGenDenominatorTrunc z q (N + 1) =
      crankGenDenominatorTrunc z q N *
        (1 - z * q * q ^ N) * (1 - z⁻¹ * q * q ^ N) := by
  simp [crankGenDenominatorTrunc, qPoch_succ]
  ring

theorem crankGenNumeratorTrunc_one (q : R) :
    crankGenNumeratorTrunc q 1 = 1 - q := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenDenominatorTrunc_one (z q : R) :
    crankGenDenominatorTrunc z q 1 = (1 - z * q) * (1 - z⁻¹ * q) := by
  simp [crankGenDenominatorTrunc, qPoch]

theorem crankGenNumeratorTrunc_two (q : R) :
    crankGenNumeratorTrunc q 2 = (1 - q) * (1 - q ^ 2) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenDenominatorTrunc_two (z q : R) :
    crankGenDenominatorTrunc z q 2 =
      ((1 - z * q) * (1 - z * q ^ 2)) * ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring

theorem crankGenNumeratorTrunc_three (q : R) :
    crankGenNumeratorTrunc q 3 = (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

/-- At z = 1, the crank numerator and denominator simplify:
numerator = (q;q)_N, denominator uses (q;q)_N^2, so the ratio is 1/(q;q)_N
(the partition generating function). This is Chan's Eq. (14.1). -/
theorem crankGenNumeratorTrunc_eq_qPochhammer (q : R) (N : Nat) :
    crankGenNumeratorTrunc q N = qPochhammer q N := rfl

theorem crankGenNumeratorTrunc_four (q : R) :
    crankGenNumeratorTrunc q 4 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenNumeratorTrunc_five (q : R) :
    crankGenNumeratorTrunc q 5 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenNumeratorTrunc_six (q : R) :
    crankGenNumeratorTrunc q 6 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenDenominatorTrunc_three (z q : R) :
    crankGenDenominatorTrunc z q 3 =
      ((1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3)) *
      ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring

theorem crankGenDenominatorTrunc_four (z q : R) :
    crankGenDenominatorTrunc z q 4 =
      ((1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3) * (1 - z * q ^ 4)) *
      ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3) * (1 - z⁻¹ * q ^ 4)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring

theorem crankGenDenominatorTrunc_five (z q : R) :
    crankGenDenominatorTrunc z q 5 =
      ((1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3) * (1 - z * q ^ 4) * (1 - z * q ^ 5)) *
      ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3) * (1 - z⁻¹ * q ^ 4) * (1 - z⁻¹ * q ^ 5)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring

theorem crankGenDenominatorTrunc_six (z q : R) :
    crankGenDenominatorTrunc z q 6 =
      ((1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3) * (1 - z * q ^ 4) * (1 - z * q ^ 5) * (1 - z * q ^ 6)) *
      ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3) * (1 - z⁻¹ * q ^ 4) * (1 - z⁻¹ * q ^ 5) * (1 - z⁻¹ * q ^ 6)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring

theorem crankGenNumeratorTrunc_seven (q : R) :
    crankGenNumeratorTrunc q 7 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenNumeratorTrunc_eight (q : R) :
    crankGenNumeratorTrunc q 8 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenDenominatorTrunc_seven (z q : R) :
    crankGenDenominatorTrunc z q 7 =
      ((1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3) * (1 - z * q ^ 4) *
       (1 - z * q ^ 5) * (1 - z * q ^ 6) * (1 - z * q ^ 7)) *
      ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3) * (1 - z⁻¹ * q ^ 4) *
       (1 - z⁻¹ * q ^ 5) * (1 - z⁻¹ * q ^ 6) * (1 - z⁻¹ * q ^ 7)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring

theorem crankGenDenominatorTrunc_eight (z q : R) :
    crankGenDenominatorTrunc z q 8 =
      ((1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3) * (1 - z * q ^ 4) *
       (1 - z * q ^ 5) * (1 - z * q ^ 6) * (1 - z * q ^ 7) * (1 - z * q ^ 8)) *
      ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3) * (1 - z⁻¹ * q ^ 4) *
       (1 - z⁻¹ * q ^ 5) * (1 - z⁻¹ * q ^ 6) * (1 - z⁻¹ * q ^ 7) * (1 - z⁻¹ * q ^ 8)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring

theorem crankGenNumeratorTrunc_nine (q : R) :
    crankGenNumeratorTrunc q 9 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenDenominatorTrunc_nine (z q : R) :
    crankGenDenominatorTrunc z q 9 =
      ((1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3) * (1 - z * q ^ 4) *
       (1 - z * q ^ 5) * (1 - z * q ^ 6) * (1 - z * q ^ 7) * (1 - z * q ^ 8) * (1 - z * q ^ 9)) *
      ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3) * (1 - z⁻¹ * q ^ 4) *
       (1 - z⁻¹ * q ^ 5) * (1 - z⁻¹ * q ^ 6) * (1 - z⁻¹ * q ^ 7) * (1 - z⁻¹ * q ^ 8) * (1 - z⁻¹ * q ^ 9)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring

theorem crankGenNumeratorTrunc_ten (q : R) :
    crankGenNumeratorTrunc q 10 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenDenominatorTrunc_ten (z q : R) :
    crankGenDenominatorTrunc z q 10 =
      ((1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3) * (1 - z * q ^ 4) *
       (1 - z * q ^ 5) * (1 - z * q ^ 6) * (1 - z * q ^ 7) * (1 - z * q ^ 8) * (1 - z * q ^ 9) * (1 - z * q ^ 10)) *
      ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3) * (1 - z⁻¹ * q ^ 4) *
       (1 - z⁻¹ * q ^ 5) * (1 - z⁻¹ * q ^ 6) * (1 - z⁻¹ * q ^ 7) * (1 - z⁻¹ * q ^ 8) * (1 - z⁻¹ * q ^ 9) * (1 - z⁻¹ * q ^ 10)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring

theorem crankGenNumeratorTrunc_eleven (q : R) :
    crankGenNumeratorTrunc q 11 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenDenominatorTrunc_eleven (z q : R) :
    crankGenDenominatorTrunc z q 11 =
      ((1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3) * (1 - z * q ^ 4) *
       (1 - z * q ^ 5) * (1 - z * q ^ 6) * (1 - z * q ^ 7) * (1 - z * q ^ 8) * (1 - z * q ^ 9) * (1 - z * q ^ 10) * (1 - z * q ^ 11)) *
      ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3) * (1 - z⁻¹ * q ^ 4) *
       (1 - z⁻¹ * q ^ 5) * (1 - z⁻¹ * q ^ 6) * (1 - z⁻¹ * q ^ 7) * (1 - z⁻¹ * q ^ 8) * (1 - z⁻¹ * q ^ 9) * (1 - z⁻¹ * q ^ 10) * (1 - z⁻¹ * q ^ 11)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring

theorem crankGenNumeratorTrunc_twelve (q : R) :
    crankGenNumeratorTrunc q 12 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenDenominatorTrunc_twelve (z q : R) :
    crankGenDenominatorTrunc z q 12 =
      ((1 - z * q) * (1 - z * q ^ 2) * (1 - z * q ^ 3) * (1 - z * q ^ 4) *
       (1 - z * q ^ 5) * (1 - z * q ^ 6) * (1 - z * q ^ 7) * (1 - z * q ^ 8) * (1 - z * q ^ 9) * (1 - z * q ^ 10) * (1 - z * q ^ 11) * (1 - z * q ^ 12)) *
      ((1 - z⁻¹ * q) * (1 - z⁻¹ * q ^ 2) * (1 - z⁻¹ * q ^ 3) * (1 - z⁻¹ * q ^ 4) *
       (1 - z⁻¹ * q ^ 5) * (1 - z⁻¹ * q ^ 6) * (1 - z⁻¹ * q ^ 7) * (1 - z⁻¹ * q ^ 8) * (1 - z⁻¹ * q ^ 9) * (1 - z⁻¹ * q ^ 10) * (1 - z⁻¹ * q ^ 11) * (1 - z⁻¹ * q ^ 12)) := by
  simp [crankGenDenominatorTrunc, qPoch]
  ring

theorem crankGenNumeratorTrunc_thirteen (q : R) :
    crankGenNumeratorTrunc q 13 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenNumeratorTrunc_fourteen (q : R) :
    crankGenNumeratorTrunc q 14 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenNumeratorTrunc_fifteen (q : R) :
    crankGenNumeratorTrunc q 15 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenNumeratorTrunc_sixteen (q : R) :
    crankGenNumeratorTrunc q 16 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenNumeratorTrunc_seventeen (q : R) :
    crankGenNumeratorTrunc q 17 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenNumeratorTrunc_eighteen (q : R) :
    crankGenNumeratorTrunc q 18 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenNumeratorTrunc_nineteen (q : R) :
    crankGenNumeratorTrunc q 19 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

theorem crankGenNumeratorTrunc_twenty (q : R) :
    crankGenNumeratorTrunc q 20 =
      (1 - q) * (1 - q ^ 2) * (1 - q ^ 3) * (1 - q ^ 4) * (1 - q ^ 5) * (1 - q ^ 6) * (1 - q ^ 7) * (1 - q ^ 8) * (1 - q ^ 9) * (1 - q ^ 10) * (1 - q ^ 11) * (1 - q ^ 12) * (1 - q ^ 13) * (1 - q ^ 14) * (1 - q ^ 15) * (1 - q ^ 16) * (1 - q ^ 17) * (1 - q ^ 18) * (1 - q ^ 19) * (1 - q ^ 20) := by
  simp [crankGenNumeratorTrunc, qPochhammer]

end Field

/-! ### Crank statistic on partitions (Andrews-Garvan 1988)

The crank `c(λ)` of a partition `λ` is defined as:
- If `1 ∉ parts(λ)`: `c(λ) = largest part of λ`.
- If `1 ∈ parts(λ)`: let `ω(λ) = #{occurrences of 1 in λ}`, and
  `μ(λ) = #{parts of λ strictly greater than ω(λ)}`. Then `c(λ) = μ(λ) - ω(λ)`.

Andrews and Garvan showed (1988) that the crank refines the partition function
in such a way that the residue classes modulo 5, 7, 11 explain the
Ramanujan congruences combinatorially.

We work with `Nat.Partition n` from Mathlib (parts is a `Multiset ℕ`). -/

section Crank

open Nat

/-- Number of 1's in a partition: `ω(lam) = (lam.parts).count 1`. -/
def crankOnes {n : Nat} (lam : Nat.Partition n) : Nat :=
  lam.parts.count 1

/-- Number of parts of `lam` strictly greater than `ω(lam)`. -/
noncomputable def crankMu {n : Nat} (lam : Nat.Partition n) : Nat :=
  (lam.parts.filter (fun x => x > crankOnes lam)).card

/-- Largest part of a partition `lam` (or 0 for the empty partition). -/
noncomputable def crankLargest {n : Nat} (lam : Nat.Partition n) : Nat :=
  lam.parts.fold max 0

/-- **The Andrews-Garvan crank** `c(lam) : ℤ`. -/
noncomputable def crank {n : Nat} (lam : Nat.Partition n) : Int :=
  if 1 ∈ lam.parts then
    (crankMu lam : Int) - (crankOnes lam : Int)
  else
    (crankLargest lam : Int)

/-- Crank distribution of partitions of 4 (mod 5).
The 5 partitions of 4 have cranks {4, 0, 2, -2, -4}, distinct residues mod 5.
This explains Ramanujan's `p(4) ≡ 0 (mod 5)` combinatorially: the 5 partitions
partition into 5 classes mod 5 of crank, each class containing exactly 1 partition. -/
noncomputable def crankDistMod5OfFour : Multiset (ZMod 5) :=
  (Finset.univ : Finset (Nat.Partition 4)).val.map (fun p => ((crank p) : ZMod 5))

/-- The unique-largest-part partition `[n]` (single part of size `n`, for `n ≥ 2`) has
crank `n`, since `1 ∉ parts` and the largest part is `n`. -/
theorem crank_singleton (n : Nat) (hn : 2 ≤ n) :
    let p : Nat.Partition n := {
      parts := {n}
      parts_pos := by intro a ha; rw [Multiset.mem_singleton] at ha; omega
      parts_sum := by rw [Multiset.sum_singleton] }
    (crank p : Int) = n := by
  show (if (1 : ℕ) ∈ ({n} : Multiset ℕ) then
        ((crankMu _ : Int) - (crankOnes _ : Int)) else (crankLargest _ : Int)) = (n : Int)
  rw [if_neg (by rw [Multiset.mem_singleton]; omega)]
  show ((({n} : Multiset ℕ).fold max 0 : Nat) : Int) = (n : Int)
  rw [show ({n} : Multiset ℕ) = (n ::ₘ 0 : Multiset ℕ) from rfl]
  rw [Multiset.fold_cons_left]
  simp

/-- The all-ones partition `[1, 1, ..., 1]` of `n` (n copies of 1, for `n ≥ 1`) has
crank `-n`: `ω = n` (n ones), `μ = 0` (no parts > n), so crank = 0 - n = -n. -/
theorem crank_allOnes (n : Nat) (hn : 1 ≤ n) :
    let p : Nat.Partition n := {
      parts := Multiset.replicate n 1
      parts_pos := by
        intro a ha; rw [Multiset.mem_replicate] at ha; omega
      parts_sum := by
        rw [Multiset.sum_replicate]; simp }
    (crank p : Int) = -n := by
  show (if (1 : ℕ) ∈ (Multiset.replicate n 1 : Multiset ℕ) then
        ((crankMu _ : Int) - (crankOnes _ : Int))
        else (crankLargest _ : Int)) = -(n : Int)
  have h_mem : (1 : ℕ) ∈ (Multiset.replicate n 1 : Multiset ℕ) := by
    rw [Multiset.mem_replicate]; exact ⟨by omega, rfl⟩
  rw [if_pos h_mem]
  -- Compute crankOnes = n
  have h_ones : crankOnes (n := n) ⟨Multiset.replicate n 1,
      by intro a ha; rw [Multiset.mem_replicate] at ha; omega,
      by rw [Multiset.sum_replicate]; simp⟩ = n := by
    show (Multiset.replicate n 1).count 1 = n
    rw [Multiset.count_replicate]; simp
  -- Compute crankMu = 0: no parts > n in {1, 1, ..., 1}
  have h_mu : crankMu (n := n) ⟨Multiset.replicate n 1,
      by intro a ha; rw [Multiset.mem_replicate] at ha; omega,
      by rw [Multiset.sum_replicate]; simp⟩ = 0 := by
    show ((Multiset.replicate n 1).filter (fun x => x > _)).card = 0
    rw [Multiset.card_eq_zero]
    apply Multiset.filter_eq_nil.mpr
    intro x hx
    rw [Multiset.mem_replicate] at hx
    obtain ⟨_, rfl⟩ := hx
    show ¬ 1 > _
    rw [h_ones]
    omega
  rw [h_ones, h_mu]
  simp

end Crank

end Ch14
end PartIII
end QseriesFormalization
