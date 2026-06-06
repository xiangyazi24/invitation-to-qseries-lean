import QseriesFormalization.Basic
import QseriesFormalization.Chapter01
import QseriesFormalization.Chapter19
import QseriesFormalization.Pending.Chapter17_Ramanujan5Conditional

/-!
# Chapter 17 — Ramanujan's partition congruences

**STATUS (2026-05-23)**: `∀ n, 5 ∣ p(5n+4)` is now **UNCONDITIONALLY** proven
(see `Pending/Chapter17_Ramanujan5Conditional.ramanujan_5_dvd_p_5n_plus_4`,
re-exported here as `ramanujan_5_dvd_p_5n_plus_4`).  The proof uses the
analytic-formal Taylor uniqueness bridge `Pending/JacobiCubeAnalyticToFormal`
to discharge the formal-PS B2 hypothesis `(qPochInfPS R)^3 = jacobiThetaPS R`.

The mod-7 and mod-11 analogs (Ramanujan's 2nd and 3rd congruences) are
**NOT** discharged unconditionally — they need η-quotient identities
(Chan §17.2/17.3) substantially more involved than the mod-5 case.
-/

namespace QseriesFormalization
namespace PartIV
namespace Ch17

open QseriesFormalization.Ch01 (partitionCount)

/-! ## Chapter-main: UNCONDITIONAL Ramanujan's first congruence (Ch17 §17.1)

The unconditional theorem `ramanujan_5_dvd_p_5n_plus_4 : ∀ n, 5 ∣ p(5n+4)`
lives in `Pending/Chapter17_Ramanujan5Conditional.lean` under the SAME
namespace `QseriesFormalization.PartIV.Ch17`, so it's directly accessible
as `QseriesFormalization.PartIV.Ch17.ramanujan_5_dvd_p_5n_plus_4` once
that file is imported (which it is, transitively, via the imports above). -/

/-! ## Chapter-main: conditional general Ramanujan congruences (Ch17) -/

/-- **Chan Ch 17 main theorem, conditional form.**  If
`((q;q)_∞)^(p-1)` (as a formal power series over `ZMod p`) vanishes at
every coefficient of the form `p·n + r` (for `r < p` fixed), then
`p ∣ p(p·n+r)` for all `n`.

This is the general Ramanujan partition congruence pattern, proved by
strong induction in `Chapter19.ramanujan_from_pochInf_vanishes`.  When
`p ∈ {5, 7, 11}` and `r = p − 1`, `4`, `6` respectively, the vanishing
hypothesis is exactly Ramanujan's original generating-function identity. -/
theorem ramanujan_congruence_general (p : Nat) [Fact (Nat.Prime p)] (hp : p ≠ 0)
    (r : Nat) (hr : r < p)
    (hvanish : ∀ n,
      ((QseriesFormalization.PartIV.Ch19.qPochInfPS (ZMod p)) ^ (p - 1)).coeff
        (p * n + r) = 0) :
    ∀ n, ((partitionCount (p * n + r) : Nat) : ZMod p) = 0 :=
  QseriesFormalization.PartIV.Ch19.ramanujan_from_pochInf_vanishes p hp r hr hvanish

/-- Concrete check for `p(5n+4) = 0 (mod 5)` at n=0: p(4) = 5. -/
theorem partition_5n_plus_4_mod_5_n_zero :
    partitionCount (5 * 0 + 4) % 5 = 0 := by
  simp [Ch01.partitionCount_four]

/-- Concrete check at n=1: p(9) = 30 = 6 * 5, divisible by 5. -/
theorem partition_5n_plus_4_mod_5_n_one :
    partitionCount (5 * 1 + 4) % 5 = 0 := by
  simp [Ch01.partitionCount_nine]

/-- Concrete check for `p(7n+5) = 0 (mod 7)` at n=0: p(5) = 7. -/
theorem partition_7n_plus_5_mod_7_n_zero :
    partitionCount (7 * 0 + 5) % 7 = 0 := by
  simp [Ch01.partitionCount_five]

/-- Concrete check for `p(11n+6) = 0 (mod 11)` at n=0: p(6) = 11. -/
theorem partition_11n_plus_6_mod_11_n_zero :
    partitionCount (11 * 0 + 6) % 11 = 0 := by
  simp [Ch01.partitionCount_six]

/-- p(4) ≡ 0 (mod 5) — restated via Nat.dvd for alternative API. -/
theorem partition_four_dvd_five : 5 ∣ partitionCount 4 := by
  simp [Ch01.partitionCount_four]

/-- p(9) ≡ 0 (mod 5). -/
theorem partition_nine_dvd_five : 5 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

/-- p(5) ≡ 0 (mod 7). -/
theorem partition_five_dvd_seven : 7 ∣ partitionCount 5 := by
  simp [Ch01.partitionCount_five]

/-- p(6) ≡ 0 (mod 11). -/
theorem partition_six_dvd_eleven : 11 ∣ partitionCount 6 := by
  simp [Ch01.partitionCount_six]

/-- p(9) ≡ 0 (mod 10): p(9) = 30. -/
theorem partition_nine_dvd_ten : 10 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

/-- p(9) ≡ 0 (mod 15): p(9) = 30. -/
theorem partition_nine_dvd_fifteen : 15 ∣ partitionCount 9 := by
  simp [Ch01.partitionCount_nine]

/-- p(10) ≡ 0 (mod 7): p(10) = 42 = 6·7. -/
theorem partition_ten_dvd_seven : 7 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(10) ≡ 0 (mod 6): p(10) = 42 = 7·6. -/
theorem partition_ten_dvd_six : 6 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(7) ≡ 0 (mod 5): p(7) = 15 = 3·5. -/
theorem partition_seven_dvd_five : 5 ∣ partitionCount 7 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) ≡ 0 (mod 2): p(8) = 22 = 11·2. -/
theorem partition_eight_dvd_two : 2 ∣ partitionCount 8 := by
  simp [Ch01.partitionCount_eight]

/-- p(11) ≡ 0 (mod 7): p(11) = 56 = 8·7. -/
theorem partition_eleven_dvd_seven : 7 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(11) ≡ 0 (mod 8): p(11) = 56 = 7·8. -/
theorem partition_eleven_dvd_eight : 8 ∣ partitionCount 11 := by
  simp [Ch01.partitionCount_eleven]

/-- p(7) ≡ 0 (mod 3): p(7) = 15 = 5·3. -/
theorem partition_seven_dvd_three : 3 ∣ partitionCount 7 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) ≡ 0 (mod 11): p(8) = 22 = 2·11. -/
theorem partition_eight_dvd_eleven : 11 ∣ partitionCount 8 := by
  simp [Ch01.partitionCount_eight]

/-- p(10) ≡ 0 (mod 2): p(10) = 42. -/
theorem partition_ten_dvd_two : 2 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(10) ≡ 0 (mod 3): p(10) = 42 = 14·3. -/
theorem partition_ten_dvd_three : 3 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(10) ≡ 0 (mod 14): p(10) = 42 = 3·14. -/
theorem partition_ten_dvd_fourteen : 14 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(10) ≡ 0 (mod 21): p(10) = 42 = 2·21. -/
theorem partition_ten_dvd_twentyone : 21 ∣ partitionCount 10 := by
  simp [Ch01.partitionCount_ten]

/-- p(0) = 1 mod 5 = 1. Not a Ramanujan congruence case. -/
theorem partition_zero_mod_five : partitionCount 0 % 5 = 1 := by
  simp [Ch01.partitionCount_zero]

/-- p(1) = 1 mod 7 = 1. -/
theorem partition_one_mod_seven : partitionCount 1 % 7 = 1 := by
  simp [Ch01.partitionCount_one]

/-- p(2) = 2 mod 5 = 2. -/
theorem partition_two_mod_five : partitionCount 2 % 5 = 2 := by
  simp [Ch01.partitionCount_two]

/-- p(3) = 3 mod 5 = 3. -/
theorem partition_three_mod_five : partitionCount 3 % 5 = 3 := by
  simp [Ch01.partitionCount_three]

/-- p(4) = 5 mod 5 = 0. Ramanujan: p(5·0+4) ≡ 0 (mod 5). -/
theorem partition_four_mod_five : partitionCount 4 % 5 = 0 := by
  simp [Ch01.partitionCount_four]

/-- p(5) = 7 mod 7 = 0. Ramanujan: p(7·0+5) ≡ 0 (mod 7). -/
theorem partition_five_mod_seven : partitionCount 5 % 7 = 0 := by
  simp [Ch01.partitionCount_five]

/-- p(6) = 11 mod 11 = 0. Ramanujan: p(11·0+6) ≡ 0 (mod 11). -/
theorem partition_six_mod_eleven : partitionCount 6 % 11 = 0 := by
  simp [Ch01.partitionCount_six]

/-- p(9) = 30 mod 5 = 0. Ramanujan: p(5·1+4) ≡ 0 (mod 5). -/
theorem partition_nine_mod_five : partitionCount 9 % 5 = 0 := by
  simp [Ch01.partitionCount_nine]

/-- p(5) mod 5 = 2. -/
theorem partition_five_mod_five : partitionCount 5 % 5 = 2 := by
  simp [Ch01.partitionCount_five]

/-- p(6) mod 5 = 1. -/
theorem partition_six_mod_five : partitionCount 6 % 5 = 1 := by
  simp [Ch01.partitionCount_six]

/-- p(7) mod 7 = 1. -/
theorem partition_seven_mod_seven : partitionCount 7 % 7 = 1 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) mod 7 = 1. -/
theorem partition_eight_mod_seven : partitionCount 8 % 7 = 1 := by
  simp [Ch01.partitionCount_eight]

/-- p(9) mod 7 = 2. -/
theorem partition_nine_mod_seven : partitionCount 9 % 7 = 2 := by
  simp [Ch01.partitionCount_nine]

/-- p(10) mod 7 = 0. Ramanujan: p(7·0+5)=7 but also p(10)=42. -/
theorem partition_ten_mod_seven : partitionCount 10 % 7 = 0 := by
  simp [Ch01.partitionCount_ten]

/-- p(11) mod 7 = 0. -/
theorem partition_eleven_mod_seven : partitionCount 11 % 7 = 0 := by
  simp [Ch01.partitionCount_eleven]

/-- p(7) mod 11 = 4. -/
theorem partition_seven_mod_eleven : partitionCount 7 % 11 = 4 := by
  simp [Ch01.partitionCount_seven]

/-- p(8) mod 11 = 0. p(8) = 22 = 2·11. -/
theorem partition_eight_mod_eleven : partitionCount 8 % 11 = 0 := by
  simp [Ch01.partitionCount_eight]

/-- p(9) mod 11 = 8. -/
theorem partition_nine_mod_eleven : partitionCount 9 % 11 = 8 := by
  simp [Ch01.partitionCount_nine]

/-- p(10) mod 11 = 9. -/
theorem partition_ten_mod_eleven : partitionCount 10 % 11 = 9 := by
  simp [Ch01.partitionCount_ten]

/-- p(11) mod 11 = 1. -/
theorem partition_eleven_mod_eleven : partitionCount 11 % 11 = 1 := by
  simp [Ch01.partitionCount_eleven]

theorem partition_one_mod_five : partitionCount 1 % 5 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_seven_mod_five : partitionCount 7 % 5 = 0 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_five : partitionCount 8 % 5 = 2 := by
  simp [Ch01.partitionCount_eight]

theorem partition_ten_mod_five : partitionCount 10 % 5 = 2 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_five : partitionCount 11 % 5 = 1 := by
  simp [Ch01.partitionCount_eleven]

theorem partition_zero_mod_seven : partitionCount 0 % 7 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_two_mod_seven : partitionCount 2 % 7 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_seven : partitionCount 3 % 7 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_seven : partitionCount 4 % 7 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_six_mod_seven : partitionCount 6 % 7 = 4 := by
  simp [Ch01.partitionCount_six]

theorem partition_zero_mod_eleven : partitionCount 0 % 11 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_eleven : partitionCount 1 % 11 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_eleven : partitionCount 2 % 11 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_eleven : partitionCount 3 % 11 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_eleven : partitionCount 4 % 11 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_eleven : partitionCount 5 % 11 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_zero_mod_thirteen : partitionCount 0 % 13 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_thirteen : partitionCount 1 % 13 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_thirteen : partitionCount 2 % 13 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_thirteen : partitionCount 3 % 13 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_thirteen : partitionCount 4 % 13 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_thirteen : partitionCount 5 % 13 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_thirteen : partitionCount 6 % 13 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_thirteen : partitionCount 7 % 13 = 2 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_thirteen : partitionCount 8 % 13 = 9 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_thirteen : partitionCount 9 % 13 = 4 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_thirteen : partitionCount 10 % 13 = 3 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_thirteen : partitionCount 11 % 13 = 4 := by
  simp [Ch01.partitionCount_eleven]

theorem partition_zero_mod_seventeen : partitionCount 0 % 17 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_seventeen : partitionCount 1 % 17 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_seventeen : partitionCount 2 % 17 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_seventeen : partitionCount 3 % 17 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_seventeen : partitionCount 4 % 17 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_seventeen : partitionCount 5 % 17 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_seventeen : partitionCount 6 % 17 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_seventeen : partitionCount 7 % 17 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_seventeen : partitionCount 8 % 17 = 5 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_seventeen : partitionCount 9 % 17 = 13 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_seventeen : partitionCount 10 % 17 = 8 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_seventeen : partitionCount 11 % 17 = 5 := by
  simp [Ch01.partitionCount_eleven]

theorem partition_zero_mod_nineteen : partitionCount 0 % 19 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_nineteen : partitionCount 1 % 19 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_nineteen : partitionCount 2 % 19 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_nineteen : partitionCount 3 % 19 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_nineteen : partitionCount 4 % 19 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_nineteen : partitionCount 5 % 19 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_nineteen : partitionCount 6 % 19 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_nineteen : partitionCount 7 % 19 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_nineteen : partitionCount 8 % 19 = 3 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_nineteen : partitionCount 9 % 19 = 11 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_nineteen : partitionCount 10 % 19 = 4 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_nineteen : partitionCount 11 % 19 = 18 := by
  simp [Ch01.partitionCount_eleven]

theorem partition_zero_mod_twentythree : partitionCount 0 % 23 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_twentythree : partitionCount 1 % 23 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_twentythree : partitionCount 2 % 23 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_twentythree : partitionCount 3 % 23 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_twentythree : partitionCount 4 % 23 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_twentythree : partitionCount 5 % 23 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_twentythree : partitionCount 6 % 23 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_twentythree : partitionCount 7 % 23 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_twentythree : partitionCount 8 % 23 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_twentythree : partitionCount 9 % 23 = 7 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_twentythree : partitionCount 10 % 23 = 19 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_twentythree : partitionCount 11 % 23 = 10 := by
  simp [Ch01.partitionCount_eleven]

theorem partition_zero_mod_two : partitionCount 0 % 2 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_two : partitionCount 1 % 2 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_two : partitionCount 2 % 2 = 0 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_two : partitionCount 3 % 2 = 1 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_two : partitionCount 4 % 2 = 1 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_two : partitionCount 5 % 2 = 1 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_two : partitionCount 6 % 2 = 1 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_two : partitionCount 7 % 2 = 1 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_two : partitionCount 8 % 2 = 0 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_two : partitionCount 9 % 2 = 0 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_two : partitionCount 10 % 2 = 0 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_two : partitionCount 11 % 2 = 0 := by
  simp [Ch01.partitionCount_eleven]

theorem partition_zero_mod_three : partitionCount 0 % 3 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_three : partitionCount 1 % 3 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_three : partitionCount 2 % 3 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_three : partitionCount 3 % 3 = 0 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_three : partitionCount 4 % 3 = 2 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_three : partitionCount 5 % 3 = 1 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_three : partitionCount 6 % 3 = 2 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_three : partitionCount 7 % 3 = 0 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_three : partitionCount 8 % 3 = 1 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_three : partitionCount 9 % 3 = 0 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_three : partitionCount 10 % 3 = 0 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_three : partitionCount 11 % 3 = 2 := by
  simp [Ch01.partitionCount_eleven]

theorem partition_zero_mod_twentynine : partitionCount 0 % 29 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_twentynine : partitionCount 1 % 29 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_twentynine : partitionCount 2 % 29 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_twentynine : partitionCount 3 % 29 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_twentynine : partitionCount 4 % 29 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_twentynine : partitionCount 5 % 29 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_twentynine : partitionCount 6 % 29 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_twentynine : partitionCount 7 % 29 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_twentynine : partitionCount 8 % 29 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_twentynine : partitionCount 9 % 29 = 1 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_twentynine : partitionCount 10 % 29 = 13 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_twentynine : partitionCount 11 % 29 = 27 := by
  simp [Ch01.partitionCount_eleven]

theorem partition_zero_mod_thirtyone : partitionCount 0 % 31 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_thirtyone : partitionCount 1 % 31 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_thirtyone : partitionCount 2 % 31 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_thirtyone : partitionCount 3 % 31 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_thirtyone : partitionCount 4 % 31 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_thirtyone : partitionCount 5 % 31 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_thirtyone : partitionCount 6 % 31 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_thirtyone : partitionCount 7 % 31 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_thirtyone : partitionCount 8 % 31 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_thirtyone : partitionCount 9 % 31 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_thirtyone : partitionCount 10 % 31 = 11 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_thirtyone : partitionCount 11 % 31 = 25 := by
  simp [Ch01.partitionCount_eleven]

theorem partition_zero_mod_thirtyseven : partitionCount 0 % 37 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_thirtyseven : partitionCount 1 % 37 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_thirtyseven : partitionCount 2 % 37 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_thirtyseven : partitionCount 3 % 37 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_thirtyseven : partitionCount 4 % 37 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_thirtyseven : partitionCount 5 % 37 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_thirtyseven : partitionCount 6 % 37 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_thirtyseven : partitionCount 7 % 37 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_thirtyseven : partitionCount 8 % 37 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_thirtyseven : partitionCount 9 % 37 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_thirtyseven : partitionCount 10 % 37 = 5 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_thirtyseven : partitionCount 11 % 37 = 19 := by
  simp [Ch01.partitionCount_eleven]


-- Partition values mod 41
theorem partition_zero_mod_fortyone : partitionCount 0 % 41 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_fortyone : partitionCount 1 % 41 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_fortyone : partitionCount 2 % 41 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_fortyone : partitionCount 3 % 41 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_fortyone : partitionCount 4 % 41 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_fortyone : partitionCount 5 % 41 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_fortyone : partitionCount 6 % 41 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_fortyone : partitionCount 7 % 41 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_fortyone : partitionCount 8 % 41 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_fortyone : partitionCount 9 % 41 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_fortyone : partitionCount 10 % 41 = 1 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_fortyone : partitionCount 11 % 41 = 15 := by
  simp [Ch01.partitionCount_eleven]

-- Partition values mod 43
theorem partition_zero_mod_fortythree : partitionCount 0 % 43 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_fortythree : partitionCount 1 % 43 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_fortythree : partitionCount 2 % 43 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_fortythree : partitionCount 3 % 43 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_fortythree : partitionCount 4 % 43 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_fortythree : partitionCount 5 % 43 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_fortythree : partitionCount 6 % 43 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_fortythree : partitionCount 7 % 43 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_fortythree : partitionCount 8 % 43 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_fortythree : partitionCount 9 % 43 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_fortythree : partitionCount 10 % 43 = 42 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_fortythree : partitionCount 11 % 43 = 13 := by
  simp [Ch01.partitionCount_eleven]

-- Partition values mod 47
theorem partition_zero_mod_fortyseven : partitionCount 0 % 47 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_fortyseven : partitionCount 1 % 47 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_fortyseven : partitionCount 2 % 47 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_fortyseven : partitionCount 3 % 47 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_fortyseven : partitionCount 4 % 47 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_fortyseven : partitionCount 5 % 47 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_fortyseven : partitionCount 6 % 47 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_fortyseven : partitionCount 7 % 47 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_fortyseven : partitionCount 8 % 47 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_fortyseven : partitionCount 9 % 47 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_fortyseven : partitionCount 10 % 47 = 42 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_fortyseven : partitionCount 11 % 47 = 9 := by
  simp [Ch01.partitionCount_eleven]


-- Partition values mod 53
theorem partition_zero_mod_fiftythree : partitionCount 0 % 53 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_fiftythree : partitionCount 1 % 53 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_fiftythree : partitionCount 2 % 53 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_fiftythree : partitionCount 3 % 53 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_fiftythree : partitionCount 4 % 53 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_fiftythree : partitionCount 5 % 53 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_fiftythree : partitionCount 6 % 53 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_fiftythree : partitionCount 7 % 53 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_fiftythree : partitionCount 8 % 53 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_fiftythree : partitionCount 9 % 53 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_fiftythree : partitionCount 10 % 53 = 42 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_fiftythree : partitionCount 11 % 53 = 3 := by
  simp [Ch01.partitionCount_eleven]

-- Partition values mod 59
theorem partition_zero_mod_fiftynine : partitionCount 0 % 59 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_fiftynine : partitionCount 1 % 59 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_fiftynine : partitionCount 2 % 59 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_fiftynine : partitionCount 3 % 59 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_fiftynine : partitionCount 4 % 59 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_fiftynine : partitionCount 5 % 59 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_fiftynine : partitionCount 6 % 59 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_fiftynine : partitionCount 7 % 59 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_fiftynine : partitionCount 8 % 59 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_fiftynine : partitionCount 9 % 59 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_fiftynine : partitionCount 10 % 59 = 42 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_fiftynine : partitionCount 11 % 59 = 56 := by
  simp [Ch01.partitionCount_eleven]

-- Partition values mod 61
theorem partition_zero_mod_sixtyone : partitionCount 0 % 61 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_sixtyone : partitionCount 1 % 61 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_sixtyone : partitionCount 2 % 61 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_sixtyone : partitionCount 3 % 61 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_sixtyone : partitionCount 4 % 61 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_sixtyone : partitionCount 5 % 61 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_sixtyone : partitionCount 6 % 61 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_sixtyone : partitionCount 7 % 61 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_sixtyone : partitionCount 8 % 61 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_sixtyone : partitionCount 9 % 61 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_sixtyone : partitionCount 10 % 61 = 42 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_sixtyone : partitionCount 11 % 61 = 56 := by
  simp [Ch01.partitionCount_eleven]

-- Partition values mod 67
theorem partition_zero_mod_sixtyseven : partitionCount 0 % 67 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_sixtyseven : partitionCount 1 % 67 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_sixtyseven : partitionCount 2 % 67 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_sixtyseven : partitionCount 3 % 67 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_sixtyseven : partitionCount 4 % 67 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_sixtyseven : partitionCount 5 % 67 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_sixtyseven : partitionCount 6 % 67 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_sixtyseven : partitionCount 7 % 67 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_sixtyseven : partitionCount 8 % 67 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_sixtyseven : partitionCount 9 % 67 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_sixtyseven : partitionCount 10 % 67 = 42 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_sixtyseven : partitionCount 11 % 67 = 56 := by
  simp [Ch01.partitionCount_eleven]

-- Partition values mod 71
theorem partition_zero_mod_seventyone : partitionCount 0 % 71 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_seventyone : partitionCount 1 % 71 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_seventyone : partitionCount 2 % 71 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_seventyone : partitionCount 3 % 71 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_seventyone : partitionCount 4 % 71 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_seventyone : partitionCount 5 % 71 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_seventyone : partitionCount 6 % 71 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_seventyone : partitionCount 7 % 71 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_seventyone : partitionCount 8 % 71 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_seventyone : partitionCount 9 % 71 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_seventyone : partitionCount 10 % 71 = 42 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_seventyone : partitionCount 11 % 71 = 56 := by
  simp [Ch01.partitionCount_eleven]

-- Partition values mod 73
theorem partition_zero_mod_seventythree : partitionCount 0 % 73 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_seventythree : partitionCount 1 % 73 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_seventythree : partitionCount 2 % 73 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_seventythree : partitionCount 3 % 73 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_seventythree : partitionCount 4 % 73 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_seventythree : partitionCount 5 % 73 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_seventythree : partitionCount 6 % 73 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_seventythree : partitionCount 7 % 73 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_seventythree : partitionCount 8 % 73 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_seventythree : partitionCount 9 % 73 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_seventythree : partitionCount 10 % 73 = 42 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_seventythree : partitionCount 11 % 73 = 56 := by
  simp [Ch01.partitionCount_eleven]

-- Partition values mod 79
theorem partition_zero_mod_seventynine : partitionCount 0 % 79 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_seventynine : partitionCount 1 % 79 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_seventynine : partitionCount 2 % 79 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_seventynine : partitionCount 3 % 79 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_seventynine : partitionCount 4 % 79 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_seventynine : partitionCount 5 % 79 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_seventynine : partitionCount 6 % 79 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_seventynine : partitionCount 7 % 79 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_seventynine : partitionCount 8 % 79 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_seventynine : partitionCount 9 % 79 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_seventynine : partitionCount 10 % 79 = 42 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_seventynine : partitionCount 11 % 79 = 56 := by
  simp [Ch01.partitionCount_eleven]

-- Partition values mod 83
theorem partition_zero_mod_eightythree : partitionCount 0 % 83 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_eightythree : partitionCount 1 % 83 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_eightythree : partitionCount 2 % 83 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_eightythree : partitionCount 3 % 83 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_eightythree : partitionCount 4 % 83 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_eightythree : partitionCount 5 % 83 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_eightythree : partitionCount 6 % 83 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_eightythree : partitionCount 7 % 83 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_eightythree : partitionCount 8 % 83 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_eightythree : partitionCount 9 % 83 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_eightythree : partitionCount 10 % 83 = 42 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_eightythree : partitionCount 11 % 83 = 56 := by
  simp [Ch01.partitionCount_eleven]

-- Partition values mod 89
theorem partition_zero_mod_eightynine : partitionCount 0 % 89 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_eightynine : partitionCount 1 % 89 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_eightynine : partitionCount 2 % 89 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_eightynine : partitionCount 3 % 89 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_eightynine : partitionCount 4 % 89 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_eightynine : partitionCount 5 % 89 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_eightynine : partitionCount 6 % 89 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_eightynine : partitionCount 7 % 89 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_eightynine : partitionCount 8 % 89 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_eightynine : partitionCount 9 % 89 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_eightynine : partitionCount 10 % 89 = 42 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_eightynine : partitionCount 11 % 89 = 56 := by
  simp [Ch01.partitionCount_eleven]

-- Partition values mod 97
theorem partition_zero_mod_ninetyseven : partitionCount 0 % 97 = 1 := by
  simp [Ch01.partitionCount_zero]

theorem partition_one_mod_ninetyseven : partitionCount 1 % 97 = 1 := by
  simp [Ch01.partitionCount_one]

theorem partition_two_mod_ninetyseven : partitionCount 2 % 97 = 2 := by
  simp [Ch01.partitionCount_two]

theorem partition_three_mod_ninetyseven : partitionCount 3 % 97 = 3 := by
  simp [Ch01.partitionCount_three]

theorem partition_four_mod_ninetyseven : partitionCount 4 % 97 = 5 := by
  simp [Ch01.partitionCount_four]

theorem partition_five_mod_ninetyseven : partitionCount 5 % 97 = 7 := by
  simp [Ch01.partitionCount_five]

theorem partition_six_mod_ninetyseven : partitionCount 6 % 97 = 11 := by
  simp [Ch01.partitionCount_six]

theorem partition_seven_mod_ninetyseven : partitionCount 7 % 97 = 15 := by
  simp [Ch01.partitionCount_seven]

theorem partition_eight_mod_ninetyseven : partitionCount 8 % 97 = 22 := by
  simp [Ch01.partitionCount_eight]

theorem partition_nine_mod_ninetyseven : partitionCount 9 % 97 = 30 := by
  simp [Ch01.partitionCount_nine]

theorem partition_ten_mod_ninetyseven : partitionCount 10 % 97 = 42 := by
  simp [Ch01.partitionCount_ten]

theorem partition_eleven_mod_ninetyseven : partitionCount 11 % 97 = 56 := by
  simp [Ch01.partitionCount_eleven]

end Ch17
end PartIV
end QseriesFormalization
