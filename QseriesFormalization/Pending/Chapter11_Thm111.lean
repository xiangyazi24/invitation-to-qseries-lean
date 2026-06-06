import QseriesFormalization.Pending.Chapter11_RRCF_Convergent
import QseriesFormalization.Pending.Chapter13_RRCF_RForm
import QseriesFormalization.Pending.Chapter16_MBI_Proof

/-!
# Chapter 11 Theorem 11.1 — `rrcf_r_via_CF = rrcf_r`

## Current status

**Coefficient matches proved at degrees 0–20** from both sides independently:
- CF side: `rrcf_r_via_CF.coeff k` (from convergent stabilization)
- Product side: `rrcf_r.coeff k` (from pentagonal014/pentagonal023 Cauchy product)

These are unconditional verifications. The full theorem (∀ k) remains open.

## What's needed for the full proof

The Rogers-Ramanujan identity as a formal power series:
`∑_{n≥0} X^{n²}/(X;X)_n = 1/pentagonal023SeriesPS` (G(q) side)
`∑_{n≥0} X^{n(n+1)}/(X;X)_n = 1/pentagonal014SeriesPS` (H(q) side)

This connects the analytic series (which generates the CF via functional
equations, cf. Ch07 `rrJInf`) to the product form (pentagonal series).
The repo has the Bailey pair machinery (Ch09 unconditional Bailey lemma)
and JTP (Ch02/03), but the formal-PS RR identity is not yet assembled.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch11Thm111

open QseriesFormalization.Pending.Ch11RRCFConvergent
open QseriesFormalization.Pending.Ch13RRCF
open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.Ch16MBIProof
open PowerSeries

/-! ## Pentagonal series coefficients at small degrees

For `pentagonal014SeriesPS ℚ` (exponents `k(5k-3)/2`):
  k=0 → 0, k=1 → 1, k=-1 → 4, k=2 → 7, k=-2 → 13

For `pentagonal023SeriesPS ℚ` (exponents `k(5k-1)/2`):
  k=0 → 0, k=1 → 2, k=-1 → 3, k=2 → 9, k=-2 → 11 -/

theorem coeff_one_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 1 = -1 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_one_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 1 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_two_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 2 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_two_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 2 = -1 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_three_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 3 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_three_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 3 = -1 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_four_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 4 = -1 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_four_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 4 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_five_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 5 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_five_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 5 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

/-! ## Formal inverse coefficients of `pentagonal023SeriesPS ℚ`

Computed from `f · f⁻¹ = 1` via the recurrence for formal inverse
coefficients. -/

private theorem inv_const : constantCoeff (pentagonal023SeriesPS ℚ) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_zero_pentagonal023SeriesPS_rat]

private theorem inv_coeff_zero :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 0 = 1 := by
  rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_inv, inv_const, inv_one]

theorem coeff_one_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 1 = 0 := by
  rw [PowerSeries.coeff_inv 1]
  simp only [if_neg one_ne_zero, inv_const, inv_one]
  rw [show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (lt_irrefl 1), if_pos Nat.zero_lt_one]
  rw [inv_coeff_zero, coeff_one_pentagonal023SeriesPS_rat]
  ring

theorem coeff_two_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 2 = 1 := by
  rw [PowerSeries.coeff_inv 2]
  simp only [if_neg (by decide : (2 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) = {(0, 2), (1, 1), (2, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (by omega : ¬(2 < 2)), if_pos (by omega : 1 < 2), if_pos (by omega : 0 < 2)]
  rw [inv_coeff_zero, coeff_one_inv_pentagonal023,
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat]
  ring

theorem coeff_three_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 3 = 1 := by
  rw [PowerSeries.coeff_inv 3]
  simp only [if_neg (by decide : (3 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 3 : Finset (ℕ × ℕ)) =
    {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  rw [inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat]
  ring

theorem coeff_four_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 4 = 1 := by
  rw [PowerSeries.coeff_inv 4]
  simp only [if_neg (by decide : (4 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
    {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega)]
  rw [inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023,
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat]
  ring

theorem coeff_five_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 5 = 2 := by
  rw [PowerSeries.coeff_inv 5]
  simp only [if_neg (by decide : (5 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 5 : Finset (ℕ × ℕ)) =
    {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  rw [inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat]
  ring

/-! ## Coefficients of `rrcf_r` from the product form

`rrcf_r = pentagonal014SeriesPS ℚ * (pentagonal023SeriesPS ℚ)⁻¹` -/

theorem coeff_one_rrcf_r : rrcf_r.coeff 1 = -1 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 1 : Finset (ℕ × ℕ)) = {(0, 1), (1, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_zero_pentagonal014SeriesPS_rat, coeff_one_inv_pentagonal023,
      coeff_one_pentagonal014SeriesPS_rat, inv_coeff_zero]
  ring

theorem coeff_two_rrcf_r : rrcf_r.coeff 2 = 1 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) = {(0, 2), (1, 1), (2, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_zero_pentagonal014SeriesPS_rat, coeff_two_inv_pentagonal023,
      coeff_one_pentagonal014SeriesPS_rat, coeff_one_inv_pentagonal023,
      coeff_two_pentagonal014SeriesPS_rat, inv_coeff_zero]
  ring

theorem coeff_three_rrcf_r : rrcf_r.coeff 3 = 0 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 3 : Finset (ℕ × ℕ)) =
        {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_zero_pentagonal014SeriesPS_rat, coeff_three_inv_pentagonal023,
      coeff_one_pentagonal014SeriesPS_rat, coeff_two_inv_pentagonal023,
      coeff_two_pentagonal014SeriesPS_rat, coeff_one_inv_pentagonal023,
      coeff_three_pentagonal014SeriesPS_rat, inv_coeff_zero]
  ring

theorem coeff_four_rrcf_r : rrcf_r.coeff 4 = -1 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
        {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [coeff_zero_pentagonal014SeriesPS_rat, coeff_four_inv_pentagonal023,
      coeff_one_pentagonal014SeriesPS_rat, coeff_three_inv_pentagonal023,
      coeff_two_pentagonal014SeriesPS_rat, coeff_two_inv_pentagonal023,
      coeff_three_pentagonal014SeriesPS_rat, coeff_one_inv_pentagonal023,
      coeff_four_pentagonal014SeriesPS_rat, inv_coeff_zero]
  ring

theorem coeff_five_rrcf_r : rrcf_r.coeff 5 = 1 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 5 : Finset (ℕ × ℕ)) =
        {(0, 5), (1, 4), (2, 3), (3, 2), (4, 1), (5, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_zero_pentagonal014SeriesPS_rat, coeff_five_inv_pentagonal023,
      coeff_one_pentagonal014SeriesPS_rat, coeff_four_inv_pentagonal023,
      coeff_two_pentagonal014SeriesPS_rat, coeff_three_inv_pentagonal023,
      coeff_three_pentagonal014SeriesPS_rat, coeff_two_inv_pentagonal023,
      coeff_four_pentagonal014SeriesPS_rat, coeff_one_inv_pentagonal023,
      coeff_five_pentagonal014SeriesPS_rat, inv_coeff_zero]
  ring

/-! ## Coefficient matches: CF side = Product side

These establish `rrcf_r.coeff k = rrcf_r_via_CF.coeff k` at degrees 0–5
unconditionally, by combining the CF-side computations (in
`Chapter11_RRCF_Convergent.lean`) with the product-side computations above. -/

theorem coeff_match_zero :
    rrcf_r.coeff 0 = rrcf_r_via_CF.coeff 0 := by
  rw [coeff_zero_rrcf_r, coeff_zero_rrcf_r_via_CF]

theorem coeff_match_one :
    rrcf_r.coeff 1 = rrcf_r_via_CF.coeff 1 := by
  rw [coeff_one_rrcf_r, coeff_one_rrcf_r_via_CF]

theorem coeff_match_two :
    rrcf_r.coeff 2 = rrcf_r_via_CF.coeff 2 := by
  rw [coeff_two_rrcf_r, coeff_two_rrcf_r_via_CF]

theorem coeff_match_three :
    rrcf_r.coeff 3 = rrcf_r_via_CF.coeff 3 := by
  rw [coeff_three_rrcf_r, coeff_three_rrcf_r_via_CF]

theorem coeff_match_four :
    rrcf_r.coeff 4 = rrcf_r_via_CF.coeff 4 := by
  rw [coeff_four_rrcf_r, coeff_four_rrcf_r_via_CF]

theorem coeff_match_five :
    rrcf_r.coeff 5 = rrcf_r_via_CF.coeff 5 := by
  rw [coeff_five_rrcf_r, coeff_five_rrcf_r_via_CF]

/-! ## Pentagonal series coefficients at degrees 6-10 -/

theorem coeff_six_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 6 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_six_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 6 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_seven_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 7 = 1 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_seven_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 7 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_eight_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 8 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_eight_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 8 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_nine_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 9 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_nine_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 9 = 1 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_ten_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 10 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_ten_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 10 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

/-! ## Pentagonal series coefficients at degrees 11-20 -/

theorem coeff_eleven_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 11 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_eleven_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 11 = 1 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_twelve_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 12 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_twelve_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 12 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_thirteen_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 13 = 1 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_thirteen_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 13 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_fourteen_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 14 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_fourteen_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 14 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_fifteen_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 15 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_fifteen_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 15 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_sixteen_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 16 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_sixteen_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 16 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_seventeen_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 17 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_seventeen_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 17 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_eighteen_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 18 = -1 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_eighteen_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 18 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_nineteen_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 19 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_nineteen_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 19 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

theorem coeff_twenty_pentagonal014SeriesPS_rat :
    (pentagonal014SeriesPS ℚ).coeff 20 = 0 := by
  simp only [coeff_pentagonal014SeriesPS]
  unfold pentagonal014Coeff pentagonal014Exp negOnePowInt
  norm_cast

theorem coeff_twenty_pentagonal023SeriesPS_rat :
    (pentagonal023SeriesPS ℚ).coeff 20 = 0 := by
  simp only [coeff_pentagonal023SeriesPS]
  unfold pentagonal023Coeff pentagonal023Exp negOnePowInt
  norm_cast

/-! ## Formal inverse coefficients of `pentagonal023SeriesPS ℚ` at degrees 6-10 -/

theorem coeff_six_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 6 = 2 := by
  rw [PowerSeries.coeff_inv 6]
  simp only [if_neg (by decide : (6 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 6 : Finset (ℕ × ℕ)) =
    {(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (6, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  rw [inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023,
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat]
  ring

theorem coeff_seven_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 7 = 3 := by
  rw [PowerSeries.coeff_inv 7]
  simp only [if_neg (by decide : (7 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 7 : Finset (ℕ × ℕ)) =
    {(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1), (7, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega)]
  rw [inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat]
  ring

theorem coeff_eight_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 8 = 4 := by
  rw [PowerSeries.coeff_inv 8]
  simp only [if_neg (by decide : (8 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 8 : Finset (ℕ × ℕ)) =
    {(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2), (7, 1), (8, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  rw [inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023,
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat]
  ring

theorem coeff_nine_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 9 = 4 := by
  rw [PowerSeries.coeff_inv 9]
  simp only [if_neg (by decide : (9 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 9 : Finset (ℕ × ℕ)) =
    {(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3), (7, 2), (8, 1),
     (9, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega)]
  rw [inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat,
      coeff_nine_pentagonal023SeriesPS_rat]
  ring

theorem coeff_ten_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 10 = 7 := by
  rw [PowerSeries.coeff_inv 10]
  simp only [if_neg (by decide : (10 : ℕ) ≠ 0), inv_const, inv_one]
  rw [show (Finset.antidiagonal 10 : Finset (ℕ × ℕ)) =
    {(0, 10), (1, 9), (2, 8), (3, 7), (4, 6), (5, 5), (6, 4), (7, 3), (8, 2),
     (9, 1), (10, 0)} from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_pos (by omega)]
  rw [inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023,
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat,
      coeff_nine_pentagonal023SeriesPS_rat, coeff_ten_pentagonal023SeriesPS_rat]
  ring

/-! ## Formal inverse coefficients of `pentagonal023SeriesPS ℚ` at degrees 11-20 -/

private theorem coeff_inv_pentagonal023_recurrence (n : ℕ) (hn : n ≠ 0) :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff n =
      -∑ k ∈ Finset.range n, (pentagonal023SeriesPS ℚ).coeff (k + 1) *
        ((pentagonal023SeriesPS ℚ)⁻¹).coeff (n - 1 - k) := by
  rw [PowerSeries.coeff_inv n]
  simp only [if_neg hn, inv_const, inv_one]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun a b => if b < n then
        (pentagonal023SeriesPS ℚ).coeff a * ((pentagonal023SeriesPS ℚ)⁻¹).coeff b else 0) n]
  rw [Finset.sum_range_succ']
  simp only [tsub_zero]
  rw [if_neg (by omega : ¬ n < n), add_zero]
  rw [neg_mul, one_mul]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have hlt : n - (k + 1) < n := by omega
  rw [if_pos hlt]
  have hk1 : k + 1 ≤ n := Nat.succ_le_of_lt hk
  have heq : n - (k + 1) = n - 1 - k := by omega
  rw [heq]

theorem coeff_eleven_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 11 = 6 := by
  rw [coeff_inv_pentagonal023_recurrence 11 (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat,
      coeff_nine_pentagonal023SeriesPS_rat, coeff_ten_pentagonal023SeriesPS_rat,
      coeff_eleven_pentagonal023SeriesPS_rat, inv_coeff_zero, coeff_one_inv_pentagonal023,
      coeff_two_inv_pentagonal023, coeff_three_inv_pentagonal023,
      coeff_four_inv_pentagonal023, coeff_five_inv_pentagonal023,
      coeff_six_inv_pentagonal023, coeff_seven_inv_pentagonal023,
      coeff_eight_inv_pentagonal023, coeff_nine_inv_pentagonal023,
      coeff_ten_inv_pentagonal023
    ]
  ring

theorem coeff_twelve_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 12 = 10 := by
  rw [coeff_inv_pentagonal023_recurrence 12 (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat,
      coeff_nine_pentagonal023SeriesPS_rat, coeff_ten_pentagonal023SeriesPS_rat,
      coeff_eleven_pentagonal023SeriesPS_rat, coeff_twelve_pentagonal023SeriesPS_rat,
      inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023
    ]
  ring

theorem coeff_thirteen_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 13 = 11 := by
  rw [coeff_inv_pentagonal023_recurrence 13 (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat,
      coeff_nine_pentagonal023SeriesPS_rat, coeff_ten_pentagonal023SeriesPS_rat,
      coeff_eleven_pentagonal023SeriesPS_rat, coeff_twelve_pentagonal023SeriesPS_rat,
      coeff_thirteen_pentagonal023SeriesPS_rat, inv_coeff_zero, coeff_one_inv_pentagonal023,
      coeff_two_inv_pentagonal023, coeff_three_inv_pentagonal023,
      coeff_four_inv_pentagonal023, coeff_five_inv_pentagonal023,
      coeff_six_inv_pentagonal023, coeff_seven_inv_pentagonal023,
      coeff_eight_inv_pentagonal023, coeff_nine_inv_pentagonal023,
      coeff_ten_inv_pentagonal023, coeff_eleven_inv_pentagonal023,
      coeff_twelve_inv_pentagonal023
    ]
  ring

theorem coeff_fourteen_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 14 = 13 := by
  rw [coeff_inv_pentagonal023_recurrence 14 (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat,
      coeff_nine_pentagonal023SeriesPS_rat, coeff_ten_pentagonal023SeriesPS_rat,
      coeff_eleven_pentagonal023SeriesPS_rat, coeff_twelve_pentagonal023SeriesPS_rat,
      coeff_thirteen_pentagonal023SeriesPS_rat, coeff_fourteen_pentagonal023SeriesPS_rat,
      inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023
    ]
  ring

theorem coeff_fifteen_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 15 = 18 := by
  rw [coeff_inv_pentagonal023_recurrence 15 (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat,
      coeff_nine_pentagonal023SeriesPS_rat, coeff_ten_pentagonal023SeriesPS_rat,
      coeff_eleven_pentagonal023SeriesPS_rat, coeff_twelve_pentagonal023SeriesPS_rat,
      coeff_thirteen_pentagonal023SeriesPS_rat, coeff_fourteen_pentagonal023SeriesPS_rat,
      coeff_fifteen_pentagonal023SeriesPS_rat, inv_coeff_zero, coeff_one_inv_pentagonal023,
      coeff_two_inv_pentagonal023, coeff_three_inv_pentagonal023,
      coeff_four_inv_pentagonal023, coeff_five_inv_pentagonal023,
      coeff_six_inv_pentagonal023, coeff_seven_inv_pentagonal023,
      coeff_eight_inv_pentagonal023, coeff_nine_inv_pentagonal023,
      coeff_ten_inv_pentagonal023, coeff_eleven_inv_pentagonal023,
      coeff_twelve_inv_pentagonal023, coeff_thirteen_inv_pentagonal023,
      coeff_fourteen_inv_pentagonal023
    ]
  ring

theorem coeff_sixteen_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 16 = 19 := by
  rw [coeff_inv_pentagonal023_recurrence 16 (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat,
      coeff_nine_pentagonal023SeriesPS_rat, coeff_ten_pentagonal023SeriesPS_rat,
      coeff_eleven_pentagonal023SeriesPS_rat, coeff_twelve_pentagonal023SeriesPS_rat,
      coeff_thirteen_pentagonal023SeriesPS_rat, coeff_fourteen_pentagonal023SeriesPS_rat,
      coeff_fifteen_pentagonal023SeriesPS_rat, coeff_sixteen_pentagonal023SeriesPS_rat,
      inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023, coeff_fourteen_inv_pentagonal023,
      coeff_fifteen_inv_pentagonal023
    ]
  ring

theorem coeff_seventeen_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 17 = 25 := by
  rw [coeff_inv_pentagonal023_recurrence 17 (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat,
      coeff_nine_pentagonal023SeriesPS_rat, coeff_ten_pentagonal023SeriesPS_rat,
      coeff_eleven_pentagonal023SeriesPS_rat, coeff_twelve_pentagonal023SeriesPS_rat,
      coeff_thirteen_pentagonal023SeriesPS_rat, coeff_fourteen_pentagonal023SeriesPS_rat,
      coeff_fifteen_pentagonal023SeriesPS_rat, coeff_sixteen_pentagonal023SeriesPS_rat,
      coeff_seventeen_pentagonal023SeriesPS_rat, inv_coeff_zero,
      coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023, coeff_fourteen_inv_pentagonal023,
      coeff_fifteen_inv_pentagonal023, coeff_sixteen_inv_pentagonal023
    ]
  ring

theorem coeff_eighteen_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 18 = 30 := by
  rw [coeff_inv_pentagonal023_recurrence 18 (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat,
      coeff_nine_pentagonal023SeriesPS_rat, coeff_ten_pentagonal023SeriesPS_rat,
      coeff_eleven_pentagonal023SeriesPS_rat, coeff_twelve_pentagonal023SeriesPS_rat,
      coeff_thirteen_pentagonal023SeriesPS_rat, coeff_fourteen_pentagonal023SeriesPS_rat,
      coeff_fifteen_pentagonal023SeriesPS_rat, coeff_sixteen_pentagonal023SeriesPS_rat,
      coeff_seventeen_pentagonal023SeriesPS_rat, coeff_eighteen_pentagonal023SeriesPS_rat,
      inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023, coeff_fourteen_inv_pentagonal023,
      coeff_fifteen_inv_pentagonal023, coeff_sixteen_inv_pentagonal023,
      coeff_seventeen_inv_pentagonal023
    ]
  ring

theorem coeff_nineteen_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 19 = 33 := by
  rw [coeff_inv_pentagonal023_recurrence 19 (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat,
      coeff_nine_pentagonal023SeriesPS_rat, coeff_ten_pentagonal023SeriesPS_rat,
      coeff_eleven_pentagonal023SeriesPS_rat, coeff_twelve_pentagonal023SeriesPS_rat,
      coeff_thirteen_pentagonal023SeriesPS_rat, coeff_fourteen_pentagonal023SeriesPS_rat,
      coeff_fifteen_pentagonal023SeriesPS_rat, coeff_sixteen_pentagonal023SeriesPS_rat,
      coeff_seventeen_pentagonal023SeriesPS_rat, coeff_eighteen_pentagonal023SeriesPS_rat,
      coeff_nineteen_pentagonal023SeriesPS_rat, inv_coeff_zero, coeff_one_inv_pentagonal023,
      coeff_two_inv_pentagonal023, coeff_three_inv_pentagonal023,
      coeff_four_inv_pentagonal023, coeff_five_inv_pentagonal023,
      coeff_six_inv_pentagonal023, coeff_seven_inv_pentagonal023,
      coeff_eight_inv_pentagonal023, coeff_nine_inv_pentagonal023,
      coeff_ten_inv_pentagonal023, coeff_eleven_inv_pentagonal023,
      coeff_twelve_inv_pentagonal023, coeff_thirteen_inv_pentagonal023,
      coeff_fourteen_inv_pentagonal023, coeff_fifteen_inv_pentagonal023,
      coeff_sixteen_inv_pentagonal023, coeff_seventeen_inv_pentagonal023,
      coeff_eighteen_inv_pentagonal023
    ]
  ring

theorem coeff_twenty_inv_pentagonal023 :
    ((pentagonal023SeriesPS ℚ)⁻¹).coeff 20 = 45 := by
  rw [coeff_inv_pentagonal023_recurrence 20 (by decide)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_one_pentagonal023SeriesPS_rat, coeff_two_pentagonal023SeriesPS_rat,
      coeff_three_pentagonal023SeriesPS_rat, coeff_four_pentagonal023SeriesPS_rat,
      coeff_five_pentagonal023SeriesPS_rat, coeff_six_pentagonal023SeriesPS_rat,
      coeff_seven_pentagonal023SeriesPS_rat, coeff_eight_pentagonal023SeriesPS_rat,
      coeff_nine_pentagonal023SeriesPS_rat, coeff_ten_pentagonal023SeriesPS_rat,
      coeff_eleven_pentagonal023SeriesPS_rat, coeff_twelve_pentagonal023SeriesPS_rat,
      coeff_thirteen_pentagonal023SeriesPS_rat, coeff_fourteen_pentagonal023SeriesPS_rat,
      coeff_fifteen_pentagonal023SeriesPS_rat, coeff_sixteen_pentagonal023SeriesPS_rat,
      coeff_seventeen_pentagonal023SeriesPS_rat, coeff_eighteen_pentagonal023SeriesPS_rat,
      coeff_nineteen_pentagonal023SeriesPS_rat, coeff_twenty_pentagonal023SeriesPS_rat,
      inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023, coeff_fourteen_inv_pentagonal023,
      coeff_fifteen_inv_pentagonal023, coeff_sixteen_inv_pentagonal023,
      coeff_seventeen_inv_pentagonal023, coeff_eighteen_inv_pentagonal023,
      coeff_nineteen_inv_pentagonal023
    ]
  ring

/-! ## Coefficients of `rrcf_r` from the product form at degrees 6-10 -/

theorem coeff_six_rrcf_r : rrcf_r.coeff 6 = -1 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 6 : Finset (ℕ × ℕ)) =
        {(0, 6), (1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (6, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [coeff_zero_pentagonal014SeriesPS_rat, coeff_six_inv_pentagonal023,
      coeff_one_pentagonal014SeriesPS_rat, coeff_five_inv_pentagonal023,
      coeff_two_pentagonal014SeriesPS_rat, coeff_four_inv_pentagonal023,
      coeff_three_pentagonal014SeriesPS_rat, coeff_three_inv_pentagonal023,
      coeff_four_pentagonal014SeriesPS_rat, coeff_two_inv_pentagonal023,
      coeff_five_pentagonal014SeriesPS_rat, coeff_one_inv_pentagonal023,
      coeff_six_pentagonal014SeriesPS_rat, inv_coeff_zero]
  ring

theorem coeff_seven_rrcf_r : rrcf_r.coeff 7 = 1 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 7 : Finset (ℕ × ℕ)) =
        {(0, 7), (1, 6), (2, 5), (3, 4), (4, 3), (5, 2), (6, 1), (7, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_zero_pentagonal014SeriesPS_rat, coeff_seven_inv_pentagonal023,
      coeff_one_pentagonal014SeriesPS_rat, coeff_six_inv_pentagonal023,
      coeff_two_pentagonal014SeriesPS_rat, coeff_five_inv_pentagonal023,
      coeff_three_pentagonal014SeriesPS_rat, coeff_four_inv_pentagonal023,
      coeff_four_pentagonal014SeriesPS_rat, coeff_three_inv_pentagonal023,
      coeff_five_pentagonal014SeriesPS_rat, coeff_two_inv_pentagonal023,
      coeff_six_pentagonal014SeriesPS_rat, coeff_one_inv_pentagonal023,
      coeff_seven_pentagonal014SeriesPS_rat, inv_coeff_zero]
  ring

theorem coeff_eight_rrcf_r : rrcf_r.coeff 8 = 0 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 8 : Finset (ℕ × ℕ)) =
        {(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2), (7, 1), (8, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [coeff_zero_pentagonal014SeriesPS_rat, coeff_eight_inv_pentagonal023,
      coeff_one_pentagonal014SeriesPS_rat, coeff_seven_inv_pentagonal023,
      coeff_two_pentagonal014SeriesPS_rat, coeff_six_inv_pentagonal023,
      coeff_three_pentagonal014SeriesPS_rat, coeff_five_inv_pentagonal023,
      coeff_four_pentagonal014SeriesPS_rat, coeff_four_inv_pentagonal023,
      coeff_five_pentagonal014SeriesPS_rat, coeff_three_inv_pentagonal023,
      coeff_six_pentagonal014SeriesPS_rat, coeff_two_inv_pentagonal023,
      coeff_seven_pentagonal014SeriesPS_rat, coeff_one_inv_pentagonal023,
      coeff_eight_pentagonal014SeriesPS_rat, inv_coeff_zero]
  ring

theorem coeff_nine_rrcf_r : rrcf_r.coeff 9 = -1 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 9 : Finset (ℕ × ℕ)) =
        {(0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3), (7, 2), (8, 1),
         (9, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [coeff_zero_pentagonal014SeriesPS_rat, coeff_nine_inv_pentagonal023,
      coeff_one_pentagonal014SeriesPS_rat, coeff_eight_inv_pentagonal023,
      coeff_two_pentagonal014SeriesPS_rat, coeff_seven_inv_pentagonal023,
      coeff_three_pentagonal014SeriesPS_rat, coeff_six_inv_pentagonal023,
      coeff_four_pentagonal014SeriesPS_rat, coeff_five_inv_pentagonal023,
      coeff_five_pentagonal014SeriesPS_rat, coeff_four_inv_pentagonal023,
      coeff_six_pentagonal014SeriesPS_rat, coeff_three_inv_pentagonal023,
      coeff_seven_pentagonal014SeriesPS_rat, coeff_two_inv_pentagonal023,
      coeff_eight_pentagonal014SeriesPS_rat, coeff_one_inv_pentagonal023,
      coeff_nine_pentagonal014SeriesPS_rat, inv_coeff_zero]
  ring

theorem coeff_ten_rrcf_r : rrcf_r.coeff 10 = 2 := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul,
      show (Finset.antidiagonal 10 : Finset (ℕ × ℕ)) =
        {(0, 10), (1, 9), (2, 8), (3, 7), (4, 6), (5, 5), (6, 4), (7, 3), (8, 2),
         (9, 1), (10, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  rw [coeff_zero_pentagonal014SeriesPS_rat, coeff_ten_inv_pentagonal023,
      coeff_one_pentagonal014SeriesPS_rat, coeff_nine_inv_pentagonal023,
      coeff_two_pentagonal014SeriesPS_rat, coeff_eight_inv_pentagonal023,
      coeff_three_pentagonal014SeriesPS_rat, coeff_seven_inv_pentagonal023,
      coeff_four_pentagonal014SeriesPS_rat, coeff_six_inv_pentagonal023,
      coeff_five_pentagonal014SeriesPS_rat, coeff_five_inv_pentagonal023,
      coeff_six_pentagonal014SeriesPS_rat, coeff_four_inv_pentagonal023,
      coeff_seven_pentagonal014SeriesPS_rat, coeff_three_inv_pentagonal023,
      coeff_eight_pentagonal014SeriesPS_rat, coeff_two_inv_pentagonal023,
      coeff_nine_pentagonal014SeriesPS_rat, coeff_one_inv_pentagonal023,
      coeff_ten_pentagonal014SeriesPS_rat, inv_coeff_zero]
  ring

/-! ## Coefficients of `rrcf_r` from the product form at degrees 11-20 -/

private theorem coeff_rrcf_r_cauchy (n : ℕ) :
    rrcf_r.coeff n =
      ∑ k ∈ Finset.range (n + 1), (pentagonal014SeriesPS ℚ).coeff k *
        ((pentagonal023SeriesPS ℚ)⁻¹).coeff (n - k) := by
  unfold rrcf_r
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (f := fun a b => (pentagonal014SeriesPS ℚ).coeff a *
        ((pentagonal023SeriesPS ℚ)⁻¹).coeff b) n]

theorem coeff_eleven_rrcf_r : rrcf_r.coeff 11 = -3 := by
  rw [coeff_rrcf_r_cauchy 11]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_zero_pentagonal014SeriesPS_rat, coeff_one_pentagonal014SeriesPS_rat,
      coeff_two_pentagonal014SeriesPS_rat, coeff_three_pentagonal014SeriesPS_rat,
      coeff_four_pentagonal014SeriesPS_rat, coeff_five_pentagonal014SeriesPS_rat,
      coeff_six_pentagonal014SeriesPS_rat, coeff_seven_pentagonal014SeriesPS_rat,
      coeff_eight_pentagonal014SeriesPS_rat, coeff_nine_pentagonal014SeriesPS_rat,
      coeff_ten_pentagonal014SeriesPS_rat, coeff_eleven_pentagonal014SeriesPS_rat,
      inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023
    ]
  ring

theorem coeff_twelve_rrcf_r : rrcf_r.coeff 12 = 2 := by
  rw [coeff_rrcf_r_cauchy 12]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_zero_pentagonal014SeriesPS_rat, coeff_one_pentagonal014SeriesPS_rat,
      coeff_two_pentagonal014SeriesPS_rat, coeff_three_pentagonal014SeriesPS_rat,
      coeff_four_pentagonal014SeriesPS_rat, coeff_five_pentagonal014SeriesPS_rat,
      coeff_six_pentagonal014SeriesPS_rat, coeff_seven_pentagonal014SeriesPS_rat,
      coeff_eight_pentagonal014SeriesPS_rat, coeff_nine_pentagonal014SeriesPS_rat,
      coeff_ten_pentagonal014SeriesPS_rat, coeff_eleven_pentagonal014SeriesPS_rat,
      coeff_twelve_pentagonal014SeriesPS_rat, inv_coeff_zero, coeff_one_inv_pentagonal023,
      coeff_two_inv_pentagonal023, coeff_three_inv_pentagonal023,
      coeff_four_inv_pentagonal023, coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023
    ]
  ring

theorem coeff_thirteen_rrcf_r : rrcf_r.coeff 13 = 0 := by
  rw [coeff_rrcf_r_cauchy 13]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_zero_pentagonal014SeriesPS_rat, coeff_one_pentagonal014SeriesPS_rat,
      coeff_two_pentagonal014SeriesPS_rat, coeff_three_pentagonal014SeriesPS_rat,
      coeff_four_pentagonal014SeriesPS_rat, coeff_five_pentagonal014SeriesPS_rat,
      coeff_six_pentagonal014SeriesPS_rat, coeff_seven_pentagonal014SeriesPS_rat,
      coeff_eight_pentagonal014SeriesPS_rat, coeff_nine_pentagonal014SeriesPS_rat,
      coeff_ten_pentagonal014SeriesPS_rat, coeff_eleven_pentagonal014SeriesPS_rat,
      coeff_twelve_pentagonal014SeriesPS_rat, coeff_thirteen_pentagonal014SeriesPS_rat,
      inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023
    ]
  ring

theorem coeff_fourteen_rrcf_r : rrcf_r.coeff 14 = -2 := by
  rw [coeff_rrcf_r_cauchy 14]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_zero_pentagonal014SeriesPS_rat, coeff_one_pentagonal014SeriesPS_rat,
      coeff_two_pentagonal014SeriesPS_rat, coeff_three_pentagonal014SeriesPS_rat,
      coeff_four_pentagonal014SeriesPS_rat, coeff_five_pentagonal014SeriesPS_rat,
      coeff_six_pentagonal014SeriesPS_rat, coeff_seven_pentagonal014SeriesPS_rat,
      coeff_eight_pentagonal014SeriesPS_rat, coeff_nine_pentagonal014SeriesPS_rat,
      coeff_ten_pentagonal014SeriesPS_rat, coeff_eleven_pentagonal014SeriesPS_rat,
      coeff_twelve_pentagonal014SeriesPS_rat, coeff_thirteen_pentagonal014SeriesPS_rat,
      coeff_fourteen_pentagonal014SeriesPS_rat, inv_coeff_zero, coeff_one_inv_pentagonal023,
      coeff_two_inv_pentagonal023, coeff_three_inv_pentagonal023,
      coeff_four_inv_pentagonal023, coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023, coeff_fourteen_inv_pentagonal023
    ]
  ring

theorem coeff_fifteen_rrcf_r : rrcf_r.coeff 15 = 4 := by
  rw [coeff_rrcf_r_cauchy 15]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_zero_pentagonal014SeriesPS_rat, coeff_one_pentagonal014SeriesPS_rat,
      coeff_two_pentagonal014SeriesPS_rat, coeff_three_pentagonal014SeriesPS_rat,
      coeff_four_pentagonal014SeriesPS_rat, coeff_five_pentagonal014SeriesPS_rat,
      coeff_six_pentagonal014SeriesPS_rat, coeff_seven_pentagonal014SeriesPS_rat,
      coeff_eight_pentagonal014SeriesPS_rat, coeff_nine_pentagonal014SeriesPS_rat,
      coeff_ten_pentagonal014SeriesPS_rat, coeff_eleven_pentagonal014SeriesPS_rat,
      coeff_twelve_pentagonal014SeriesPS_rat, coeff_thirteen_pentagonal014SeriesPS_rat,
      coeff_fourteen_pentagonal014SeriesPS_rat, coeff_fifteen_pentagonal014SeriesPS_rat,
      inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023, coeff_fourteen_inv_pentagonal023,
      coeff_fifteen_inv_pentagonal023
    ]
  ring

theorem coeff_sixteen_rrcf_r : rrcf_r.coeff 16 = -4 := by
  rw [coeff_rrcf_r_cauchy 16]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_zero_pentagonal014SeriesPS_rat, coeff_one_pentagonal014SeriesPS_rat,
      coeff_two_pentagonal014SeriesPS_rat, coeff_three_pentagonal014SeriesPS_rat,
      coeff_four_pentagonal014SeriesPS_rat, coeff_five_pentagonal014SeriesPS_rat,
      coeff_six_pentagonal014SeriesPS_rat, coeff_seven_pentagonal014SeriesPS_rat,
      coeff_eight_pentagonal014SeriesPS_rat, coeff_nine_pentagonal014SeriesPS_rat,
      coeff_ten_pentagonal014SeriesPS_rat, coeff_eleven_pentagonal014SeriesPS_rat,
      coeff_twelve_pentagonal014SeriesPS_rat, coeff_thirteen_pentagonal014SeriesPS_rat,
      coeff_fourteen_pentagonal014SeriesPS_rat, coeff_fifteen_pentagonal014SeriesPS_rat,
      coeff_sixteen_pentagonal014SeriesPS_rat, inv_coeff_zero, coeff_one_inv_pentagonal023,
      coeff_two_inv_pentagonal023, coeff_three_inv_pentagonal023,
      coeff_four_inv_pentagonal023, coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023, coeff_fourteen_inv_pentagonal023,
      coeff_fifteen_inv_pentagonal023, coeff_sixteen_inv_pentagonal023
    ]
  ring

theorem coeff_seventeen_rrcf_r : rrcf_r.coeff 17 = 3 := by
  rw [coeff_rrcf_r_cauchy 17]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_zero_pentagonal014SeriesPS_rat, coeff_one_pentagonal014SeriesPS_rat,
      coeff_two_pentagonal014SeriesPS_rat, coeff_three_pentagonal014SeriesPS_rat,
      coeff_four_pentagonal014SeriesPS_rat, coeff_five_pentagonal014SeriesPS_rat,
      coeff_six_pentagonal014SeriesPS_rat, coeff_seven_pentagonal014SeriesPS_rat,
      coeff_eight_pentagonal014SeriesPS_rat, coeff_nine_pentagonal014SeriesPS_rat,
      coeff_ten_pentagonal014SeriesPS_rat, coeff_eleven_pentagonal014SeriesPS_rat,
      coeff_twelve_pentagonal014SeriesPS_rat, coeff_thirteen_pentagonal014SeriesPS_rat,
      coeff_fourteen_pentagonal014SeriesPS_rat, coeff_fifteen_pentagonal014SeriesPS_rat,
      coeff_sixteen_pentagonal014SeriesPS_rat, coeff_seventeen_pentagonal014SeriesPS_rat,
      inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023, coeff_fourteen_inv_pentagonal023,
      coeff_fifteen_inv_pentagonal023, coeff_sixteen_inv_pentagonal023,
      coeff_seventeen_inv_pentagonal023
    ]
  ring

theorem coeff_eighteen_rrcf_r : rrcf_r.coeff 18 = -1 := by
  rw [coeff_rrcf_r_cauchy 18]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_zero_pentagonal014SeriesPS_rat, coeff_one_pentagonal014SeriesPS_rat,
      coeff_two_pentagonal014SeriesPS_rat, coeff_three_pentagonal014SeriesPS_rat,
      coeff_four_pentagonal014SeriesPS_rat, coeff_five_pentagonal014SeriesPS_rat,
      coeff_six_pentagonal014SeriesPS_rat, coeff_seven_pentagonal014SeriesPS_rat,
      coeff_eight_pentagonal014SeriesPS_rat, coeff_nine_pentagonal014SeriesPS_rat,
      coeff_ten_pentagonal014SeriesPS_rat, coeff_eleven_pentagonal014SeriesPS_rat,
      coeff_twelve_pentagonal014SeriesPS_rat, coeff_thirteen_pentagonal014SeriesPS_rat,
      coeff_fourteen_pentagonal014SeriesPS_rat, coeff_fifteen_pentagonal014SeriesPS_rat,
      coeff_sixteen_pentagonal014SeriesPS_rat, coeff_seventeen_pentagonal014SeriesPS_rat,
      coeff_eighteen_pentagonal014SeriesPS_rat, inv_coeff_zero, coeff_one_inv_pentagonal023,
      coeff_two_inv_pentagonal023, coeff_three_inv_pentagonal023,
      coeff_four_inv_pentagonal023, coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023, coeff_fourteen_inv_pentagonal023,
      coeff_fifteen_inv_pentagonal023, coeff_sixteen_inv_pentagonal023,
      coeff_seventeen_inv_pentagonal023, coeff_eighteen_inv_pentagonal023
    ]
  ring

theorem coeff_nineteen_rrcf_r : rrcf_r.coeff 19 = -3 := by
  rw [coeff_rrcf_r_cauchy 19]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_zero_pentagonal014SeriesPS_rat, coeff_one_pentagonal014SeriesPS_rat,
      coeff_two_pentagonal014SeriesPS_rat, coeff_three_pentagonal014SeriesPS_rat,
      coeff_four_pentagonal014SeriesPS_rat, coeff_five_pentagonal014SeriesPS_rat,
      coeff_six_pentagonal014SeriesPS_rat, coeff_seven_pentagonal014SeriesPS_rat,
      coeff_eight_pentagonal014SeriesPS_rat, coeff_nine_pentagonal014SeriesPS_rat,
      coeff_ten_pentagonal014SeriesPS_rat, coeff_eleven_pentagonal014SeriesPS_rat,
      coeff_twelve_pentagonal014SeriesPS_rat, coeff_thirteen_pentagonal014SeriesPS_rat,
      coeff_fourteen_pentagonal014SeriesPS_rat, coeff_fifteen_pentagonal014SeriesPS_rat,
      coeff_sixteen_pentagonal014SeriesPS_rat, coeff_seventeen_pentagonal014SeriesPS_rat,
      coeff_eighteen_pentagonal014SeriesPS_rat, coeff_nineteen_pentagonal014SeriesPS_rat,
      inv_coeff_zero, coeff_one_inv_pentagonal023, coeff_two_inv_pentagonal023,
      coeff_three_inv_pentagonal023, coeff_four_inv_pentagonal023,
      coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023, coeff_fourteen_inv_pentagonal023,
      coeff_fifteen_inv_pentagonal023, coeff_sixteen_inv_pentagonal023,
      coeff_seventeen_inv_pentagonal023, coeff_eighteen_inv_pentagonal023,
      coeff_nineteen_inv_pentagonal023
    ]
  ring

theorem coeff_twenty_rrcf_r : rrcf_r.coeff 20 = 6 := by
  rw [coeff_rrcf_r_cauchy 20]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub]
  rw [
      coeff_zero_pentagonal014SeriesPS_rat, coeff_one_pentagonal014SeriesPS_rat,
      coeff_two_pentagonal014SeriesPS_rat, coeff_three_pentagonal014SeriesPS_rat,
      coeff_four_pentagonal014SeriesPS_rat, coeff_five_pentagonal014SeriesPS_rat,
      coeff_six_pentagonal014SeriesPS_rat, coeff_seven_pentagonal014SeriesPS_rat,
      coeff_eight_pentagonal014SeriesPS_rat, coeff_nine_pentagonal014SeriesPS_rat,
      coeff_ten_pentagonal014SeriesPS_rat, coeff_eleven_pentagonal014SeriesPS_rat,
      coeff_twelve_pentagonal014SeriesPS_rat, coeff_thirteen_pentagonal014SeriesPS_rat,
      coeff_fourteen_pentagonal014SeriesPS_rat, coeff_fifteen_pentagonal014SeriesPS_rat,
      coeff_sixteen_pentagonal014SeriesPS_rat, coeff_seventeen_pentagonal014SeriesPS_rat,
      coeff_eighteen_pentagonal014SeriesPS_rat, coeff_nineteen_pentagonal014SeriesPS_rat,
      coeff_twenty_pentagonal014SeriesPS_rat, inv_coeff_zero, coeff_one_inv_pentagonal023,
      coeff_two_inv_pentagonal023, coeff_three_inv_pentagonal023,
      coeff_four_inv_pentagonal023, coeff_five_inv_pentagonal023, coeff_six_inv_pentagonal023,
      coeff_seven_inv_pentagonal023, coeff_eight_inv_pentagonal023,
      coeff_nine_inv_pentagonal023, coeff_ten_inv_pentagonal023,
      coeff_eleven_inv_pentagonal023, coeff_twelve_inv_pentagonal023,
      coeff_thirteen_inv_pentagonal023, coeff_fourteen_inv_pentagonal023,
      coeff_fifteen_inv_pentagonal023, coeff_sixteen_inv_pentagonal023,
      coeff_seventeen_inv_pentagonal023, coeff_eighteen_inv_pentagonal023,
      coeff_nineteen_inv_pentagonal023, coeff_twenty_inv_pentagonal023
    ]
  ring

/-! ## Coefficient matches at degrees 6-10 -/

theorem coeff_match_six :
    rrcf_r.coeff 6 = rrcf_r_via_CF.coeff 6 := by
  rw [coeff_six_rrcf_r, coeff_six_rrcf_r_via_CF]

theorem coeff_match_seven :
    rrcf_r.coeff 7 = rrcf_r_via_CF.coeff 7 := by
  rw [coeff_seven_rrcf_r, coeff_seven_rrcf_r_via_CF]

theorem coeff_match_eight :
    rrcf_r.coeff 8 = rrcf_r_via_CF.coeff 8 := by
  rw [coeff_eight_rrcf_r, coeff_eight_rrcf_r_via_CF]

theorem coeff_match_nine :
    rrcf_r.coeff 9 = rrcf_r_via_CF.coeff 9 := by
  rw [coeff_nine_rrcf_r, coeff_nine_rrcf_r_via_CF]

theorem coeff_match_ten :
    rrcf_r.coeff 10 = rrcf_r_via_CF.coeff 10 := by
  rw [coeff_ten_rrcf_r, coeff_ten_rrcf_r_via_CF]

/-! ## Coefficient matches at degrees 11-20 -/

theorem coeff_match_eleven :
    rrcf_r.coeff 11 = rrcf_r_via_CF.coeff 11 := by
  rw [coeff_eleven_rrcf_r, coeff_eleven_rrcf_r_via_CF]

theorem coeff_match_twelve :
    rrcf_r.coeff 12 = rrcf_r_via_CF.coeff 12 := by
  rw [coeff_twelve_rrcf_r, coeff_twelve_rrcf_r_via_CF]

theorem coeff_match_thirteen :
    rrcf_r.coeff 13 = rrcf_r_via_CF.coeff 13 := by
  rw [coeff_thirteen_rrcf_r, coeff_thirteen_rrcf_r_via_CF]

theorem coeff_match_fourteen :
    rrcf_r.coeff 14 = rrcf_r_via_CF.coeff 14 := by
  rw [coeff_fourteen_rrcf_r, coeff_fourteen_rrcf_r_via_CF]

theorem coeff_match_fifteen :
    rrcf_r.coeff 15 = rrcf_r_via_CF.coeff 15 := by
  rw [coeff_fifteen_rrcf_r, coeff_fifteen_rrcf_r_via_CF]

theorem coeff_match_sixteen :
    rrcf_r.coeff 16 = rrcf_r_via_CF.coeff 16 := by
  rw [coeff_sixteen_rrcf_r, coeff_sixteen_rrcf_r_via_CF]

theorem coeff_match_seventeen :
    rrcf_r.coeff 17 = rrcf_r_via_CF.coeff 17 := by
  rw [coeff_seventeen_rrcf_r, coeff_seventeen_rrcf_r_via_CF]

theorem coeff_match_eighteen :
    rrcf_r.coeff 18 = rrcf_r_via_CF.coeff 18 := by
  rw [coeff_eighteen_rrcf_r, coeff_eighteen_rrcf_r_via_CF]

theorem coeff_match_nineteen :
    rrcf_r.coeff 19 = rrcf_r_via_CF.coeff 19 := by
  rw [coeff_nineteen_rrcf_r, coeff_nineteen_rrcf_r_via_CF]

theorem coeff_match_twenty :
    rrcf_r.coeff 20 = rrcf_r_via_CF.coeff 20 := by
  rw [coeff_twenty_rrcf_r, coeff_twenty_rrcf_r_via_CF]

/-! ## Consolidated coefficient-match interfaces -/

/-- The product form `rrcf_r` and the continued-fraction limit
`rrcf_r_via_CF` have identical coefficients through degree `20`. -/
theorem coeff_match_of_le_twenty {k : ℕ} (hk : k ≤ 20) :
    rrcf_r.coeff k = rrcf_r_via_CF.coeff k := by
  interval_cases k <;> simp [
    coeff_match_zero, coeff_match_one, coeff_match_two, coeff_match_three,
    coeff_match_four, coeff_match_five, coeff_match_six, coeff_match_seven,
    coeff_match_eight, coeff_match_nine, coeff_match_ten, coeff_match_eleven,
    coeff_match_twelve, coeff_match_thirteen, coeff_match_fourteen,
    coeff_match_fifteen, coeff_match_sixteen, coeff_match_seventeen,
    coeff_match_eighteen, coeff_match_nineteen, coeff_match_twenty]

/-- Finite-vector form of `coeff_match_of_le_twenty`, convenient for bounded
coefficient checks. -/
theorem coeff_match_fin_twentyone (k : Fin 21) :
    rrcf_r.coeff k.1 = rrcf_r_via_CF.coeff k.1 :=
  coeff_match_of_le_twenty (by omega)

/-- Strict-bound form of `coeff_match_of_le_twenty`. -/
theorem coeff_match_of_lt_twentyone {k : ℕ} (hk : k < 21) :
    rrcf_r.coeff k = rrcf_r_via_CF.coeff k :=
  coeff_match_of_le_twenty (by omega)

/-- Symmetric strict-bound coefficient match through truncation length `21`. -/
theorem coeff_match_symm_of_lt_twentyone {k : ℕ} (hk : k < 21) :
    rrcf_r_via_CF.coeff k = rrcf_r.coeff k :=
  (coeff_match_of_lt_twentyone hk).symm

/-- Uniform finite-index form for any truncation length at most `21`. -/
theorem coeff_match_fin_of_le_twentyone {N : ℕ} (hN : N ≤ 21) (k : Fin N) :
    rrcf_r.coeff k.1 = rrcf_r_via_CF.coeff k.1 :=
  coeff_match_of_lt_twentyone (by omega)

/-- Symmetric finite-index form for any truncation length at most `21`. -/
theorem coeff_match_fin_symm_of_le_twentyone {N : ℕ} (hN : N ≤ 21) (k : Fin N) :
    rrcf_r_via_CF.coeff k.1 = rrcf_r.coeff k.1 :=
  coeff_match_symm_of_lt_twentyone (by omega)

/-- Difference form of the coefficient match through degree `20`. -/
theorem coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_le_twenty
    {k : ℕ} (hk : k ≤ 20) :
    (rrcf_r - rrcf_r_via_CF).coeff k = 0 := by
  rw [map_sub, coeff_match_of_le_twenty hk]
  simp

/-- Reverse-difference form of the coefficient match through degree `20`. -/
theorem coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_le_twenty
    {k : ℕ} (hk : k ≤ 20) :
    (rrcf_r_via_CF - rrcf_r).coeff k = 0 := by
  rw [map_sub, ← coeff_match_of_le_twenty hk]
  simp

/-- Strict-bound difference form through truncation length `21`. -/
theorem coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_lt_twentyone
    {k : ℕ} (hk : k < 21) :
    (rrcf_r - rrcf_r_via_CF).coeff k = 0 :=
  coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_le_twenty (by omega)

/-- Strict-bound reverse-difference form through truncation length `21`. -/
theorem coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_lt_twentyone
    {k : ℕ} (hk : k < 21) :
    (rrcf_r_via_CF - rrcf_r).coeff k = 0 :=
  coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_le_twenty (by omega)

/-- The product form and CF-limit form agree after truncation through degree
`20`. -/
theorem trunc_rrcf_r_eq_rrcf_r_via_CF_through_twenty :
    PowerSeries.trunc 21 rrcf_r =
      PowerSeries.trunc 21 rrcf_r_via_CF := by
  ext k
  by_cases hk : k < 21
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hk, if_pos hk]
    exact coeff_match_of_le_twenty (by omega)
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hk, if_neg hk]

/-- The coefficient match through degree `20` is equivalently a zero truncated
difference. -/
theorem trunc_rrcf_r_sub_rrcf_r_via_CF_eq_zero_through_twenty :
    PowerSeries.trunc 21 (rrcf_r - rrcf_r_via_CF) = 0 := by
  ext k
  by_cases hk : k < 21
  · rw [PowerSeries.coeff_trunc, if_pos hk,
      coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_le_twenty (by omega)]
    simp
  · rw [PowerSeries.coeff_trunc, if_neg hk]
    simp

/-- Reverse zero truncated-difference form through degree `20`. -/
theorem trunc_rrcf_r_via_CF_sub_rrcf_r_eq_zero_through_twenty :
    PowerSeries.trunc 21 (rrcf_r_via_CF - rrcf_r) = 0 := by
  ext k
  by_cases hk : k < 21
  · rw [PowerSeries.coeff_trunc, if_pos hk,
      coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_le_twenty (by omega)]
    simp
  · rw [PowerSeries.coeff_trunc, if_neg hk]
    simp

/-- The product and CF-limit forms agree after every truncation length
`N ≤ 21`. -/
theorem trunc_rrcf_r_eq_rrcf_r_via_CF_of_le_twentyone
    (N : ℕ) (hN : N ≤ 21) :
    PowerSeries.trunc N rrcf_r =
      PowerSeries.trunc N rrcf_r_via_CF := by
  ext k
  by_cases hk : k < N
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hk, if_pos hk]
    exact coeff_match_of_lt_twentyone (by omega)
  · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hk, if_neg hk]

/-- Symmetric truncation equality for every truncation length at most `21`. -/
theorem trunc_rrcf_r_via_CF_eq_rrcf_r_of_le_twentyone
    (N : ℕ) (hN : N ≤ 21) :
    PowerSeries.trunc N rrcf_r_via_CF =
      PowerSeries.trunc N rrcf_r :=
  (trunc_rrcf_r_eq_rrcf_r_via_CF_of_le_twentyone N hN).symm

/-- Every truncated difference of length at most `21` is zero. -/
theorem trunc_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_le_twentyone
    (N : ℕ) (hN : N ≤ 21) :
    PowerSeries.trunc N (rrcf_r - rrcf_r_via_CF) = 0 := by
  ext k
  by_cases hk : k < N
  · rw [PowerSeries.coeff_trunc, if_pos hk,
      coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_lt_twentyone (by omega)]
    simp
  · rw [PowerSeries.coeff_trunc, if_neg hk]
    simp

/-- Reverse truncated difference form for every length at most `21`. -/
theorem trunc_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_le_twentyone
    (N : ℕ) (hN : N ≤ 21) :
    PowerSeries.trunc N (rrcf_r_via_CF - rrcf_r) = 0 := by
  ext k
  by_cases hk : k < N
  · rw [PowerSeries.coeff_trunc, if_pos hk,
      coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_lt_twentyone (by omega)]
    simp
  · rw [PowerSeries.coeff_trunc, if_neg hk]
    simp

/-- X-adic form of the coefficient match through degree `20`: the difference
is divisible by `X^21`. -/
theorem X_pow_twentyone_dvd_rrcf_r_sub_rrcf_r_via_CF :
    (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r - rrcf_r_via_CF) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  exact coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_lt_twentyone hk

/-- Reverse X-adic divisibility form through degree `20`. -/
theorem X_pow_twentyone_dvd_rrcf_r_via_CF_sub_rrcf_r :
    (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r_via_CF - rrcf_r) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  exact coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_lt_twentyone hk

/-- If the first difference has a nonzero coefficient, it must occur at
degree at least `21`. -/
theorem twentyone_le_of_coeff_rrcf_r_sub_rrcf_r_via_CF_ne_zero
    {k : ℕ} (hk : (rrcf_r - rrcf_r_via_CF).coeff k ≠ 0) :
    21 ≤ k := by
  by_contra hlt
  push_neg at hlt
  exact hk (coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_lt_twentyone hlt)

/-- Reverse-difference version of the same first-possible-nonzero bound. -/
theorem twentyone_le_of_coeff_rrcf_r_via_CF_sub_rrcf_r_ne_zero
    {k : ℕ} (hk : (rrcf_r_via_CF - rrcf_r).coeff k ≠ 0) :
    21 ≤ k := by
  by_contra hlt
  push_neg at hlt
  exact hk (coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_lt_twentyone hlt)

/-! ## Named residual series -/

/-- Formal residual for the coefficient comparison `rrcf_r = rrcf_r_via_CF`. -/
noncomputable def rrcf_r_matchResidual : ℚ⟦X⟧ :=
  rrcf_r - rrcf_r_via_CF

/-- The named residual is the difference of the product and CF-limit forms. -/
theorem rrcf_r_matchResidual_eq_sub :
    rrcf_r_matchResidual = rrcf_r - rrcf_r_via_CF :=
  rfl

/-- Coefficient form of the named forward residual. -/
theorem coeff_rrcf_r_matchResidual_eq_sub (k : ℕ) :
    rrcf_r_matchResidual.coeff k =
      rrcf_r.coeff k - rrcf_r_via_CF.coeff k := by
  rw [rrcf_r_matchResidual_eq_sub, map_sub]

/-- Vanishing of a forward residual coefficient is exactly coefficient
agreement at that degree. -/
theorem coeff_rrcf_r_matchResidual_eq_zero_iff_coeff_eq (k : ℕ) :
    rrcf_r_matchResidual.coeff k = 0 ↔
      rrcf_r.coeff k = rrcf_r_via_CF.coeff k := by
  rw [coeff_rrcf_r_matchResidual_eq_sub, sub_eq_zero]

/-- A truncated forward residual is zero iff the two truncated forms agree. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_iff_eq (N : ℕ) :
    PowerSeries.trunc N rrcf_r_matchResidual = 0 ↔
      PowerSeries.trunc N rrcf_r = PowerSeries.trunc N rrcf_r_via_CF := by
  constructor
  · intro h
    ext k
    by_cases hk : k < N
    · have hres : rrcf_r_matchResidual.coeff k = 0 := by
        have hcoeff := congrArg (fun p => p.coeff k) h
        simpa [PowerSeries.coeff_trunc, hk] using hcoeff
      have hcoeff :
          rrcf_r.coeff k = rrcf_r_via_CF.coeff k :=
        (coeff_rrcf_r_matchResidual_eq_zero_iff_coeff_eq k).1 hres
      rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hk, if_pos hk]
      exact hcoeff
    · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hk, if_neg hk]
  · intro h
    ext k
    by_cases hk : k < N
    · have hcoeff :
          rrcf_r.coeff k = rrcf_r_via_CF.coeff k := by
        have hcoeff' := congrArg (fun p => p.coeff k) h
        simpa [PowerSeries.coeff_trunc, hk] using hcoeff'
      have hres : rrcf_r_matchResidual.coeff k = 0 :=
        (coeff_rrcf_r_matchResidual_eq_zero_iff_coeff_eq k).2 hcoeff
      rw [PowerSeries.coeff_trunc, if_pos hk, hres]
      simp
    · rw [PowerSeries.coeff_trunc, if_neg hk]
      simp

/-- Truncated equality of the product and CF-limit forms is equivalent to
coefficientwise equality below the truncation length. -/
theorem trunc_rrcf_r_eq_rrcf_r_via_CF_iff_coeff_eq (N : ℕ) :
    PowerSeries.trunc N rrcf_r = PowerSeries.trunc N rrcf_r_via_CF ↔
      ∀ k : ℕ, k < N → rrcf_r.coeff k = rrcf_r_via_CF.coeff k := by
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

/-- A truncated forward residual is zero iff the product and CF-limit
coefficients agree below the truncation length. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_iff_coeff_eq (N : ℕ) :
    PowerSeries.trunc N rrcf_r_matchResidual = 0 ↔
      ∀ k : ℕ, k < N → rrcf_r.coeff k = rrcf_r_via_CF.coeff k := by
  rw [trunc_rrcf_r_matchResidual_eq_zero_iff_eq,
    trunc_rrcf_r_eq_rrcf_r_via_CF_iff_coeff_eq]

/-- Extract coefficient agreement below `N` from a zero truncated forward
residual. -/
theorem coeff_rrcf_r_eq_rrcf_r_via_CF_of_trunc_matchResidual_eq_zero
    {N k : ℕ} (h : PowerSeries.trunc N rrcf_r_matchResidual = 0)
    (hk : k < N) :
    rrcf_r.coeff k = rrcf_r_via_CF.coeff k :=
  (trunc_rrcf_r_matchResidual_eq_zero_iff_coeff_eq N).1 h k hk

/-- Build zero truncated forward residual from coefficient agreement below the
truncation length. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_of_coeff_eq
    {N : ℕ} (h : ∀ k : ℕ, k < N → rrcf_r.coeff k = rrcf_r_via_CF.coeff k) :
    PowerSeries.trunc N rrcf_r_matchResidual = 0 :=
  (trunc_rrcf_r_matchResidual_eq_zero_iff_coeff_eq N).2 h

/-- A truncated forward residual is zero iff its coefficients vanish below the
truncation length. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_iff_coeff_zero (N : ℕ) :
    PowerSeries.trunc N rrcf_r_matchResidual = 0 ↔
      ∀ k : ℕ, k < N → rrcf_r_matchResidual.coeff k = 0 := by
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

/-- Extract forward residual coefficient vanishing below `N` from a zero
truncated residual. -/
theorem coeff_rrcf_r_matchResidual_eq_zero_of_trunc_eq_zero
    {N k : ℕ} (h : PowerSeries.trunc N rrcf_r_matchResidual = 0)
    (hk : k < N) :
    rrcf_r_matchResidual.coeff k = 0 :=
  (trunc_rrcf_r_matchResidual_eq_zero_iff_coeff_zero N).1 h k hk

/-- Build zero truncated forward residual from residual coefficient vanishing
below the truncation length. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_of_coeff_zero
    {N : ℕ} (h : ∀ k : ℕ, k < N → rrcf_r_matchResidual.coeff k = 0) :
    PowerSeries.trunc N rrcf_r_matchResidual = 0 :=
  (trunc_rrcf_r_matchResidual_eq_zero_iff_coeff_zero N).2 h

/-- The named residual has zero coefficients through degree `20`. -/
theorem coeff_rrcf_r_matchResidual_eq_zero_of_lt_twentyone
    {k : ℕ} (hk : k < 21) :
    rrcf_r_matchResidual.coeff k = 0 := by
  rw [rrcf_r_matchResidual_eq_sub]
  exact coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_lt_twentyone hk

/-- Finite-index form of the residual coefficient vanishing through degree
`20`. -/
theorem coeff_rrcf_r_matchResidual_eq_zero_fin_twentyone (k : Fin 21) :
    rrcf_r_matchResidual.coeff k.1 = 0 :=
  coeff_rrcf_r_matchResidual_eq_zero_of_lt_twentyone (by omega)

/-- Non-strict form of the named residual coefficient vanishing through degree
`20`. -/
theorem coeff_rrcf_r_matchResidual_eq_zero_of_le_twenty
    {k : ℕ} (hk : k ≤ 20) :
    rrcf_r_matchResidual.coeff k = 0 :=
  coeff_rrcf_r_matchResidual_eq_zero_of_lt_twentyone (by omega)

/-- Finite-index form of the named residual coefficient vanishing for any
truncation length at most `21`. -/
theorem coeff_rrcf_r_matchResidual_eq_zero_fin_of_le_twentyone
    {N : ℕ} (hN : N ≤ 21) (k : Fin N) :
    rrcf_r_matchResidual.coeff k.1 = 0 :=
  coeff_rrcf_r_matchResidual_eq_zero_of_lt_twentyone (by omega)

/-- Every truncation of the named residual of length at most `21` is zero. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_of_le_twentyone
    (N : ℕ) (hN : N ≤ 21) :
    PowerSeries.trunc N rrcf_r_matchResidual = 0 := by
  rw [rrcf_r_matchResidual_eq_sub]
  exact trunc_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_le_twentyone N hN

/-- The named residual truncates to zero through degree `20`. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_through_twenty :
    PowerSeries.trunc 21 rrcf_r_matchResidual = 0 :=
  trunc_rrcf_r_matchResidual_eq_zero_of_le_twentyone 21 (by omega)

/-- X-adic form for the named residual: it is divisible by `X^21`. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchResidual :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual := by
  rw [rrcf_r_matchResidual_eq_sub]
  exact X_pow_twentyone_dvd_rrcf_r_sub_rrcf_r_via_CF

/-- X-adic divisibility of the named residual is equivalent to vanishing of
its coefficients below degree `21`. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_coeff_zero :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual ↔
      ∀ k : ℕ, k < 21 → rrcf_r_matchResidual.coeff k = 0 := by
  rw [PowerSeries.X_pow_dvd_iff]

/-- X-adic divisibility of the named residual is equivalent to its truncation
through degree `20` being zero. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_trunc_eq_zero :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual ↔
      PowerSeries.trunc 21 rrcf_r_matchResidual = 0 := by
  rw [X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_coeff_zero,
    trunc_rrcf_r_matchResidual_eq_zero_iff_coeff_zero 21]

/-- Extract low-degree coefficient vanishing from X-adic divisibility of the
named residual. -/
theorem coeff_rrcf_r_matchResidual_eq_zero_of_X_pow_twentyone_dvd
    {k : ℕ} (h : (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual) (hk : k < 21) :
    rrcf_r_matchResidual.coeff k = 0 :=
  (X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_coeff_zero.1 h) k hk

/-- Build X-adic divisibility of the named residual from low-degree coefficient
vanishing. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchResidual_of_coeff_zero
    (h : ∀ k : ℕ, k < 21 → rrcf_r_matchResidual.coeff k = 0) :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual :=
  X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_coeff_zero.2 h

/-- X-adic divisibility of the named residual implies zero truncation through
degree `20`. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_of_X_pow_twentyone_dvd
    (h : (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual) :
    PowerSeries.trunc 21 rrcf_r_matchResidual = 0 :=
  X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_trunc_eq_zero.1 h

/-- Zero truncation through degree `20` implies X-adic divisibility of the
named residual. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchResidual_of_trunc_eq_zero
    (h : PowerSeries.trunc 21 rrcf_r_matchResidual = 0) :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual :=
  X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_trunc_eq_zero.2 h

/-- X-adic divisibility of the named residual gives coefficient agreement
below degree `21`. -/
theorem coeff_rrcf_r_eq_rrcf_r_via_CF_of_X_pow_twentyone_dvd_matchResidual
    {k : ℕ} (h : (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual) (hk : k < 21) :
    rrcf_r.coeff k = rrcf_r_via_CF.coeff k :=
  (coeff_rrcf_r_matchResidual_eq_zero_iff_coeff_eq k).1
    (coeff_rrcf_r_matchResidual_eq_zero_of_X_pow_twentyone_dvd h hk)

/-- X-adic divisibility of the named residual gives truncation equality through
degree `20`. -/
theorem trunc_rrcf_r_eq_rrcf_r_via_CF_of_X_pow_twentyone_dvd_matchResidual
    (h : (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual) :
    PowerSeries.trunc 21 rrcf_r = PowerSeries.trunc 21 rrcf_r_via_CF :=
  (trunc_rrcf_r_matchResidual_eq_zero_iff_eq 21).1
    (trunc_rrcf_r_matchResidual_eq_zero_of_X_pow_twentyone_dvd h)

/-- Low-degree coefficient agreement gives X-adic divisibility of the named
residual. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchResidual_of_coeff_eq
    (h : ∀ k : ℕ, k < 21 → rrcf_r.coeff k = rrcf_r_via_CF.coeff k) :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual :=
  X_pow_twentyone_dvd_rrcf_r_matchResidual_of_coeff_zero
    (fun k hk => (coeff_rrcf_r_matchResidual_eq_zero_iff_coeff_eq k).2 (h k hk))

/-- The proved X-adic divisibility of the named residual recovers coefficient
agreement through degree `20`. -/
theorem coeff_rrcf_r_eq_rrcf_r_via_CF_of_lt_twentyone_via_X_pow_twentyone_dvd
    {k : ℕ} (hk : k < 21) :
    rrcf_r.coeff k = rrcf_r_via_CF.coeff k :=
  coeff_rrcf_r_eq_rrcf_r_via_CF_of_X_pow_twentyone_dvd_matchResidual
    X_pow_twentyone_dvd_rrcf_r_matchResidual hk

/-- The proved X-adic divisibility of the named residual recovers truncation
equality through degree `20`. -/
theorem trunc_rrcf_r_eq_rrcf_r_via_CF_through_twenty_via_X_pow_twentyone_dvd :
    PowerSeries.trunc 21 rrcf_r = PowerSeries.trunc 21 rrcf_r_via_CF :=
  trunc_rrcf_r_eq_rrcf_r_via_CF_of_X_pow_twentyone_dvd_matchResidual
    X_pow_twentyone_dvd_rrcf_r_matchResidual

/-- If the named residual has a nonzero coefficient, it must occur at degree at
least `21`. -/
theorem twentyone_le_of_coeff_rrcf_r_matchResidual_ne_zero
    {k : ℕ} (hk : rrcf_r_matchResidual.coeff k ≠ 0) :
    21 ≤ k := by
  apply twentyone_le_of_coeff_rrcf_r_sub_rrcf_r_via_CF_ne_zero
  simpa [rrcf_r_matchResidual_eq_sub] using hk

/-- Reverse formal residual for the coefficient comparison
`rrcf_r_via_CF = rrcf_r`. -/
noncomputable def rrcf_r_matchReverseResidual : ℚ⟦X⟧ :=
  rrcf_r_via_CF - rrcf_r

/-- The named reverse residual is the reverse difference of the two forms. -/
theorem rrcf_r_matchReverseResidual_eq_sub :
    rrcf_r_matchReverseResidual = rrcf_r_via_CF - rrcf_r :=
  rfl

/-- Coefficient form of the named reverse residual. -/
theorem coeff_rrcf_r_matchReverseResidual_eq_sub (k : ℕ) :
    rrcf_r_matchReverseResidual.coeff k =
      rrcf_r_via_CF.coeff k - rrcf_r.coeff k := by
  rw [rrcf_r_matchReverseResidual_eq_sub, map_sub]

/-- Vanishing of a reverse residual coefficient is exactly coefficient
agreement at that degree, with the sides swapped. -/
theorem coeff_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_eq (k : ℕ) :
    rrcf_r_matchReverseResidual.coeff k = 0 ↔
      rrcf_r_via_CF.coeff k = rrcf_r.coeff k := by
  rw [coeff_rrcf_r_matchReverseResidual_eq_sub, sub_eq_zero]

/-- A truncated reverse residual is zero iff the two truncated forms agree in
reverse order. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_iff_eq (N : ℕ) :
    PowerSeries.trunc N rrcf_r_matchReverseResidual = 0 ↔
      PowerSeries.trunc N rrcf_r_via_CF = PowerSeries.trunc N rrcf_r := by
  constructor
  · intro h
    ext k
    by_cases hk : k < N
    · have hres : rrcf_r_matchReverseResidual.coeff k = 0 := by
        have hcoeff := congrArg (fun p => p.coeff k) h
        simpa [PowerSeries.coeff_trunc, hk] using hcoeff
      have hcoeff :
          rrcf_r_via_CF.coeff k = rrcf_r.coeff k :=
        (coeff_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_eq k).1 hres
      rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_pos hk, if_pos hk]
      exact hcoeff
    · rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, if_neg hk, if_neg hk]
  · intro h
    ext k
    by_cases hk : k < N
    · have hcoeff :
          rrcf_r_via_CF.coeff k = rrcf_r.coeff k := by
        have hcoeff' := congrArg (fun p => p.coeff k) h
        simpa [PowerSeries.coeff_trunc, hk] using hcoeff'
      have hres : rrcf_r_matchReverseResidual.coeff k = 0 :=
        (coeff_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_eq k).2 hcoeff
      rw [PowerSeries.coeff_trunc, if_pos hk, hres]
      simp
    · rw [PowerSeries.coeff_trunc, if_neg hk]
      simp

/-- Truncated equality of the CF-limit and product forms is equivalent to
coefficientwise equality below the truncation length, with the sides swapped. -/
theorem trunc_rrcf_r_via_CF_eq_rrcf_r_iff_coeff_eq (N : ℕ) :
    PowerSeries.trunc N rrcf_r_via_CF = PowerSeries.trunc N rrcf_r ↔
      ∀ k : ℕ, k < N → rrcf_r_via_CF.coeff k = rrcf_r.coeff k := by
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

/-- A truncated reverse residual is zero iff the CF-limit and product
coefficients agree below the truncation length. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_eq (N : ℕ) :
    PowerSeries.trunc N rrcf_r_matchReverseResidual = 0 ↔
      ∀ k : ℕ, k < N → rrcf_r_via_CF.coeff k = rrcf_r.coeff k := by
  rw [trunc_rrcf_r_matchReverseResidual_eq_zero_iff_eq,
    trunc_rrcf_r_via_CF_eq_rrcf_r_iff_coeff_eq]

/-- Extract reverse coefficient agreement below `N` from a zero truncated
reverse residual. -/
theorem coeff_rrcf_r_via_CF_eq_rrcf_r_of_trunc_matchReverseResidual_eq_zero
    {N k : ℕ} (h : PowerSeries.trunc N rrcf_r_matchReverseResidual = 0)
    (hk : k < N) :
    rrcf_r_via_CF.coeff k = rrcf_r.coeff k :=
  (trunc_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_eq N).1 h k hk

/-- Build zero truncated reverse residual from reverse coefficient agreement
below the truncation length. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_of_coeff_eq
    {N : ℕ} (h : ∀ k : ℕ, k < N → rrcf_r_via_CF.coeff k = rrcf_r.coeff k) :
    PowerSeries.trunc N rrcf_r_matchReverseResidual = 0 :=
  (trunc_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_eq N).2 h

/-- A truncated reverse residual is zero iff its coefficients vanish below the
truncation length. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_zero (N : ℕ) :
    PowerSeries.trunc N rrcf_r_matchReverseResidual = 0 ↔
      ∀ k : ℕ, k < N → rrcf_r_matchReverseResidual.coeff k = 0 := by
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
truncated reverse residual. -/
theorem coeff_rrcf_r_matchReverseResidual_eq_zero_of_trunc_eq_zero
    {N k : ℕ} (h : PowerSeries.trunc N rrcf_r_matchReverseResidual = 0)
    (hk : k < N) :
    rrcf_r_matchReverseResidual.coeff k = 0 :=
  (trunc_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_zero N).1 h k hk

/-- Build zero truncated reverse residual from reverse residual coefficient
vanishing below the truncation length. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_of_coeff_zero
    {N : ℕ} (h : ∀ k : ℕ, k < N → rrcf_r_matchReverseResidual.coeff k = 0) :
    PowerSeries.trunc N rrcf_r_matchReverseResidual = 0 :=
  (trunc_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_zero N).2 h

/-- The named reverse residual has zero coefficients through degree `20`. -/
theorem coeff_rrcf_r_matchReverseResidual_eq_zero_of_lt_twentyone
    {k : ℕ} (hk : k < 21) :
    rrcf_r_matchReverseResidual.coeff k = 0 := by
  rw [rrcf_r_matchReverseResidual_eq_sub]
  exact coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_lt_twentyone hk

/-- Finite-index form of the reverse residual coefficient vanishing through
degree `20`. -/
theorem coeff_rrcf_r_matchReverseResidual_eq_zero_fin_twentyone (k : Fin 21) :
    rrcf_r_matchReverseResidual.coeff k.1 = 0 :=
  coeff_rrcf_r_matchReverseResidual_eq_zero_of_lt_twentyone (by omega)

/-- Non-strict form of the named reverse residual coefficient vanishing through
degree `20`. -/
theorem coeff_rrcf_r_matchReverseResidual_eq_zero_of_le_twenty
    {k : ℕ} (hk : k ≤ 20) :
    rrcf_r_matchReverseResidual.coeff k = 0 :=
  coeff_rrcf_r_matchReverseResidual_eq_zero_of_lt_twentyone (by omega)

/-- Finite-index form of the named reverse residual coefficient vanishing for
any truncation length at most `21`. -/
theorem coeff_rrcf_r_matchReverseResidual_eq_zero_fin_of_le_twentyone
    {N : ℕ} (hN : N ≤ 21) (k : Fin N) :
    rrcf_r_matchReverseResidual.coeff k.1 = 0 :=
  coeff_rrcf_r_matchReverseResidual_eq_zero_of_lt_twentyone (by omega)

/-- Every truncation of the named reverse residual of length at most `21` is
zero. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_of_le_twentyone
    (N : ℕ) (hN : N ≤ 21) :
    PowerSeries.trunc N rrcf_r_matchReverseResidual = 0 := by
  rw [rrcf_r_matchReverseResidual_eq_sub]
  exact trunc_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_le_twentyone N hN

/-- The named reverse residual truncates to zero through degree `20`. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_through_twenty :
    PowerSeries.trunc 21 rrcf_r_matchReverseResidual = 0 :=
  trunc_rrcf_r_matchReverseResidual_eq_zero_of_le_twentyone 21 (by omega)

/-- X-adic form for the named reverse residual: it is divisible by `X^21`. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchReverseResidual :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual := by
  rw [rrcf_r_matchReverseResidual_eq_sub]
  exact X_pow_twentyone_dvd_rrcf_r_via_CF_sub_rrcf_r

/-- X-adic divisibility of the named reverse residual is equivalent to
vanishing of its coefficients below degree `21`. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_iff_coeff_zero :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual ↔
      ∀ k : ℕ, k < 21 → rrcf_r_matchReverseResidual.coeff k = 0 := by
  rw [PowerSeries.X_pow_dvd_iff]

/-- X-adic divisibility of the named reverse residual is equivalent to its
truncation through degree `20` being zero. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_iff_trunc_eq_zero :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual ↔
      PowerSeries.trunc 21 rrcf_r_matchReverseResidual = 0 := by
  rw [X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_iff_coeff_zero,
    trunc_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_zero 21]

/-- Extract low-degree coefficient vanishing from X-adic divisibility of the
named reverse residual. -/
theorem coeff_rrcf_r_matchReverseResidual_eq_zero_of_X_pow_twentyone_dvd
    {k : ℕ} (h : (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual) (hk : k < 21) :
    rrcf_r_matchReverseResidual.coeff k = 0 :=
  (X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_iff_coeff_zero.1 h) k hk

/-- Build X-adic divisibility of the named reverse residual from low-degree
coefficient vanishing. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_of_coeff_zero
    (h : ∀ k : ℕ, k < 21 → rrcf_r_matchReverseResidual.coeff k = 0) :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual :=
  X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_iff_coeff_zero.2 h

/-- X-adic divisibility of the named reverse residual implies zero truncation
through degree `20`. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_of_X_pow_twentyone_dvd
    (h : (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual) :
    PowerSeries.trunc 21 rrcf_r_matchReverseResidual = 0 :=
  X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_iff_trunc_eq_zero.1 h

/-- Zero truncation through degree `20` implies X-adic divisibility of the named
reverse residual. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_of_trunc_eq_zero
    (h : PowerSeries.trunc 21 rrcf_r_matchReverseResidual = 0) :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual :=
  X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_iff_trunc_eq_zero.2 h

/-- X-adic divisibility of the named reverse residual gives coefficient
agreement below degree `21`, with the sides swapped. -/
theorem coeff_rrcf_r_via_CF_eq_rrcf_r_of_X_pow_twentyone_dvd_matchReverseResidual
    {k : ℕ} (h : (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual) (hk : k < 21) :
    rrcf_r_via_CF.coeff k = rrcf_r.coeff k :=
  (coeff_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_eq k).1
    (coeff_rrcf_r_matchReverseResidual_eq_zero_of_X_pow_twentyone_dvd h hk)

/-- X-adic divisibility of the named reverse residual gives reverse truncation
equality through degree `20`. -/
theorem trunc_rrcf_r_via_CF_eq_rrcf_r_of_X_pow_twentyone_dvd_matchReverseResidual
    (h : (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual) :
    PowerSeries.trunc 21 rrcf_r_via_CF = PowerSeries.trunc 21 rrcf_r :=
  (trunc_rrcf_r_matchReverseResidual_eq_zero_iff_eq 21).1
    (trunc_rrcf_r_matchReverseResidual_eq_zero_of_X_pow_twentyone_dvd h)

/-- Low-degree reverse coefficient agreement gives X-adic divisibility of the
named reverse residual. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_of_coeff_eq
    (h : ∀ k : ℕ, k < 21 → rrcf_r_via_CF.coeff k = rrcf_r.coeff k) :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual :=
  X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_of_coeff_zero
    (fun k hk => (coeff_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_eq k).2 (h k hk))

/-- The proved X-adic divisibility of the named reverse residual recovers
reverse coefficient agreement through degree `20`. -/
theorem coeff_rrcf_r_via_CF_eq_rrcf_r_of_lt_twentyone_via_X_pow_twentyone_dvd
    {k : ℕ} (hk : k < 21) :
    rrcf_r_via_CF.coeff k = rrcf_r.coeff k :=
  coeff_rrcf_r_via_CF_eq_rrcf_r_of_X_pow_twentyone_dvd_matchReverseResidual
    X_pow_twentyone_dvd_rrcf_r_matchReverseResidual hk

/-- The proved X-adic divisibility of the named reverse residual recovers
reverse truncation equality through degree `20`. -/
theorem trunc_rrcf_r_via_CF_eq_rrcf_r_through_twenty_via_X_pow_twentyone_dvd :
    PowerSeries.trunc 21 rrcf_r_via_CF = PowerSeries.trunc 21 rrcf_r :=
  trunc_rrcf_r_via_CF_eq_rrcf_r_of_X_pow_twentyone_dvd_matchReverseResidual
    X_pow_twentyone_dvd_rrcf_r_matchReverseResidual

/-- If the named reverse residual has a nonzero coefficient, it must occur at
degree at least `21`. -/
theorem twentyone_le_of_coeff_rrcf_r_matchReverseResidual_ne_zero
    {k : ℕ} (hk : rrcf_r_matchReverseResidual.coeff k ≠ 0) :
    21 ≤ k := by
  apply twentyone_le_of_coeff_rrcf_r_via_CF_sub_rrcf_r_ne_zero
  simpa [rrcf_r_matchReverseResidual_eq_sub] using hk

/-- The reverse residual is the negative of the forward residual. -/
theorem rrcf_r_matchReverseResidual_eq_neg_matchResidual :
    rrcf_r_matchReverseResidual = -rrcf_r_matchResidual := by
  rw [rrcf_r_matchReverseResidual_eq_sub, rrcf_r_matchResidual_eq_sub]
  ring

/-- The forward residual is the negative of the reverse residual. -/
theorem rrcf_r_matchResidual_eq_neg_matchReverseResidual :
    rrcf_r_matchResidual = -rrcf_r_matchReverseResidual := by
  rw [rrcf_r_matchReverseResidual_eq_neg_matchResidual]
  simp

/-- The forward and reverse residuals add to zero. -/
theorem rrcf_r_matchResidual_add_matchReverseResidual_eq_zero :
    rrcf_r_matchResidual + rrcf_r_matchReverseResidual = 0 := by
  rw [rrcf_r_matchReverseResidual_eq_neg_matchResidual]
  simp

/-- The reverse and forward residuals add to zero. -/
theorem rrcf_r_matchReverseResidual_add_matchResidual_eq_zero :
    rrcf_r_matchReverseResidual + rrcf_r_matchResidual = 0 := by
  rw [rrcf_r_matchReverseResidual_eq_neg_matchResidual]
  simp

/-- Coefficient form of the fact that the forward and reverse residuals add to
zero. -/
theorem coeff_rrcf_r_matchResidual_add_matchReverseResidual_eq_zero (k : ℕ) :
    (rrcf_r_matchResidual + rrcf_r_matchReverseResidual).coeff k = 0 := by
  rw [rrcf_r_matchResidual_add_matchReverseResidual_eq_zero]
  simp

/-- Coefficient form of the fact that the reverse and forward residuals add to
zero. -/
theorem coeff_rrcf_r_matchReverseResidual_add_matchResidual_eq_zero (k : ℕ) :
    (rrcf_r_matchReverseResidual + rrcf_r_matchResidual).coeff k = 0 := by
  rw [rrcf_r_matchReverseResidual_add_matchResidual_eq_zero]
  simp

/-- Truncated form of the fact that the forward and reverse residuals add to
zero. -/
theorem trunc_rrcf_r_matchResidual_add_matchReverseResidual_eq_zero (N : ℕ) :
    PowerSeries.trunc N (rrcf_r_matchResidual + rrcf_r_matchReverseResidual) = 0 := by
  rw [rrcf_r_matchResidual_add_matchReverseResidual_eq_zero]
  simp

/-- Truncated form of the fact that the reverse and forward residuals add to
zero. -/
theorem trunc_rrcf_r_matchReverseResidual_add_matchResidual_eq_zero (N : ℕ) :
    PowerSeries.trunc N (rrcf_r_matchReverseResidual + rrcf_r_matchResidual) = 0 := by
  rw [rrcf_r_matchReverseResidual_add_matchResidual_eq_zero]
  simp

/-- Coefficient relation between the reverse and forward residuals. -/
theorem coeff_rrcf_r_matchReverseResidual_eq_neg_matchResidual (k : ℕ) :
    rrcf_r_matchReverseResidual.coeff k =
      -rrcf_r_matchResidual.coeff k := by
  rw [rrcf_r_matchReverseResidual_eq_neg_matchResidual, map_neg]

/-- Coefficient relation between the forward and reverse residuals. -/
theorem coeff_rrcf_r_matchResidual_eq_neg_matchReverseResidual (k : ℕ) :
    rrcf_r_matchResidual.coeff k =
      -rrcf_r_matchReverseResidual.coeff k := by
  rw [rrcf_r_matchResidual_eq_neg_matchReverseResidual, map_neg]

/-- The forward residual vanishes iff the product and CF-limit forms are equal. -/
theorem rrcf_r_matchResidual_eq_zero_iff :
    rrcf_r_matchResidual = 0 ↔ rrcf_r = rrcf_r_via_CF := by
  rw [rrcf_r_matchResidual_eq_sub, sub_eq_zero]

/-- The reverse residual vanishes iff the CF-limit and product forms are equal. -/
theorem rrcf_r_matchReverseResidual_eq_zero_iff :
    rrcf_r_matchReverseResidual = 0 ↔ rrcf_r_via_CF = rrcf_r := by
  rw [rrcf_r_matchReverseResidual_eq_sub, sub_eq_zero]

/-- Forward residual vanishing gives the desired product-form equality. -/
theorem rrcf_r_eq_rrcf_r_via_CF_of_matchResidual_eq_zero
    (h : rrcf_r_matchResidual = 0) :
    rrcf_r = rrcf_r_via_CF :=
  rrcf_r_matchResidual_eq_zero_iff.1 h

/-- Forward residual vanishing also gives the equality with sides swapped. -/
theorem rrcf_r_via_CF_eq_rrcf_r_of_matchResidual_eq_zero
    (h : rrcf_r_matchResidual = 0) :
    rrcf_r_via_CF = rrcf_r :=
  (rrcf_r_matchResidual_eq_zero_iff.1 h).symm

/-- Equality of the product and CF-limit forms gives forward residual
vanishing. -/
theorem rrcf_r_matchResidual_eq_zero_of_rrcf_r_eq_rrcf_r_via_CF
    (h : rrcf_r = rrcf_r_via_CF) :
    rrcf_r_matchResidual = 0 :=
  rrcf_r_matchResidual_eq_zero_iff.2 h

/-- Equality of the CF-limit and product forms also gives forward residual
vanishing. -/
theorem rrcf_r_matchResidual_eq_zero_of_rrcf_r_via_CF_eq_rrcf_r
    (h : rrcf_r_via_CF = rrcf_r) :
    rrcf_r_matchResidual = 0 :=
  rrcf_r_matchResidual_eq_zero_of_rrcf_r_eq_rrcf_r_via_CF h.symm

/-- Reverse residual vanishing gives the same equality, with sides swapped. -/
theorem rrcf_r_eq_rrcf_r_via_CF_of_matchReverseResidual_eq_zero
    (h : rrcf_r_matchReverseResidual = 0) :
    rrcf_r = rrcf_r_via_CF :=
  (rrcf_r_matchReverseResidual_eq_zero_iff.1 h).symm

/-- Reverse residual vanishing gives the CF-limit/product equality. -/
theorem rrcf_r_via_CF_eq_rrcf_r_of_matchReverseResidual_eq_zero
    (h : rrcf_r_matchReverseResidual = 0) :
    rrcf_r_via_CF = rrcf_r :=
  rrcf_r_matchReverseResidual_eq_zero_iff.1 h

/-- Equality of the CF-limit and product forms gives reverse residual
vanishing. -/
theorem rrcf_r_matchReverseResidual_eq_zero_of_rrcf_r_via_CF_eq_rrcf_r
    (h : rrcf_r_via_CF = rrcf_r) :
    rrcf_r_matchReverseResidual = 0 :=
  rrcf_r_matchReverseResidual_eq_zero_iff.2 h

/-- Equality of the product and CF-limit forms also gives reverse residual
vanishing. -/
theorem rrcf_r_matchReverseResidual_eq_zero_of_rrcf_r_eq_rrcf_r_via_CF
    (h : rrcf_r = rrcf_r_via_CF) :
    rrcf_r_matchReverseResidual = 0 :=
  rrcf_r_matchReverseResidual_eq_zero_of_rrcf_r_via_CF_eq_rrcf_r h.symm

/-- Equality of the product and CF-limit forms is equivalent to coefficientwise
equality. -/
theorem rrcf_r_eq_rrcf_r_via_CF_iff_coeff_eq :
    rrcf_r = rrcf_r_via_CF ↔
      ∀ k : ℕ, rrcf_r.coeff k = rrcf_r_via_CF.coeff k := by
  constructor
  · intro h k
    rw [h]
  · intro h
    ext k
    exact h k

/-- Forward residual vanishes iff all product and CF-limit coefficients agree. -/
theorem rrcf_r_matchResidual_eq_zero_iff_coeff_eq :
    rrcf_r_matchResidual = 0 ↔
      ∀ k : ℕ, rrcf_r.coeff k = rrcf_r_via_CF.coeff k := by
  rw [rrcf_r_matchResidual_eq_zero_iff,
    rrcf_r_eq_rrcf_r_via_CF_iff_coeff_eq]

/-- Coefficientwise agreement gives forward residual vanishing. -/
theorem rrcf_r_matchResidual_eq_zero_of_coeff_eq
    (h : ∀ k : ℕ, rrcf_r.coeff k = rrcf_r_via_CF.coeff k) :
    rrcf_r_matchResidual = 0 :=
  rrcf_r_matchResidual_eq_zero_iff_coeff_eq.2 h

/-- Forward residual vanishing gives coefficientwise agreement. -/
theorem coeff_rrcf_r_eq_rrcf_r_via_CF_of_matchResidual_eq_zero
    (h : rrcf_r_matchResidual = 0) (k : ℕ) :
    rrcf_r.coeff k = rrcf_r_via_CF.coeff k :=
  rrcf_r_matchResidual_eq_zero_iff_coeff_eq.1 h k

/-- Forward residual vanishing gives coefficientwise agreement with sides
swapped. -/
theorem coeff_rrcf_r_via_CF_eq_rrcf_r_of_matchResidual_eq_zero
    (h : rrcf_r_matchResidual = 0) (k : ℕ) :
    rrcf_r_via_CF.coeff k = rrcf_r.coeff k :=
  (coeff_rrcf_r_eq_rrcf_r_via_CF_of_matchResidual_eq_zero h k).symm

/-- Coefficientwise agreement with sides swapped also gives forward residual
vanishing. -/
theorem rrcf_r_matchResidual_eq_zero_of_coeff_eq_symm
    (h : ∀ k : ℕ, rrcf_r_via_CF.coeff k = rrcf_r.coeff k) :
    rrcf_r_matchResidual = 0 :=
  rrcf_r_matchResidual_eq_zero_of_coeff_eq (fun k => (h k).symm)

/-- Equality of the CF-limit and product forms is equivalent to coefficientwise
equality, with the two sides swapped. -/
theorem rrcf_r_via_CF_eq_rrcf_r_iff_coeff_eq :
    rrcf_r_via_CF = rrcf_r ↔
      ∀ k : ℕ, rrcf_r_via_CF.coeff k = rrcf_r.coeff k := by
  constructor
  · intro h k
    rw [h]
  · intro h
    ext k
    exact h k

/-- Reverse residual vanishes iff all CF-limit and product coefficients agree. -/
theorem rrcf_r_matchReverseResidual_eq_zero_iff_coeff_eq :
    rrcf_r_matchReverseResidual = 0 ↔
      ∀ k : ℕ, rrcf_r_via_CF.coeff k = rrcf_r.coeff k := by
  rw [rrcf_r_matchReverseResidual_eq_zero_iff,
    rrcf_r_via_CF_eq_rrcf_r_iff_coeff_eq]

/-- Coefficientwise agreement in reverse order gives reverse residual
vanishing. -/
theorem rrcf_r_matchReverseResidual_eq_zero_of_coeff_eq
    (h : ∀ k : ℕ, rrcf_r_via_CF.coeff k = rrcf_r.coeff k) :
    rrcf_r_matchReverseResidual = 0 :=
  rrcf_r_matchReverseResidual_eq_zero_iff_coeff_eq.2 h

/-- Reverse residual vanishing gives coefficientwise agreement in reverse
order. -/
theorem coeff_rrcf_r_via_CF_eq_rrcf_r_of_matchReverseResidual_eq_zero
    (h : rrcf_r_matchReverseResidual = 0) (k : ℕ) :
    rrcf_r_via_CF.coeff k = rrcf_r.coeff k :=
  rrcf_r_matchReverseResidual_eq_zero_iff_coeff_eq.1 h k

/-- Reverse residual vanishing gives coefficientwise agreement in forward
order. -/
theorem coeff_rrcf_r_eq_rrcf_r_via_CF_of_matchReverseResidual_eq_zero
    (h : rrcf_r_matchReverseResidual = 0) (k : ℕ) :
    rrcf_r.coeff k = rrcf_r_via_CF.coeff k :=
  (coeff_rrcf_r_via_CF_eq_rrcf_r_of_matchReverseResidual_eq_zero h k).symm

/-- Coefficientwise agreement in forward order also gives reverse residual
vanishing. -/
theorem rrcf_r_matchReverseResidual_eq_zero_of_coeff_eq_symm
    (h : ∀ k : ℕ, rrcf_r.coeff k = rrcf_r_via_CF.coeff k) :
    rrcf_r_matchReverseResidual = 0 :=
  rrcf_r_matchReverseResidual_eq_zero_of_coeff_eq (fun k => (h k).symm)

/-- The forward residual vanishes iff the reverse residual vanishes. -/
theorem rrcf_r_matchResidual_eq_zero_iff_matchReverseResidual_eq_zero :
    rrcf_r_matchResidual = 0 ↔ rrcf_r_matchReverseResidual = 0 := by
  rw [rrcf_r_matchReverseResidual_eq_neg_matchResidual]
  simp

/-- Forward residual vanishing gives reverse residual vanishing. -/
theorem rrcf_r_matchReverseResidual_eq_zero_of_matchResidual_eq_zero
    (h : rrcf_r_matchResidual = 0) :
    rrcf_r_matchReverseResidual = 0 :=
  rrcf_r_matchResidual_eq_zero_iff_matchReverseResidual_eq_zero.1 h

/-- The reverse residual vanishes iff the forward residual vanishes. -/
theorem rrcf_r_matchReverseResidual_eq_zero_iff_matchResidual_eq_zero :
    rrcf_r_matchReverseResidual = 0 ↔ rrcf_r_matchResidual = 0 :=
  rrcf_r_matchResidual_eq_zero_iff_matchReverseResidual_eq_zero.symm

/-- Reverse residual vanishing gives forward residual vanishing. -/
theorem rrcf_r_matchResidual_eq_zero_of_matchReverseResidual_eq_zero
    (h : rrcf_r_matchReverseResidual = 0) :
    rrcf_r_matchResidual = 0 :=
  rrcf_r_matchReverseResidual_eq_zero_iff_matchResidual_eq_zero.1 h

/-- Coefficientwise vanishing of the forward residual is equivalent to
coefficientwise vanishing of the reverse residual. -/
theorem coeff_rrcf_r_matchResidual_eq_zero_iff_matchReverseResidual_eq_zero
    (k : ℕ) :
    rrcf_r_matchResidual.coeff k = 0 ↔
      rrcf_r_matchReverseResidual.coeff k = 0 := by
  rw [coeff_rrcf_r_matchReverseResidual_eq_neg_matchResidual]
  simp

/-- Forward residual coefficient vanishing gives reverse residual coefficient
vanishing. -/
theorem coeff_rrcf_r_matchReverseResidual_eq_zero_of_matchResidual_eq_zero
    {k : ℕ} (h : rrcf_r_matchResidual.coeff k = 0) :
    rrcf_r_matchReverseResidual.coeff k = 0 :=
  (coeff_rrcf_r_matchResidual_eq_zero_iff_matchReverseResidual_eq_zero k).1 h

/-- Coefficientwise vanishing of the reverse residual is equivalent to
coefficientwise vanishing of the forward residual. -/
theorem coeff_rrcf_r_matchReverseResidual_eq_zero_iff_matchResidual_eq_zero
    (k : ℕ) :
    rrcf_r_matchReverseResidual.coeff k = 0 ↔
      rrcf_r_matchResidual.coeff k = 0 :=
  (coeff_rrcf_r_matchResidual_eq_zero_iff_matchReverseResidual_eq_zero k).symm

/-- Reverse residual coefficient vanishing gives forward residual coefficient
vanishing. -/
theorem coeff_rrcf_r_matchResidual_eq_zero_of_matchReverseResidual_eq_zero
    {k : ℕ} (h : rrcf_r_matchReverseResidual.coeff k = 0) :
    rrcf_r_matchResidual.coeff k = 0 :=
  (coeff_rrcf_r_matchReverseResidual_eq_zero_iff_matchResidual_eq_zero k).1 h

/-- Zero truncation of the forward residual is equivalent to zero truncation of
the reverse residual. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_iff_matchReverseResidual_eq_zero
    (N : ℕ) :
    PowerSeries.trunc N rrcf_r_matchResidual = 0 ↔
      PowerSeries.trunc N rrcf_r_matchReverseResidual = 0 := by
  rw [trunc_rrcf_r_matchResidual_eq_zero_iff_coeff_zero,
    trunc_rrcf_r_matchReverseResidual_eq_zero_iff_coeff_zero]
  constructor
  · intro h k hk
    exact coeff_rrcf_r_matchReverseResidual_eq_zero_of_matchResidual_eq_zero
      (h k hk)
  · intro h k hk
    exact coeff_rrcf_r_matchResidual_eq_zero_of_matchReverseResidual_eq_zero
      (h k hk)

/-- Zero truncation of the reverse residual is equivalent to zero truncation of
the forward residual. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_iff_matchResidual_eq_zero
    (N : ℕ) :
    PowerSeries.trunc N rrcf_r_matchReverseResidual = 0 ↔
      PowerSeries.trunc N rrcf_r_matchResidual = 0 :=
  (trunc_rrcf_r_matchResidual_eq_zero_iff_matchReverseResidual_eq_zero N).symm

/-- Zero truncation of the forward residual gives zero truncation of the
reverse residual. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_of_matchResidual_eq_zero
    {N : ℕ} (h : PowerSeries.trunc N rrcf_r_matchResidual = 0) :
    PowerSeries.trunc N rrcf_r_matchReverseResidual = 0 :=
  (trunc_rrcf_r_matchResidual_eq_zero_iff_matchReverseResidual_eq_zero N).1 h

/-- Zero truncation of the reverse residual gives zero truncation of the
forward residual. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_of_matchReverseResidual_eq_zero
    {N : ℕ} (h : PowerSeries.trunc N rrcf_r_matchReverseResidual = 0) :
    PowerSeries.trunc N rrcf_r_matchResidual = 0 :=
  (trunc_rrcf_r_matchReverseResidual_eq_zero_iff_matchResidual_eq_zero N).1 h

/-- `X^21` divisibility is the same for the forward and reverse residuals. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_matchReverseResidual :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual ↔
      (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual := by
  rw [X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_coeff_zero,
    X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_iff_coeff_zero]
  constructor
  · intro h k hk
    exact coeff_rrcf_r_matchReverseResidual_eq_zero_of_matchResidual_eq_zero
      (h k hk)
  · intro h k hk
    exact coeff_rrcf_r_matchResidual_eq_zero_of_matchReverseResidual_eq_zero
      (h k hk)

/-- Forward residual `X^21` divisibility gives reverse residual `X^21`
divisibility. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_of_matchResidual
    (h : (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual) :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual :=
  X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_matchReverseResidual.1 h

/-- Reverse residual `X^21` divisibility gives forward residual `X^21`
divisibility. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchResidual_of_matchReverseResidual
    (h : (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual) :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual :=
  X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_matchReverseResidual.2 h

/-- The forward and reverse residuals have equivalent zero truncations through
degree `20`. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_iff_matchReverseResidual_eq_zero_through_twenty :
    PowerSeries.trunc 21 rrcf_r_matchResidual = 0 ↔
      PowerSeries.trunc 21 rrcf_r_matchReverseResidual = 0 :=
  trunc_rrcf_r_matchResidual_eq_zero_iff_matchReverseResidual_eq_zero 21

/-- The reverse residual truncates to zero through degree `20`, recovered from
the forward residual. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_through_twenty_from_matchResidual :
    PowerSeries.trunc 21 rrcf_r_matchReverseResidual = 0 :=
  trunc_rrcf_r_matchReverseResidual_eq_zero_of_matchResidual_eq_zero
    trunc_rrcf_r_matchResidual_eq_zero_through_twenty

/-- The forward residual truncates to zero through degree `20`, recovered from
the reverse residual. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_through_twenty_from_matchReverseResidual :
    PowerSeries.trunc 21 rrcf_r_matchResidual = 0 :=
  trunc_rrcf_r_matchResidual_eq_zero_of_matchReverseResidual_eq_zero
    trunc_rrcf_r_matchReverseResidual_eq_zero_through_twenty

/-- `X^21` divisibility of the reverse residual, recovered from the forward
residual divisibility. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_from_matchResidual :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual :=
  X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_of_matchResidual
    X_pow_twentyone_dvd_rrcf_r_matchResidual

/-- `X^21` divisibility of the forward residual, recovered from the reverse
residual divisibility. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchResidual_from_matchReverseResidual :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual :=
  X_pow_twentyone_dvd_rrcf_r_matchResidual_of_matchReverseResidual
    X_pow_twentyone_dvd_rrcf_r_matchReverseResidual

/-- There is no product-versus-CF coefficient mismatch below degree `21`. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_ne_rrcf_r_via_CF :
    ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r.coeff k ≠ rrcf_r_via_CF.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_match_of_lt_twentyone hk)

/-- There is no product-versus-CF coefficient mismatch through degree `20`. -/
theorem not_exists_le_twenty_coeff_rrcf_r_ne_rrcf_r_via_CF :
    ¬ ∃ k : ℕ, k ≤ 20 ∧ rrcf_r.coeff k ≠ rrcf_r_via_CF.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_match_of_le_twenty hk)

/-- There is no CF-versus-product coefficient mismatch below degree `21`. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_via_CF_ne_rrcf_r :
    ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_via_CF.coeff k ≠ rrcf_r.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne ((coeff_match_of_lt_twentyone hk).symm)

/-- There is no CF-versus-product coefficient mismatch through degree `20`. -/
theorem not_exists_le_twenty_coeff_rrcf_r_via_CF_ne_rrcf_r :
    ¬ ∃ k : ℕ, k ≤ 20 ∧ rrcf_r_via_CF.coeff k ≠ rrcf_r.coeff k := by
  rintro ⟨k, hk, hne⟩
  exact hne ((coeff_match_of_le_twenty hk).symm)

/-- The raw forward difference has no nonzero coefficient below degree `21`. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_sub_rrcf_r_via_CF_ne_zero :
    ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r - rrcf_r_via_CF).coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_lt_twentyone hk)

/-- The raw forward difference has no nonzero coefficient through degree `20`. -/
theorem not_exists_le_twenty_coeff_rrcf_r_sub_rrcf_r_via_CF_ne_zero :
    ¬ ∃ k : ℕ, k ≤ 20 ∧ (rrcf_r - rrcf_r_via_CF).coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_le_twenty hk)

/-- The raw reverse difference has no nonzero coefficient below degree `21`. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_via_CF_sub_rrcf_r_ne_zero :
    ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r_via_CF - rrcf_r).coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_lt_twentyone hk)

/-- The raw reverse difference has no nonzero coefficient through degree `20`. -/
theorem not_exists_le_twenty_coeff_rrcf_r_via_CF_sub_rrcf_r_ne_zero :
    ¬ ∃ k : ℕ, k ≤ 20 ∧ (rrcf_r_via_CF - rrcf_r).coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_le_twenty hk)

/-- There is no nonzero forward residual coefficient below degree `21`. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_matchResidual_ne_zero :
    ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchResidual.coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_rrcf_r_matchResidual_eq_zero_of_lt_twentyone hk)

/-- There is no nonzero forward residual coefficient through degree `20`. -/
theorem not_exists_le_twenty_coeff_rrcf_r_matchResidual_ne_zero :
    ¬ ∃ k : ℕ, k ≤ 20 ∧ rrcf_r_matchResidual.coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_rrcf_r_matchResidual_eq_zero_of_le_twenty hk)

/-- There is no nonzero reverse residual coefficient below degree `21`. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_matchReverseResidual_ne_zero :
    ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchReverseResidual.coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_rrcf_r_matchReverseResidual_eq_zero_of_lt_twentyone hk)

/-- There is no nonzero reverse residual coefficient through degree `20`. -/
theorem not_exists_le_twenty_coeff_rrcf_r_matchReverseResidual_ne_zero :
    ¬ ∃ k : ℕ, k ≤ 20 ∧ rrcf_r_matchReverseResidual.coeff k ≠ 0 := by
  rintro ⟨k, hk, hne⟩
  exact hne (coeff_rrcf_r_matchReverseResidual_eq_zero_of_le_twenty hk)

/-- Every nonzero coefficient of the raw forward difference occurs at degree
at least `21`. -/
theorem coeff_rrcf_r_sub_rrcf_r_via_CF_ne_zero_ge_twentyone
    {k : ℕ} (hk : (rrcf_r - rrcf_r_via_CF).coeff k ≠ 0) :
    21 ≤ k :=
  twentyone_le_of_coeff_rrcf_r_sub_rrcf_r_via_CF_ne_zero hk

/-- Every nonzero coefficient of the raw reverse difference occurs at degree
at least `21`. -/
theorem coeff_rrcf_r_via_CF_sub_rrcf_r_ne_zero_ge_twentyone
    {k : ℕ} (hk : (rrcf_r_via_CF - rrcf_r).coeff k ≠ 0) :
    21 ≤ k :=
  twentyone_le_of_coeff_rrcf_r_via_CF_sub_rrcf_r_ne_zero hk

/-- Every nonzero coefficient of the named forward residual occurs at degree
at least `21`. -/
theorem coeff_rrcf_r_matchResidual_ne_zero_ge_twentyone
    {k : ℕ} (hk : rrcf_r_matchResidual.coeff k ≠ 0) :
    21 ≤ k :=
  twentyone_le_of_coeff_rrcf_r_matchResidual_ne_zero hk

/-- Every nonzero coefficient of the named reverse residual occurs at degree
at least `21`. -/
theorem coeff_rrcf_r_matchReverseResidual_ne_zero_ge_twentyone
    {k : ℕ} (hk : rrcf_r_matchReverseResidual.coeff k ≠ 0) :
    21 ≤ k :=
  twentyone_le_of_coeff_rrcf_r_matchReverseResidual_ne_zero hk

/-- Below degree `21`, the raw forward difference has no nonzero
coefficient, in implication form. -/
theorem coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_not_twentyone_le
    {k : ℕ} (hk : ¬ 21 ≤ k) :
    (rrcf_r - rrcf_r_via_CF).coeff k = 0 :=
  coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_lt_twentyone (by omega)

/-- Below degree `21`, the raw reverse difference has no nonzero coefficient,
in implication form. -/
theorem coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_not_twentyone_le
    {k : ℕ} (hk : ¬ 21 ≤ k) :
    (rrcf_r_via_CF - rrcf_r).coeff k = 0 :=
  coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_lt_twentyone (by omega)

/-- Below degree `21`, the named forward residual has no nonzero coefficient,
in implication form. -/
theorem coeff_rrcf_r_matchResidual_eq_zero_of_not_twentyone_le
    {k : ℕ} (hk : ¬ 21 ≤ k) :
    rrcf_r_matchResidual.coeff k = 0 :=
  coeff_rrcf_r_matchResidual_eq_zero_of_lt_twentyone (by omega)

/-- Below degree `21`, the named reverse residual has no nonzero coefficient,
in implication form. -/
theorem coeff_rrcf_r_matchReverseResidual_eq_zero_of_not_twentyone_le
    {k : ℕ} (hk : ¬ 21 ≤ k) :
    rrcf_r_matchReverseResidual.coeff k = 0 :=
  coeff_rrcf_r_matchReverseResidual_eq_zero_of_lt_twentyone (by omega)

/-- Raw forward `X^21` divisibility is equivalent to having no nonzero
coefficient below degree `21`. -/
theorem X_pow_twentyone_dvd_rrcf_r_sub_rrcf_r_via_CF_iff_not_exists_lt_twentyone_coeff_ne_zero :
    (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r - rrcf_r_via_CF) ↔
      ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r - rrcf_r_via_CF).coeff k ≠ 0 := by
  rw [PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h
    rintro ⟨k, hk, hne⟩
    exact hne (h k hk)
  · intro h k hk
    by_cases hzero : (rrcf_r - rrcf_r_via_CF).coeff k = 0
    · exact hzero
    · exact False.elim (h ⟨k, hk, hzero⟩)

/-- Raw reverse `X^21` divisibility is equivalent to having no nonzero
coefficient below degree `21`. -/
theorem X_pow_twentyone_dvd_rrcf_r_via_CF_sub_rrcf_r_iff_not_exists_lt_twentyone_coeff_ne_zero :
    (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r_via_CF - rrcf_r) ↔
      ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r_via_CF - rrcf_r).coeff k ≠ 0 := by
  rw [PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h
    rintro ⟨k, hk, hne⟩
    exact hne (h k hk)
  · intro h k hk
    by_cases hzero : (rrcf_r_via_CF - rrcf_r).coeff k = 0
    · exact hzero
    · exact False.elim (h ⟨k, hk, hzero⟩)

/-- Named forward residual `X^21` divisibility is equivalent to having no
nonzero coefficient below degree `21`. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_not_exists_lt_twentyone_coeff_ne_zero :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual ↔
      ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchResidual.coeff k ≠ 0 := by
  rw [X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_coeff_zero]
  constructor
  · intro h
    rintro ⟨k, hk, hne⟩
    exact hne (h k hk)
  · intro h k hk
    by_cases hzero : rrcf_r_matchResidual.coeff k = 0
    · exact hzero
    · exact False.elim (h ⟨k, hk, hzero⟩)

/-- Named reverse residual `X^21` divisibility is equivalent to having no
nonzero coefficient below degree `21`. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_iff_not_exists_lt_twentyone_coeff_ne_zero :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual ↔
      ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchReverseResidual.coeff k ≠ 0 := by
  rw [X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_iff_coeff_zero]
  constructor
  · intro h
    rintro ⟨k, hk, hne⟩
    exact hne (h k hk)
  · intro h k hk
    by_cases hzero : rrcf_r_matchReverseResidual.coeff k = 0
    · exact hzero
    · exact False.elim (h ⟨k, hk, hzero⟩)

/-- A length-`21` truncation is zero iff there is no nonzero coefficient below
degree `21`. -/
theorem trunc_twentyone_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero
    (p : ℚ⟦X⟧) :
    PowerSeries.trunc 21 p = 0 ↔
      ¬ ∃ k : ℕ, k < 21 ∧ p.coeff k ≠ 0 := by
  constructor
  · intro h
    rintro ⟨k, hk, hne⟩
    have hcoeff := congrArg (fun q => q.coeff k) h
    exact hne (by simpa [PowerSeries.coeff_trunc, hk] using hcoeff)
  · intro h
    ext k
    by_cases hk : k < 21
    · rw [PowerSeries.coeff_trunc, if_pos hk]
      by_cases hzero : p.coeff k = 0
      · exact hzero
      · exact False.elim (h ⟨k, hk, hzero⟩)
    · rw [PowerSeries.coeff_trunc, if_neg hk]
      simp

/-- `X^21` divisibility is equivalent to having no nonzero coefficient below
degree `21`. -/
theorem X_pow_twentyone_dvd_iff_not_exists_lt_twentyone_coeff_ne_zero
    (p : ℚ⟦X⟧) :
    (X ^ 21 : ℚ⟦X⟧) ∣ p ↔
      ¬ ∃ k : ℕ, k < 21 ∧ p.coeff k ≠ 0 := by
  rw [PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h
    rintro ⟨k, hk, hne⟩
    exact hne (h k hk)
  · intro h k hk
    by_cases hzero : p.coeff k = 0
    · exact hzero
    · exact False.elim (h ⟨k, hk, hzero⟩)

/-- A length-`21` zero truncation is equivalent to `X^21` divisibility. -/
theorem trunc_twentyone_eq_zero_iff_X_pow_twentyone_dvd
    (p : ℚ⟦X⟧) :
    PowerSeries.trunc 21 p = 0 ↔ (X ^ 21 : ℚ⟦X⟧) ∣ p := by
  rw [trunc_twentyone_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero,
    X_pow_twentyone_dvd_iff_not_exists_lt_twentyone_coeff_ne_zero]

/-- `X^21` divisibility is equivalent to a length-`21` zero truncation. -/
theorem X_pow_twentyone_dvd_iff_trunc_twentyone_eq_zero
    (p : ℚ⟦X⟧) :
    (X ^ 21 : ℚ⟦X⟧) ∣ p ↔ PowerSeries.trunc 21 p = 0 :=
  (trunc_twentyone_eq_zero_iff_X_pow_twentyone_dvd p).symm

/-- The raw forward difference truncates to zero through degree `20` iff it is
divisible by `X^21`. -/
theorem trunc_rrcf_r_sub_rrcf_r_via_CF_eq_zero_iff_X_pow_twentyone_dvd :
    PowerSeries.trunc 21 (rrcf_r - rrcf_r_via_CF) = 0 ↔
      (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r - rrcf_r_via_CF) :=
  trunc_twentyone_eq_zero_iff_X_pow_twentyone_dvd
    (rrcf_r - rrcf_r_via_CF)

/-- The raw reverse difference truncates to zero through degree `20` iff it is
divisible by `X^21`. -/
theorem trunc_rrcf_r_via_CF_sub_rrcf_r_eq_zero_iff_X_pow_twentyone_dvd :
    PowerSeries.trunc 21 (rrcf_r_via_CF - rrcf_r) = 0 ↔
      (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r_via_CF - rrcf_r) :=
  trunc_twentyone_eq_zero_iff_X_pow_twentyone_dvd
    (rrcf_r_via_CF - rrcf_r)

/-- The named forward residual truncates to zero through degree `20` iff it is
divisible by `X^21`. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_iff_X_pow_twentyone_dvd :
    PowerSeries.trunc 21 rrcf_r_matchResidual = 0 ↔
      (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual :=
  trunc_twentyone_eq_zero_iff_X_pow_twentyone_dvd rrcf_r_matchResidual

/-- The named reverse residual truncates to zero through degree `20` iff it is
divisible by `X^21`. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_iff_X_pow_twentyone_dvd :
    PowerSeries.trunc 21 rrcf_r_matchReverseResidual = 0 ↔
      (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual :=
  trunc_twentyone_eq_zero_iff_X_pow_twentyone_dvd rrcf_r_matchReverseResidual

/-- The raw forward difference truncates to zero through degree `20` iff it has
no nonzero coefficient below degree `21`. -/
theorem trunc_rrcf_r_sub_rrcf_r_via_CF_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero :
    PowerSeries.trunc 21 (rrcf_r - rrcf_r_via_CF) = 0 ↔
      ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r - rrcf_r_via_CF).coeff k ≠ 0 :=
  trunc_twentyone_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero
    (rrcf_r - rrcf_r_via_CF)

/-- The raw reverse difference truncates to zero through degree `20` iff it has
no nonzero coefficient below degree `21`. -/
theorem trunc_rrcf_r_via_CF_sub_rrcf_r_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero :
    PowerSeries.trunc 21 (rrcf_r_via_CF - rrcf_r) = 0 ↔
      ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r_via_CF - rrcf_r).coeff k ≠ 0 :=
  trunc_twentyone_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero
    (rrcf_r_via_CF - rrcf_r)

/-- The named forward residual truncates to zero through degree `20` iff it has
no nonzero coefficient below degree `21`. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero :
    PowerSeries.trunc 21 rrcf_r_matchResidual = 0 ↔
      ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchResidual.coeff k ≠ 0 :=
  trunc_twentyone_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero
    rrcf_r_matchResidual

/-- The named reverse residual truncates to zero through degree `20` iff it has
no nonzero coefficient below degree `21`. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero :
    PowerSeries.trunc 21 rrcf_r_matchReverseResidual = 0 ↔
      ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchReverseResidual.coeff k ≠ 0 :=
  trunc_twentyone_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero
    rrcf_r_matchReverseResidual

/-- Finite-index raw forward-difference coefficient form through degree `20`. -/
theorem coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_fin_twentyone (k : Fin 21) :
    (rrcf_r - rrcf_r_via_CF).coeff k.1 = 0 :=
  coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_lt_twentyone (by omega)

/-- Finite-index raw reverse-difference coefficient form through degree `20`. -/
theorem coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_fin_twentyone (k : Fin 21) :
    (rrcf_r_via_CF - rrcf_r).coeff k.1 = 0 :=
  coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_lt_twentyone (by omega)

/-- Uniform finite-index raw forward-difference coefficient form for any
truncation length at most `21`. -/
theorem coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_fin_of_le_twentyone
    {N : ℕ} (hN : N ≤ 21) (k : Fin N) :
    (rrcf_r - rrcf_r_via_CF).coeff k.1 = 0 :=
  coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_lt_twentyone (by omega)

/-- Uniform finite-index raw reverse-difference coefficient form for any
truncation length at most `21`. -/
theorem coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_fin_of_le_twentyone
    {N : ℕ} (hN : N ≤ 21) (k : Fin N) :
    (rrcf_r_via_CF - rrcf_r).coeff k.1 = 0 :=
  coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_lt_twentyone (by omega)

/-- Symmetric finite-vector form of the coefficient match through degree `20`. -/
theorem coeff_match_fin_symm_twentyone (k : Fin 21) :
    rrcf_r_via_CF.coeff k.1 = rrcf_r.coeff k.1 :=
  (coeff_match_fin_twentyone k).symm

/-- Below degree `21`, the product and CF-limit coefficients agree, in
implication form. -/
theorem coeff_match_of_not_twentyone_le
    {k : ℕ} (hk : ¬ 21 ≤ k) :
    rrcf_r.coeff k = rrcf_r_via_CF.coeff k :=
  coeff_match_of_lt_twentyone (by omega)

/-- Below degree `21`, the CF-limit and product coefficients agree, with the
sides swapped, in implication form. -/
theorem coeff_match_symm_of_not_twentyone_le
    {k : ℕ} (hk : ¬ 21 ≤ k) :
    rrcf_r_via_CF.coeff k = rrcf_r.coeff k :=
  (coeff_match_of_not_twentyone_le hk).symm

/-- The symmetric finite-index coefficient match for any truncation length at
most `21`, recovered from the fixed `Fin 21` form. -/
theorem coeff_match_fin_symm_of_le_twentyone_via_fin_twentyone
    {N : ℕ} (hN : N ≤ 21) (k : Fin N) :
    rrcf_r_via_CF.coeff k.1 = rrcf_r.coeff k.1 :=
  coeff_match_symm_of_lt_twentyone (by omega)

/-- Extract coefficient agreement below `N` directly from truncated equality
of the product and CF-limit forms. -/
theorem coeff_rrcf_r_eq_rrcf_r_via_CF_of_trunc_eq
    {N k : ℕ}
    (h : PowerSeries.trunc N rrcf_r =
      PowerSeries.trunc N rrcf_r_via_CF)
    (hk : k < N) :
    rrcf_r.coeff k = rrcf_r_via_CF.coeff k :=
  (trunc_rrcf_r_eq_rrcf_r_via_CF_iff_coeff_eq N).1 h k hk

/-- Extract reverse coefficient agreement below `N` directly from reverse
truncated equality of the CF-limit and product forms. -/
theorem coeff_rrcf_r_via_CF_eq_rrcf_r_of_trunc_eq
    {N k : ℕ}
    (h : PowerSeries.trunc N rrcf_r_via_CF =
      PowerSeries.trunc N rrcf_r)
    (hk : k < N) :
    rrcf_r_via_CF.coeff k = rrcf_r.coeff k :=
  (trunc_rrcf_r_via_CF_eq_rrcf_r_iff_coeff_eq N).1 h k hk

/-- Extract coefficient agreement below `N` from reverse truncated equality,
with the coefficient equality put in forward order. -/
theorem coeff_rrcf_r_eq_rrcf_r_via_CF_of_reverse_trunc_eq
    {N k : ℕ}
    (h : PowerSeries.trunc N rrcf_r_via_CF =
      PowerSeries.trunc N rrcf_r)
    (hk : k < N) :
    rrcf_r.coeff k = rrcf_r_via_CF.coeff k :=
  (coeff_rrcf_r_via_CF_eq_rrcf_r_of_trunc_eq h hk).symm

/-- Extract reverse coefficient agreement below `N` from forward truncated
equality. -/
theorem coeff_rrcf_r_via_CF_eq_rrcf_r_of_forward_trunc_eq
    {N k : ℕ}
    (h : PowerSeries.trunc N rrcf_r =
      PowerSeries.trunc N rrcf_r_via_CF)
    (hk : k < N) :
    rrcf_r_via_CF.coeff k = rrcf_r.coeff k :=
  (coeff_rrcf_r_eq_rrcf_r_via_CF_of_trunc_eq h hk).symm

/-- The through-degree-`20` truncated equality gives coefficient agreement
below degree `21`. -/
theorem coeff_rrcf_r_eq_rrcf_r_via_CF_of_lt_twentyone_via_trunc_eq
    {k : ℕ} (hk : k < 21) :
    rrcf_r.coeff k = rrcf_r_via_CF.coeff k :=
  coeff_rrcf_r_eq_rrcf_r_via_CF_of_trunc_eq
    trunc_rrcf_r_eq_rrcf_r_via_CF_through_twenty hk

/-- The reverse through-degree-`20` truncated equality gives reverse
coefficient agreement below degree `21`. -/
theorem coeff_rrcf_r_via_CF_eq_rrcf_r_of_lt_twentyone_via_trunc_eq
    {k : ℕ} (hk : k < 21) :
    rrcf_r_via_CF.coeff k = rrcf_r.coeff k :=
  coeff_rrcf_r_via_CF_eq_rrcf_r_of_trunc_eq
    (trunc_rrcf_r_via_CF_eq_rrcf_r_of_le_twentyone 21 (by omega)) hk

/-- The raw forward difference has no nonzero coefficient below degree `21`,
recovered from `X^21` divisibility. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_sub_rrcf_r_via_CF_ne_zero_from_X_pow_twentyone_dvd
    (h : (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r - rrcf_r_via_CF)) :
    ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r - rrcf_r_via_CF).coeff k ≠ 0 :=
  X_pow_twentyone_dvd_rrcf_r_sub_rrcf_r_via_CF_iff_not_exists_lt_twentyone_coeff_ne_zero.1 h

/-- The raw reverse difference has no nonzero coefficient below degree `21`,
recovered from `X^21` divisibility. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_via_CF_sub_rrcf_r_ne_zero_from_X_pow_twentyone_dvd
    (h : (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r_via_CF - rrcf_r)) :
    ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r_via_CF - rrcf_r).coeff k ≠ 0 :=
  X_pow_twentyone_dvd_rrcf_r_via_CF_sub_rrcf_r_iff_not_exists_lt_twentyone_coeff_ne_zero.1 h

/-- The named forward residual has no nonzero coefficient below degree `21`,
recovered from `X^21` divisibility. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_matchResidual_ne_zero_from_X_pow_twentyone_dvd
    (h : (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual) :
    ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchResidual.coeff k ≠ 0 :=
  X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_not_exists_lt_twentyone_coeff_ne_zero.1 h

/-- The named reverse residual has no nonzero coefficient below degree `21`,
recovered from `X^21` divisibility. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_matchReverseResidual_ne_zero_from_X_pow_twentyone_dvd
    (h : (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual) :
    ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchReverseResidual.coeff k ≠ 0 :=
  X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_iff_not_exists_lt_twentyone_coeff_ne_zero.1 h

/-- The raw forward difference has no nonzero coefficient below degree `21`,
recovered from zero truncation through degree `20`. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_sub_rrcf_r_via_CF_ne_zero_from_trunc_eq_zero
    (h : PowerSeries.trunc 21 (rrcf_r - rrcf_r_via_CF) = 0) :
    ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r - rrcf_r_via_CF).coeff k ≠ 0 :=
  trunc_rrcf_r_sub_rrcf_r_via_CF_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero.1 h

/-- The raw reverse difference has no nonzero coefficient below degree `21`,
recovered from zero truncation through degree `20`. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_via_CF_sub_rrcf_r_ne_zero_from_trunc_eq_zero
    (h : PowerSeries.trunc 21 (rrcf_r_via_CF - rrcf_r) = 0) :
    ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r_via_CF - rrcf_r).coeff k ≠ 0 :=
  trunc_rrcf_r_via_CF_sub_rrcf_r_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero.1 h

/-- The named forward residual has no nonzero coefficient below degree `21`,
recovered from zero truncation through degree `20`. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_matchResidual_ne_zero_from_trunc_eq_zero
    (h : PowerSeries.trunc 21 rrcf_r_matchResidual = 0) :
    ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchResidual.coeff k ≠ 0 :=
  trunc_rrcf_r_matchResidual_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero.1 h

/-- The named reverse residual has no nonzero coefficient below degree `21`,
recovered from zero truncation through degree `20`. -/
theorem not_exists_lt_twentyone_coeff_rrcf_r_matchReverseResidual_ne_zero_from_trunc_eq_zero
    (h : PowerSeries.trunc 21 rrcf_r_matchReverseResidual = 0) :
    ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchReverseResidual.coeff k ≠ 0 :=
  trunc_rrcf_r_matchReverseResidual_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero.1 h

/-- The raw forward difference truncates to zero through degree `20`, recovered
from the no-low-degree-counterexample form. -/
theorem trunc_rrcf_r_sub_rrcf_r_via_CF_eq_zero_through_twenty_from_not_exists
    (h : ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r - rrcf_r_via_CF).coeff k ≠ 0) :
    PowerSeries.trunc 21 (rrcf_r - rrcf_r_via_CF) = 0 :=
  trunc_rrcf_r_sub_rrcf_r_via_CF_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero.2 h

/-- The raw reverse difference truncates to zero through degree `20`, recovered
from the no-low-degree-counterexample form. -/
theorem trunc_rrcf_r_via_CF_sub_rrcf_r_eq_zero_through_twenty_from_not_exists
    (h : ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r_via_CF - rrcf_r).coeff k ≠ 0) :
    PowerSeries.trunc 21 (rrcf_r_via_CF - rrcf_r) = 0 :=
  trunc_rrcf_r_via_CF_sub_rrcf_r_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero.2 h

/-- The named forward residual truncates to zero through degree `20`, recovered
from the no-low-degree-counterexample form. -/
theorem trunc_rrcf_r_matchResidual_eq_zero_through_twenty_from_not_exists
    (h : ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchResidual.coeff k ≠ 0) :
    PowerSeries.trunc 21 rrcf_r_matchResidual = 0 :=
  trunc_rrcf_r_matchResidual_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero.2 h

/-- The named reverse residual truncates to zero through degree `20`, recovered
from the no-low-degree-counterexample form. -/
theorem trunc_rrcf_r_matchReverseResidual_eq_zero_through_twenty_from_not_exists
    (h : ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchReverseResidual.coeff k ≠ 0) :
    PowerSeries.trunc 21 rrcf_r_matchReverseResidual = 0 :=
  trunc_rrcf_r_matchReverseResidual_eq_zero_iff_not_exists_lt_twentyone_coeff_ne_zero.2 h

/-- Raw forward `X^21` divisibility, recovered from the
no-low-degree-counterexample form. -/
theorem X_pow_twentyone_dvd_rrcf_r_sub_rrcf_r_via_CF_from_not_exists
    (h : ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r - rrcf_r_via_CF).coeff k ≠ 0) :
    (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r - rrcf_r_via_CF) :=
  X_pow_twentyone_dvd_rrcf_r_sub_rrcf_r_via_CF_iff_not_exists_lt_twentyone_coeff_ne_zero.2 h

/-- Raw reverse `X^21` divisibility, recovered from the
no-low-degree-counterexample form. -/
theorem X_pow_twentyone_dvd_rrcf_r_via_CF_sub_rrcf_r_from_not_exists
    (h : ¬ ∃ k : ℕ, k < 21 ∧ (rrcf_r_via_CF - rrcf_r).coeff k ≠ 0) :
    (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r_via_CF - rrcf_r) :=
  X_pow_twentyone_dvd_rrcf_r_via_CF_sub_rrcf_r_iff_not_exists_lt_twentyone_coeff_ne_zero.2 h

/-- Named forward residual `X^21` divisibility, recovered from the
no-low-degree-counterexample form. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchResidual_from_not_exists
    (h : ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchResidual.coeff k ≠ 0) :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchResidual :=
  X_pow_twentyone_dvd_rrcf_r_matchResidual_iff_not_exists_lt_twentyone_coeff_ne_zero.2 h

/-- Named reverse residual `X^21` divisibility, recovered from the
no-low-degree-counterexample form. -/
theorem X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_from_not_exists
    (h : ¬ ∃ k : ℕ, k < 21 ∧ rrcf_r_matchReverseResidual.coeff k ≠ 0) :
    (X ^ 21 : ℚ⟦X⟧) ∣ rrcf_r_matchReverseResidual :=
  X_pow_twentyone_dvd_rrcf_r_matchReverseResidual_iff_not_exists_lt_twentyone_coeff_ne_zero.2 h

/-- Extract raw forward-difference coefficient vanishing below degree `21`
from `X^21` divisibility. -/
theorem coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_X_pow_twentyone_dvd
    {k : ℕ} (h : (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r - rrcf_r_via_CF))
    (hk : k < 21) :
    (rrcf_r - rrcf_r_via_CF).coeff k = 0 :=
  (PowerSeries.X_pow_dvd_iff.1 h) k hk

/-- Extract raw reverse-difference coefficient vanishing below degree `21`
from `X^21` divisibility. -/
theorem coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_X_pow_twentyone_dvd
    {k : ℕ} (h : (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r_via_CF - rrcf_r))
    (hk : k < 21) :
    (rrcf_r_via_CF - rrcf_r).coeff k = 0 :=
  (PowerSeries.X_pow_dvd_iff.1 h) k hk

/-- Raw forward zero truncation through degree `20`, recovered from raw
`X^21` divisibility. -/
theorem trunc_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_X_pow_twentyone_dvd
    (h : (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r - rrcf_r_via_CF)) :
    PowerSeries.trunc 21 (rrcf_r - rrcf_r_via_CF) = 0 :=
  trunc_rrcf_r_sub_rrcf_r_via_CF_eq_zero_iff_X_pow_twentyone_dvd.2 h

/-- Raw reverse zero truncation through degree `20`, recovered from raw
`X^21` divisibility. -/
theorem trunc_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_X_pow_twentyone_dvd
    (h : (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r_via_CF - rrcf_r)) :
    PowerSeries.trunc 21 (rrcf_r_via_CF - rrcf_r) = 0 :=
  trunc_rrcf_r_via_CF_sub_rrcf_r_eq_zero_iff_X_pow_twentyone_dvd.2 h

/-- Raw forward `X^21` divisibility, recovered from zero truncation through
degree `20`. -/
theorem X_pow_twentyone_dvd_rrcf_r_sub_rrcf_r_via_CF_of_trunc_eq_zero
    (h : PowerSeries.trunc 21 (rrcf_r - rrcf_r_via_CF) = 0) :
    (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r - rrcf_r_via_CF) :=
  trunc_rrcf_r_sub_rrcf_r_via_CF_eq_zero_iff_X_pow_twentyone_dvd.1 h

/-- Raw reverse `X^21` divisibility, recovered from zero truncation through
degree `20`. -/
theorem X_pow_twentyone_dvd_rrcf_r_via_CF_sub_rrcf_r_of_trunc_eq_zero
    (h : PowerSeries.trunc 21 (rrcf_r_via_CF - rrcf_r) = 0) :
    (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r_via_CF - rrcf_r) :=
  trunc_rrcf_r_via_CF_sub_rrcf_r_eq_zero_iff_X_pow_twentyone_dvd.1 h

/-- Raw forward `X^21` divisibility gives coefficient agreement below degree
`21`. -/
theorem coeff_rrcf_r_eq_rrcf_r_via_CF_of_X_pow_twentyone_dvd_raw
    {k : ℕ} (h : (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r - rrcf_r_via_CF))
    (hk : k < 21) :
    rrcf_r.coeff k = rrcf_r_via_CF.coeff k := by
  have hzero :=
    coeff_rrcf_r_sub_rrcf_r_via_CF_eq_zero_of_X_pow_twentyone_dvd h hk
  have hsub : rrcf_r.coeff k - rrcf_r_via_CF.coeff k = 0 := by
    simpa [map_sub] using hzero
  exact sub_eq_zero.1 hsub

/-- Raw reverse `X^21` divisibility gives reverse coefficient agreement below
degree `21`. -/
theorem coeff_rrcf_r_via_CF_eq_rrcf_r_of_X_pow_twentyone_dvd_raw
    {k : ℕ} (h : (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r_via_CF - rrcf_r))
    (hk : k < 21) :
    rrcf_r_via_CF.coeff k = rrcf_r.coeff k := by
  have hzero :=
    coeff_rrcf_r_via_CF_sub_rrcf_r_eq_zero_of_X_pow_twentyone_dvd h hk
  have hsub : rrcf_r_via_CF.coeff k - rrcf_r.coeff k = 0 := by
    simpa [map_sub] using hzero
  exact sub_eq_zero.1 hsub

/-- Raw forward `X^21` divisibility gives truncated equality through degree
`20`. -/
theorem trunc_rrcf_r_eq_rrcf_r_via_CF_of_X_pow_twentyone_dvd_raw
  (h : (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r - rrcf_r_via_CF)) :
    PowerSeries.trunc 21 rrcf_r = PowerSeries.trunc 21 rrcf_r_via_CF :=
  (trunc_rrcf_r_eq_rrcf_r_via_CF_iff_coeff_eq 21).2
    (fun _ hk => coeff_rrcf_r_eq_rrcf_r_via_CF_of_X_pow_twentyone_dvd_raw h hk)

/-- Raw reverse `X^21` divisibility gives reverse truncated equality through
degree `20`. -/
theorem trunc_rrcf_r_via_CF_eq_rrcf_r_of_X_pow_twentyone_dvd_raw
  (h : (X ^ 21 : ℚ⟦X⟧) ∣ (rrcf_r_via_CF - rrcf_r)) :
    PowerSeries.trunc 21 rrcf_r_via_CF = PowerSeries.trunc 21 rrcf_r :=
  (trunc_rrcf_r_via_CF_eq_rrcf_r_iff_coeff_eq 21).2
    (fun _ hk => coeff_rrcf_r_via_CF_eq_rrcf_r_of_X_pow_twentyone_dvd_raw h hk)

/-! ## The main theorem (OPEN)

The full `rrcf_r_via_CF = rrcf_r` (Chan §11 Theorem 11.1) requires the
Rogers-Ramanujan identity as a formal power series identity, connecting
the analytic series `∑ X^{n²}/(X;X)_n` to `1/pentagonal023SeriesPS`.

The repo has:
- Ch07: `rrJInf` (analytic series) + functional equation
- Ch09: `BaileyTransform_preserves_pair_unconditional` (finite Bailey lemma)
- Ch19: formal Euler pentagonal + tprod infrastructure

Assembly path: Bailey pair → finite RR identity → formal-PS limit →
`rrcf_r = H(q)/G(q)` → CF convergence via functional equation → QED.
-/

end Ch11Thm111
end Pending
end QseriesFormalization
