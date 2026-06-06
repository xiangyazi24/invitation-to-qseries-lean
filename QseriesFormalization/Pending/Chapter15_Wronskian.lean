import QseriesFormalization.Chapter01_PartitionCount12
import QseriesFormalization.Pending.Chapter11_Thm111
import QseriesFormalization.Pending.Chapter15_FormalDeriv

/-!
# Chapter 15 Wronskian check

This file records the obstruction in the requested Wronskian statement.

The requested handoff uses `pentagonal014SeriesPS` and `pentagonal023SeriesPS`
as if they were the Rogers-Ramanujan products without the `(q^5;q^5)_∞`
factor.  In this repository they are the Jacobi triple product series
`(q,q^4,q^5;q^5)_∞` and `(q^2,q^3,q^5;q^5)_∞`, so they already include that
factor.  With these definitions, the requested RHS has the wrong coefficient
at degree `5`.
-/

namespace QseriesFormalization
namespace Pending
namespace Ch15Wronskian

open PowerSeries
open scoped PowerSeries
open QseriesFormalization.PartIV.Ch19
open QseriesFormalization.Pending.Ch13RRCF
open QseriesFormalization.Pending.Ch11Thm111
open QseriesFormalization.Pending.Ch15FormalDeriv
open QseriesFormalization.Pending.Ch16MBIProof
open QseriesFormalization.Pending.JacobiCubeAnalyticToFormal
open QseriesFormalization.Pending.JTPFormalPSPentagonal

noncomputable abbrev P14 : ℚ⟦X⟧ := pentagonal014SeriesPS ℚ
noncomputable abbrev P23 : ℚ⟦X⟧ := pentagonal023SeriesPS ℚ
noncomputable abbrev E : ℚ⟦X⟧ := qPochInfPS ℚ
noncomputable abbrev E5 : ℚ⟦X⟧ :=
  PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (qPochInfPS ℚ)

/-- The requested pentagonal-level Wronskian left hand side. -/
noncomputable def wronskianPentagonalLHS : ℚ⟦X⟧ :=
  P14 * P23 + 5 * (P23 * thetaOp P14 - P14 * thetaOp P23)

/-- The requested RHS, using `P14` and `P23` as in the handoff. -/
noncomputable def wronskianPentagonalClaimedRHS : ℚ⟦X⟧ :=
  E ^ 4 * P14 ^ 2 * P23 ^ 2

private theorem coeff_P14_zero : pentagonal014Coeff ℚ 0 = 1 := by
  simpa using coeff_zero_pentagonal014SeriesPS_rat

private theorem coeff_P14_one : pentagonal014Coeff ℚ 1 = -1 := by
  simpa using coeff_one_pentagonal014SeriesPS_rat

private theorem coeff_P14_two : pentagonal014Coeff ℚ 2 = 0 := by
  simpa using coeff_two_pentagonal014SeriesPS_rat

private theorem coeff_P14_three : pentagonal014Coeff ℚ 3 = 0 := by
  simpa using coeff_three_pentagonal014SeriesPS_rat

private theorem coeff_P14_four : pentagonal014Coeff ℚ 4 = -1 := by
  simpa using coeff_four_pentagonal014SeriesPS_rat

private theorem coeff_P14_five : pentagonal014Coeff ℚ 5 = 0 := by
  simpa using coeff_five_pentagonal014SeriesPS_rat

private theorem coeff_P23_zero : pentagonal023Coeff ℚ 0 = 1 := by
  simpa using coeff_zero_pentagonal023SeriesPS_rat

private theorem coeff_P23_one : pentagonal023Coeff ℚ 1 = 0 := by
  simpa using coeff_one_pentagonal023SeriesPS_rat

private theorem coeff_P23_two : pentagonal023Coeff ℚ 2 = -1 := by
  simpa using coeff_two_pentagonal023SeriesPS_rat

private theorem coeff_P23_three : pentagonal023Coeff ℚ 3 = -1 := by
  simpa using coeff_three_pentagonal023SeriesPS_rat

private theorem coeff_P23_four : pentagonal023Coeff ℚ 4 = 0 := by
  simpa using coeff_four_pentagonal023SeriesPS_rat

private theorem coeff_P23_five : pentagonal023Coeff ℚ 5 = 0 := by
  simpa using coeff_five_pentagonal023SeriesPS_rat

private theorem coeff_P14_mul_P23_five : (P14 * P23).coeff 5 = 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, P14, P23]
  rw [coeff_P14_zero, coeff_P14_one, coeff_P14_two, coeff_P14_three,
    coeff_P14_four, coeff_P14_five, coeff_P23_zero, coeff_P23_one,
    coeff_P23_two, coeff_P23_three, coeff_P23_four, coeff_P23_five]
  norm_num

private theorem coeff_P23_mul_theta_P14_five : (P23 * thetaOp P14).coeff 5 = 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, P14, P23, coeff_thetaOp]
  rw [coeff_P14_one, coeff_P14_two, coeff_P14_three, coeff_P14_four,
    coeff_P14_five, coeff_P23_zero, coeff_P23_one, coeff_P23_two,
    coeff_P23_three, coeff_P23_four]
  norm_num

private theorem coeff_P14_mul_theta_P23_five : (P14 * thetaOp P23).coeff 5 = 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, P14, P23, coeff_thetaOp]
  rw [coeff_P14_one, coeff_P14_two, coeff_P14_three, coeff_P14_four,
    coeff_P23_one, coeff_P23_two, coeff_P23_three, coeff_P23_four,
    coeff_P23_five]
  norm_num

private theorem coeff_wronskian_derivative_part_five :
    (5 * (P23 * thetaOp P14 - P14 * thetaOp P23)).coeff 5 = 0 := by
  have hdiff : (P23 * thetaOp P14 - P14 * thetaOp P23).coeff 5 = 0 := by
    simp [coeff_P23_mul_theta_P14_five, coeff_P14_mul_theta_P23_five]
  rw [show (5 : ℚ⟦X⟧) = PowerSeries.C (5 : ℚ) by
    exact (map_natCast (PowerSeries.C : ℚ →+* ℚ⟦X⟧) 5).symm]
  rw [PowerSeries.coeff_C_mul, hdiff]
  norm_num

/-- The requested LHS has coefficient `0` at degree `5`. -/
theorem coeff_wronskianPentagonalLHS_five :
    wronskianPentagonalLHS.coeff 5 = 0 := by
  unfold wronskianPentagonalLHS
  simp [coeff_P14_mul_P23_five, coeff_wronskian_derivative_part_five]

private theorem jacobiTripleSign_zero : jacobiTripleSign 0 = 1 := by
  rw [show (0 : ℕ) = 0 * (0 + 1) / 2 by norm_num, jacobiTripleSign_triangular]
  norm_num

private theorem jacobiTripleSign_one : jacobiTripleSign 1 = -3 := by
  rw [show (1 : ℕ) = 1 * (1 + 1) / 2 by norm_num, jacobiTripleSign_triangular]
  norm_num

private theorem jacobiTripleSign_two : jacobiTripleSign 2 = 0 := by
  rw [jacobiTripleSign_of_not_triangular]
  intro k hk h
  interval_cases k <;> norm_num at h

private theorem jacobiTripleSign_three : jacobiTripleSign 3 = 5 := by
  rw [show (3 : ℕ) = 2 * (2 + 1) / 2 by norm_num, jacobiTripleSign_triangular]
  norm_num

private theorem jacobiTripleSign_four : jacobiTripleSign 4 = 0 := by
  rw [jacobiTripleSign_of_not_triangular]
  intro k hk h
  interval_cases k <;> norm_num at h

private theorem jacobiTripleSign_five : jacobiTripleSign 5 = 0 := by
  rw [jacobiTripleSign_of_not_triangular]
  intro k hk h
  interval_cases k <;> norm_num at h

private theorem coeff_E_pow_six_five : (E ^ 6).coeff 5 = 0 := by
  rw [E, qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two]
  rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  rw [jacobiTripleSign_zero, jacobiTripleSign_one, jacobiTripleSign_two,
    jacobiTripleSign_three, jacobiTripleSign_four, jacobiTripleSign_five]
  norm_num

private theorem coeff_qPochInfPS_zero_rat : (qPochInfPS ℚ).coeff 0 = 1 := by
  rw [coeff_qPochInfPS_eq_pentagonalSign, QseriesFormalization.Ch01.pentagonalSign_values.1]
  norm_num

private theorem coeff_qPochInfPS_one_rat : (qPochInfPS ℚ).coeff 1 = -1 := by
  rw [coeff_qPochInfPS_eq_pentagonalSign,
    QseriesFormalization.Ch01.pentagonalSign_values.2.1]
  norm_num

private theorem coeff_E5_zero : E5.coeff 0 = 1 := by
  rw [E5, PowerSeries.coeff_expand, if_pos (by norm_num : 5 ∣ 0)]
  norm_num [coeff_qPochInfPS_zero_rat]

private theorem coeff_E5_one : E5.coeff 1 = 0 := by
  rw [E5, PowerSeries.coeff_expand, if_neg (by norm_num : ¬ 5 ∣ 1)]

private theorem coeff_E5_two : E5.coeff 2 = 0 := by
  rw [E5, PowerSeries.coeff_expand, if_neg (by norm_num : ¬ 5 ∣ 2)]

private theorem coeff_E5_three : E5.coeff 3 = 0 := by
  rw [E5, PowerSeries.coeff_expand, if_neg (by norm_num : ¬ 5 ∣ 3)]

private theorem coeff_E5_four : E5.coeff 4 = 0 := by
  rw [E5, PowerSeries.coeff_expand, if_neg (by norm_num : ¬ 5 ∣ 4)]

private theorem coeff_E5_five : E5.coeff 5 = -1 := by
  rw [E5, PowerSeries.coeff_expand, if_pos (by norm_num : 5 ∣ 5)]
  norm_num [coeff_qPochInfPS_one_rat]

private theorem coeff_E5_sq_one : (E5 ^ 2).coeff 1 = 0 := by
  rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, coeff_E5_zero, coeff_E5_one]

private theorem coeff_E5_sq_two : (E5 ^ 2).coeff 2 = 0 := by
  rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, coeff_E5_zero, coeff_E5_one, coeff_E5_two]

private theorem coeff_E5_sq_three : (E5 ^ 2).coeff 3 = 0 := by
  rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, coeff_E5_zero, coeff_E5_one, coeff_E5_two,
    coeff_E5_three]

private theorem coeff_E5_sq_four : (E5 ^ 2).coeff 4 = 0 := by
  rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, coeff_E5_zero, coeff_E5_one, coeff_E5_two,
    coeff_E5_three, coeff_E5_four]

private theorem coeff_E5_sq_five : (E5 ^ 2).coeff 5 = -2 := by
  rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, coeff_E5_zero, coeff_E5_one, coeff_E5_two,
    coeff_E5_three, coeff_E5_four, coeff_E5_five]

private theorem claimed_rhs_rewrites_to_E6_E5sq :
    E ^ 4 * P14 ^ 2 * P23 ^ 2 = E ^ 6 * E5 ^ 2 := by
  change (qPochInfPS ℚ) ^ 4 * (pentagonal014SeriesPS ℚ) ^ 2 *
      (pentagonal023SeriesPS ℚ) ^ 2 =
    (qPochInfPS ℚ) ^ 6 *
      (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (qPochInfPS ℚ)) ^ 2
  calc
    (qPochInfPS ℚ) ^ 4 * (pentagonal014SeriesPS ℚ) ^ 2 *
        (pentagonal023SeriesPS ℚ) ^ 2
        = (qPochInfPS ℚ) ^ 4 *
            (pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ) ^ 2 := by
          ring
    _ = (qPochInfPS ℚ) ^ 4 *
          (qPochInfPS ℚ *
            PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (qPochInfPS ℚ)) ^ 2 := by
          rw [pentagonal014Series_mul_pentagonal023Series_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat]
    _ = (qPochInfPS ℚ) ^ 6 *
          (PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (qPochInfPS ℚ)) ^ 2 := by
          ring

/-- The requested RHS has coefficient `-2` at degree `5`. -/
theorem coeff_wronskianPentagonalClaimedRHS_five :
    wronskianPentagonalClaimedRHS.coeff 5 = -2 := by
  unfold wronskianPentagonalClaimedRHS
  rw [claimed_rhs_rewrites_to_E6_E5sq, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  rw [coeff_E5_sq_one, coeff_E5_sq_two, coeff_E5_sq_three, coeff_E5_sq_four,
    coeff_E5_sq_five, coeff_E_pow_six_five]
  rw [E, constantCoeff_qPochInfPS]
  norm_num

/-- Coefficient-level counterexample to the requested Wronskian statement. -/
theorem wronskian_pentagonal_claimed_coeff_five_ne :
    wronskianPentagonalLHS.coeff 5 ≠ wronskianPentagonalClaimedRHS.coeff 5 := by
  rw [coeff_wronskianPentagonalLHS_five, coeff_wronskianPentagonalClaimedRHS_five]
  norm_num

/-- The requested statement is false with the repository's `pentagonal014/023` definitions. -/
theorem rogers_ramanujan_wronskian_cleared_as_stated_false :
    wronskianPentagonalLHS ≠ wronskianPentagonalClaimedRHS := by
  intro h
  exact wronskian_pentagonal_claimed_coeff_five_ne (congrArg (fun f : ℚ⟦X⟧ => f.coeff 5) h)

end Ch15Wronskian
end Pending
end QseriesFormalization
