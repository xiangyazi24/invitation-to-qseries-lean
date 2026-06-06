import QseriesFormalization.Chapter01_PartitionCount14

/-!
# Chapter 1 — `partitionCount 15 = 176` via the Euler-pentagonal recurrence

15 is a pentagonal number (15 = 3·(3·3 + 1)/2), so σ(15) = (-1)^3 = -1.
The recurrence at n = 15:

  p(15) = p(14) + p(13) − p(10) − p(8) + p(3) + p(0)
        = 135 + 101 − 42 − 22 + 3 + 1 = 176.
-/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_15 :
    QseriesFormalization.PartI.Ch05.pentagonalSign 13 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 14 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 15 = -1 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **Chan §1: `p(15) = 176`**.  Note σ(15) = -1, so `p(0) · σ(15)` enters
the recurrence non-trivially. -/
theorem partitionCount_fifteen : partitionCount 15 = 176 := by
  have h_id : partitionGenFun ℤ * qPochInfPS ℤ = 1 :=
    partitionGenFun_mul_qPochInfPS ℤ
  have h15 : (partitionGenFun ℤ * qPochInfPS ℤ).coeff 15 = 0 := by
    rw [h_id]; simp
  rw [PowerSeries.coeff_mul] at h15
  have h_pg : ∀ k, (partitionGenFun ℤ).coeff k = (partitionCount k : ℤ) :=
    coeff_partitionGenFun
  have h_qp : ∀ m, (qPochInfPS ℤ).coeff m =
      QseriesFormalization.PartI.Ch05.pentagonalSign m :=
    fun m => coeff_qPochInfPS_int_eq_pentagonalSign m
  simp only [h_pg, h_qp] at h15
  rw [show (Finset.antidiagonal 15 :
      Finset (ℕ × ℕ)) =
        {(0, 15), (1, 14), (2, 13), (3, 12), (4, 11), (5, 10), (6, 9),
         (7, 8), (8, 7), (9, 6), (10, 5), (11, 4), (12, 3), (13, 2),
         (14, 1), (15, 0)} from by decide] at h15
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton] at h15
  simp only [Prod.fst, Prod.snd] at h15
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15⟩ := pentagonalSign_at_13_to_15
  rw [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0,
      partitionCount_zero, partitionCount_one, partitionCount_two,
      partitionCount_three, partitionCount_four, partitionCount_five,
      partitionCount_six, partitionCount_seven, partitionCount_eight,
      partitionCount_nine, partitionCount_ten, partitionCount_eleven,
      partitionCount_twelve, partitionCount_thirteen,
      partitionCount_fourteen] at h15
  ring_nf at h15
  have h_int : (partitionCount 15 : ℤ) = 176 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
