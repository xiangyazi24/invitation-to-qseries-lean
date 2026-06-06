import QseriesFormalization.Chapter01_PartitionCount13

/-!
# Chapter 1 — `partitionCount 14 = 135` via the Euler-pentagonal recurrence

p(14) = p(13) + p(12) − p(9) − p(7) + p(2)
      = 101 + 77 − 30 − 15 + 2 = 135.

Pentagonal signs at 14 are zero (14 ∉ pentagonal-number set near 14).
-/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_14 :
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 13 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 14 = 0 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **Chan §1: `p(14) = 135`**. -/
theorem partitionCount_fourteen : partitionCount 14 = 135 := by
  have h_id : partitionGenFun ℤ * qPochInfPS ℤ = 1 :=
    partitionGenFun_mul_qPochInfPS ℤ
  have h14 : (partitionGenFun ℤ * qPochInfPS ℤ).coeff 14 = 0 := by
    rw [h_id]; simp
  rw [PowerSeries.coeff_mul] at h14
  have h_pg : ∀ k, (partitionGenFun ℤ).coeff k = (partitionCount k : ℤ) :=
    coeff_partitionGenFun
  have h_qp : ∀ m, (qPochInfPS ℤ).coeff m =
      QseriesFormalization.PartI.Ch04Franklin.pentagonalSign m :=
    fun m => coeff_qPochInfPS_int_eq_pentagonalSign m
  simp only [h_pg, h_qp] at h14
  rw [show (Finset.antidiagonal 14 :
      Finset (ℕ × ℕ)) =
        {(0, 14), (1, 13), (2, 12), (3, 11), (4, 10), (5, 9), (6, 8),
         (7, 7), (8, 6), (9, 5), (10, 4), (11, 3), (12, 2), (13, 1), (14, 0)}
        from by decide] at h14
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at h14
  simp only [Prod.fst, Prod.snd] at h14
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14⟩ := pentagonalSign_at_13_14
  rw [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0,
      partitionCount_zero, partitionCount_one, partitionCount_two,
      partitionCount_three, partitionCount_four, partitionCount_five,
      partitionCount_six, partitionCount_seven, partitionCount_eight,
      partitionCount_nine, partitionCount_ten, partitionCount_eleven,
      partitionCount_twelve, partitionCount_thirteen] at h14
  ring_nf at h14
  have h_int : (partitionCount 14 : ℤ) = 135 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
