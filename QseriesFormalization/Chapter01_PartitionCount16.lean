import QseriesFormalization.Chapter01_PartitionCount15

/-!
# Chapter 1 — `partitionCount 16 = 231` via the Euler-pentagonal recurrence

  p(16) = p(15) + p(14) − p(11) − p(9) + p(4) + p(1)
        = 176 + 135 − 56 − 30 + 5 + 1 = 231.

σ(16) = 0 (16 is not pentagonal).
-/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_16 :
    QseriesFormalization.PartI.Ch05.pentagonalSign 13 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 14 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 15 = -1 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 16 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem partitionCount_sixteen : partitionCount 16 = 231 := by
  have h_id : partitionGenFun ℤ * qPochInfPS ℤ = 1 :=
    partitionGenFun_mul_qPochInfPS ℤ
  have h16 : (partitionGenFun ℤ * qPochInfPS ℤ).coeff 16 = 0 := by
    rw [h_id]; simp
  rw [PowerSeries.coeff_mul] at h16
  have h_pg : ∀ k, (partitionGenFun ℤ).coeff k = (partitionCount k : ℤ) :=
    coeff_partitionGenFun
  have h_qp : ∀ m, (qPochInfPS ℤ).coeff m =
      QseriesFormalization.PartI.Ch05.pentagonalSign m :=
    fun m => coeff_qPochInfPS_int_eq_pentagonalSign m
  simp only [h_pg, h_qp] at h16
  rw [show (Finset.antidiagonal 16 :
      Finset (ℕ × ℕ)) =
        {(0, 16), (1, 15), (2, 14), (3, 13), (4, 12), (5, 11), (6, 10),
         (7, 9), (8, 8), (9, 7), (10, 6), (11, 5), (12, 4), (13, 3),
         (14, 2), (15, 1), (16, 0)} from by decide] at h16
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at h16
  simp only [Prod.fst, Prod.snd] at h16
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15, s16⟩ := pentagonalSign_at_13_to_16
  rw [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0,
      partitionCount_zero, partitionCount_one, partitionCount_two,
      partitionCount_three, partitionCount_four, partitionCount_five,
      partitionCount_six, partitionCount_seven, partitionCount_eight,
      partitionCount_nine, partitionCount_ten, partitionCount_eleven,
      partitionCount_twelve, partitionCount_thirteen,
      partitionCount_fourteen, partitionCount_fifteen] at h16
  ring_nf at h16
  have h_int : (partitionCount 16 : ℤ) = 231 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
