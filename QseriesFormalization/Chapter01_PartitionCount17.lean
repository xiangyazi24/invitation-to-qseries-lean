import QseriesFormalization.Chapter01_PartitionCount16

/-! # Chapter 1 — `partitionCount 17 = 297` -/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_17 :
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 13 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 14 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 15 = -1 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 16 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 17 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem partitionCount_seventeen : partitionCount 17 = 297 := by
  have h_id : partitionGenFun ℤ * qPochInfPS ℤ = 1 :=
    partitionGenFun_mul_qPochInfPS ℤ
  have h17 : (partitionGenFun ℤ * qPochInfPS ℤ).coeff 17 = 0 := by
    rw [h_id]; simp
  rw [PowerSeries.coeff_mul] at h17
  have h_pg : ∀ k, (partitionGenFun ℤ).coeff k = (partitionCount k : ℤ) :=
    coeff_partitionGenFun
  have h_qp : ∀ m, (qPochInfPS ℤ).coeff m =
      QseriesFormalization.PartI.Ch04Franklin.pentagonalSign m :=
    fun m => coeff_qPochInfPS_int_eq_pentagonalSign m
  simp only [h_pg, h_qp] at h17
  rw [show (Finset.antidiagonal 17 :
      Finset (ℕ × ℕ)) =
        {(0, 17), (1, 16), (2, 15), (3, 14), (4, 13), (5, 12), (6, 11),
         (7, 10), (8, 9), (9, 8), (10, 7), (11, 6), (12, 5), (13, 4),
         (14, 3), (15, 2), (16, 1), (17, 0)} from by decide] at h17
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton] at h17
  simp only [Prod.fst, Prod.snd] at h17
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15, s16, s17⟩ := pentagonalSign_at_13_to_17
  rw [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0,
      partitionCount_zero, partitionCount_one, partitionCount_two,
      partitionCount_three, partitionCount_four, partitionCount_five,
      partitionCount_six, partitionCount_seven, partitionCount_eight,
      partitionCount_nine, partitionCount_ten, partitionCount_eleven,
      partitionCount_twelve, partitionCount_thirteen,
      partitionCount_fourteen, partitionCount_fifteen,
      partitionCount_sixteen] at h17
  ring_nf at h17
  have h_int : (partitionCount 17 : ℤ) = 297 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
