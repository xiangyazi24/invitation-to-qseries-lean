import QseriesFormalization.Chapter01_PartitionCount12

/-!
# Chapter 1 — `partitionCount 13 = 101` via the Euler-pentagonal recurrence

Same approach as `Chapter01_PartitionCount12.lean`: extract the
coefficient at `n = 13` from the formal-PS identity
`partitionGenFun ℤ * qPochInfPS ℤ = 1`.

Pentagonal signs at `0..13`: non-zero at `m ∈ {0, 1, 2, 5, 7, 12}`,
with signs `+1, -1, -1, +1, +1, -1`.  The recurrence at `n = 13` is

  p(13) − p(12) − p(11) + p(8) + p(6) − p(1) = 0,

so `p(13) = 77 + 56 − 22 − 11 + 1 = 101`.
-/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

/-- Pentagonal sign at index 13.  All m < 13 already covered by
`Chapter01_PartitionCount12.pentagonalSign_values`. -/
private theorem pentagonalSign_at_13 :
    QseriesFormalization.PartI.Ch05.pentagonalSign 13 = 0 := by
  decide

/-- **Chan §1: `p(13) = 101`**. -/
theorem partitionCount_thirteen : partitionCount 13 = 101 := by
  have h_id : partitionGenFun ℤ * qPochInfPS ℤ = 1 :=
    partitionGenFun_mul_qPochInfPS ℤ
  have h13 : (partitionGenFun ℤ * qPochInfPS ℤ).coeff 13 = 0 := by
    rw [h_id]; simp
  rw [PowerSeries.coeff_mul] at h13
  have h_pg : ∀ k, (partitionGenFun ℤ).coeff k = (partitionCount k : ℤ) :=
    coeff_partitionGenFun
  have h_qp : ∀ m, (qPochInfPS ℤ).coeff m =
      QseriesFormalization.PartI.Ch05.pentagonalSign m :=
    fun m => coeff_qPochInfPS_int_eq_pentagonalSign m
  simp only [h_pg, h_qp] at h13
  rw [show (Finset.antidiagonal 13 :
      Finset (ℕ × ℕ)) =
        {(0, 13), (1, 12), (2, 11), (3, 10), (4, 9), (5, 8), (6, 7),
         (7, 6), (8, 5), (9, 4), (10, 3), (11, 2), (12, 1), (13, 0)} from by
        decide] at h13
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton] at h13
  simp only [Prod.fst, Prod.snd] at h13
  -- Substitute all 14 pentagonal signs and 13 partition counts.
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  have s13 := pentagonalSign_at_13
  rw [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0,
      partitionCount_zero, partitionCount_one, partitionCount_two,
      partitionCount_three, partitionCount_four, partitionCount_five,
      partitionCount_six, partitionCount_seven, partitionCount_eight,
      partitionCount_nine, partitionCount_ten, partitionCount_eleven,
      partitionCount_twelve] at h13
  ring_nf at h13
  have h_int : (partitionCount 13 : ℤ) = 101 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
