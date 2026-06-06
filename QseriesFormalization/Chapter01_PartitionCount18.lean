import QseriesFormalization.Chapter01_RecurrenceGeneral
import QseriesFormalization.Chapter01_PartitionCount17

/-! # Chapter 1 — `partitionCount 18 = 385` -/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_18 :
    QseriesFormalization.PartI.Ch05.pentagonalSign 13 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 14 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 15 = -1 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 16 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 17 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 18 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem partitionCount_eighteen : partitionCount 18 = 385 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 18) (by omega)
  rw [show (Finset.antidiagonal 18 :
      Finset (ℕ × ℕ)) =
        {(0, 18), (1, 17), (2, 16), (3, 15), (4, 14), (5, 13), (6, 12),
         (7, 11), (8, 10), (9, 9), (10, 8), (11, 7), (12, 6), (13, 5),
         (14, 4), (15, 3), (16, 2), (17, 1), (18, 0)} from by decide] at h
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at h
  simp only [Prod.fst, Prod.snd] at h
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15, s16, s17, s18⟩ := pentagonalSign_at_13_to_18
  rw [s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3,
      s2, s1, s0,
      partitionCount_zero, partitionCount_one, partitionCount_two,
      partitionCount_three, partitionCount_four, partitionCount_five,
      partitionCount_six, partitionCount_seven, partitionCount_eight,
      partitionCount_nine, partitionCount_ten, partitionCount_eleven,
      partitionCount_twelve, partitionCount_thirteen,
      partitionCount_fourteen, partitionCount_fifteen,
      partitionCount_sixteen, partitionCount_seventeen] at h
  ring_nf at h
  have h_int : (partitionCount 18 : ℤ) = 385 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
