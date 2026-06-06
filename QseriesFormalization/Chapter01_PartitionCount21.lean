import QseriesFormalization.Chapter01_PartitionCount20

/-! # Chapter 1 — `partitionCount 21 = 792` -/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_21 :
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 13 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 14 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 15 = -1 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 16 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 17 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 18 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 19 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 20 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 21 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem partitionCount_twentyone : partitionCount 21 = 792 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 21) (by omega)
  rw [show (Finset.antidiagonal 21 :
      Finset (ℕ × ℕ)) =
        {(0, 21), (1, 20), (2, 19), (3, 18), (4, 17), (5, 16), (6, 15),
         (7, 14), (8, 13), (9, 12), (10, 11), (11, 10), (12, 9), (13, 8),
         (14, 7), (15, 6), (16, 5), (17, 4), (18, 3), (19, 2), (20, 1),
         (21, 0)} from by decide] at h
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton] at h
  simp only [Prod.fst, Prod.snd] at h
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15, s16, s17, s18, s19, s20, s21⟩ :=
    pentagonalSign_at_13_to_21
  rw [s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8,
      s7, s6, s5, s4, s3, s2, s1, s0,
      partitionCount_zero, partitionCount_one, partitionCount_two,
      partitionCount_three, partitionCount_four, partitionCount_five,
      partitionCount_six, partitionCount_seven, partitionCount_eight,
      partitionCount_nine, partitionCount_ten, partitionCount_eleven,
      partitionCount_twelve, partitionCount_thirteen,
      partitionCount_fourteen, partitionCount_fifteen,
      partitionCount_sixteen, partitionCount_seventeen,
      partitionCount_eighteen, partitionCount_nineteen,
      partitionCount_twenty] at h
  ring_nf at h
  have h_int : (partitionCount 21 : ℤ) = 792 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
