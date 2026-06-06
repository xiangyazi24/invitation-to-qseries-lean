import QseriesFormalization.Chapter01_PartitionCount30

/-! # Chapter 1 — `partitionCount 31 = 6842` -/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_31 :
    QseriesFormalization.PartI.Ch05.pentagonalSign 13 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 14 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 15 = -1 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 16 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 17 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 18 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 19 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 20 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 21 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 22 = 1 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 23 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 24 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 25 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 26 = 1 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 27 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 28 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 29 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 30 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 31 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_⟩ <;> decide

theorem partitionCount_thirtyone : partitionCount 31 = 6842 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 31) (by omega)
  rw [show (Finset.antidiagonal 31 :
      Finset (ℕ × ℕ)) =
        {(0, 31), (1, 30), (2, 29), (3, 28), (4, 27), (5, 26), (6, 25),
         (7, 24), (8, 23), (9, 22), (10, 21), (11, 20), (12, 19), (13, 18),
         (14, 17), (15, 16), (16, 15), (17, 14), (18, 13), (19, 12), (20, 11),
         (21, 10), (22, 9), (23, 8), (24, 7), (25, 6), (26, 5), (27, 4),
         (28, 3), (29, 2), (30, 1), (31, 0)} from by decide] at h
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
  obtain ⟨s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26,
          s27, s28, s29, s30, s31⟩ := pentagonalSign_at_13_to_31
  rw [s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20, s19, s18,
      s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2,
      s1, s0,
      partitionCount_zero, partitionCount_one, partitionCount_two,
      partitionCount_three, partitionCount_four, partitionCount_five,
      partitionCount_six, partitionCount_seven, partitionCount_eight,
      partitionCount_nine, partitionCount_ten, partitionCount_eleven,
      partitionCount_twelve, partitionCount_thirteen,
      partitionCount_fourteen, partitionCount_fifteen,
      partitionCount_sixteen, partitionCount_seventeen,
      partitionCount_eighteen, partitionCount_nineteen,
      partitionCount_twenty, partitionCount_twentyone,
      partitionCount_twentytwo, partitionCount_twentythree,
      partitionCount_twentyfour, partitionCount_twentyfive,
      partitionCount_twentysix, partitionCount_twentyseven,
      partitionCount_twentyeight, partitionCount_twentynine,
      partitionCount_thirty] at h
  ring_nf at h
  have h_int : (partitionCount 31 : ℤ) = 6842 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
