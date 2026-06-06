import QseriesFormalization.Chapter01_PartitionCount37

/-! # Chapter 1 — `partitionCount 38 = 26015` -/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_38 :
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
    QseriesFormalization.PartI.Ch05.pentagonalSign 31 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 32 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 33 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 34 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 35 = -1 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 36 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 37 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 38 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem partitionCount_thirtyeight : partitionCount 38 = 26015 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 38) (by omega)
  rw [show (Finset.antidiagonal 38 :
      Finset (ℕ × ℕ)) =
        {(0, 38), (1, 37), (2, 36), (3, 35), (4, 34), (5, 33), (6, 32),
         (7, 31), (8, 30), (9, 29), (10, 28), (11, 27), (12, 26), (13, 25),
         (14, 24), (15, 23), (16, 22), (17, 21), (18, 20), (19, 19), (20, 18),
         (21, 17), (22, 16), (23, 15), (24, 14), (25, 13), (26, 12), (27, 11),
         (28, 10), (29, 9), (30, 8), (31, 7), (32, 6), (33, 5), (34, 4),
         (35, 3), (36, 2), (37, 1), (38, 0)} from by decide] at h
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
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at h
  simp only [Prod.fst, Prod.snd] at h
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26,
          s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38⟩ :=
    pentagonalSign_at_13_to_38
  rw [s38, s37, s36, s35, s34, s33, s32, s31, s30, s29, s28, s27, s26, s25,
      s24, s23, s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11,
      s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0,
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
      partitionCount_thirty, partitionCount_thirtyone,
      partitionCount_thirtytwo, partitionCount_thirtythree,
      partitionCount_thirtyfour, partitionCount_thirtyfive,
      partitionCount_thirtysix, partitionCount_thirtyseven] at h
  ring_nf at h
  have h_int : (partitionCount 38 : ℤ) = 26015 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
