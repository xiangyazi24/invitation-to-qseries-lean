import QseriesFormalization.Chapter01_PartitionCount49

set_option maxRecDepth 2048

/-! # Chapter 1 — `partitionCount 50 = 204226` -/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_50 :
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
    QseriesFormalization.PartI.Ch05.pentagonalSign 38 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 39 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 40 = -1 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 41 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 42 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 43 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 44 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 45 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 46 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 47 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 48 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 49 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 50 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem partitionCount_fifty : partitionCount 50 = 204226 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 50) (by omega)
  rw [show (Finset.antidiagonal 50 :
      Finset (ℕ × ℕ)) =
        {(0, 50), (1, 49), (2, 48), (3, 47), (4, 46), (5, 45), (6, 44),
         (7, 43), (8, 42), (9, 41), (10, 40), (11, 39), (12, 38), (13, 37),
         (14, 36), (15, 35), (16, 34), (17, 33), (18, 32), (19, 31), (20, 30),
         (21, 29), (22, 28), (23, 27), (24, 26), (25, 25), (26, 24), (27, 23),
         (28, 22), (29, 21), (30, 20), (31, 19), (32, 18), (33, 17), (34, 16),
         (35, 15), (36, 14), (37, 13), (38, 12), (39, 11), (40, 10), (41, 9),
         (42, 8), (43, 7), (44, 6), (45, 5), (46, 4), (47, 3), (48, 2),
         (49, 1), (50, 0)} from by decide] at h
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
          s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39,
          s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50⟩ :=
    pentagonalSign_at_13_to_50
  rw [s50, s49, s48, s47, s46, s45, s44, s43, s42, s41, s40, s39, s38, s37,
      s36, s35, s34, s33, s32, s31, s30, s29, s28, s27, s26, s25, s24, s23,
      s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8,
      s7, s6, s5, s4, s3, s2, s1, s0,
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
      partitionCount_thirtysix, partitionCount_thirtyseven,
      partitionCount_thirtyeight, partitionCount_thirtynine,
      partitionCount_forty, partitionCount_fortyone,
      partitionCount_fortytwo, partitionCount_fortythree,
      partitionCount_fortyfour, partitionCount_fortyfive,
      partitionCount_fortysix, partitionCount_fortyseven,
      partitionCount_fortyeight, partitionCount_fortynine] at h
  ring_nf at h
  have h_int : (partitionCount 50 : ℤ) = 204226 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
