import QseriesFormalization.Chapter01_PartitionCount45

set_option maxRecDepth 2048

/-! # Chapter 1 — `partitionCount 46 = 105558` -/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_46 :
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 13 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 14 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 15 = -1 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 16 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 17 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 18 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 19 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 20 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 21 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 22 = 1 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 23 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 24 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 25 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 26 = 1 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 27 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 28 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 29 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 30 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 31 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 32 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 33 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 34 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 35 = -1 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 36 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 37 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 38 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 39 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 40 = -1 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 41 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 42 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 43 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 44 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 45 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 46 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩ <;> decide

theorem partitionCount_fortysix : partitionCount 46 = 105558 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 46) (by omega)
  rw [show (Finset.antidiagonal 46 :
      Finset (ℕ × ℕ)) =
        {(0, 46), (1, 45), (2, 44), (3, 43), (4, 42), (5, 41), (6, 40),
         (7, 39), (8, 38), (9, 37), (10, 36), (11, 35), (12, 34), (13, 33),
         (14, 32), (15, 31), (16, 30), (17, 29), (18, 28), (19, 27), (20, 26),
         (21, 25), (22, 24), (23, 23), (24, 22), (25, 21), (26, 20), (27, 19),
         (28, 18), (29, 17), (30, 16), (31, 15), (32, 14), (33, 13), (34, 12),
         (35, 11), (36, 10), (37, 9), (38, 8), (39, 7), (40, 6), (41, 5),
         (42, 4), (43, 3), (44, 2), (45, 1), (46, 0)} from by decide] at h
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
      Finset.sum_singleton] at h
  simp only [Prod.fst, Prod.snd] at h
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26,
          s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39,
          s40, s41, s42, s43, s44, s45, s46⟩ := pentagonalSign_at_13_to_46
  rw [s46, s45, s44, s43, s42, s41, s40, s39, s38, s37, s36, s35, s34, s33,
      s32, s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20, s19,
      s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4,
      s3, s2, s1, s0,
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
      partitionCount_fortyfour, partitionCount_fortyfive] at h
  ring_nf at h
  have h_int : (partitionCount 46 : ℤ) = 105558 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
