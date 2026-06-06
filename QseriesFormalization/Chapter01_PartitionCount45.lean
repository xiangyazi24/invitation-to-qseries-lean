import QseriesFormalization.Chapter01_PartitionCount44

set_option maxRecDepth 2048

/-! # Chapter 1 — `partitionCount 45 = 89134` -/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_45 :
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
    QseriesFormalization.PartI.Ch05.pentagonalSign 45 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_⟩ <;> decide

theorem partitionCount_fortyfive : partitionCount 45 = 89134 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 45) (by omega)
  rw [show (Finset.antidiagonal 45 :
      Finset (ℕ × ℕ)) =
        {(0, 45), (1, 44), (2, 43), (3, 42), (4, 41), (5, 40), (6, 39),
         (7, 38), (8, 37), (9, 36), (10, 35), (11, 34), (12, 33), (13, 32),
         (14, 31), (15, 30), (16, 29), (17, 28), (18, 27), (19, 26), (20, 25),
         (21, 24), (22, 23), (23, 22), (24, 21), (25, 20), (26, 19), (27, 18),
         (28, 17), (29, 16), (30, 15), (31, 14), (32, 13), (33, 12), (34, 11),
         (35, 10), (36, 9), (37, 8), (38, 7), (39, 6), (40, 5), (41, 4),
         (42, 3), (43, 2), (44, 1), (45, 0)} from by decide] at h
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
      Finset.sum_insert (by decide),
      Finset.sum_singleton] at h
  simp only [Prod.fst, Prod.snd] at h
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26,
          s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39,
          s40, s41, s42, s43, s44, s45⟩ := pentagonalSign_at_13_to_45
  rw [s45, s44, s43, s42, s41, s40, s39, s38, s37, s36, s35, s34, s33, s32,
      s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20, s19, s18,
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
      partitionCount_thirty, partitionCount_thirtyone,
      partitionCount_thirtytwo, partitionCount_thirtythree,
      partitionCount_thirtyfour, partitionCount_thirtyfive,
      partitionCount_thirtysix, partitionCount_thirtyseven,
      partitionCount_thirtyeight, partitionCount_thirtynine,
      partitionCount_forty, partitionCount_fortyone,
      partitionCount_fortytwo, partitionCount_fortythree,
      partitionCount_fortyfour] at h
  ring_nf at h
  have h_int : (partitionCount 45 : ℤ) = 89134 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
