import QseriesFormalization.Chapter01_PartitionCount42

/-! # Chapter 1 — `partitionCount 43 = 63261` -/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_43 :
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
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 43 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

theorem partitionCount_fortythree : partitionCount 43 = 63261 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 43) (by omega)
  rw [show (Finset.antidiagonal 43 :
      Finset (ℕ × ℕ)) =
        {(0, 43), (1, 42), (2, 41), (3, 40), (4, 39), (5, 38), (6, 37),
         (7, 36), (8, 35), (9, 34), (10, 33), (11, 32), (12, 31), (13, 30),
         (14, 29), (15, 28), (16, 27), (17, 26), (18, 25), (19, 24), (20, 23),
         (21, 22), (22, 21), (23, 20), (24, 19), (25, 18), (26, 17), (27, 16),
         (28, 15), (29, 14), (30, 13), (31, 12), (32, 11), (33, 10), (34, 9),
         (35, 8), (36, 7), (37, 6), (38, 5), (39, 4), (40, 3), (41, 2),
         (42, 1), (43, 0)} from by decide] at h
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
      Finset.sum_insert (by decide),
      Finset.sum_singleton] at h
  simp only [Prod.fst, Prod.snd] at h
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26,
          s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39,
          s40, s41, s42, s43⟩ := pentagonalSign_at_13_to_43
  rw [s43, s42, s41, s40, s39, s38, s37, s36, s35, s34, s33, s32, s31, s30,
      s29, s28, s27, s26, s25, s24, s23, s22, s21, s20, s19, s18, s17, s16,
      s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0,
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
      partitionCount_fortytwo] at h
  ring_nf at h
  have h_int : (partitionCount 43 : ℤ) = 63261 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
