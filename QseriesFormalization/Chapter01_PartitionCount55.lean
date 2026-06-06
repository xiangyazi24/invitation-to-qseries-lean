import QseriesFormalization.Chapter01_PartitionCount54
import QseriesFormalization.Chapter01_PentagonalSignBundle

set_option maxRecDepth 2048

/-! # Chapter 1 — `partitionCount 55 = 451276` -/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

theorem partitionCount_fiftyfive : partitionCount 55 = 451276 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 55) (by omega)
  rw [show (Finset.antidiagonal 55 :
      Finset (ℕ × ℕ)) =
        {(0, 55), (1, 54), (2, 53), (3, 52), (4, 51), (5, 50), (6, 49),
         (7, 48), (8, 47), (9, 46), (10, 45), (11, 44), (12, 43), (13, 42),
         (14, 41), (15, 40), (16, 39), (17, 38), (18, 37), (19, 36), (20, 35),
         (21, 34), (22, 33), (23, 32), (24, 31), (25, 30), (26, 29), (27, 28),
         (28, 27), (29, 26), (30, 25), (31, 24), (32, 23), (33, 22), (34, 21),
         (35, 20), (36, 19), (37, 18), (38, 17), (39, 16), (40, 15), (41, 14),
         (42, 13), (43, 12), (44, 11), (45, 10), (46, 9), (47, 8), (48, 7),
         (49, 6), (50, 5), (51, 4), (52, 3), (53, 2), (54, 1), (55, 0)}
        from by decide] at h
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
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide),
      Finset.sum_singleton] at h
  simp only [Prod.fst, Prod.snd] at h
  rw [pentagonalSign_at_55, pentagonalSign_at_54, pentagonalSign_at_53,
      pentagonalSign_at_52, pentagonalSign_at_51, pentagonalSign_at_50,
      pentagonalSign_at_49, pentagonalSign_at_48, pentagonalSign_at_47,
      pentagonalSign_at_46, pentagonalSign_at_45, pentagonalSign_at_44,
      pentagonalSign_at_43, pentagonalSign_at_42, pentagonalSign_at_41,
      pentagonalSign_at_40, pentagonalSign_at_39, pentagonalSign_at_38,
      pentagonalSign_at_37, pentagonalSign_at_36, pentagonalSign_at_35,
      pentagonalSign_at_34, pentagonalSign_at_33, pentagonalSign_at_32,
      pentagonalSign_at_31, pentagonalSign_at_30, pentagonalSign_at_29,
      pentagonalSign_at_28, pentagonalSign_at_27, pentagonalSign_at_26,
      pentagonalSign_at_25, pentagonalSign_at_24, pentagonalSign_at_23,
      pentagonalSign_at_22, pentagonalSign_at_21, pentagonalSign_at_20,
      pentagonalSign_at_19, pentagonalSign_at_18, pentagonalSign_at_17,
      pentagonalSign_at_16, pentagonalSign_at_15, pentagonalSign_at_14,
      pentagonalSign_at_13, pentagonalSign_at_12, pentagonalSign_at_11,
      pentagonalSign_at_10, pentagonalSign_at_9, pentagonalSign_at_8,
      pentagonalSign_at_7, pentagonalSign_at_6, pentagonalSign_at_5,
      pentagonalSign_at_4, pentagonalSign_at_3, pentagonalSign_at_2,
      pentagonalSign_at_1, pentagonalSign_at_0,
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
      partitionCount_fortyeight, partitionCount_fortynine,
      partitionCount_fifty, partitionCount_fiftyone,
      partitionCount_fiftytwo, partitionCount_fiftythree,
      partitionCount_fiftyfour] at h
  ring_nf at h
  have h_int : (partitionCount 55 : ℤ) = 451276 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
