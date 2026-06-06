import QseriesFormalization.Chapter01_PartitionCount53

set_option maxRecDepth 2048

/-!
# Chapter 1 — `partitionCount 54 = 386155`

p(54) is the unique partition count that enables **two** new Ramanujan
congruence cases simultaneously:
  - `5 ∣ p(54)` at n = 10  (since 5·10 + 4 = 54)
  - `7 ∣ p(54)` at n = 7   (since 7·7 + 5 = 54)

Verified: 386155 = 77231·5 = 55165·7.
-/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_54 :
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
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 46 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 47 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 48 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 49 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 50 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 51 = 1 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 52 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 53 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 54 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem partitionCount_fiftyfour : partitionCount 54 = 386155 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 54) (by omega)
  rw [show (Finset.antidiagonal 54 :
      Finset (ℕ × ℕ)) =
        {(0, 54), (1, 53), (2, 52), (3, 51), (4, 50), (5, 49), (6, 48),
         (7, 47), (8, 46), (9, 45), (10, 44), (11, 43), (12, 42), (13, 41),
         (14, 40), (15, 39), (16, 38), (17, 37), (18, 36), (19, 35), (20, 34),
         (21, 33), (22, 32), (23, 31), (24, 30), (25, 29), (26, 28), (27, 27),
         (28, 26), (29, 25), (30, 24), (31, 23), (32, 22), (33, 21), (34, 20),
         (35, 19), (36, 18), (37, 17), (38, 16), (39, 15), (40, 14), (41, 13),
         (42, 12), (43, 11), (44, 10), (45, 9), (46, 8), (47, 7), (48, 6),
         (49, 5), (50, 4), (51, 3), (52, 2), (53, 1), (54, 0)}
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
      Finset.sum_singleton] at h
  simp only [Prod.fst, Prod.snd] at h
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26,
          s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39,
          s40, s41, s42, s43, s44, s45, s46, s47, s48, s49, s50, s51, s52,
          s53, s54⟩ := pentagonalSign_at_13_to_54
  rw [s54, s53, s52, s51, s50, s49, s48, s47, s46, s45, s44, s43, s42, s41,
      s40, s39, s38, s37, s36, s35, s34, s33, s32, s31, s30, s29, s28, s27,
      s26, s25, s24, s23, s22, s21, s20, s19, s18, s17, s16, s15, s14, s13,
      s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0,
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
      partitionCount_fiftytwo, partitionCount_fiftythree] at h
  ring_nf at h
  have h_int : (partitionCount 54 : ℤ) = 386155 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
