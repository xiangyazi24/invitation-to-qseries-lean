import QseriesFormalization.Chapter01_PartitionCount34

/-!
# Chapter 1 — `partitionCount 35 = 14883`

35 is the next pentagonal number after 26: `35 = 5·(3·5 − 1)/2` (k=5
minus side), so σ(35) = (−1)^5 = −1.  At n = 35 the recurrence picks up
p(0)·σ(35) = −1·1 = −1 as the new nontrivial contribution.

  p(35) = p(34) + p(33) − p(30) − p(28) + p(23) + p(20) − p(13) − p(9) + p(0)
        = 12310 + 10143 − 5604 − 3718 + 1255 + 627 − 101 − 30 + 1
        = 14883.
-/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_35 :
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
    QseriesFormalization.PartI.Ch05.pentagonalSign 35 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem partitionCount_thirtyfive : partitionCount 35 = 14883 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 35) (by omega)
  rw [show (Finset.antidiagonal 35 :
      Finset (ℕ × ℕ)) =
        {(0, 35), (1, 34), (2, 33), (3, 32), (4, 31), (5, 30), (6, 29),
         (7, 28), (8, 27), (9, 26), (10, 25), (11, 24), (12, 23), (13, 22),
         (14, 21), (15, 20), (16, 19), (17, 18), (18, 17), (19, 16), (20, 15),
         (21, 14), (22, 13), (23, 12), (24, 11), (25, 10), (26, 9), (27, 8),
         (28, 7), (29, 6), (30, 5), (31, 4), (32, 3), (33, 2), (34, 1),
         (35, 0)} from by decide] at h
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
      Finset.sum_insert (by decide),
      Finset.sum_singleton] at h
  simp only [Prod.fst, Prod.snd] at h
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26,
          s27, s28, s29, s30, s31, s32, s33, s34, s35⟩ :=
    pentagonalSign_at_13_to_35
  rw [s35, s34, s33, s32, s31, s30, s29, s28, s27, s26, s25, s24, s23, s22,
      s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7,
      s6, s5, s4, s3, s2, s1, s0,
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
      partitionCount_thirtyfour] at h
  ring_nf at h
  have h_int : (partitionCount 35 : ℤ) = 14883 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
