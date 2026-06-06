import QseriesFormalization.Chapter01_PartitionCount25

/-!
# Chapter 1 — `partitionCount 26 = 2436`

26 is the second pentagonal number from k=4 (the "plus side"):
`26 = 4·(3·4 + 1)/2`, so σ(26) = (−1)^4 = +1.

This is the next non-zero σ after σ(22) = +1.

  p(26) = p(25) + p(24) − p(21) − p(19) + p(14) + p(11) − p(4) − p(0)
        = 1958 + 1575 − 792 − 490 + 135 + 56 − 5 − 1 = 2436.
-/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_26 :
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
    QseriesFormalization.PartI.Ch05.pentagonalSign 26 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem partitionCount_twentysix : partitionCount 26 = 2436 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 26) (by omega)
  rw [show (Finset.antidiagonal 26 :
      Finset (ℕ × ℕ)) =
        {(0, 26), (1, 25), (2, 24), (3, 23), (4, 22), (5, 21), (6, 20),
         (7, 19), (8, 18), (9, 17), (10, 16), (11, 15), (12, 14), (13, 13),
         (14, 12), (15, 11), (16, 10), (17, 9), (18, 8), (19, 7), (20, 6),
         (21, 5), (22, 4), (23, 3), (24, 2), (25, 1), (26, 0)}
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
      Finset.sum_singleton] at h
  simp only [Prod.fst, Prod.snd] at h
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26⟩ :=
    pentagonalSign_at_13_to_26
  rw [s26, s25, s24, s23, s22, s21, s20, s19, s18, s17, s16, s15, s14, s13,
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
      partitionCount_twentyfour, partitionCount_twentyfive] at h
  ring_nf at h
  have h_int : (partitionCount 26 : ℤ) = 2436 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
