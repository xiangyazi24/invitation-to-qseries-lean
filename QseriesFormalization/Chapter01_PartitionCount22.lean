import QseriesFormalization.Chapter01_PartitionCount21

/-!
# Chapter 1 — `partitionCount 22 = 1002`

22 is the next pentagonal number after 15: `22 = 4·(3·4 − 1)/2`, so
`σ(22) = (−1)^4 = +1`.  The recurrence at `n = 22`:

  p(22) = p(21) + p(20) − p(17) − p(15) + p(10) + p(7) − p(0)·σ(22)
        = 792 + 627 − 297 − 176 + 42 + 15 − 1·1     (note σ(22) = +1 enters as +p(0)·1 negated)
        = 1002.
-/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

private theorem pentagonalSign_at_13_to_22 :
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 13 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 14 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 15 = -1 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 16 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 17 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 18 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 19 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 20 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 21 = 0 ∧
    QseriesFormalization.PartI.Ch04Franklin.pentagonalSign 22 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem partitionCount_twentytwo : partitionCount 22 = 1002 := by
  have h := partitionCount_pentagonalSign_convolution_pos
    (n := 22) (by omega)
  rw [show (Finset.antidiagonal 22 :
      Finset (ℕ × ℕ)) =
        {(0, 22), (1, 21), (2, 20), (3, 19), (4, 18), (5, 17), (6, 16),
         (7, 15), (8, 14), (9, 13), (10, 12), (11, 11), (12, 10), (13, 9),
         (14, 8), (15, 7), (16, 6), (17, 5), (18, 4), (19, 3), (20, 2),
         (21, 1), (22, 0)} from by decide] at h
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
      Finset.sum_singleton] at h
  simp only [Prod.fst, Prod.snd] at h
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  obtain ⟨s13, s14, s15, s16, s17, s18, s19, s20, s21, s22⟩ :=
    pentagonalSign_at_13_to_22
  rw [s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9,
      s8, s7, s6, s5, s4, s3, s2, s1, s0,
      partitionCount_zero, partitionCount_one, partitionCount_two,
      partitionCount_three, partitionCount_four, partitionCount_five,
      partitionCount_six, partitionCount_seven, partitionCount_eight,
      partitionCount_nine, partitionCount_ten, partitionCount_eleven,
      partitionCount_twelve, partitionCount_thirteen,
      partitionCount_fourteen, partitionCount_fifteen,
      partitionCount_sixteen, partitionCount_seventeen,
      partitionCount_eighteen, partitionCount_nineteen,
      partitionCount_twenty, partitionCount_twentyone] at h
  ring_nf at h
  have h_int : (partitionCount 22 : ℤ) = 1002 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
