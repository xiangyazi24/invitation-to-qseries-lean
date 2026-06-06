import QseriesFormalization.Chapter01_GenFun
import QseriesFormalization.Chapter05_Franklin

/-!
# Chapter 1 — `partitionCount 12 = 77` via the Euler-pentagonal recurrence

Chan §1 establishes the partition counting function `p(n)`.  This file
extends the verified values `partitionCount_zero .. partitionCount_eleven`
by one step:

  p(12) = 77

The proof uses the formal-power-series identity
`partitionGenFun ℤ * qPochInfPS ℤ = 1` (proved in Chapter 19): extracting
the coefficient at `n = 12` gives the Euler-pentagonal recurrence

  p(12) − p(11) − p(10) + p(7) + p(5) − p(0) = 0

(from the non-zero `pentagonalSign` values at `m ∈ {1,2,5,7,12}`).

Substituting the known small partition counts then yields
`p(12) = 56 + 42 − 15 − 7 + 1 = 77`.
-/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

/-- Pentagonal sign values at `0..12` (small concrete computations).
Made public so downstream `Chapter01_PartitionCount{13,14,...}.lean` files
can re-use the same bundle of small `decide` checks without re-doing them. -/
theorem pentagonalSign_values :
    QseriesFormalization.PartI.Ch05.pentagonalSign 0 = 1 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 1 = -1 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 2 = -1 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 3 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 4 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 5 = 1 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 6 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 7 = 1 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 8 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 9 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 10 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 11 = 0 ∧
    QseriesFormalization.PartI.Ch05.pentagonalSign 12 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

/-- **Chan §1: `p(12) = 77`**.

This extends the explicit-value chain `partitionCount_zero ..
partitionCount_eleven` by one.  Proof via the formal-PS recurrence
`(partitionGenFun ℤ) · (qPochInfPS ℤ) = 1` at coefficient 12. -/
theorem partitionCount_twelve : partitionCount 12 = 77 := by
  -- Step 1: `(partitionGenFun ℤ) · (qPochInfPS ℤ) = 1`.
  have h_id : partitionGenFun ℤ * qPochInfPS ℤ = 1 :=
    partitionGenFun_mul_qPochInfPS ℤ
  -- Step 2: extract coefficient at 12.
  have h12 : (partitionGenFun ℤ * qPochInfPS ℤ).coeff 12 = 0 := by
    rw [h_id]; simp
  rw [PowerSeries.coeff_mul] at h12
  -- Step 3: identify each factor's coefficients.
  -- `(partitionGenFun ℤ).coeff k = (partitionCount k : ℤ)` for all k.
  -- `(qPochInfPS ℤ).coeff m = pentagonalSign m` for all m.
  have h_pg : ∀ k, (partitionGenFun ℤ).coeff k = (partitionCount k : ℤ) :=
    coeff_partitionGenFun
  have h_qp : ∀ m, (qPochInfPS ℤ).coeff m =
      QseriesFormalization.PartI.Ch05.pentagonalSign m :=
    fun m => coeff_qPochInfPS_int_eq_pentagonalSign m
  -- Step 4: simplify the convolution sum using h_pg + h_qp.
  simp only [h_pg, h_qp] at h12
  -- Step 5: rewrite the antidiagonal sum as a finite explicit sum.
  rw [show (Finset.antidiagonal 12 :
      Finset (ℕ × ℕ)) =
        {(0, 12), (1, 11), (2, 10), (3, 9), (4, 8), (5, 7), (6, 6),
         (7, 5), (8, 4), (9, 3), (10, 2), (11, 1), (12, 0)} from by decide] at h12
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at h12
  simp only [Prod.fst, Prod.snd] at h12
  -- Step 6: plug in all pentagonal signs and small partition counts.
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    pentagonalSign_values
  rw [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0,
      partitionCount_zero, partitionCount_one, partitionCount_two,
      partitionCount_three, partitionCount_four, partitionCount_five,
      partitionCount_six, partitionCount_seven, partitionCount_eight,
      partitionCount_nine, partitionCount_ten, partitionCount_eleven] at h12
  -- h12 is now a concrete linear-arithmetic equation in (partitionCount 12 : ℤ).
  -- Reduce h12 to a clean form by ring normalisation.
  ring_nf at h12
  -- Now h12 should be: ↑(partitionCount 12) - 77 = 0  (or similar).
  have h_int : (partitionCount 12 : ℤ) = 77 := by linarith
  exact_mod_cast h_int

end Ch01
end QseriesFormalization
