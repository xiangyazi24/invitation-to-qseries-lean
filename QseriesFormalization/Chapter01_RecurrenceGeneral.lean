import QseriesFormalization.Chapter01_GenFun
import QseriesFormalization.Chapter05_Franklin

/-!
# Chapter 1 — Euler-pentagonal recurrence for `partitionCount`, general form

A single general lemma capturing the recurrence

  partitionCount n  =  − ∑_{k = 0}^{n − 1} partitionCount k · pentagonalSign (n − k)
                       (for `n ≥ 1`, integer form)

extracted from `(partitionGenFun ℤ) · (qPochInfPS ℤ) = 1` at coefficient
`n`.  Equivalently, the coefficient identity

  ∑_{k = 0}^{n} partitionCount k · pentagonalSign (n − k)  =  0   (n ≥ 1)

(which simply moves `partitionCount n · pentagonalSign 0 = partitionCount n`
to the other side; `pentagonalSign 0 = 1`).

This lets downstream code obtain any `partitionCount N` via a few `decide`s
on `pentagonalSign m` for `m ≤ N`, plus the previously-verified
`partitionCount` values, without rewriting the convolution-sum unfolding
each time.
-/

namespace QseriesFormalization
namespace Ch01

open QseriesFormalization.PartIV.Ch19

/-- **Convolution-sum form** of the Euler-pentagonal recurrence over ℤ.

For every `n : ℕ`,

  ∑_{(i, j) ∈ antidiagonal n} (partitionCount i : ℤ) · pentagonalSign j

equals `(1 : ℤ⟦X⟧).coeff n`.

Concretely:
  • `n = 0`: the sum is `partitionCount 0 · pentagonalSign 0 = 1 · 1 = 1`,
            matching `(1 : ℤ⟦X⟧).coeff 0 = 1`.
  • `n ≥ 1`: the sum equals `0`, giving the recurrence above. -/
theorem partitionCount_pentagonalSign_convolution_pos {n : ℕ} (hn : 1 ≤ n) :
    ∑ ij ∈ Finset.antidiagonal n,
      (partitionCount ij.1 : ℤ) * QseriesFormalization.PartI.Ch05.pentagonalSign ij.2
      = 0 := by
  have h_id : partitionGenFun ℤ * qPochInfPS ℤ = 1 :=
    partitionGenFun_mul_qPochInfPS ℤ
  have h_pg : ∀ k, (partitionGenFun ℤ).coeff k = (partitionCount k : ℤ) :=
    coeff_partitionGenFun
  have h_qp : ∀ m, (qPochInfPS ℤ).coeff m =
      QseriesFormalization.PartI.Ch05.pentagonalSign m :=
    fun m => coeff_qPochInfPS_int_eq_pentagonalSign m
  have hmul : (partitionGenFun ℤ * qPochInfPS ℤ).coeff n = 0 := by
    rw [h_id]
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn) with ⟨m, rfl⟩
    simp
  rw [PowerSeries.coeff_mul] at hmul
  simp only [h_pg, h_qp] at hmul
  exact hmul

end Ch01
end QseriesFormalization
