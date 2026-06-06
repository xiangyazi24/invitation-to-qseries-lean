import QseriesFormalization.Chapter03

/-!
# Finite JTP at `z = 1`

At `z = 1`, the finite Jacobi triple product has a zero factor
`(1; q)_n` for every `n >= 1`.  After the usual normalization by
`(q; q)_{2n}`, the product side is therefore the Kronecker delta sequence.
-/

namespace QseriesFormalization
namespace Pending
namespace RRFiniteJTPAtOne

open QseriesFormalization.PartI.Ch03

variable {R : Type*} [Field R]

/-- The zero factor in `(1; q)_n`: for every `n >= 1`, `(1; q)_n = 0`. -/
theorem qPoch_one_eq_zero (q : R) (n : Nat) (hn : 1 <= n) :
    qPoch (1 : R) q n = 0 := by
  cases n with
  | zero =>
      omega
  | succ m =>
      induction m with
      | zero =>
          simp [qPoch]
      | succ k ih =>
          rw [qPoch_succ]
          rw [ih (by omega)]
          simp

/-- Succ-indexed form of `qPoch_one_eq_zero`. -/
@[simp] theorem qPoch_one_succ_eq_zero (q : R) (n : Nat) :
    qPoch (1 : R) q (n + 1) = 0 :=
  qPoch_one_eq_zero q (n + 1) (by omega)

/--
The finite JTP product side specialized to `z = 1`.

This is the product-side identity before dividing by `(q; q)_{2n}`.
-/
theorem finite_jtp_at_one_product (q : R) (hq : q ≠ 0) (n : Nat) :
    qPoch (1 : R) q n * qPoch q q n = finiteJTPRHS q 1 n := by
  simpa using finite_jacobi_triple_product q (1 : R) one_ne_zero hq n

/-- The normalized product side which becomes the Bailey `beta*` sequence. -/
noncomputable def betaStarFromFiniteJTP (q : R) (n : Nat) : R :=
  (qPoch (1 : R) q n * qPoch q q n) / qPoch q q (2 * n)

@[simp] theorem betaStarFromFiniteJTP_zero (q : R) :
    betaStarFromFiniteJTP q 0 = 1 := by
  simp [betaStarFromFiniteJTP]

theorem betaStarFromFiniteJTP_eq_zero_of_pos (q : R) (n : Nat) (hn : 1 <= n) :
    betaStarFromFiniteJTP q n = 0 := by
  rw [betaStarFromFiniteJTP, qPoch_one_eq_zero q n hn]
  simp

/-- The finite JTP at `z = 1` gives the trivial Bailey beta sequence. -/
theorem betaStarFromFiniteJTP_eq_delta (q : R) (n : Nat) :
    betaStarFromFiniteJTP q n = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hpos : 1 <= n := by omega
    simp [hn, betaStarFromFiniteJTP_eq_zero_of_pos q n hpos]

end RRFiniteJTPAtOne
end Pending
end QseriesFormalization
