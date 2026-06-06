import QseriesFormalization.Chapter09_BaileyLemma
import QseriesFormalization.Chapter03

/-!
# Rogers-Ramanujan Bailey pair seed at `x = 1` in `ℚ⟦X⟧`

## The JTP-derived Bailey pair

From Chan §9.1, the RR proof uses the Bailey pair `(α*, β*)` defined by
setting `z = 1` in the finite JTP (Chan Eq 9.15) and "folding" the
bilateral sum to k ≥ 0:

  `β*_n = δ_{n,0}`       (since `(1;q)_n = 0` for n ≥ 1)
  `α*_0 = 1`
  `α*_k = (-1)^k q^{k(k-1)/2} (q^{k/2} + q^{-k/2})` for k ≥ 1
       = `(-1)^k q^{k(k-1)/2} (1 + q^k)`     (clearing q^{-k/2})

In `ℚ⟦X⟧` with `q = X`:

  `β*_n = if n = 0 then 1 else 0`
  `α*_k = (-1)^k · X^{k(k-1)/2} · (1 + X^k)` for k ≥ 1, `α*_0 = 1`

## Verification as Bailey pair

`β* = M(1, X) α*` means:
  `δ_{n,0} = ∑_{k=0}^n α*_k / ((X;X)_{n-k} · (X;X)_{n+k})`

This is exactly the finite JTP at z=1 (Chan Eq 9.15) with the fold.

## Application

`theorem92 1 X α* β*` then gives `L² β* = M D² α*`, which at component n
is the finite Rogers-Ramanujan identity. At n → ∞ this gives the RR
identities.
-/

namespace QseriesFormalization
namespace Pending
namespace RRBaileyPairSeed

open PowerSeries
open QseriesFormalization.PartII.Ch09

/-- The α* sequence of the JTP-derived Bailey pair at x=1 in ℚ⟦X⟧:
  α*_0 = 1, α*_k = (-1)^k · X^{k(k-1)/2} · (1 + X^k) for k ≥ 1. -/
noncomputable def rrAlphaStar : ℕ → ℚ⟦X⟧
  | 0 => 1
  | k + 1 => (-1 : ℚ⟦X⟧) ^ (k + 1) * X ^ ((k + 1) * k / 2) * (1 + X ^ (k + 1))

/-- The β* sequence: Kronecker delta. -/
noncomputable def rrBetaStar (n : ℕ) : ℚ⟦X⟧ :=
  if n = 0 then 1 else 0

@[simp] theorem rrAlphaStar_zero : rrAlphaStar 0 = 1 := rfl

@[simp] theorem rrBetaStar_zero : rrBetaStar 0 = 1 := rfl

@[simp] theorem rrBetaStar_succ (n : ℕ) : rrBetaStar (n + 1) = 0 := by
  unfold rrBetaStar; simp

-- KEY THEOREM (commented out): The JTP-derived pair is a Bailey pair at x=1.
-- IsBaileyPairByM requires [Field R], but ℚ⟦X⟧ is NOT a field.
-- The Bailey lemma infrastructure in Chapter09_BaileyLemma works over ℂ.
--
-- CORRECT APPROACH: Use the ANALYTIC path:
-- 1. Over ℂ with |q| < 1: `theorem92` gives the finite RR identity
-- 2. Take n → ∞ using `summable_rrJTerm` (Ch07)
-- 3. Get `rrJInf 1 q · (q;q)_∞ = pentagonal023-series(q)` analytically
-- 4. Extract coefficients → formal-PS identity over ℚ
--
-- This file defines the SEED for reference; the actual proof goes through ℂ.

-- theorem rrBaileyPairSeed :
--     IsBaileyPairByM (1 : ℚ⟦X⟧) X rrAlphaStar rrBetaStar := by
--   sorry  -- blocked: needs [Field ℚ⟦X⟧], which doesn't hold

/-! ## Key lemma: `qPoch 1 q n = 0` for n ≥ 1

This is why `β* = δ_{n,0}` — the `(z;q)_n` factor at z=1 vanishes
for n ≥ 1 because the k=0 factor `(1 - z·q⁰) = (1 - 1) = 0`. -/

theorem qPoch_one_eq_zero {R : Type*} [CommRing R] (q : R) :
    ∀ n : ℕ, 1 ≤ n → qPoch (1 : R) q n = 0
  | 0, h => absurd h (by omega)
  | 1, _ => by simp [qPoch, pow_zero, mul_one, sub_self, mul_zero]
  | n + 2, _ => by
      unfold qPoch
      rw [qPoch_one_eq_zero q (n + 1) (by omega), zero_mul]

/-! ## First application of L: `(L 1 q δ_0)_n = 1/(q;q)_n`

When β = δ_{n,0}, the operator L picks out only the k=0 term. -/

section FirstL
variable {R : Type*} [Field R]

/-- Kronecker delta as a function. -/
noncomputable def delta0 : ℕ → R := fun n => if n = 0 then 1 else 0

theorem L_one_delta0_eq (q : R) (n : ℕ) :
    L (1 : R) q delta0 n = 1 / qPochhammer q n := by
  unfold L
  have : ∀ k ∈ Finset.range (n + 1), k ≠ 0 →
      (1 : R) ^ k * q ^ (k * k) / qPochhammer q (n - k) * delta0 k = 0 := by
    intro k _ hk; unfold delta0; simp [hk]
  rw [Finset.sum_eq_single 0 this (by simp)]
  unfold delta0; simp [pow_zero, one_mul, Nat.sub_zero, one_div]

/-- Second application of L gives the finite RR sum:
`(L² 1 q δ_0)_n = ∑_{k=0}^n q^{k²} / ((q;q)_{n-k} · (q;q)_k)` -/
theorem L2_one_delta0_eq (q : R) (n : ℕ) :
    L2 (1 : R) q delta0 n =
      ∑ k ∈ Finset.range (n + 1),
        q ^ (k * k) / (qPochhammer q (n - k) * qPochhammer q k) := by
  unfold L2
  show L 1 q (fun j => L 1 q delta0 j) n = _
  conv_lhs => arg 3; ext j; rw [L_one_delta0_eq]
  unfold L
  congr 1; ext k
  simp only [one_pow, one_mul]
  ring

end FirstL

end RRBaileyPairSeed
end Pending
end QseriesFormalization
