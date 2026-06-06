import Mathlib.Data.ZMod.Basic

/-!
# Chapter 17 — Ramanujan-Watson mod-5 residue analysis

Key combinatorial facts at the heart of Ramanujan's 1919 proof of
`∀ n, 5 ∣ p(5n+4)`.  Working in `ZMod 5` (where 2 is invertible with
inverse 3), the triangular and pentagonal exponents become:

  - **Triangular** `T_k = k(k+1)/2`; in ZMod 5: `3·k·(k+1)`.
    Range: `{0, 1, 3} ⊂ ZMod 5`.
  - **Pentagonal** `P_j = j(3j+1)/2`; in ZMod 5: `3·j·(3j+1)`.
    Range: `{0, 1, 2} ⊂ ZMod 5`.

The Jacobi coefficient `2k+1` vanishes in ZMod 5 exactly when `k ≡ 2`,
which is exactly when `T_k ≡ 3` (mod 5).  So contributing pairs have
`T_k ∈ {0, 1}` and `P_j ∈ {0, 1, 2}`, giving `T_k + P_j ∈ {0,1,2,3}` —
**never 4**.

This file proves the enumeration facts by `decide` on `Fin 5` / `ZMod 5`.
-/

namespace QseriesFormalization
namespace PartIV
namespace Ch17

open ZMod

/-- The triangular number `T_k = k(k+1)/2`, expressed in `ZMod 5` via
the inverse of 2 (which is 3 mod 5).  So `T_k mod 5 = 3 · k · (k+1) mod 5`. -/
def triangularMod5 (k : ZMod 5) : ZMod 5 := 3 * k * (k + 1)

/-- The pentagonal number `P_j = j(3j+1)/2`, expressed in `ZMod 5` via
the inverse of 2. -/
def pentagonalMod5 (j : ZMod 5) : ZMod 5 := 3 * j * (3 * j + 1)

/-- **Triangular residues mod 5**: for every `k : ZMod 5`,
`triangularMod5 k ∈ {0, 1, 3}`. -/
theorem triangularMod5_range : ∀ k : ZMod 5,
    triangularMod5 k = 0 ∨ triangularMod5 k = 1 ∨ triangularMod5 k = 3 := by
  decide

/-- **Pentagonal residues mod 5**: for every `j : ZMod 5`,
`pentagonalMod5 j ∈ {0, 1, 2}`. -/
theorem pentagonalMod5_range : ∀ j : ZMod 5,
    pentagonalMod5 j = 0 ∨ pentagonalMod5 j = 1 ∨ pentagonalMod5 j = 2 := by
  decide

/-- **Jacobi coefficient vanishing**: in ZMod 5, `2k + 1 = 0` iff `k = 2`. -/
theorem jacobi_coeff_zero_iff : ∀ k : ZMod 5,
    (2 * k + 1 : ZMod 5) = 0 ↔ k = 2 := by decide

/-- **Key correlation**: when the Jacobi coefficient `2k+1` is non-zero in
ZMod 5, the triangular residue `triangularMod5 k` is in `{0, 1}` only
(not `3`). -/
theorem triangular_when_jacobi_nonzero (k : ZMod 5)
    (h : (2 * k + 1 : ZMod 5) ≠ 0) :
    triangularMod5 k = 0 ∨ triangularMod5 k = 1 := by
  fin_cases k <;> first | (exfalso; apply h; decide) | (left; decide) |
    (right; decide)

/-- **The 4-residue obstruction** (the heart of Ramanujan's proof):
for all triangular k and pentagonal j contributing non-trivially mod 5
(i.e., `2k+1 ≢ 0`), the sum `triangularMod5 k + pentagonalMod5 j ≠ 4` in
ZMod 5. -/
theorem triangular_plus_pentagonal_ne_four
    (k j : ZMod 5) (hk : (2 * k + 1 : ZMod 5) ≠ 0) :
    triangularMod5 k + pentagonalMod5 j ≠ 4 := by
  -- triangularMod5 k ∈ {0, 1} (by triangular_when_jacobi_nonzero)
  -- pentagonalMod5 j ∈ {0, 1, 2} (by pentagonalMod5_range)
  -- Sum ∈ {0,1,2,3} — never 4 in ZMod 5.
  rcases triangular_when_jacobi_nonzero k hk with htri | htri <;>
  rcases pentagonalMod5_range j with hp | hp | hp <;>
  rw [htri, hp] <;> decide

end Ch17
end PartIV
end QseriesFormalization
