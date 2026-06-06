# Task 39: Ch4 — Euler pentagonal truncation N=1 explicit values

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`Chapter04.lean` defines `eulerPentagonalProductTrunc` and
`eulerPentagonalSeriesTrunc`. The N=0 sanity is proved (both = 1).

At N=1:
- LHS: `qPochhammer q 1 = 1 - q`
- RHS: bilateralSum at N=1 has terms j = 0, ±1.
  - j=0: (-1)^0 · q^{0} = 1
  - j=1: (-1)^1 · q^{pentagonalIndex 1} = -q^{1·4/2} = -q^2
  - j=-1: (-1)^{(-1).toNat} · q^{pentagonalIndex (-1)} = (-1)^0 · q^{(-1)·(-2)/2} = q^1
  - Sum = 1 + q - q^2

So at N=1: LHS = 1-q, RHS = 1+q-q²; **they differ** by `2q - q²`.
Document this discrepancy as a closed-form theorem.

## Goal

Add to `Chapter04.lean`:

```lean
theorem eulerPentagonalProductTrunc_one (q : R) :
    eulerPentagonalProductTrunc q 1 = 1 - q := by
  rfl  -- or simp + norm

theorem eulerPentagonalSeriesTrunc_one (q : R) :
    eulerPentagonalSeriesTrunc q 1 = 1 + q - q^2 := by
  …

/-- The truncated Euler pentagonal identity does NOT hold at N=1. -/
theorem eulerPentagonal_N1_difference (q : R) :
    eulerPentagonalSeriesTrunc q 1 - eulerPentagonalProductTrunc q 1 =
      2 * q - q^2 := by
  rw [eulerPentagonalProductTrunc_one, eulerPentagonalSeriesTrunc_one]
  ring
```

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter04.lean`.
- If pentagonalIndex / Int.toNat make the simp ugly, you may need to
  explicitly compute `pentagonalIndex 1 = 2`, `pentagonalIndex (-1) = 1`.

## Deliverable

Modified `Chapter04.lean` + reply file.
