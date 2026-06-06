# Task 21: Ch11 — Rogers-Ramanujan continued fraction scaffold (Part III)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Chan Ch 11 is "A list of theorems to be proven" — a specs page for
Part III. Key objects (Definitions 11.1, 11.2, 11.3):

- `R(q) := q^{1/5} / (1 + q/(1 + q²/(1 + …)))` — Rogers-Ramanujan
  continued fraction (definition over ℂ for `|q| < 1`).
- `G(q) := 1 / ((q; q^5)_∞ (q^4; q^5)_∞)`
- `H(q) := 1 / ((q^2; q^5)_∞ (q^3; q^5)_∞)`
- `α := (1 + √5) / 2`, `β := (1 - √5) / 2`
- `f(-q) := (q; q)_∞`

Theorem 11.1 (Rogers): `R(q) = q^{1/5} · H(q) / G(q)`.

These all involve infinite products / continued fractions, so concrete
defs need ℂ + tprod.

## Goal

Scaffold `Chapter11.lean` with concrete `noncomputable def`s for the
**finite truncated** versions of these objects + the **constants
α, β** (which are real and don't need analytic infrastructure):

```lean
import QseriesFormalization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic

namespace QseriesFormalization
namespace PartIII
namespace Ch11

/-- The Golden Ratio `(1 + √5) / 2`. -/
noncomputable def α : ℝ := (1 + Real.sqrt 5) / 2

/-- The negative reciprocal `(1 - √5) / 2`. -/
noncomputable def β : ℝ := (1 - Real.sqrt 5) / 2

/-- Sanity: `α + β = 1`. -/
theorem α_add_β : α + β = 1 := …

/-- Sanity: `α · β = -1`. -/
theorem α_mul_β : α * β = -1 := …

/-- Sanity: `α² = α + 1` (golden ratio identity). -/
theorem α_sq : α^2 = α + 1 := …

/-- `G_n(q) := ∏_{k=1}^N 1/((1 - q^{5k-4})(1 - q^{5k-1}))`, finite. -/
noncomputable def G_trunc (q : ℂ) (N : Nat) : ℂ :=
  match N with
  | 0 => 1
  | Nat.succ n =>
      G_trunc q n / ((1 - q ^ (5 * (n + 1) - 4)) * (1 - q ^ (5 * (n + 1) - 1)))

/-- `H_n(q) := ∏_{k=1}^N 1/((1 - q^{5k-3})(1 - q^{5k-2}))`, finite. -/
noncomputable def H_trunc (q : ℂ) (N : Nat) : ℂ :=
  match N with
  | 0 => 1
  | Nat.succ n =>
      H_trunc q n / ((1 - q ^ (5 * (n + 1) - 3)) * (1 - q ^ (5 * (n + 1) - 2)))

/-- N=0 sanity for G_trunc and H_trunc. -/
theorem G_trunc_zero (q : ℂ) : G_trunc q 0 = 1 := rfl
theorem H_trunc_zero (q : ℂ) : H_trunc q 0 = 1 := rfl

end Ch11
end PartIII
end QseriesFormalization
```

## Hints

- For `α + β = 1`: unfold both, simplify `((1+√5)+(1-√5))/2 = 2/2 = 1`.
- For `α · β = -1`: `((1+√5)(1-√5))/4 = (1-5)/4 = -1`.
- For `α^2 = α + 1`: square `(1+√5)/2`, get `(1+2√5+5)/4 = (6+2√5)/4 = (3+√5)/2`. RHS: `(1+√5)/2 + 1 = (3+√5)/2`. Match.
- These should close cleanly with `field_simp` + `Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)` + `ring`.

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`.**
- `lake build` clean.
- Touch only `Chapter11.lean`.

## Deliverable

1. Modified `Chapter11.lean`.
2. Reply file with status, lake build final line.
