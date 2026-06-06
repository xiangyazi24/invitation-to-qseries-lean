# Task 14: Replace Ch 2 axioms with `tprod` / `tsum`-based `noncomputable def`s

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`QseriesFormalization/Chapter02.lean` currently has three axioms that
are the **last** axioms in the project (after task 13 cleared Ch 4):

```lean
axiom jacobiInfiniteProduct (q z : R) : R
axiom jacobiInfiniteSeries (q z : R) : R
axiom jacobiTripleProduct (q z : R) :
  jacobiInfiniteProduct q z = jacobiInfiniteSeries q z
```

Per project policy (no axiom escapes), these need to go. The infinite
product / bilateral series, however, do require analytic infrastructure
to define — which Mathlib provides via `tprod` and `tsum`.

## Goal

Convert these axioms to `noncomputable def`s using Mathlib's `tprod`
and `tsum`. The `jacobiTripleProduct` axiom becomes a `theorem ... := by
sorry` — the theorem statement is real, the proof is genuinely TODO.
**A `sorry` here is honest** (open work, not an axiom escape).

Concretely, in `Chapter02.lean`:

1.  Strengthen the typeclass on `R` for the infinite-form definitions.
    Either:
    - Replace the local `[Field R]` block with a separate
      `section InfiniteForms` where `R` carries `[CommMonoid R]
      [TopologicalSpace R]` (for `tprod`) and corresponding sum
      typeclasses (`[AddCommMonoid R]`, `[TopologicalSpace R]`,
      `[T2Space R]`).
    - Or specialize to `R = ℂ` (or `R := ℂ` for concreteness).

    Pick whichever produces a cleaner `lake build` with the rest of the
    file untouched. **Specializing to ℂ** is probably easiest.

2.  Define:

    ```lean
    /-- The infinite Jacobi triple product side
    `∏_{n=1}^∞ (1 - q^{2n})(1 + z q^{2n-1})(1 + z⁻¹ q^{2n-1})`.
    Returns 1 if the family is not multipliable. -/
    noncomputable def jacobiInfiniteProduct (q z : ℂ) : ℂ :=
      ∏' n : ℕ+, (1 - q ^ (2 * n.val)) *
                  (1 + z * q ^ (2 * n.val - 1)) *
                  (1 + z⁻¹ * q ^ (2 * n.val - 1))
    ```

    (Use `ℕ+` or `Finset.Ioi 0` or `{n : ℕ | n ≥ 1}` — whichever Mathlib
    plays with most easily; the resulting product over a non-multipliable
    family defaults to `1` per Mathlib conventions, which is fine.)

3.  Define:

    ```lean
    /-- The bilateral series `∑_{n = -∞}^{∞} z^n q^{n^2}`. -/
    noncomputable def jacobiInfiniteSeries (q z : ℂ) : ℂ :=
      ∑' n : ℤ, z ^ n * q ^ (n^2)
    ```

    For `z^n` with `n : ℤ`, you may need `zpow` (i.e. `z ^ (n : ℤ)`).
    `q ^ (n^2)` with `n^2 : ℤ` again needs `zpow`. Be careful that
    `n^2 ≥ 0` so even though it's `Int`, the value is non-negative —
    Mathlib's `zpow` handles negative exponents via inversion which is
    exactly what we want for `z⁻¹` factors implicit in `z^n` for `n<0`.

4.  Replace the `axiom jacobiTripleProduct` with:

    ```lean
    /--
    Jacobi's triple product identity (Chan Theorem 2.1, Eq 2.1).
    Statement only; the analytic proof via Chan's functional-equation
    method is open work — see Chan Ch 2 pp. 5-7.
    -/
    theorem jacobiTripleProduct (q z : ℂ) (hq : ‖q‖ < 1) (hz : z ≠ 0) :
        jacobiInfiniteProduct q z = jacobiInfiniteSeries q z := by
      sorry
    ```

5.  Update any consumer in `Chapter04.lean` (e.g.
    `theorem41LHS`, `eulerPentagonalProduct`) that referenced the old
    `R`-generic `jacobiInfiniteProduct`. They probably need to be
    specialized to ℂ now (or rewritten via the truncated defs from
    task 13).

## Constraints

- **No `axiom`.** Sorry IS allowed for `jacobiTripleProduct` (genuine
  open work). No other sorries.
- `lake build` clean.
- Touch `Chapter02.lean` and any minimum-needed downstream files
  (likely `Chapter04.lean` for the `theorem41LHS` / `eulerPentagonalProduct`
  signatures).

## Deliverable

1. Modified files.
2. Reply file with status, lake build final line, list of remaining
   sorries (should be just one — `jacobiTripleProduct`).
