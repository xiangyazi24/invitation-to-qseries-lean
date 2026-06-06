# Task 13: Replace remaining Ch 4 axioms with finite-truncation `def`s

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`QseriesFormalization/Chapter04.lean` currently still has these axioms:

```lean
axiom theorem41RHS (q : R) (a : Nat) : R
axiom theorem41 (q : R) (a : Nat) : theorem41LHS q a = theorem41RHS q a

axiom eulerPentagonalSeries (q : R) : R
axiom eulerPentagonalTheorem (q : R) :
  eulerPentagonalProduct q = eulerPentagonalSeries q

axiom theorem43RHS (q : R) : R
axiom theorem43 (q : R) :
  jacobiInfiniteProduct (q ^ 2) q = theorem43RHS q

axiom quintupleProductLHS (q z : R) : R
axiom quintupleProductRHS (q z : R) : R
axiom quintupleProductTheorem (q z : R) :
  quintupleProductLHS q z = quintupleProductRHS q z
```

These `axiom` declarations violate the project's "no axiom" policy.
Project policy: `axiom` is reserved for genuine Mathlib gaps, **not**
for unproven Chan theorems.

The `jacobiInfiniteProduct` / `jacobiInfiniteSeries` / `jacobiTripleProduct`
axioms in `Chapter02.lean` still need analytic infrastructure (tprod /
tsum) and stay as axioms for now (their replacement is a separate task).

## Goal

In `Chapter04.lean`, replace each axiom with a **finite-truncation
`noncomputable def`** mirroring the pattern used in
`eulerPentagonalProductTrunc` / `eulerPentagonalSeriesTrunc` (already in
the file). The infinite identities themselves remain unproven (they
depend on Ch 2 infrastructure), but at least the RHS objects become
concrete `def`s instead of bare `axiom` constants.

Specifically:

1.  Drop the `axiom` declarations (`theorem41RHS`, `theorem41`,
    `eulerPentagonalSeries`, `eulerPentagonalTheorem`, `theorem43RHS`,
    `theorem43`, `quintupleProductLHS`, `quintupleProductRHS`,
    `quintupleProductTheorem`).

2.  Rephrase as truncated statements + N=0 sanity checks. Use the
    existing `eulerPentagonalProductTrunc` / `eulerPentagonalSeriesTrunc`
    / `bilateralSum` / `pentagonalIndex` as templates. Suggested
    pattern for each:

    ```lean
    /-- Theorem 4.1 LHS truncated: ∏_{n=1}^{N} (1 - q^{5n})(1 - q^{5n-2-2a})(1 - q^{5n-3+2a}). -/
    noncomputable def theorem41LHSTrunc (q : R) (a N : Nat) : R := …

    /-- Theorem 4.1 RHS truncated: ∑_{j=-N}^{N} (-1)^j q^{j(5j+1)/2 - 2aj}. -/
    noncomputable def theorem41RHSTrunc (q : R) (a N : Nat) : R := …

    /-- N=0 sanity check: both truncated sides equal 1. -/
    theorem theorem41_truncated_zero (q : R) (a : Nat) :
        theorem41LHSTrunc q a 0 = 1 ∧ theorem41RHSTrunc q a 0 = 1 := …
    ```

    Repeat for Theorem 4.3 and the quintuple product identity.

3.  For pentagonal numbers in Theorem 4.1, the exponent
    `j(5j+1)/2 - 2aj` may be negative for some `j` and `a`. Use
    `Int.toNat` (as in `pentagonalIndex`) and accept that for indices
    where the formula is genuinely negative the truncation contains a
    "wrong" term — these only matter for the *limit* identity, and we're
    only checking finite `N=0` sanity.

4.  For the quintuple product (Theorem 4.4), Chan's Eq (2.12) gives
    the LHS as a four-fold infinite product and the RHS as a more
    complex bilateral sum. Truncate analogously.

5.  Watch `Nat.sub` truncation when `5n - 2 - 2a` etc. evaluate at
    small `n`. If you hit `Nat.sub` zero-truncation issues, cast to
    `Int` and back, or guard with `n ≥ 1`.

6.  Comment **briefly** that the actual infinite identity (matching
    Chan's Theorem 4.1, 4.2 limit, 4.3, 4.4) requires Ch 2 analytic
    infrastructure, which is **deferred**.

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`.**
- `lake build` clean.
- Touch only `Chapter04.lean`.

## Deliverable

1. Modified `Chapter04.lean` — all 9 listed axioms gone, replaced by
   `noncomputable def`s + N=0 sanity theorems where reasonable.
2. Reply file with status, lake build final line, and a note on which
   if any sanity theorems you couldn't close (and why).
