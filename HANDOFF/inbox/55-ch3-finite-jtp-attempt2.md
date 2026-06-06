# Task 55: Ch3 — finite JTP general n, attempt 2

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`Chapter03.lean` has `finite_jacobi_triple_product_zero/one/two` and
substitution infrastructure (`qPoch_substitute_div_qpow`,
`qPoch_substitute_div_qpow_two_mul`) from t06 + t17.

The general `n` case was blocked at the termwise reindexing of the
q-binomial sum into `finiteJTPSummand`, with the arithmetic subgoal:

```
((((k : Int) - (n : Int)) * (((k : Int) - (n : Int)) - 1) / 2).toNat) + n * k =
  k * (k - 1) / 2 + triangular n
```

## Goal

Try a fresh approach. Either:

(a) Resolve the `Int.toNat` subgoal directly via case-split on
    `k ≥ n` vs `k < n` and careful Int arithmetic, then close the
    main theorem.

(b) Re-derive `finiteJTPRHS` or `finiteJTPSummand` using a different
    parameterization (e.g., a Finset sum over `Finset.Icc (-n : ℤ) n`)
    that sidesteps `Int.toNat`.

(c) Prove the n=3 case explicitly (analogous to t17's n=2). This adds
    one more concrete data point even if the general case stays open.

If both (a) and (b) are too gnarly, deliver (c) — n=3 explicit case —
as the partial result. Document blocker.

Touch only Chapter03.lean. No axiom/sorry/native_decide. lake build clean.

## Deliverable

Modified Chapter03.lean + reply with status (completed / partial /
blocked) and details.
