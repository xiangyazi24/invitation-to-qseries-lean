# Task 20: Arithmetic lemmas for triangular / pentagonal / partition

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`Basic.lean` defines `triangular n = n(n+1)/2` and `pentagonalNumber k =
k(3k-1)/2`. We have only the trivial `_zero` / `_one` simp lemmas. More
arithmetic structure would help downstream proofs.

## Goal

Add to `QseriesFormalization/Basic.lean` (in the existing
`namespace QseriesFormalization` block, after the existing
`triangular` and `pentagonalNumber` definitions):

```lean
/-- `triangular` recursion: T(n+1) = T(n) + (n+1). -/
theorem triangular_succ (n : Nat) :
    triangular (Nat.succ n) = triangular n + Nat.succ n

/-- `triangular` doubled is n(n+1). -/
theorem two_mul_triangular (n : Nat) :
    2 * triangular n = n * (n + 1)

/-- pentagonalNumber recursion: P(k+1) = P(k) + (3k+1). -/
theorem pentagonalNumber_succ (k : Nat) :
    pentagonalNumber (Nat.succ k) = pentagonalNumber k + (3 * k + 1)

/-- Concrete values of pentagonal numbers `0, 1, 5, 12, 22, …`. -/
theorem pentagonalNumber_two : pentagonalNumber 2 = 5
theorem pentagonalNumber_three : pentagonalNumber 3 = 12
theorem pentagonalNumber_four : pentagonalNumber 4 = 22
theorem pentagonalNumber_five : pentagonalNumber 5 = 35
```

(Note `2 = 5, 3 = 12, 4 = 22, 5 = 35` come from `k(3k-1)/2`:
2·5/2 = 5, 3·8/2 = 12, 4·11/2 = 22, 5·14/2 = 35.)

## Hints

- `triangular_succ`: rewrite `(n+1)(n+2)/2 = n(n+1)/2 + (n+1)` using
  the `Nat.div` rules and `omega`.
- `two_mul_triangular`: clear by computation; `2 * (n*(n+1)/2) = n*(n+1)`
  uses `Nat.div_mul_eq_mul_div` plus the fact `n*(n+1)` is even.
- `pentagonalNumber_succ`: similar pattern.
- Concrete values: `decide` or `norm_num [pentagonalNumber]`.

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`.**
- `lake build` clean.
- Touch only `Basic.lean`.

## Deliverable

1. Modified `Basic.lean`.
2. Reply file with status, lake build final line.
