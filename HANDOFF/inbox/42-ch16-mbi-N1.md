# Task 42: Ch16 — MBI truncation N=1 explicit values

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`Chapter16.lean` defines `mbiLHSTrunc`, `mbiRHSTrunc` for Ramanujan's
"Most Beautiful Identity". At N=0 both = 5 (using p(4) = 5).

At N=1:
- mbiLHSTrunc q 1 = `p(4) + p(9)·q = 5 + 30q`
- mbiRHSNumeratorTrunc q 1 = (1-q^5)^5
- mbiRHSDenominatorTrunc q 1 = (1-q)^6
- mbiRHSTrunc q 1 = 5 (1-q^5)^5 / (1-q)^6

These don't match exactly but document the explicit values.

## Goal

Add to `Chapter16.lean`:

```lean
theorem mbiLHSTrunc_one (q : R) :
    mbiLHSTrunc q 1 =
      (Ch01.partitionCount 4 : R) + (Ch01.partitionCount 9 : R) * q := by
  …

theorem mbiRHSNumeratorTrunc_one (q : R) :
    mbiRHSNumeratorTrunc q 1 = (1 - q ^ 5) ^ 5 := by
  …

theorem mbiRHSDenominatorTrunc_one (q : R) :
    mbiRHSDenominatorTrunc q 1 = (1 - q) ^ 6 := by
  …
```

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter16.lean`.

## Deliverable

Modified `Chapter16.lean` + reply file.
