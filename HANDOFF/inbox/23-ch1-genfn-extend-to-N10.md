# Task 23: Extend partitionGenFn closed form to N=10

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`Chapter01.lean` has `partitionGenFn q 4 = 1 + q + 2q² + 3q³ + 5q⁴`
proven via the p(0..4) values.

Now p(0..11) are all proved. We can write a closed-form version of
the truncated generating function up to N=10:

`partitionGenFn q 10 = 1 + q + 2q² + 3q³ + 5q⁴ + 7q⁵ + 11q⁶ + 15q⁷ +
                        22q⁸ + 30q⁹ + 42q¹⁰`

## Goal

Add to `Chapter01.lean`:

```lean
section CommRing

variable {R : Type*} [CommRing R]

theorem partitionGenFn_ten (q : R) :
    partitionGenFn q 10 =
      1 + q + 2 * q^2 + 3 * q^3 + 5 * q^4 +
      7 * q^5 + 11 * q^6 + 15 * q^7 + 22 * q^8 + 30 * q^9 + 42 * q^10 := by
  …

end CommRing
```

The proof should unfold `partitionGenFn`, `natSum_succ` and the eleven
`partitionCount_*` lemmas, then close with `simp` + `ring` or `simp` +
`norm_num` + `ring`.

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter01.lean`.

## Deliverable

1. Modified `Chapter01.lean`.
2. Reply file with status, lake build final line.
