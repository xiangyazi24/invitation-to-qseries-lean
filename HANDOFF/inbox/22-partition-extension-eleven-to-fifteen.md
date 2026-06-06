# Task 22: Extend partitionCount table to p(11..15)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`Chapter01.lean` proves `partitionCount n` for `n = 0..10`. Extend to:
- `p(11) = 56`
- `p(12) = 77`
- `p(13) = 101`
- `p(14) = 135`
- `p(15) = 176`

(OEIS A000041.)

## Goal

Continue the existing `partition_n_cases` pattern in `Chapter01.lean`.
At higher `n` the case-analysis grows polynomially. If `decide` becomes
too slow at some `n`, **stop at the last n that compiles cleanly** and
document the cutoff. Don't fall back to `native_decide`.

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter01.lean`.
- If `decide` runs more than ~5 minutes for any `n`, stop at the
  previous `n` rather than wait.

## Deliverable

1. Modified `Chapter01.lean`.
2. Reply file with status, reached `n`, lake build final line.
