# Task 18: Extend partitionCount table to p(7..10)

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`Chapter01.lean` already has `partitionCount n = p(n)` proved for
`n = 0, 1, ..., 6` using a `partition_n_cases` case-analysis pattern
(case-split on `p.parts.card`, enumerate canonical representatives).

## Goal

Extend the table to:
- `p(7) = 15`
- `p(8) = 22`
- `p(9) = 30`
- `p(10) = 42`

(These are the values Euler tabulated; OEIS A000041.)

The pattern is the same as `partition_six_cases` — define canonical
`Nat.Partition` representatives, prove a `partition_n_cases` lemma by
splitting on `p.parts.card`, then show
`Finset.univ : Finset (Nat.Partition n) = {<canonicals>}` and close by
`decide`.

The case-analysis grows polynomially with `n`, so `partition_ten_cases`
will be sizeable. If `decide` for the universe equality at `n = 10`
becomes slow, you can break it into a chain of `Finset.insert` rewrites
or fall back to `native_decide` — but **try `decide` first** as it's
the project default.

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`.**
- `lake build` clean.
- Touch only `Chapter01.lean`.
- If `decide` is genuinely too slow at any `n`, deliver up to the last
  `n` that works and document the cutoff in the reply file.

## Deliverable

1. Modified `Chapter01.lean`.
2. Reply file with status, lake build final line, and any cutoff note.
