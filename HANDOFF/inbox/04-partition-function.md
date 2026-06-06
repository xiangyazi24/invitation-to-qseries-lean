# Task 04: Partition function `p(n)` — definition and small values

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.
**`lake build` must end clean.**

## Background

Chan, *An Invitation to q-Series* Definition 1.1 / Eq (1.8): a partition
of `n` is a weakly decreasing list of positive integers summing to `n`,
and `p(n)` (the partition function) counts these. The first five values
are

`p(0) = 1, p(1) = 1, p(2) = 2, p(3) = 3, p(4) = 5`

(Chan Example 1.1 lists `P(4) = {4, 3+1, 2+2, 2+1+1, 1+1+1+1}` so
`p(4) = 5`.)

Mathlib already has `Nat.Partition n` as a `structure` in
`Mathlib.Combinatorics.Enumerative.Partition.Basic`. It is
`Fintype`-instanced via Mathlib (look for the existing instance — if
absent, derive one in our file).

## Goal

Add to `QseriesFormalization/Chapter01.lean` (the Introduction file):

```lean
import QseriesFormalization.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic

…

/-- The partition function `p(n)` (Chan Def 1.1, Eq 1.8). -/
def partitionCount (n : Nat) : Nat := Fintype.card (Nat.Partition n)

/-- `p(0) = 1`. -/
theorem partitionCount_zero : partitionCount 0 = 1 := …

/-- `p(1) = 1`. -/
theorem partitionCount_one : partitionCount 1 = 1 := …

/-- `p(2) = 2`. -/
theorem partitionCount_two : partitionCount 2 = 2 := …

/-- `p(3) = 3`. -/
theorem partitionCount_three : partitionCount 3 = 3 := …

/-- `p(4) = 5` (Chan Example 1.1). -/
theorem partitionCount_four : partitionCount 4 = 5 := …
```

## Hints

- If `Fintype` for `Nat.Partition n` is not inferred automatically, you
  may need to add `decide` instances or use a different reflection path.
- **`decide` is preferred over `native_decide`**. The latter is forbidden
  by project policy (no axiom-style escape; see project memory
  `feedback_no_axiom_escape`).
- If `decide` is too slow even for `n = 4`, try unfolding via `Finset`
  cardinality or hand-listing the partitions and proving bijection.
- Do not duplicate `Nat.Partition` — reuse Mathlib's.

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`** in the final code.
- `lake build` clean.
- Touch only `Chapter01.lean` (you may also need to add the import to
  `Basic.lean` or to the umbrella file if needed; minimize footprint).

## Deliverable

1. Modified files (probably just `Chapter01.lean`).
2. Reply file with status, diff summary, `lake build` final line.
   If `decide` is too slow or `Fintype` is missing for some `n`, report
   the obstruction and your workaround.
