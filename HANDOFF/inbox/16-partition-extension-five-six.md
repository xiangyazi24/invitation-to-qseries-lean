# Task 16: Extend partition function values to p(5)=7 and p(6)=11

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`Chapter01.lean` proves `p(0)=1` through `p(4)=5` using a
`partition_n_cases` case-analysis pattern (case-split on `p.parts.card`,
enumerate canonical representatives, conclude by `decide` on a finite
universe).

The next two values are well-known:
- `p(5) = 7`: partitions of 5 are `5; 4+1; 3+2; 3+1+1; 2+2+1; 2+1+1+1; 1+1+1+1+1` (7 partitions).
- `p(6) = 11`: partitions of 6 are `6; 5+1; 4+2; 4+1+1; 3+3; 3+2+1; 3+1+1+1; 2+2+2; 2+2+1+1; 2+1+1+1+1; 1+1+1+1+1+1` (11 partitions).

## Goal

Extend `Chapter01.lean` with:

1. Canonical `Nat.Partition` representatives for each partition of 5
   and 6 (use the existing `partitionOfParts` helper).
2. `partition_five_cases` and `partition_six_cases` lemmas matching the
   existing pattern.
3. Theorems:
   ```lean
   theorem partitionCount_five : partitionCount 5 = 7
   theorem partitionCount_six : partitionCount 6 = 11
   ```

## Constraints

- **No `axiom`, no `sorry`, no `native_decide`.**
- `lake build` clean.
- Touch only `Chapter01.lean`.
- Follow the existing case-analysis pattern (`partition_four_cases` is
  the largest existing exemplar).

## Deliverable

1. Modified `Chapter01.lean`.
2. Reply file with status, lake build final line.
