# Task 38: Ch1 — Euler pentagonal recurrence for partition function

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

Currently `partitionCount n` for `n = 0..11` is proved by explicit
case-enumeration (very slow at n=12+). Euler's pentagonal recurrence
provides an `O(n)`-step alternative:

`p(n) = ∑_{k≥1, m_k ≤ n} (-1)^{k+1} (p(n − m_k) + p(n − m_{-k}))`

where `m_k = k(3k-1)/2` (generalized pentagonal numbers).

## Goal

Add to `Chapter01.lean` a separate computational definition
`partitionCountRec : Nat → Nat` based on the recurrence:

```lean
/-- Pentagonal recurrence value at n with depth bound. -/
def partitionCountRec : Nat → Nat
  | 0 => 1
  | Nat.succ n =>
      -- compute p(n+1) = Σ_{k≥1} (-1)^{k+1} (p(n+1 - k(3k-1)/2) + p(n+1 - k(3k+1)/2))
      sorry  -- replace with real recursion!
```

(I wrote `sorry` for clarity; you must NOT use `sorry`. Implement the
recurrence using a finite Finset.range or recursion on `n`.)

A standard implementation: bound `k` by `n` (since `k(3k-1)/2 > n` for
`k > sqrt(2n/3) + 1`). Use `Nat.recAux` or a strong recursion.

Then prove (or attempt) `partitionCountRec n = partitionCount n` for
`n = 0..11` using the proved partition values.

If implementing the recursion is too involved, deliver instead just
the table-extension via:

```lean
theorem partitionCount_twelve : partitionCount 12 = 77
theorem partitionCount_thirteen : partitionCount 13 = 101
```

with whatever workable strategy (note these may also hit
heartbeats — if so document and stop).

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Chapter01.lean`.
- If you can't make progress beyond p(11), deliver a clear blocker note.

## Deliverable

Modified `Chapter01.lean` + reply file.
