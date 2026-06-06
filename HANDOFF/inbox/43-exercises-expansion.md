# Task 43: Exercises.lean — add exercises tied to new chapter content

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`Exercises.lean` currently has only Ch1-4 exercises. New content is
available in Ch7 (RR truncation), Ch11 (α/β/G/H), Ch12 (R(q) value),
Ch16 (MBI truncation), Ch17 (Ramanujan congruences), Ch18 (t-cores).

## Goal

Add a `Chapter7Exercises`, `Chapter11Exercises`, `Chapter17Exercises`
block to `Exercises.lean`:

```lean
import QseriesFormalization.Basic
import QseriesFormalization.Chapter01
import QseriesFormalization.Chapter02
import QseriesFormalization.Chapter03
import QseriesFormalization.Chapter04
import QseriesFormalization.Chapter07
import QseriesFormalization.Chapter11
import QseriesFormalization.Chapter17

namespace QseriesFormalization

section Chapter7Exercises

variable {R : Type*} [Field R]

/-- Exercise: rogersRamanujanLHSTrunc at N=0 equals 1. -/
theorem exercise7_lhs_zero (q : R) (a : Nat) :
    PartII.Ch07.rogersRamanujanLHSTrunc q a 0 = 1 := by
  simp [PartII.Ch07.rogersRamanujanLHSTrunc, natSum, qPochhammer]

end Chapter7Exercises

section Chapter11Exercises

/-- Exercise: α + β = 1 (golden ratio sanity). -/
theorem exercise11_α_add_β : PartIII.Ch11.α + PartIII.Ch11.β = 1 :=
  PartIII.Ch11.α_add_β

end Chapter11Exercises

section Chapter17Exercises

/-- Exercise: p(4) divisible by 5 (smallest case of p(5n+4) ≡ 0 mod 5). -/
theorem exercise17_partition_4_mod_5 :
    Ch01.partitionCount 4 % 5 = 0 :=
  PartIV.Ch17.partition_5n_plus_4_mod_5_n_zero

end Chapter17Exercises

… (existing Ch1-4 exercises) …

end QseriesFormalization
```

## Constraints

- No `axiom`, no `sorry`, no `native_decide`.
- `lake build` clean.
- Touch only `Exercises.lean`.

## Deliverable

Modified `Exercises.lean` + reply file.
