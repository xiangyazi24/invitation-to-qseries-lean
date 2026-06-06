Status: done.

Modified files:
- `QseriesFormalization/Chapter01.lean`

Diff summary:
- Imported `Mathlib.Combinatorics.Enumerative.Partition.Basic`.
- Added `partitionCount (n : Nat) : Nat := Fintype.card (Nat.Partition n)`.
- Proved `partitionCount_zero`, `partitionCount_one`, `partitionCount_two`,
  `partitionCount_three`, and `partitionCount_four`.
- Reused Mathlib's `Nat.Partition`; no duplicate partition definition.
- `decide` worked directly for `p(0)` and `p(1)`, but not for `p(2)` through
  `p(4)` because the existing `Fintype` instance does not reduce far enough
  under `decide`. Workaround: explicitly classify `Nat.Partition n` for
  `n = 2, 3, 4` by multiset cardinality, positivity, and sum, then compute the
  resulting finite sets with `decide`.

Forbidden constructs check:
- No `axiom`.
- No `sorry`.
- No `native_decide`.

Validation:
- `lake env lean QseriesFormalization/Chapter01.lean`
- `lake build`

Final build line:

```text
Build completed successfully (7908 jobs).
```
