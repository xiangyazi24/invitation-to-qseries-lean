# DS Task: Extend Ch01 partitionCount to higher N

You are generating Lean 4 / Mathlib v4.27.0 code. Output ONLY Lean code (no
markdown fences, no commentary).

## Context

`Chapter01.lean` currently has `partitionCount n = Fintype.card (Nat.Partition n)`
proved for n = 0, 1, 2, ..., 11 with values 1, 1, 2, 3, 5, 7, 11, 15, 22, 30,
42, 56. The proofs are mechanical — each is `decide` or `native_decide` or a
direct `rfl` followed by `rfl` (which Lean evaluates the Fintype.card at).

Existing template:

```lean
theorem partitionCount_eleven : partitionCount 11 = 56 := by
  decide
```

(Looking at the file: each is `theorem partitionCount_<word> : partitionCount n = value := by decide` or similar.)

## Task

Add the partition values for n = 12, 13, 14, 15. Standard values:
- p(12) = 77
- p(13) = 101
- p(14) = 135
- p(15) = 176

Names follow the existing pattern:

  partitionCount_twelve : partitionCount 12 = 77 := by decide
  partitionCount_thirteen : partitionCount 13 = 101 := by decide
  partitionCount_fourteen : partitionCount 14 = 135 := by decide
  partitionCount_fifteen : partitionCount 15 = 176 := by decide

If `decide` is too slow, try `native_decide`. If that's still too slow, use
the recursion theorem `partitionCountRec_eq_partitionCount_*` already in the
file (compute partitionCountRec n then equate).

## Constraints

- No `sorry`, no `axiom`.
- No `native_decide` if you can avoid it (the project policy avoids it).
- Output ONLY 4 theorems, one for each n.

## Output

Just the four theorems. No surrounding text or markdown.
