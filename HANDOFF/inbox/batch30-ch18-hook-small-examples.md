# Batch 30: Ch18 — hook-length small examples

## Context

`QseriesFormalization/Chapter18.lean` now has a hook-length section before the
existing generating-function truncation section:

- `FerrersCell`
- `armLength`
- `legLength`
- `hookLength`
- `HasHookDivisibleBy`
- `IsTCoreByHooks`
- `tCore_hookLength_characterization`
- concrete hook lengths for `[3, 2, 1]`

This is theory infrastructure for Chan Chapter 18's t-core hook-length
characterization. The goal is to add small concrete examples, not truncation
tables.

## Goal

Touch only `QseriesFormalization/Chapter18.lean`.

Add hook-length examples for the partition `[4, 2]` after the existing
`[3, 2, 1]` hook lemmas:

```lean
theorem hookLength_four_two_zero_zero :
    hookLength [4, 2] 0 0 = 5 := by ...

theorem hookLength_four_two_zero_one :
    hookLength [4, 2] 0 1 = 4 := by ...

theorem hookLength_four_two_zero_two :
    hookLength [4, 2] 0 2 = 2 := by ...

theorem hookLength_four_two_zero_three :
    hookLength [4, 2] 0 3 = 1 := by ...

theorem hookLength_four_two_one_zero :
    hookLength [4, 2] 1 0 = 2 := by ...

theorem hookLength_four_two_one_one :
    hookLength [4, 2] 1 1 = 1 := by ...
```

Then prove one hook-divisibility example:

```lean
theorem hasHookDivisibleBy_two_four_two :
    HasHookDivisibleBy 2 [4, 2] := by ...
```

Use the existing definitions. Expected proof style:

```lean
  norm_num [hookLength, armLength, legLength]
```

and for the divisibility theorem, choose cell `(0,1)` or `(1,0)`.

## Constraints

- No `sorry`, no `axiom`, no `native_decide`.
- Do not extend t-core truncation tables.
- Build only this chapter:

```bash
lake build QseriesFormalization.Chapter18
```

Also run:

```bash
rg -n "sorry|axiom|native_decide" QseriesFormalization/Chapter18.lean
```

Expected result for the `rg` command: no matches.

## Report

Write a short reply under
`HANDOFF/outbox/batch30-ch18-hook-small-examples-reply.md` with:

- declarations added
- build result
- whether the forbidden-token check had matches
