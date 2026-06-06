# Batch 42: Exercises — Ch18 one-core obstruction wrappers

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Chapter18.lean` now has additional hook-length facts for
the `t = 1` boundary case.

This batch is mechanical. Touch only `QseriesFormalization/Exercises.lean`.

## Goal

Add wrappers in the existing `Chapter18Exercises` section for:

- `PartIV.Ch18.hasHookDivisibleBy_one_iff_exists_FerrersCell`
- `PartIV.Ch18.not_oneCoreByHooks_of_FerrersCell`
- `PartIV.Ch18.FerrersCell_cons_zero_zero`
- `PartIV.Ch18.not_oneCoreByHooks_cons_pos`

Use exact theorem statements from Chapter18. Avoid `sorry`, `axiom`, and
`native_decide`.

## Validation

Run only:

```bash
lake build QseriesFormalization.Exercises
rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean
```

The build may replay Chapter 2 and print its known `jacobiTripleProduct`
`sorry` warning. That is not introduced by this batch.

## Report

Write `HANDOFF/outbox/batch42-exercises-ch18-one-core-obstruction-wrappers-reply.md`
with:

- declarations added
- build result
- forbidden-token check result
