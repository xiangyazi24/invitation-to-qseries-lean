# Batch 38: Exercises — Ch18 t-core boundary wrappers

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Chapter18.lean` now has additional hook-length boundary
facts for `t`-cores.

This batch is mechanical. Touch only `QseriesFormalization/Exercises.lean`.

## Goal

Add wrappers in the existing `Chapter18Exercises` section for:

- `PartIV.Ch18.nilCoreByHooks`
- `PartIV.Ch18.oneCoreByHooks_iff_no_FerrersCell`

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

Write `HANDOFF/outbox/batch38-exercises-ch18-core-boundary-wrappers-reply.md`
with:

- declarations added
- build result
- forbidden-token check result
