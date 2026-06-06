# Batch 34: Exercises — low truncation wrappers

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Exercises.lean` is the current flat exercise file.
This batch is mechanical. Do not change chapter files.

## Goal

Touch only `QseriesFormalization/Exercises.lean`.

Add wrappers for these already-proved facts:

Chapter 6:
- `PartI.Ch06.dedekindEtaTrunc_three`
- `PartI.Ch06.dedekindEtaTrunc_four`

Chapter 8:
- `PartII.Ch08.D_partialSum_two`
- `PartII.Ch08.D_trunc_two`

Chapter 10:
- `PartII.Ch10.ramanujanMockF_trunc_two`

Use exact theorem statements from the chapter files. Keep the existing section
style. Avoid `sorry`, `axiom`, and `native_decide`.

## Validation

Run only:

```bash
lake build QseriesFormalization.Exercises
rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean
```

The build may replay Chapter 2 and print its known `jacobiTripleProduct`
`sorry` warning. That is not introduced by this batch.

## Report

Write `HANDOFF/outbox/batch34-exercises-low-truncation-wrappers-reply.md` with:

- declarations added
- build result
- forbidden-token check result
