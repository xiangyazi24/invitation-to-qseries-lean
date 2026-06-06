# Batch 35: Exercises — Ch11/Ch12 wrappers

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Exercises.lean` is the current flat exercise file.
This batch is mechanical. Do not change chapter files.

## Goal

Touch only `QseriesFormalization/Exercises.lean`.

Add wrappers for these already-proved facts:

Chapter 11:
- `PartIII.Ch11.α_mul_β`
- `PartIII.Ch11.α_sq`
- `PartIII.Ch11.β_sq`
- `PartIII.Ch11.α_cubed`
- `PartIII.Ch11.β_cubed`
- `PartIII.Ch11.α_inv`

Chapter 12:
- `PartIII.Ch12.R_trunc_three_eq`
- `PartIII.Ch12.R_trunc_four_eq`
- `PartIII.Ch12.R_trunc_five_eq`

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

Write `HANDOFF/outbox/batch35-exercises-ch11-ch12-wrappers-reply.md` with:

- declarations added
- build result
- forbidden-token check result
