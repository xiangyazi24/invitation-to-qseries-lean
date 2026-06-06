# Batch 39: Exercises — Ch09 Bailey transform one-step wrappers

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Chapter09.lean` now has one-step finite Bailey-transform
scaffold facts.

This batch is mechanical. Touch only `QseriesFormalization/Exercises.lean`.

## Goal

Add wrappers in the existing `Chapter9Exercises` section for:

- `PartII.Ch09.BaileyBeta_one_expand`
- `PartII.Ch09.BaileyBeta_transformAlpha_one_expand`
- `PartII.Ch09.BaileyTransformBeta_rrBeta_one_expand`

Use exact theorem statements from Chapter09. Avoid `sorry`, `axiom`, and
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

Write `HANDOFF/outbox/batch39-exercises-ch09-transform-one-wrappers-reply.md`
with:

- declarations added
- build result
- forbidden-token check result
