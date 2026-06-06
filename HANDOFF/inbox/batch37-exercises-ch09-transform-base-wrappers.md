# Batch 37: Exercises — Ch09 Bailey transform base wrappers

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Chapter09.lean` now has zero-depth finite Bailey-transform
facts. This is mechanical exercise exposure.

Touch only `QseriesFormalization/Exercises.lean`.

## Goal

Add wrappers in the existing `Chapter9Exercises` section for:

- `PartII.Ch09.BaileyBeta_transformAlpha_zero`
- `PartII.Ch09.BaileyTransform_preserves_pair_zero`
- `PartII.Ch09.BaileyTransformBeta_rrBeta_zero`
- `PartII.Ch09.BaileyTransform_preserves_rr_pair_zero`

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

Write `HANDOFF/outbox/batch37-exercises-ch09-transform-base-wrappers-reply.md`
with:

- declarations added
- build result
- forbidden-token check result
