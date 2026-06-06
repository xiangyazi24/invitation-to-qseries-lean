# Batch 32: Exercises — basic wrappers for Chapters 14, 19, 20

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Exercises.lean` is the current flat exercise file.
Recent batches added wrappers for Chapters 5, 6, 8, 9, 10, 12, 15, and 18.

This batch is mechanical. Do not change chapter files.

## Goal

Touch only `QseriesFormalization/Exercises.lean`.

Add imports if missing:

```lean
import QseriesFormalization.Chapter14
import QseriesFormalization.Chapter19
import QseriesFormalization.Chapter20
```

Add exercise-wrapper sections for these already-proved facts:

Chapter 14:
- `PartIII.Ch14.crankGenTrunc_zero`
- `PartIII.Ch14.crankGenNumeratorTrunc_one`
- `PartIII.Ch14.crankGenDenominatorTrunc_one`

Chapter 19:
- `PartIV.Ch19.ramanujan_5_n0`
- `PartIV.Ch19.ramanujan_7_n0`
- `PartIV.Ch19.ramanujan_11_n0`
- `PartIV.Ch19.p10_mod_7`
- `PartIV.Ch19.p6_mod_11`

Chapter 20:
- `PartIV.Ch20.etaPolyPart_one`
- `PartIV.Ch20.etaPolyPart_two`
- `PartIV.Ch20.discriminantPolyPart_one`

Use direct wrappers with the exact theorem statements from the chapter files.
Use existing section style in `Exercises.lean`. Avoid adding `sorry`, `axiom`,
or `native_decide`.

## Validation

Run only:

```bash
lake build QseriesFormalization.Exercises
rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean
```

The build may replay Chapter 2 and print its known `jacobiTripleProduct`
`sorry` warning. That is not introduced by this batch.

## Report

Write `HANDOFF/outbox/batch32-exercises-late-basic-wrappers-reply.md` with:

- declarations added
- build result
- forbidden-token check result
