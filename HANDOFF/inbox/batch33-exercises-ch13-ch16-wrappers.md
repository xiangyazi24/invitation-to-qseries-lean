# Batch 33: Exercises — wrappers for Chapters 13 and 16

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Exercises.lean` is the current flat exercise file.
Do not change chapter files.

## Goal

Touch only `QseriesFormalization/Exercises.lean`.

Add imports if missing:

```lean
import QseriesFormalization.Chapter13
import QseriesFormalization.Chapter16
```

Add exercise-wrapper sections for these already-proved facts.

Chapter 13:
- `PartIII.Ch13.deepIdentityLHSTrunc_zero`
- `PartIII.Ch13.deepIdentityLHSTrunc_one`
- `PartIII.Ch13.deepIdentityLHSTrunc_two`

Chapter 16:
- `PartIV.Ch16.mbiLHSTrunc_one`
- `PartIV.Ch16.mbiRHSNumeratorTrunc_one`
- `PartIV.Ch16.mbiRHSDenominatorTrunc_one`
- `PartIV.Ch16.mbi_truncated_zero`

Use direct wrappers with the exact theorem statements from the chapter files.
Keep the existing namespace and style in `Exercises.lean`. Avoid `sorry`,
`axiom`, and `native_decide`.

## Validation

Run only:

```bash
lake build QseriesFormalization.Exercises
rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean
```

The build may replay Chapter 2 and print its known `jacobiTripleProduct`
`sorry` warning. That is not introduced by this batch.

## Report

Write `HANDOFF/outbox/batch33-exercises-ch13-ch16-wrappers-reply.md` with:

- declarations added
- build result
- forbidden-token check result
