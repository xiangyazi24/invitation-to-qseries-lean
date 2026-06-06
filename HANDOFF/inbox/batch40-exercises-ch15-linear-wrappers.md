# Batch 40: Exercises — Ch15 q-Taylor linearity wrappers

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Chapter15.lean` now has linearity facts for finite
monomial-basis polynomials and top-term q-Taylor reconstructions.

This batch is mechanical. Touch only `QseriesFormalization/Exercises.lean`.

## Goal

Add wrappers in the existing `Chapter15Exercises` section for:

- `PartIII.Ch15.qPolynomialTrunc_add`
- `PartIII.Ch15.qPolynomialTrunc_smul`
- `PartIII.Ch15.qTaylorPolynomialTopTrunc_add`
- `PartIII.Ch15.qTaylorPolynomialTopTrunc_smul`

Use exact theorem statements from Chapter15. Avoid `sorry`, `axiom`, and
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

Write `HANDOFF/outbox/batch40-exercises-ch15-linear-wrappers-reply.md`
with:

- declarations added
- build result
- forbidden-token check result
