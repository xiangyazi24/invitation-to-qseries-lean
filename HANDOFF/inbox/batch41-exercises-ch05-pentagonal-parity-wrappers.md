# Batch 41: Exercises — Ch05 pentagonal parity wrappers

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Chapter05.lean` now has part-count and parity facts for
lower/upper pentagonal fixed shapes.

This batch is mechanical. Touch only `QseriesFormalization/Exercises.lean`.

## Goal

Add wrappers in the existing `Chapter5Exercises` section for:

- `PartI.Ch05.numberOfParts_lowerPentagonalPartition`
- `PartI.Ch05.numberOfParts_upperPentagonalPartition`
- `PartI.Ch05.partParity_lowerPentagonalPartition`
- `PartI.Ch05.partParity_upperPentagonalPartition`

Use exact theorem statements from Chapter05. Avoid `sorry`, `axiom`, and
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

Write `HANDOFF/outbox/batch41-exercises-ch05-pentagonal-parity-wrappers-reply.md`
with:

- declarations added
- build result
- forbidden-token check result
