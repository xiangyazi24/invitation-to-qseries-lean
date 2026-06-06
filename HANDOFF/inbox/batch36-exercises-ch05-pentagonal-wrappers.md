# Batch 36: Exercises — Ch05 shifted pentagonal wrappers

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Chapter05.lean` now contains shifted-staircase and
pentagonal-partition facts for Franklin's involution foundations.

This batch is mechanical. Touch only `QseriesFormalization/Exercises.lean`.

## Goal

Add wrappers in the existing `Chapter5Exercises` section for these facts:

- `PartI.Ch05.shiftedStaircasePartition_three_one`
- `PartI.Ch05.numberOfParts_shiftedStaircasePartition`
- `PartI.Ch05.partitionWeight_shiftedStaircasePartition`
- `PartI.Ch05.IsStrictPartition_shiftedStaircasePartition`
- `PartI.Ch05.lowerPentagonalPartition_three`
- `PartI.Ch05.upperPentagonalPartition_three`
- `PartI.Ch05.partitionWeight_lowerPentagonalPartition`
- `PartI.Ch05.partitionWeight_upperPentagonalPartition`
- `PartI.Ch05.two_mul_upperPentagonalNumber`
- `PartI.Ch05.IsStrictPartition_lowerPentagonalPartition`
- `PartI.Ch05.IsStrictPartition_upperPentagonalPartition`

Use exact theorem statements from Chapter05. Keep naming consistent with
the existing exercise wrappers. Avoid `sorry`, `axiom`, and `native_decide`.

## Validation

Run only:

```bash
lake build QseriesFormalization.Exercises
rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean
```

The build may replay Chapter 2 and print its known `jacobiTripleProduct`
`sorry` warning. That is not introduced by this batch.

## Report

Write `HANDOFF/outbox/batch36-exercises-ch05-pentagonal-wrappers-reply.md`
with:

- declarations added
- build result
- forbidden-token check result
