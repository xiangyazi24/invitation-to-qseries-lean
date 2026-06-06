# Batch 36: Exercises — Ch05 shifted pentagonal wrappers - Reply

## Declarations Added

The following exercise wrappers were added to `QseriesFormalization/Exercises.lean`:

- `exercise5_shiftedStaircasePartition_three_one`
- `exercise5_numberOfParts_shiftedStaircasePartition`
- `exercise5_partitionWeight_shiftedStaircasePartition`
- `exercise5_IsStrictPartition_shiftedStaircasePartition`
- `exercise5_lowerPentagonalPartition_three`
- `exercise5_upperPentagonalPartition_three`
- `exercise5_partitionWeight_lowerPentagonalPartition`
- `exercise5_partitionWeight_upperPentagonalPartition`
- `exercise5_two_mul_upperPentagonalNumber`
- `exercise5_IsStrictPartition_lowerPentagonalPartition`
- `exercise5_IsStrictPartition_upperPentagonalPartition`

## Build Result

`lake build QseriesFormalization.Exercises` completed successfully.

```
⚠ [7887/7906] Replayed QseriesFormalization.Chapter02
warning: QseriesFormalization/Chapter02.lean:98:8: declaration uses 'sorry'
Build completed successfully (7906 jobs).
```

## Forbidden-Token Check Result

`rg "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean` found no matches.
