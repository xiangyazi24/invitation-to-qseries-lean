# Batch 41: Exercises — Ch05 pentagonal parity wrappers Reply

## Declarations Added

Added the following wrappers in `QseriesFormalization/Exercises.lean` under `section Chapter5Exercises`:

- `exercise5_numberOfParts_lowerPentagonalPartition`
- `exercise5_numberOfParts_upperPentagonalPartition`
- `exercise5_partParity_lowerPentagonalPartition`
- `exercise5_partParity_upperPentagonalPartition`

These wrap:
- `PartI.Ch05.numberOfParts_lowerPentagonalPartition`
- `PartI.Ch05.numberOfParts_upperPentagonalPartition`
- `PartI.Ch05.partParity_lowerPentagonalPartition`
- `PartI.Ch05.partParity_upperPentagonalPartition`

## Build Result

```bash
lake build QseriesFormalization.Exercises
```
Output:
```
⚠ [7887/7906] Replayed QseriesFormalization.Chapter02
warning: QseriesFormalization/Chapter02.lean:98:8: declaration uses 'sorry'
Build completed successfully (7906 jobs).
```
The build was successful. The warning about `sorry` in `Chapter02.lean` is pre-existing and expected.

## Forbidden-Token Check Result

```bash
rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean
```
Output: (empty)

No forbidden tokens were found in `QseriesFormalization/Exercises.lean`.
