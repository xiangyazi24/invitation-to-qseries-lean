# Batch 38: Exercises — Ch18 t-core boundary wrappers - Reply

## Goal
Add wrappers in the existing `Chapter18Exercises` section for:
- `PartIV.Ch18.nilCoreByHooks`
- `PartIV.Ch18.oneCoreByHooks_iff_no_FerrersCell`

## Declarations Added
- `exercise18_nilCoreByHooks`
- `exercise18_oneCoreByHooks_iff_no_FerrersCell`

## Build Result
The build was successful.
```bash
lake build QseriesFormalization.Exercises
```
Output:
```
⚠ [7887/7906] Replayed QseriesFormalization.Chapter02
warning: QseriesFormalization/Chapter02.lean:98:8: declaration uses 'sorry'
Build completed successfully (7906 jobs).
```
The warning is pre-existing and not introduced by this batch.

## Forbidden-Token Check Result
Checked for `sorry`, `axiom`, and `native_decide` in `QseriesFormalization/Exercises.lean`.
```bash
rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean
```
Output:
```
(empty)
```
No forbidden tokens found.
