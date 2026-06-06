# Batch 31: Exercises — easy wrappers for Chapters 6, 8, 10, 12 - Reply

## Declarations Added

Added the following exercise wrappers to `QseriesFormalization/Exercises.lean`:

### Chapter 6
- `exercise6_dedekindEtaTrunc_one`
- `exercise6_dedekindEtaTrunc_two`

### Chapter 8
- `exercise8_D_partialSum_zero`
- `exercise8_D_trunc_one`

### Chapter 10
- `exercise10_ramanujanMockF_trunc_zero`
- `exercise10_ramanujanMockF_trunc_one`

### Chapter 12
- `exercise12_R_trunc_one_eq_inv_one_plus_q`
- `exercise12_R_trunc_two_eq`

## Build Result

```bash
lake build QseriesFormalization.Exercises
```
Output:
```
Build completed successfully (7901 jobs).
```
(Note: The build replayed Chapter 2 and printed its known `jacobiTripleProduct` `sorry` warning as expected).

## Forbidden-Token Check Result

```bash
rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean
```
Output: (empty)
