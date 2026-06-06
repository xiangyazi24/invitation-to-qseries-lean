# Batch 32: Exercises — late basic wrappers — Reply

## Declarations Added

Added imports for Chapters 14, 19, and 20 in `QseriesFormalization/Exercises.lean`.

Added the following exercise wrappers:

### Chapter 14
- `exercise14_crankGenTrunc_zero`
- `exercise14_crankGenNumeratorTrunc_one`
- `exercise14_crankGenDenominatorTrunc_one`

### Chapter 19
- `exercise19_ramanujan_5_n0`
- `exercise19_ramanujan_7_n0`
- `exercise19_ramanujan_11_n0`
- `exercise19_p10_mod_7`
- `exercise19_p6_mod_11`

### Chapter 20
- `exercise20_etaPolyPart_one`
- `exercise20_etaPolyPart_two`
- `exercise20_discriminantPolyPart_one`

## Validation

### Build Result
`lake build QseriesFormalization.Exercises` completed successfully.
(Replayed `QseriesFormalization.Chapter02` with known `jacobiTripleProduct` `sorry` warning).

### Forbidden-Token Check
Ran `rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean`.
Result: No forbidden tokens found in the modified file.
