# Batch 40: Exercises — Ch15 q-Taylor linearity wrappers

## Goal
Add wrappers in the existing `Chapter15Exercises` section for:
- `PartIII.Ch15.qPolynomialTrunc_add`
- `PartIII.Ch15.qPolynomialTrunc_smul`
- `PartIII.Ch15.qTaylorPolynomialTopTrunc_add`
- `PartIII.Ch15.qTaylorPolynomialTopTrunc_smul`

## Declarations Added
- `exercise15_qPolynomialTrunc_add`
- `exercise15_qPolynomialTrunc_smul`
- `exercise15_qTaylorPolynomialTopTrunc_add`
- `exercise15_qTaylorPolynomialTopTrunc_smul`

## Validation Results

### Build Result
`lake build QseriesFormalization.Exercises` completed successfully.
Note: Replayed Chapter 02 and printed its known `jacobiTripleProduct` `sorry` warning as expected.

### Forbidden-Token Check
`rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean` returned no matches.
Found no `sorry`, `axiom`, or `native_decide` in the exercises file.
