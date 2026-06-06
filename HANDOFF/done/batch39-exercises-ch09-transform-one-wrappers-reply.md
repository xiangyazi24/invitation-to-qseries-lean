# Batch 39: Exercises — Ch09 Bailey transform one-step wrappers

## Declarations Added

The following wrapper theorems were added to `QseriesFormalization/Exercises.lean` in the `Chapter9Exercises` section:

- `exercise9_BaileyBeta_one_expand`: Wraps `PartII.Ch09.BaileyBeta_one_expand`.
- `exercise9_BaileyBeta_transformAlpha_one_expand`: Wraps `PartII.Ch09.BaileyBeta_transformAlpha_one_expand`.
- `exercise9_BaileyTransformBeta_rrBeta_one_expand`: Wraps `PartII.Ch09.BaileyTransformBeta_rrBeta_one_expand`.

## Build Result

The build command `lake build QseriesFormalization.Exercises` completed successfully.

```
Build completed successfully (7906 jobs).
```

Note: The build replayed `Chapter02.lean` and printed the known `jacobiTripleProduct` `sorry` warning, as expected.

## Forbidden-Token Check Result

The command `rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean` returned no matches (exit code 1), confirming that no forbidden tokens were introduced.
