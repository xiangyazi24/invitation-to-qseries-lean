Task 42 complete.

Changed only `QseriesFormalization/Chapter16.lean`.

Added:
- `mbiLHSTrunc_one`
- `mbiRHSNumeratorTrunc_one`
- `mbiRHSDenominatorTrunc_one`

Validation:
- `lake env lean QseriesFormalization/Chapter16.lean`
- `lake build`

Both pass. No `axiom`, `sorry`, or `native_decide` added.
