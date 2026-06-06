Done.

Changed `QseriesFormalization/Chapter04.lean` only for the Lean task:

- Added `eulerPentagonalProductTrunc_two`.
- Added `eulerPentagonalSeriesTrunc_two`:
  `eulerPentagonalSeriesTrunc q 2 = 1 + q - q ^ 2 + q ^ 5 + q ^ 7`.
- Documented that the negative-index signs are positive because the truncation uses `j.toNat`.

Validation:

- `lake build QseriesFormalization.Chapter04` passes.
- `rg -n "\b(sorry|axiom|native_decide)\b" QseriesFormalization/Chapter04.lean` finds nothing.
- Full `lake build` is blocked by existing failures in `Chapter07.lean` and `Chapter11.lean`; `Chapter04` itself built successfully in that run.
