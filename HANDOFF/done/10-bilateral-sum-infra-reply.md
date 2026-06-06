Status: done.

Modified files:
- `QseriesFormalization/Basic.lean`
- `QseriesFormalization/Chapter04.lean`

Diff summary:
- Added `bilateralSum` after `natSum`, with simp lemmas for zero/succ.
- Proved `bilateralSum_congr` over the finite support interval `[-n, n]`.
- Proved symmetry `bilateralSum_neg`.
- Added Ch 4 Euler pentagonal finite truncation definitions:
  `eulerPentagonalProductTrunc`, `pentagonalIndex`,
  `eulerPentagonalSeriesTrunc`.
- Added `euler_pentagonal_truncated_zero`.

Validation:
- `lake build`
- Final line: `Build completed successfully (7908 jobs).`
