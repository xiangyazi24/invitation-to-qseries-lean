Done.

Changed only `QseriesFormalization/Chapter11.lean` for the Lean proof work:

- Added `G_trunc_one`.
- Added `H_trunc_one`.
- No `axiom`, no `sorry`, no `native_decide`.

Validation:

- `lake build QseriesFormalization.Chapter11` succeeds.
- Full `lake build` was attempted. `Chapter11` built successfully, but the full build failed later in the already-modified `QseriesFormalization/Chapter16.lean` at line 61:
  `change` tactic failed for `mbiRHSDenominatorTrunc q 1 = (1 - q) ^ 6`.

