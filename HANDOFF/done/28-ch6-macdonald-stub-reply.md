Status: Chapter06 stub implemented.

Modified:
- QseriesFormalization/Chapter06.lean

Validation:
- `rg "sorry|axiom|native_decide" QseriesFormalization/Chapter06.lean || true`
  - no matches
- `lake build QseriesFormalization.Chapter06`
  - final line: `Build completed successfully (7886 jobs).`
- `lake build`
  - final line: `error: build failed`
  - blocker: unrelated existing errors in `QseriesFormalization/Chapter17.lean` for unknown identifiers `partitionCount_four`, `partitionCount_nine`, `partitionCount_five`, and `partitionCount_six`.

