# Reply: Ch20 v2

## Result

Completed.

## Changes

- Verified no Lean file imports the old compatibility modules:
  - `QseriesFormalization.Chapter20_TauExtend`
  - `QseriesFormalization.Chapter20_TauMult`
  - `QseriesFormalization.Chapter20_TauValues`
- Replaced each of those three files with a single comment:

```lean
-- Moved to QseriesFormalization/Chapter20.lean.
```

## Verification

Commands run:

```bash
rg -n "^import QseriesFormalization\\.Chapter20_Tau(Extend|Mult|Values)" QseriesFormalization QseriesFormalization.lean -S
lake build QseriesFormalization
```

Results:

- Import scan: no matches.
- `lake build QseriesFormalization`: passed.
  Final lines:
  - `Built QseriesFormalization.Audit (267s)`
  - `Built QseriesFormalization (3.0s)`
  - `Build completed successfully (8010 jobs).`

