Task 49 completed.

Changed only the Lean task file:
- `QseriesFormalization/Chapter20.lean`

Added:
- `etaPolyPart_one`
- `discriminantPolyPart_zero`
- `discriminantPolyPart_one`

Validation:
- `lake build QseriesFormalization.Chapter20` succeeds.
- `rg -n "sorry|axiom|native_decide" QseriesFormalization/Chapter20.lean` finds nothing.

Full `lake build` is not clean in the current workspace because unrelated pre-existing dirty files fail:
- `QseriesFormalization/Chapter06.lean`: `No goals to be solved` at lines 29, 34, 39.
- `QseriesFormalization/Chapter02.lean`: `No goals to be solved` at lines 48, 70, and a `sorry` warning at line 100.

Those files were already modified before this task and were not touched.
