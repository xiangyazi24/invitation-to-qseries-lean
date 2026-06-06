Task 51 status: completed.

Changed only `QseriesFormalization/Chapter11.lean` for Lean source edits.

Added:
- `β_sq : β ^ 2 = β + 1`
- `α_cubed : α ^ 3 = 2 * α + 1`
- `β_cubed : β ^ 3 = 2 * β + 1`
- `α_inv : α⁻¹ = α - 1`
- `β_inv : β⁻¹ = β - 1`

Validation:
- `lake env lean QseriesFormalization/Chapter11.lean` passed.
- `lake build QseriesFormalization.Chapter11` passed.
- `rg -n "sorry|axiom|native_decide" QseriesFormalization/Chapter11.lean` found nothing.
- Full `lake build` did not finish cleanly because existing `QseriesFormalization/Chapter16.lean:48` fails with `simp` maximum recursion depth. `Chapter11`, `Chapter12`, and `Exercises` built before that failure.
