Task 46 completed.

Changed:
- Added `charge_add_single`
- Added `charge_remove_single`
- Added `energy_add_single`
- Added `energy_remove_single`

Validation:
- `lake build QseriesFormalization.Chapter05` completed successfully.
- `rg -n "sorry|axiom|native_decide" QseriesFormalization/Chapter05.lean` found no matches.
- Full `lake build` did not complete because `QseriesFormalization/Chapter06.lean` currently fails with `No goals to be solved` at lines 29, 34, and 39. `QseriesFormalization.Chapter05` built successfully during that full build before the Chapter06 failure.
