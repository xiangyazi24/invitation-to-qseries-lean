Done.

Modified:
- `QseriesFormalization/Chapter06.lean`

Added:
- `dedekindEtaTrunc_one`
- `dedekindEtaTrunc_two`
- `dedekindEtaTrunc_three`

Validation:
- `lake build` succeeded.
- `QseriesFormalization/Chapter06.lean` contains no `sorry`, `axiom`, or `native_decide`.

Note:
- The requested `simp [dedekindEtaTrunc, qPochhammer]; ring` shape was simplified to `simp [dedekindEtaTrunc, qPochhammer]` because `simp` closes each goal in the current codebase, and the following `ring` produces `No goals to be solved`.
