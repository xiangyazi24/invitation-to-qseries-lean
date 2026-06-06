Task: add Chapter 18 exercise wrappers for hook-divisibility monotonicity.

Files:
- Read `QseriesFormalization/Chapter18.lean`.
- Edit only `QseriesFormalization/Exercises.lean`.

Add wrappers in `section Chapter18Exercises` for:
- `PartIV.Ch18.hasHookDivisibleBy_of_dvd`
- `PartIV.Ch18.IsTCoreByHooks.of_dvd`

Suggested theorem names:
- `exercise18_hasHookDivisibleBy_of_dvd`
- `exercise18_IsTCoreByHooks_of_dvd`

Preserve the statement shape from Chapter18 and qualify names with `PartIV.Ch18.`.

Constraints:
- No `sorry`, no `axiom`, no `native_decide`.
- Do not touch Chapter18.
- Build only `lake build QseriesFormalization.Exercises`.
- Run `rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean QseriesFormalization/Chapter18.lean`.
- Write result to `HANDOFF/outbox/batch47-exercises-ch18-hook-dvd-monotone-wrappers-reply.md`.
