Task: add Chapter 15 exercise wrapper for the cleaner q-Taylor polynomial reconstruction theorem.

Files:
- Read `QseriesFormalization/Chapter15.lean`.
- Edit only `QseriesFormalization/Exercises.lean`.

Add one wrapper in `section Chapter15Exercises` for:
- `PartIII.Ch15.qTaylorPolynomialTopTrunc_eq_of_nonzero`

Suggested theorem name:
- `exercise15_qTaylorPolynomialTopTrunc_eq_of_nonzero`

Preserve the statement shape from Chapter15 and qualify names with `PartIII.Ch15.`.

Constraints:
- No `sorry`, no `axiom`, no `native_decide`.
- Do not touch Chapter15.
- Build only `lake build QseriesFormalization.Exercises`.
- Run `rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean QseriesFormalization/Chapter15.lean`.
- Write result to `HANDOFF/outbox/batch49-exercises-ch15-qtaylor-clean-wrapper-reply.md`.
