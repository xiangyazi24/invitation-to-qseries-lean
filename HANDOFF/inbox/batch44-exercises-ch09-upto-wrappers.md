Task: add Chapter 9 exercise wrappers for the new finite Bailey-pair truncation lemmas.

Files:
- Read `QseriesFormalization/Chapter09.lean`.
- Edit only `QseriesFormalization/Exercises.lean`.

Add wrappers in `section Chapter9Exercises` for:
- `PartII.Ch09.IsBaileyPairUpTo.mono`
- `PartII.Ch09.IsBaileyPairUpTo.zero_of_one`
- `PartII.Ch09.IsBaileyPairUpTo.one`

Suggested theorem names:
- `exercise9_IsBaileyPairUpTo_mono`
- `exercise9_IsBaileyPairUpTo_zero_of_one`
- `exercise9_IsBaileyPairUpTo_one`

Constraints:
- No `sorry`, no `axiom`, no `native_decide`.
- Do not touch Chapter09.
- Build only `lake build QseriesFormalization.Exercises`.
- Run `rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean QseriesFormalization/Chapter09.lean`.
- Write result to `HANDOFF/outbox/batch44-exercises-ch09-upto-wrappers-reply.md`.
