Task: add Chapter 9 exercise wrappers for Rogers-Ramanujan Bailey seed `N=2,3` lemmas.

Files:
- Read `QseriesFormalization/Chapter09.lean`.
- Edit only `QseriesFormalization/Exercises.lean`.

Add wrappers in `section Chapter9Exercises` for these existing Chapter09 theorems:
- `PartII.Ch09.isBaileyPairUpTo_rrAlpha_rrBeta`
- `PartII.Ch09.rrAlpha_three`
- `PartII.Ch09.BaileyBeta_rrAlpha_two_expand`
- `PartII.Ch09.BaileyTerm_rrAlpha_two_zero`
- `PartII.Ch09.BaileyTerm_rrAlpha_two_one`
- `PartII.Ch09.BaileyTerm_rrAlpha_two_two`
- `PartII.Ch09.BaileyBeta_rrAlpha_two_terms`
- `PartII.Ch09.BaileyTerm_rrAlpha_three_zero`
- `PartII.Ch09.BaileyTerm_rrAlpha_three_one`
- `PartII.Ch09.BaileyTerm_rrAlpha_three_two`
- `PartII.Ch09.BaileyTerm_rrAlpha_three_three`
- `PartII.Ch09.BaileyBeta_rrAlpha_three_terms`
- `PartII.Ch09.rrBeta_three_terms`

Use names starting with `exercise9_` and preserve the exact statement shape from Chapter09, qualifying names with `PartII.Ch09.` where needed.

Constraints:
- No `sorry`, no `axiom`, no `native_decide`.
- Do not touch Chapter09.
- Build only `lake build QseriesFormalization.Exercises`.
- Run `rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean QseriesFormalization/Chapter09.lean`.
- Write result to `HANDOFF/outbox/batch45-exercises-ch09-rralpha-n2-n3-wrappers-reply.md`.
