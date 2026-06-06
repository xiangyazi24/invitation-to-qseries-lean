# Batch 58 — Ch09 Bailey N=6 Mechanical Expansion

You are working in the repository root.

## Goal

Extend the existing finite Bailey `rrAlpha` mechanical expansion from `N = 5`
to the first `N = 6` layer. This is algebraic bookkeeping only; do not change
definitions or theorem statements outside the requested N=6 expansion family.

## Files

Touch only:

- `QseriesFormalization/Chapter09.lean`
- `HANDOFF/outbox/batch58-ch09-n6-bailey-mechanical-reply.md`

Do not edit `Exercises.lean` in this batch.

## Required context

Read these parts first:

- `QseriesFormalization/Basic.lean`
- `QseriesFormalization/Chapter09.lean`
- Existing N=5 block near:
  - `BaileyBeta_rrAlpha_five_expand`
  - `BaileyTerm_rrAlpha_five_zero`
  - `BaileyTerm_rrAlpha_five_one`
  - `BaileyTerm_rrAlpha_five_two`
  - `BaileyTerm_rrAlpha_five_three`
  - `BaileyTerm_rrAlpha_five_four`
  - `BaileyTerm_rrAlpha_five_five`
  - `BaileyBeta_rrAlpha_five_terms`
  - `rrBeta_five_terms`

## Tasks

1. Add the N=6 analogue of the raw beta expansion:

   - `BaileyBeta_rrAlpha_six_expand`

2. Add the seven term simplification lemmas:

   - `BaileyTerm_rrAlpha_six_zero`
   - `BaileyTerm_rrAlpha_six_one`
   - `BaileyTerm_rrAlpha_six_two`
   - `BaileyTerm_rrAlpha_six_three`
   - `BaileyTerm_rrAlpha_six_four`
   - `BaileyTerm_rrAlpha_six_five`
   - `BaileyTerm_rrAlpha_six_six`

3. Add the assembled terms theorem:

   - `BaileyBeta_rrAlpha_six_terms`

4. If the assembly is short and stable, add:

   - `rrBeta_six_terms`

If any individual term becomes too slow or unstable, stop after the last
passing theorem and report exactly which theorem failed and the error.

## Constraints

- No `sorry`.
- No `axiom`.
- No `native_decide`.
- Build only:

  ```bash
  lake build QseriesFormalization.Chapter09
  ```

- Do not run full `lake build`.
- Keep proof style consistent with the existing N=4 and N=5 blocks.

## Reply

Write `HANDOFF/outbox/batch58-ch09-n6-bailey-mechanical-reply.md` with:

- The theorem names added.
- The exact build command and whether it passed.
- Any remaining blocker or slow theorem.
