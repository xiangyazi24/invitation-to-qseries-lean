# Batch 59 — Ch09 Transformed-Alpha N=6 Mechanical Expansion

You are working in the repository root.

## Goal

Extend the existing finite Bailey transformed-alpha mechanical expansion from
`N = 5` to the first `N = 6` layer. This is bookkeeping only: add the raw
expanded beta theorem, the seven transformed-alpha term simplifications, and
the assembled evaluated-terms theorem.

Do not attempt the coefficient identities or preservation theorem for `N = 6`
in this batch.

## Files

Touch only:

- `QseriesFormalization/Chapter09.lean`
- `HANDOFF/outbox/batch59-ch09-transformalpha-n6-mechanical-reply.md`

Do not edit `Exercises.lean` in this batch.

## Required context

Read these parts first:

- `QseriesFormalization/Chapter09.lean`
- Existing transformed-alpha block near:
  - `BaileyTransformAlpha_five`
  - `BaileyBeta_transformAlpha_five_expand`
  - `BaileyTerm_transformAlpha_five_zero`
  - `BaileyTerm_transformAlpha_five_one`
  - `BaileyTerm_transformAlpha_five_two`
  - `BaileyTerm_transformAlpha_five_three`
  - `BaileyTerm_transformAlpha_five_four`
  - `BaileyTerm_transformAlpha_five_five`
  - `BaileyBeta_transformAlpha_five_terms`

## Tasks

1. Add the direct transform-alpha value theorem:

   - `BaileyTransformAlpha_six`

   It should match the shape of `BaileyTransformAlpha_five`, with `6` in every
   finite-product index and exponent. The proof should be `rfl` if possible.

2. Add the raw transformed-alpha beta expansion:

   - `BaileyBeta_transformAlpha_six_expand`

   It should use the existing general `BaileyBeta_six_expand`.

3. Add the seven term simplification lemmas:

   - `BaileyTerm_transformAlpha_six_zero`
   - `BaileyTerm_transformAlpha_six_one`
   - `BaileyTerm_transformAlpha_six_two`
   - `BaileyTerm_transformAlpha_six_three`
   - `BaileyTerm_transformAlpha_six_four`
   - `BaileyTerm_transformAlpha_six_five`
   - `BaileyTerm_transformAlpha_six_six`

   Follow the exact `N=5` pattern. For `k < 6`, denominators should use
   `qPochhammer q (6-k)` and `qPoch (a*q) q (6+k)`. For `k = 6`, use
   `BaileyTerm_at_n_simplified` and `BaileyTransformAlpha_six`, with denominator
   `qPoch (a*q) q 12`.

4. Add the assembled evaluated-terms theorem:

   - `BaileyBeta_transformAlpha_six_terms`

   It should rewrite by the raw expansion and the seven term lemmas.

If any theorem becomes slow or unstable, stop after the last passing theorem
and report exactly which theorem failed and the Lean error.

## Constraints

- No `sorry`.
- No `axiom`.
- No `native_decide`.
- Build only:

  ```bash
  lake build QseriesFormalization.Chapter09
  ```

- Do not run full `lake build`.
- Keep proof style consistent with the existing `N=4` and `N=5` transformed-alpha blocks.

## Reply

Write `HANDOFF/outbox/batch59-ch09-transformalpha-n6-mechanical-reply.md` with:

- The theorem names added.
- The exact build command and whether it passed.
- Any remaining blocker or slow theorem.
