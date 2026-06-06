# Batch 60 — Ch09 Transformed-Beta N=6 Mechanical Expansion

You are working in the repository root.

## Goal

Extend the finite Bailey transformed-beta mechanical expansion from `N = 5`
to `N = 6`. This is bookkeeping only: add the raw seven-term transformed-beta
expansion and the version under an `IsBaileyPairUpTo ... 6` hypothesis where
the `β k` values are rewritten with the existing `BaileyBeta` terms.

Do not attempt coefficient identities, linear assembly, or preservation theorem
for `N = 6` in this batch.

## Files

Touch only:

- `QseriesFormalization/Chapter09.lean`
- `HANDOFF/outbox/batch60-ch09-transformbeta-n6-mechanical-reply.md`

Do not edit `Exercises.lean` in this batch.

## Required context

Read these parts first:

- `QseriesFormalization/Chapter09.lean`
- Existing transformed-beta blocks near:
  - `BaileyTransformBeta_five_expand`
  - `BaileyTransformBeta_of_pair_five_expand`
  - `BaileyTransformBeta_of_pair_five_terms`
  - `BaileyBeta_six_terms`

## Tasks

1. Add the raw transformed-beta expansion:

   - `BaileyTransformBeta_six_expand`

   Shape: exactly like `BaileyTransformBeta_five_expand`, with seven summands
   for `β 0` through `β 6`, denominator index `6`, and tail q-Pochhammer /
   q-factorial indices `6-k`. The proof should be:

   ```lean
   simp [BaileyTransformBeta, natSum]
   ```

2. Add the expansion under an up-to-six Bailey pair hypothesis:

   - `BaileyTransformBeta_of_pair_six_expand`

   It should rewrite the seven `β k` values using:

   ```lean
   h 0 (by omega), ..., h 6 (by omega)
   ```

   Follow the exact style of `BaileyTransformBeta_of_pair_five_expand`.

3. Add the evaluated terms theorem:

   - `BaileyTransformBeta_of_pair_six_terms`

   It should rewrite `BaileyTransformBeta_of_pair_six_expand` and then use:

   - `BaileyBeta_zero`
   - `BaileyBeta_one_terms`
   - `BaileyBeta_two_terms`
   - `BaileyBeta_three_terms`
   - `BaileyBeta_four_terms`
   - `BaileyBeta_five_terms`
   - `BaileyBeta_six_terms`

   Follow the exact shape of `BaileyTransformBeta_of_pair_five_terms`, adding
   the seventh outer coefficient and the inner seven-term `BaileyBeta_six_terms`
   expression.

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

## Reply

Write `HANDOFF/outbox/batch60-ch09-transformbeta-n6-mechanical-reply.md` with:

- The theorem names added.
- The exact build command and whether it passed.
- Any remaining blocker or slow theorem.
