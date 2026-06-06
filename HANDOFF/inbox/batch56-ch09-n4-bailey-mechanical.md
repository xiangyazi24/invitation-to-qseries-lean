# Batch 56: Chapter09 N=4 Bailey Algebra Recon

## Context

Work in `QseriesFormalization/Chapter09.lean`.

Current state:
- `BaileyTransform_preserves_pair_upTo_three_of_nonzero` is proved.
- `BaileyTransformBeta_of_pair_four_expand` exists.
- `BaileyBeta_transformAlpha_four_expand` exists.
- RR seed `BaileyBeta_rrAlpha_four_terms` and `rrBeta_four_terms` are already proved.

## Task

Do a mechanical reconnaissance for extending the finite Bailey-transform
preservation package from `N = 3` to `N = 4`.

Preferred output:
1. Identify the exact existing theorem names that should be reused for the
   `N = 4` proof.
2. If low-risk, add only wrapper/expansion lemmas that compile quickly and do
   not require large coefficient identities.
3. Do not attempt a huge `ring_nf` proof if it looks expensive; instead write
   a clear outbox note listing the missing coefficient identities.

## Constraints

- No `sorry`, no `axiom`, no `native_decide`.
- Build only:

```bash
lake build QseriesFormalization.Chapter09
```

- If you edit, keep changes local to:
  - `QseriesFormalization/Chapter09.lean`
  - optionally `QseriesFormalization/Exercises.lean` for direct wrappers
- Write final report to `HANDOFF/outbox/batch56-ch09-n4-bailey-mechanical-reply.md`.

## Notes

This is a mechanical/algebraic support task. Leave any large theory decision
or fragile coefficient proof for Codex review.
