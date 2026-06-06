# Batch 57: Chapter09 N=4 α₁ Coefficient Split Recon

## Context

Work in `QseriesFormalization/Chapter09.lean`.

Current state:
- N=4 transformed-β / transformed-α expansion scaffolding is present.
- `BaileyTransform_four_alpha_two_coefficient_identity`,
  `BaileyTransform_four_alpha_three_coefficient_identity`, and
  `BaileyTransform_four_alpha_four_coefficient_identity` are proved.
- A direct four-term α₁ common-denominator proof was too heavy: `lake build
  QseriesFormalization.Chapter09` ran for several minutes and the Lean process
  was killed without a Lean error.

## Task

Do not add a huge monolithic `ring` proof.

Please produce a mechanical recon report for the N=4 α₁ coefficient identity:
1. Propose a split into smaller helper identities, preferably by reusing
   existing ratio lemmas and reducing the final polynomial proof size.
2. If you add code, add only small ratio/helper lemmas that build quickly.
3. If a proof takes too long, stop and write the attempted statement plus
   reason it is expensive.

## Constraints

- No `sorry`, no `axiom`, no `native_decide`.
- Build only:

```bash
lake build QseriesFormalization.Chapter09
```

- Keep edits local to `QseriesFormalization/Chapter09.lean`.
- Write final report to
  `HANDOFF/outbox/batch57-ch09-n4-alpha1-split-recon-reply.md`.

## Notes

This is a mechanical algebra support task. The final theory proof will be
reviewed and integrated by Codex.
