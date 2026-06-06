# Batch 55: Exercise wrappers for Ch09 transformed-alpha N=1 terms

## Context

Work in `~/.openclaw/workspace/projects/Q-series-and-Chan-s-work`.

`QseriesFormalization/Chapter09.lean` now contains:

- `BaileyTerm_transformAlpha_one_zero`
- `BaileyTerm_transformAlpha_one_one`
- `BaileyBeta_transformAlpha_one_terms`

These are the simplified summands for `BaileyBeta` of the transformed alpha at `N=1`.

## Task

Add thin wrappers in `QseriesFormalization/Exercises.lean`, near the other Chapter 9 wrappers:

```lean
theorem exercise9_BaileyTerm_transformAlpha_one_zero ...
theorem exercise9_BaileyTerm_transformAlpha_one_one ...
theorem exercise9_BaileyBeta_transformAlpha_one_terms ...
```

The proofs should call the corresponding `PartII.Ch09` theorem.

## Constraints

- Touch only `QseriesFormalization/Exercises.lean`.
- No `sorry`, no `axiom`, no `native_decide`.
- Build only:

```bash
lake build QseriesFormalization.Exercises
```

- Write results to:

```text
HANDOFF/outbox/batch55-exercises-ch09-transform-alpha-one-wrappers-reply.md
```
