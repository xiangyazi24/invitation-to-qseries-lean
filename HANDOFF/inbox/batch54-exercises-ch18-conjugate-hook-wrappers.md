# Batch 54: Exercise wrappers for Ch18 conjugate hook packaging

## Context

Work in `~/.openclaw/workspace/projects/Q-series-and-Chan-s-work`.

`QseriesFormalization/Chapter18.lean` now contains:

- `hasHookDivisibleBy_FerrersConjugatePartition_iff_of_hookLength_eq`
- `isTCoreByHooks_FerrersConjugatePartition_iff_of_hookLength_eq`

These package Ferrers conjugation once hook lengths are known to match under transposed cells.

## Task

Add thin wrappers in `QseriesFormalization/Exercises.lean`, near the other Chapter 18 wrappers:

```lean
theorem exercise18_hasHookDivisibleBy_FerrersConjugatePartition_iff_of_hookLength_eq ...
theorem exercise18_isTCoreByHooks_FerrersConjugatePartition_iff_of_hookLength_eq ...
```

The proofs should call the corresponding `PartIV.Ch18` theorem.

## Constraints

- Touch only `QseriesFormalization/Exercises.lean`.
- No `sorry`, no `axiom`, no `native_decide`.
- Build only:

```bash
lake build QseriesFormalization.Exercises
```

- Write results to:

```text
HANDOFF/outbox/batch54-exercises-ch18-conjugate-hook-wrappers-reply.md
```
