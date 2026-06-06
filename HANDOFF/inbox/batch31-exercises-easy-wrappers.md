# Batch 31: Exercises — easy wrappers for Chapters 6, 8, 10, 12

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Exercises.lean` is currently a flat exercise file. It
already contains small exercises for Chapters 1, 2, 3, 4, 5, 7, 9, 11, 15,
17, and 18.

This batch is mechanical: add small exercise-wrapper theorems for chapters
whose main files already have proved low-index truncation lemmas.

## Goal

Touch only `QseriesFormalization/Exercises.lean`.

Add imports if missing:

```lean
import QseriesFormalization.Chapter06
import QseriesFormalization.Chapter08
import QseriesFormalization.Chapter10
import QseriesFormalization.Chapter12
```

Add these sections near the other exercise sections, preserving existing
style and namespace:

```lean
section Chapter6Exercises

variable {R : Type*} [Field R]

theorem exercise6_dedekindEtaTrunc_one (q : R) :
    PartI.Ch06.dedekindEtaTrunc q 1 = 1 - q :=
  PartI.Ch06.dedekindEtaTrunc_one q

theorem exercise6_dedekindEtaTrunc_two (q : R) :
    PartI.Ch06.dedekindEtaTrunc q 2 = (1 - q) * (1 - q ^ 2) :=
  PartI.Ch06.dedekindEtaTrunc_two q

end Chapter6Exercises
```

For Chapter 8, wrap:

- `PartII.Ch08.D_partialSum_zero`
- `PartII.Ch08.D_trunc_one`

For Chapter 10, wrap:

- `PartII.Ch10.ramanujanMockF_trunc_zero`
- `PartII.Ch10.ramanujanMockF_trunc_one`

For Chapter 12, wrap:

- `PartIII.Ch12.R_trunc_one_eq_inv_one_plus_q`
- `PartIII.Ch12.R_trunc_two_eq`

Use the exact theorem statements from those chapter files. Prefer direct
proofs by `:= ExistingTheorem ...`; avoid re-proving expansions unless needed.

## Validation

Run only:

```bash
lake build QseriesFormalization.Exercises
rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean
```

The build may replay Chapter 2 and print its known `jacobiTripleProduct`
`sorry` warning. That is not introduced by this batch.

## Report

Write `HANDOFF/outbox/batch31-exercises-easy-wrappers-reply.md` with:

- declarations added
- build result
- forbidden-token check result
