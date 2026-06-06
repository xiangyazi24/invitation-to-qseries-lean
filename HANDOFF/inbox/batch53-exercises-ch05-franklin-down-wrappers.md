# Batch 53: Exercise wrappers for Ch05 Franklin down move

## Context

Work in `~/.openclaw/workspace/projects/Q-series-and-Chan-s-work`.

`QseriesFormalization/Chapter05.lean` now contains the Franklin row-shortening branch:

- `decrementParts`
- `numberOfParts_decrementParts`
- `partSign_decrementParts`
- `partitionWeight_decrementParts_add_numberOfParts`
- `IsPartition_decrementParts`
- `PositiveParts_decrementParts_of_one_lt`
- `HasDistinctParts_decrementParts`
- `IsStrictPartition_decrementParts_of_one_lt`
- `franklinDownMove`
- `numberOfParts_franklinDownMove`
- `partSign_franklinDownMove`
- `partitionWeight_franklinDownMove`
- `IsStrictPartition_franklinDownMove`
- `franklinDownMove_strict_weight_sign`

## Task

Add thin wrappers for the theorem declarations above in `QseriesFormalization/Exercises.lean`, near the existing Chapter 5 wrappers. Use the local naming style:

```lean
theorem exercise5_<source_name> ...
```

The proofs should call the corresponding `PartI.Ch05.<source_name>` theorem.

Do not wrap the two new definitions unless nearby Chapter 5 style already does so for definitions; theorem wrappers are enough.

## Constraints

- Touch only `QseriesFormalization/Exercises.lean`.
- No `sorry`, no `axiom`, no `native_decide`.
- Build only:

```bash
lake build QseriesFormalization.Exercises
```

- Write results to:

```text
HANDOFF/outbox/batch53-exercises-ch05-franklin-down-wrappers-reply.md
```
