# Batch 43: Exercises — Ch05 Ferrers card wrappers

## Context

The long-term goal is to formalize Chan's whole book, including exercises.
`QseriesFormalization/Chapter05.lean` now has Ferrers diagram cardinality facts.

This batch was completed locally because Gemini was unstable on the previous
handoff.

## Goal

Expose these facts in `QseriesFormalization/Exercises.lean`:

- `PartI.Ch05.partitionWeight_eq_sum_getD`
- `PartI.Ch05.FerrersDiagramCells_card`

## Validation

Run:

```bash
lake build QseriesFormalization.Exercises
rg -n "sorry|axiom|native_decide" QseriesFormalization/Chapter05.lean QseriesFormalization/Exercises.lean
```

The build may replay Chapter 2 and print its known `jacobiTripleProduct`
`sorry` warning.
