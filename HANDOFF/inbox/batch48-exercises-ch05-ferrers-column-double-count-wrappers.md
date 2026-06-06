Task: add Chapter 5 exercise wrappers for Ferrers column double-counting.

Files:
- Read `QseriesFormalization/Chapter05.lean`.
- Edit only `QseriesFormalization/Exercises.lean`.

Add wrappers in `section Chapter5Exercises` for:
- `PartI.Ch05.mem_FerrersDiagramCellsByColumnsUpTo_iff`
- `PartI.Ch05.FerrersDiagramCellsByColumnsUpTo_eq_of_bound`
- `PartI.Ch05.FerrersDiagramCellsByColumnsUpTo_card`
- `PartI.Ch05.FerrersDiagramCells_card_eq_sum_column_cards_of_bound`
- `PartI.Ch05.FerrersColumnHeightsUpTo_length`
- `PartI.Ch05.partitionWeight_FerrersColumnHeightsUpTo`

Suggested theorem names:
- `exercise5_mem_FerrersDiagramCellsByColumnsUpTo_iff`
- `exercise5_FerrersDiagramCellsByColumnsUpTo_eq_of_bound`
- `exercise5_FerrersDiagramCellsByColumnsUpTo_card`
- `exercise5_FerrersDiagramCells_card_eq_sum_column_cards_of_bound`
- `exercise5_FerrersColumnHeightsUpTo_length`
- `exercise5_partitionWeight_FerrersColumnHeightsUpTo`

Preserve the statement shape from Chapter05 and qualify names with `PartI.Ch05.`.

Constraints:
- No `sorry`, no `axiom`, no `native_decide`.
- Do not touch Chapter05.
- Build only `lake build QseriesFormalization.Exercises`.
- Run `rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean QseriesFormalization/Chapter05.lean`.
- Write result to `HANDOFF/outbox/batch48-exercises-ch05-ferrers-column-double-count-wrappers-reply.md`.
