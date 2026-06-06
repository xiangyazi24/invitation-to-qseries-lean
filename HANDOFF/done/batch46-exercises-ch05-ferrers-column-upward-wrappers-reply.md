# Batch 46: Chapter 5 Ferrers column upward-closure wrappers

Added the following exercise wrappers to `QseriesFormalization/Exercises.lean`:

- `exercise5_IsPartition_getD_antitone` (wraps `PartI.Ch05.IsPartition.getD_antitone`)
- `exercise5_FerrersCell_of_le_row` (wraps `PartI.Ch05.FerrersCell_of_le_row`)
- `exercise5_FerrersColumnCells_mem_of_le_row` (wraps `PartI.Ch05.FerrersColumnCells_mem_of_le_row`)

## Verification
- `lake build QseriesFormalization.Exercises` completed successfully.
- `rg -n "sorry|axiom|native_decide"` found no matches in `QseriesFormalization/Exercises.lean` or `QseriesFormalization/Chapter05.lean`.
