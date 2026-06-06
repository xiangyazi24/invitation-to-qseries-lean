Task: add Chapter 5 exercise wrappers for Ferrers column upward-closure lemmas.

Files:
- Read `QseriesFormalization/Chapter05.lean`.
- Edit only `QseriesFormalization/Exercises.lean`.

Add wrappers in `section Chapter5Exercises` for:
- `PartI.Ch05.IsPartition.getD_antitone`
- `PartI.Ch05.FerrersCell_of_le_row`
- `PartI.Ch05.FerrersColumnCells_mem_of_le_row`

Suggested theorem names:
- `exercise5_IsPartition_getD_antitone`
- `exercise5_FerrersCell_of_le_row`
- `exercise5_FerrersColumnCells_mem_of_le_row`

Preserve the statement shape from Chapter05 and qualify Chapter05 names with `PartI.Ch05.`.

Constraints:
- No `sorry`, no `axiom`, no `native_decide`.
- Do not touch Chapter05.
- Build only `lake build QseriesFormalization.Exercises`.
- Run `rg -n "sorry|axiom|native_decide" QseriesFormalization/Exercises.lean QseriesFormalization/Chapter05.lean`.
- Write result to `HANDOFF/outbox/batch46-exercises-ch05-ferrers-column-upward-wrappers-reply.md`.
