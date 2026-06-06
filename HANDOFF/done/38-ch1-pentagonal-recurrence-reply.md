Task 38 reply

Done.

Changes:
- Added `pentagonalLower`, `pentagonalUpper`, and `partitionCountRec` to `QseriesFormalization/Chapter01.lean`.
- `partitionCountRec` is computed by Euler's pentagonal recurrence from a finite table of earlier values, using `Finset.range n` as the finite bound and `Int` internally for the alternating signs.
- Proved `partitionCountRec n = partitionCount n` for `n = 0..11`, using the existing proved `partitionCount_*` values and kernel `decide`.

Constraints:
- No `sorry`, `axiom`, or `native_decide` added to `Chapter01.lean`.
- Touched only `QseriesFormalization/Chapter01.lean` plus this reply file.

Validation:
- `lake build` completed successfully.
- The build still reports the pre-existing warning at `QseriesFormalization/Chapter02.lean:88:8` about a declaration using `sorry`; this task did not modify that file.
