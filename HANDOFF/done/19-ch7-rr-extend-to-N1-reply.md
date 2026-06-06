Status: done

Changed only `QseriesFormalization/Chapter07.lean`.

Added:
- `rogersRamanujanLHSTrunc_one` with corrected exponent `q ^ (1 + a) / (1 - q)`.
- `rogersRamanujanRHSTrunc_one_a0`.
- `rogersRamanujanRHSTrunc_one_a1`.

Validation:
- `lake build`
- Final line: `Build completed successfully (7908 jobs).`

Note:
- The build still reports the pre-existing `Chapter02.lean:88:8: declaration uses 'sorry'` warning.
