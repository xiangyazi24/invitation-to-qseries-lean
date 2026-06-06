Done.

- Added `rogersRamanujanLHSTrunc_three` in `QseriesFormalization/Chapter07.lean`.
- Proof uses definition unfolding and `simp`; no `axiom`, `sorry`, or `native_decide` was added to `Chapter07.lean`.
- Verified:
  - `lake build QseriesFormalization.Chapter07`
  - `lake build`

Note: full `lake build` succeeds, with an existing warning in `QseriesFormalization/Chapter02.lean:98:8` about `sorry`; this task did not touch that file.
