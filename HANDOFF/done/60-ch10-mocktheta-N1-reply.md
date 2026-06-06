Task 60 complete.

Changed `QseriesFormalization/Chapter10.lean`:

- Added `ramanujanMockF_trunc_one`.
- Proof uses only unfolding/simplification of `ramanujanMockF_trunc`, `natSum`, and `qPoch`.
- No `axiom`, `sorry`, or `native_decide` added.

Validation:

- `lake build` completed successfully.
- Build still reports the pre-existing `Chapter02.lean:98:8` declaration-uses-`sorry` warning; this task did not touch Chapter 2.
