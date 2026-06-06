Implemented Task 58.

- Updated `QseriesFormalization/Chapter08.lean`.
- Added `D_partialSum` as the finite Rogers-Ramanujan partial sum
  `natSum (fun n => q ^ (n * n + a * n) / qPochhammer q n) N`.
- Added `D_partialSum_zero`.
- Replaced the placeholder recursive `D_trunc` with an alias to `D_partialSum`.
- Kept `D_trunc_zero` as a simp theorem.

Validation:

- `lake build` completed successfully.
- `QseriesFormalization/Chapter08.lean` contains no `sorry`, `axiom`, or `native_decide`.

Note: the build still reports the pre-existing `Chapter02.lean` sorry warning.
