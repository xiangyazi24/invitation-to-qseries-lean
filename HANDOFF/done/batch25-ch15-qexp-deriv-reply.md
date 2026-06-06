Batch 25 completed.

Changes in `QseriesFormalization/Chapter15.lean`:
- Added `qInt_div_qFactorial_succ`.
- Added private helper `qDeriv_pow_div_factorial`.
- Added `qDeriv_qExpTrunc`, proving
  `qDeriv (fun x => qExpTrunc q x (n + 1)) q a = qExpTrunc q a n`.

Validation:
- `lake build QseriesFormalization.Chapter15` completed successfully.
