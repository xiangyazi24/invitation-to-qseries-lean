# Reply: degree-1 Chan Theorem 11.5 coefficient verification

Done.

Changed `QseriesFormalization/Pending/Chapter13_CoeffVerification.lean`:
- closed `coeff_one_chan_theorem_11_5_LHS_eq_RHS`;
- added private coefficient helpers for:
  - `(rrcf_r ^ 5).coeff 0 = 1` and `(rrcf_r ^ 5).coeff 1 = -5`;
  - `(expand 5 rrcf_r).coeff 0 = 1` and `.coeff 1 = 0`;
  - degree-0/1 coefficients of the two Chan polynomial factors in `rrcf_v`.

Verification run:

```bash
export PATH=$HOME/.elan/bin:$PATH
lake env lean QseriesFormalization/Pending/Chapter13_CoeffVerification.lean
```

Result: success. The only remaining warnings are the intended degree 2-5 `sorry` stubs:

```text
QseriesFormalization/Pending/Chapter13_CoeffVerification.lean:364:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter13_CoeffVerification.lean:371:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter13_CoeffVerification.lean:378:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter13_CoeffVerification.lean:385:8: warning: declaration uses 'sorry'
```
