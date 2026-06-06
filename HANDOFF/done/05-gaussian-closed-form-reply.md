Status: done.

Modified `QseriesFormalization/Chapter03.lean` only for the Lean proof work.

Added intermediate lemma:

- `qPochhammer_eq_pred_mul`: expands `(q;q)_n` as `(q;q)_{n-1} * (1 - q^n)` under `0 < n`.

Added target theorem:

- `gaussianBinom_mul_qPochhammer_eq`

Proof method:

- induction on `n`;
- boundary cases `m = 0` and `m = n + 1` by simplification and `gaussianBinom_self`;
- middle case uses the defining q-Pascal recursion, two induction hypotheses, `qPochhammer_eq_pred_mul`, and ring normalization.

Validation:

```text
Build completed successfully (7908 jobs).
```
