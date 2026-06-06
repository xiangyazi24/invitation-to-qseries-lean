Status: partial, with formal blocker.

Modified `QseriesFormalization/Chapter03.lean`.

Added:

- `qPoch_reflection_two_mul_shifted`: division-free rearranged reflection identity for the centered product
  `qPoch (z / q ^ n) q (2 * n)`.
- `qPoch_reflection_two_mul_unshifted_zero`: the requested unshifted form at `n = 0`.
- `qPoch_reflection_two_mul_unshifted_counterexample_n_one`: formal counterexample showing the requested unshifted
  `(z; q)_{2n}` rearranged identity fails already over `Rat` with `q = 3`, `z = 2`, `n = 1`.

Blocker: the requested theorem

```lean
qPoch z q (2 * n) * q ^ (n * (n + 1) / 2) =
  (-z) ^ n * qPoch (z⁻¹ * q) q n * qPoch z q n
```

is false as stated. At `n = 1`, `q = 3`, `z = 2`, the left side is `15` and the right side is `-1`.

Validation:

```text
Build completed successfully (7908 jobs).
```
