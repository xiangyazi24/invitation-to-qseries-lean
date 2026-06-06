# codex-ch15-v5 reply

Status: blocked; final Wronskian `sorry` not closed.

Edited:

- `QseriesFormalization/Pending/Chapter15_WronskianBridge.lean`

What was added:

- `rogers_ramanujan_wronskian_cleared_of_pentagonal_level`

This proves the reverse direction of the v4 algebra bridge:

```lean
theorem rogers_ramanujan_wronskian_cleared_of_pentagonal_level
    (hpent :
      pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
        5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
             pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ)) =
      (qPochInfPS ℚ) ^ 6) :
    rrProductA ℚ * rrProductB ℚ +
      5 * (rrProductB ℚ * thetaOp (rrProductA ℚ) -
           rrProductA ℚ * thetaOp (rrProductB ℚ)) =
    (qPochInfPS ℚ) ^ 4 * (rrProductA ℚ) ^ 2 * (rrProductB ℚ) ^ 2
```

The proof rewrites `P14 = A*C`, `P23 = B*C`, expands both theta derivatives
with `thetaOp_mul`, and cancels the unit `C^2`, where
`C = qPochAPPS ℚ 5 5`.

What I verified in the codebase:

- The formal Jacobi cube identity already exists:
  `QseriesFormalization.Pending.JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS`.
- The square corollary also exists:
  `qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two`.
- Therefore the missing piece is exactly the finite double-sum reindex proving
  the pentagonal-level Wronskian equals `(jacobiThetaPS ℚ)^2`.

Blocker:

The proposed change-of-variables route is not a direct coefficient-preserving
bijection as stated. In particular, for `m = 1`, `n = 0`:

```text
alpha = 1, beta = 0
x = 7, y = -1
R = 1, S = -3
|R| = 1, |S| = 3, so r = 0, s = 1

(-1)^(m+n) * (1 + 5*(alpha-beta)) = -6
(-1)^(r+s) * (2*r+1) * (2*s+1) = -3
```

So step 6 of the proposed plan needs an additional grouping/multiplicity
argument; it is not a plain Finset bijection from `(m,n)` to `(r,s)`.

Verification command:

```bash
lake env lean QseriesFormalization/Pending/Chapter15_WronskianBridge.lean
```

Result: success, with the one remaining direct local warning:

```text
QseriesFormalization/Pending/Chapter15_WronskianBridge.lean:295:8: warning: declaration uses 'sorry'
```
