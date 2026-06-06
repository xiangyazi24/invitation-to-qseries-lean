Implemented the coefficientwise Jacobi-cube reduction in
`QseriesFormalization/Pending/Chapter15_WronskianBridge.lean`.

Added:

- `pentagonalWronskianCoeff N`: the Cauchy-product coefficient of
  `P14*P23 + 5*(P23*theta(P14) - P14*theta(P23))`.
- `jacobiThetaSquareCoeff N`: the Cauchy-product coefficient of
  `(jacobiThetaPS ℚ)^2`.
- `coeff_pentagonal_wronskian_lhs`: proves the first definition is exactly the
  coefficient of the pentagonal-level Wronskian LHS.
- `coeff_jacobiThetaPS_sq`: proves the second definition is exactly the
  coefficient of `(jacobiThetaPS ℚ)^2`.
- `wronskian_at_pentagonal_level_of_coeff_identity`: if
  `∀ N, pentagonalWronskianCoeff N = jacobiThetaSquareCoeff N`, then the
  pentagonal-level Wronskian follows using
  `qPochInfPS_pow_six_eq_jacobiThetaPS_pow_two`.
- `pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff_le_fifty`: native
  computation verifies the coefficient identity for all `N ≤ 50`.

Build command:

```bash
lake env lean QseriesFormalization/Pending/Chapter15_WronskianBridge.lean
```

Result: succeeds. The only warning is the pre-existing
`rogers_ramanujan_wronskian_cleared` `sorry`.

I did not close the all-`N` finite double-sum identity. The direct
term-by-term matching is still the hard point: the new Lean code reduces the
Wronskian to exactly that Nat-level coefficient identity, and verifies it
computationally through degree 50, but does not prove the required global
regrouping/cancellation theorem.
