Implemented the Chapter 10 mock theta coefficient extension in
`QseriesFormalization/Pending/Chapter10_MockTheta_PS.lean`.

Important correction: for the current formal definition

`ramanujanMockSummandPS n = X^(n*n) * (qPoch (-X) X n)⁻¹^2`,

the coefficients through degree 5 stabilize at

`1, 1, -2, 3, -3, 3`,

not `1, 1, 1, 1, 2, 2`.  The positive table is inconsistent with
`(-q;q)_n^2` in the denominator, since the `n = 1` term is
`X / (1 + X)^2`.

Added:
- low-degree vanishing/stabilization lemma reducing degrees `≤ 5` to
  `ramanujanMockFPartialPS 2` for all `N ≥ 2`;
- explicit coefficient theorems for `ramanujanMockFPartialPS 2` at degrees
  `0..5`;
- stabilized coefficient theorems for arbitrary `N ≥ 2` at degrees `1..5`.

Validation:
- `lake env lean QseriesFormalization/Pending/Chapter10_MockTheta_PS.lean`
- `rg -n "\\bsorry\\b|\\baxiom\\b|native_decide" QseriesFormalization/Pending/Chapter10_MockTheta_PS.lean`
