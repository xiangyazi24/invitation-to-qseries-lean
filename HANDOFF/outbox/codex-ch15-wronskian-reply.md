# Reply: Ch15 Wronskian identity

Created `QseriesFormalization/Pending/Chapter15_Wronskian.lean`.

The requested theorem is false as stated with the repository definitions.
`pentagonal014SeriesPS` and `pentagonal023SeriesPS` are the JTP series
`(q,q^4,q^5;q^5)_∞` and `(q^2,q^3,q^5;q^5)_∞`, so they already include the
`E5 = (q^5;q^5)_∞` factor. They are not the E5-free Rogers-Ramanujan products.

I formalized the degree-5 counterexample over `ℚ⟦X⟧`:

- `coeff_wronskianPentagonalLHS_five`:
  the requested Wronskian LHS has coefficient `0` at degree `5`.
- `coeff_wronskianPentagonalClaimedRHS_five`:
  the requested RHS `E^4 * P14^2 * P23^2` has coefficient `-2` at degree `5`.
- `rogers_ramanujan_wronskian_cleared_as_stated_false`:
  the two formal power series are unequal.

The file uses the existing product identity
`pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ =
qPochInfPS ℚ * expand 5 (qPochInfPS ℚ)` to rewrite the claimed RHS as
`E^6 * E5^2`, which exposes the extra `E5^2` factor.

Validation:

```bash
lake env lean QseriesFormalization/Pending/Chapter15_Wronskian.lean
```

passed.

No `sorry`, `axiom`, or `native_decide` was added to the new file.
