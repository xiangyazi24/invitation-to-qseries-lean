Status: not closed.

I continued the direct finite-sum bridge in
`QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean`.
The file still has exactly the original final `sorry`:

```lean
theorem pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff
```

What is now proved and compiling:

1. Jacobi coefficient expansion:
   - `triangularIndex_injective`
   - `jacobiTripleSign_eq_sum_range_of_le`
   - `jacobiTripleSign_rat_eq_sum_range_of_le`
   - `jacobiThetaSquareCoeffExpanded`
   - `jacobiThetaSquareCoeff_eq_expanded`

2. Pentagonal/Wronskian coefficient expansion:
   - `pentagonal014Coeff_eq_sum_Icc_of_le`
   - `pentagonal023Coeff_eq_sum_Icc_of_le`
   - `antidiagonal_indicator_product`
   - `antidiagonal_indicator_product_rightWeight`
   - `pentagonalWronskianCoeffExpanded`
   - `pentagonalWronskianCoeff_eq_expanded`

3. Gaussian change-of-variable local algebra:
   - `jacobiToGauss_H`
   - `jacobiToGauss_norm`
   - `pentagonalToGauss_norm`
   - `pentagonalWeight_ediv_eq`
   - `pentagonalToGauss_wronskianCoeffWeight`
   - `jacobiExpandedWeight_eq_gaussH`
   - `pentagonalCoeffPairWeight_eq_wronskianRSWeight`

The current reduced target is now exactly:

```lean
pentagonalWronskianCoeffExpanded N = jacobiThetaSquareCoeffExpanded N
```

Interpreting the two sides:

- `jacobiThetaSquareCoeffExpanded N` sums `gaussH` over the Jacobi sector
  representatives
  `(A,B) = (r+s+1, r-s)`, i.e. `A+B = 2r+1 > 0` and
  `A-B = 2s+1 > 0`.
- `pentagonalWronskianCoeffExpanded N` sums the row-0 Wronskian selector over
  `(A,B) = (-k+3l, -3k-l+1)`, with
  `A^2+B^2 = 4N+1`.

So the remaining proof is no longer coefficient plumbing. It is the finite
Gaussian orbit/sector reindexing:

```lean
∑ row0-selector K over norm 4N+1
  =
∑ Jacobi-sector H over norm 4N+1
```

The earlier local t=0 orbit theorem is still available:

```lean
fiveString_t0_unitConjOrbit_identity
```

but it has not yet been connected to the two canonical finite representative
sets above. A direct single-term bijection is false: for example at `N = 1`,
one pentagonal term of weight `-6` corresponds to the two Jacobi sector terms
of weights `-3` and `-3`. The next proof step should therefore group by
unit/conjugation orbits and prove that each orbit contributes one quarter of
`unitConjOrbitK` on the pentagonal selector side and one quarter of
`unitConjOrbitH` on the Jacobi sector side.

Verification run:

```bash
lake env lean QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean
```

Result: succeeds, with only the final `sorry` warning.
