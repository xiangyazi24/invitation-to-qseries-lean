Implemented the local t=0 orbit proof in
`QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean`.

New proved pieces:

- `wronskianSelector_exists_zmod5`
- `wronskianSelector_exists_int`
- `gaussK_t0_core`
- `gaussK_conj_pair_t0_identity`
- `unitConjOrbitK_closed`
- `fiveString_t0_unitConjOrbit_identity`

The t=0 theorem now proves, for odd norm and norm prime to 5:

```lean
unitConjOrbitK (a,b) = unitConjOrbitH (a,b)
```

I also added the local t>0 interior K-vanishing fact:

- `gaussK_of_five_dvd_coords`
- `unitConjOrbitK_of_five_dvd_coords`
- `fiveStringPoint_interior_factor_five`
- `fiveStringPoint_interior_unitConjOrbitK_zero`

The last theorem proves that the interior point
`fiveStringPoint g (j + k + 2) (j + 1)` has zero `unitConjOrbitK`, because
it contains the factor `π * πbar = 5`.

Verification:

```bash
lake env lean QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean
```

Result: succeeds, with only the existing final warning:

```text
Chapter15_WronskianIndependent.lean:747:8: warning: declaration uses 'sorry'
```

I did not close `pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff`.  The
remaining missing bridge is no longer the local orbit table; it is the
coefficient-level reindexing/partition that identifies
`pentagonalWronskianCoeff` and `jacobiThetaSquareCoeff` with the Gaussian
orbit/string sums.  No such bridge is currently present in this file or in the
searched handoff material.
