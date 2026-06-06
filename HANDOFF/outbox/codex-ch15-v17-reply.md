Status: not closed.

I added the local `t=0` bridge pieces in
`QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean`.
The only remaining `sorry` is still the final coefficient theorem.

New successful pieces:

- Blueprint variables:
  - `pentagonalX m = 10*m - 3`
  - `pentagonalY n = 10*n - 1`
  - `pentagonalToGauss_R_eq`:
    `A-B = (x+2y)/5`
  - `pentagonalToGauss_S_eq`:
    `A+B = (-2x+y)/5`

- Jacobi sector formulas:
  - `jacobiToGauss_R_eq`: `A-B = 2*s+1`
  - `jacobiToGauss_S_eq`: `A+B = 2*r+1`
  - `jacobiToGauss_swap`: swapping `(r,s)` is Gaussian conjugation.

- Norm/exponent bridge:
  - `pentagonalToGauss_norm_of_exp_sum`
  - `jacobiToGauss_norm_of_tri_sum`
  - `pentagonalToGauss_RS_sq_sum`
  - `jacobiToGauss_RS_sq_sum`
  These put both sides on the same norm shell `A^2+B^2 = 4N+1`.

- Pentagonal row-0 selector bridge:
  - `pentagonalToGauss_rot0_selector`
  - `gaussK_pentagonalToGauss_eq_row0`
  - `pentagonalCoeffPairWeight_eq_gaussK`
  So each expanded pentagonal term is now literally a `gaussK` value at
  `pentagonalToGauss m n`.

- `t=0` orbit bridge:
  - `unitConjOrbitH_eq_eight_gaussH_of_norm_odd`
  - `unitConjOrbitK_eq_eight_gaussH_of_t0`
  - `gaussK_pair_eq_gaussH_pair_sum_t0`
  The last one is the useful local form:
  ```lean
  gaussK (a,b) + gaussK (a,-b) = gaussH (a,b) + gaussH (a,-b)
  ```
  assuming `a^2+b^2` is odd and not divisible by `5`.

- Residue table for the remaining sign/swap grouping:
  - `rsSignSumK`
  - `rsSwapOrbitK`
  - `rsJacobiWeight`
  - `rsSwapOrbitH`
  - `rsSwapOrbit_t0_residue_check`

The residue check proves the desired `t=0` sign/swap orbit equality modulo
`20` for odd `R,S` with `(R^2+S^2)/2` not divisible by `5`.

What remains:

The final bridge needs a lifted version of the residue table:

```lean
rsSwapOrbitK R S = rsSwapOrbitH R S
```

for arbitrary positive odd `R,S` with `((R^2+S^2)/2) % 5 ≠ 0`, then a finite
sum reindexing from:

```lean
(m,n)  ↔  selected signed/swap (R,S)
(r,s)  ↔  positive ordered odd (R,S)
```

I tried the direct `R = 20*q + r`, `S = 20*q' + s` lift with
`interval_cases`; the naive 400-case automation hit a heartbeat timeout at
2,000,000. It likely needs smaller fixed-residue lemmas, not one giant tactic
block.

Verification:

```bash
lake env lean QseriesFormalization/Pending/Chapter15_WronskianIndependent.lean
```

Result: succeeds, with only the final `sorry` warning.
