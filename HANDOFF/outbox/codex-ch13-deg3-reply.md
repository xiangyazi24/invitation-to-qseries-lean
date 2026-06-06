# Reply: degree-3 Chan Theorem 11.5 coefficient verification

Done.

Changed `QseriesFormalization/Pending/Chapter13_CoeffVerification.lean`:
- closed `coeff_three_chan_theorem_11_5_LHS_eq_RHS`;
- added the degree-3 coefficient helpers needed by the same pattern as degrees 1 and 2:
  - `(rrcf_r ^ 5).coeff 3 = -30`;
  - `(PowerSeries.expand 5 rrcf_r).coeff 3 = 0`;
  - `(rrcf_v ^ 2).coeff 3 = 0`, `(rrcf_v ^ 3).coeff 3 = 1`, `(rrcf_v ^ 4).coeff 3 = 0`;
  - LHS v-polynomial factor coefficient `2`;
  - RHS v-polynomial factor coefficient `-3`.

The final theorem expands both products with `PowerSeries.coeff_mul` over
`Finset.antidiagonal 3`, rewrites the prepared coefficient values, and closes
by `norm_num`. This gives both side coefficients as `-3`.

Verification run:

```bash
lake env lean QseriesFormalization/Pending/Chapter13_CoeffVerification.lean
```

Result: success. The only remaining warnings are the existing degree 4/5
`sorry` stubs.
