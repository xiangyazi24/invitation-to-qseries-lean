Implemented the finite Taylor bridge in
`QseriesFormalization/Pending/RR_TaylorBridge.lean`.

What is proved:

- `analyticAt_rrJInf_one_zero`:
  `fun q : ℂ => rrJInf 1 q` is analytic at `0`, using the analytic product
  identity with `pentagonal023_analytic / qPochhammer_inf`.
- `rrJInf_one_sub_inv_one_sub_isBigO`:
  `rrJInf 1 q - (1 - q)⁻¹ =O[𝓝 0] fun q => ‖q‖ ^ 4`.
- `rrJInf_one_taylorCoeff_eq_rrGPS_coeff_of_lt_four`:
  for any Taylor FMLS `p` of `rrJInf 1` at `0`,
  `n < 4 → p.coeff n = ((rrGPS).coeff n : ℂ)`.
- `exists_rrJInf_one_taylor_coeffs_agree_to_order_four`:
  packages the analytic expansion and coefficient agreement through degree `3`.

This is option (B) in the fallback finite range, not the full all-coefficients
termwise Taylor bridge.

Validation:

```bash
lake env lean QseriesFormalization/Pending/RR_TaylorBridge.lean
```

The command passes. The new file contains no `sorry`, `axiom`, or `admit`.
