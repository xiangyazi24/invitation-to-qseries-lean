Ch20 Liouville convolution update:

Worked in `QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`.

The `Finset.sum_bij` step now compiles in explicit specialized form:

```lean
theorem sum_gtPart_leftMove_weightW_eq_sum_dGtBPart_weightW
theorem sum_ltPart_rightMove_weightW_eq_sum_bGtDPart_weightW
```

These are the precise statements for the current `leftMove`/`rightMove`
definitions.  Since `leftMove` changes `d` to `b+d`, the transported summand is
`weightW (leftMove q)`, not literally `weightW q` on `gtPart`.

The P-step has also been pushed into the original strict regions:

```lean
theorem sum_dGtB_P_step_eq_sum_gtPart_leftMove_P_step
theorem sum_bGtD_P_step_eq_sum_ltPart_rightMove_P_step
theorem four_mul_sum_gtPart_leftMove_weightW_eq_gtPart_P_step
theorem four_mul_sum_ltPart_rightMove_weightW_eq_ltPart_P_step
```

The file also contains a compiled telescope/reindex collapse at the strict
region level:

```lean
theorem sum_dGtB_P_lower_eq_sum_gtPart_P
theorem sum_bGtD_P_lower_eq_sum_ltPart_P
theorem four_mul_sum_weightW_dGtB_telescope
theorem four_mul_sum_weightW_bGtD_telescope
theorem two_mul_strict_bd_P_difference_eq_boundary_P_difference
theorem four_mul_sum_strict_bd_weightW_eq_boundary_P_difference
```

This uses the already-proved bijections plus swap symmetry to turn the strict
`d>b` and `b>d` P-step sums into the boundary difference
`eqPart - eqBDPart`.

Finally, the file now has the boundary-weight consequences:

```lean
theorem four_mul_sum_eqBDPart_weightW_eq_boundary
theorem four_mul_liouvilleWSum_eq_boundary
theorem eight_mul_liouvilleBD3Sum_eq_boundary
```

So the Liouville-side weighted sum is reduced to boundary sums:

```lean
8 * liouvilleBD3Sum n =
  (∑ q ∈ eqPart n, liouvilleP (q.b : Int) (q.d : Int)) -
    ∑ q ∈ eqBDPart n, (q.b : Int) ^ 4
```

Verification:

```bash
lake env lean QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean
```

passes.

Remaining gap:

The remaining step is evaluating the two boundary sums explicitly in divisor
sigma form, then connecting `liouvilleBD3Sum` back to the original
`sigma_1 * sigma_3` convolution beyond the current finite check scaffold.
