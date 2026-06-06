## Chapter20 v21 reply

I continued in `QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`.

Completed the `a/c` partition requested in step (1):

- `eqPart`
- `gtPart`
- `ltPart`
- `mem_eqPart_iff`
- `mem_gtPart_iff`
- `mem_ltPart_iff`
- `liouvilleQ_eq_parts_union`
- `eqPart_disjoint_gtPart`
- `eqPart_disjoint_ltPart`
- `gtPart_disjoint_ltPart`
- `eqGtPart_union_disjoint_ltPart`
- `sum_liouvilleQ_eq_parts`

This gives a disjoint decomposition

`Q_n = eqPart ∪ gtPart ∪ ltPart`

and the corresponding sum decomposition for any integer weight.

I also added the `b/d` partition needed for the target regions:

- `dGtBPart`
- `bGtDPart`
- `eqBDPart`
- `mem_dGtBPart_iff`
- `mem_bGtDPart_iff`
- `mem_eqBDPart_iff`
- `liouvilleQ_eq_bd_parts_union`
- `eqBDPart_disjoint_dGtBPart`
- `eqBDPart_disjoint_bGtDPart`
- `dGtBPart_disjoint_bGtDPart`
- `eqBDDgtPart_union_disjoint_bGtDPart`
- `sum_liouvilleQ_eq_bd_parts`

Completed the `sum_bij'` skeleton from step (2):

- `leftMoveInv`
- `rightMoveInv`
- `leftMove_mem_dGtBPart`
- `rightMove_mem_bGtDPart`
- `leftMoveInv_mem_gtPart`
- `rightMoveInv_mem_ltPart`
- `leftMoveInv_leftMove`
- `leftMove_leftMoveInv`
- `rightMoveInv_rightMove`
- `rightMove_rightMoveInv`
- `sum_gtPart_leftMove`
- `sum_ltPart_rightMove`

So Lean now has actual bijective reindexings:

- `gtPart n` maps to `dGtBPart n` by `leftMove`
- `ltPart n` maps to `bGtDPart n` by `rightMove`

I also lifted the `P`-step to the two strict `b/d` regions:

- `four_mul_weightW_eq_P_step_of_dGtB`
- `four_mul_weightW_eq_P_step_of_bGtD`
- `four_mul_sum_weightW_dGtB_eq_sum_P_step`
- `four_mul_sum_weightW_bGtD_eq_sum_P_step`

These prove the finite-region forms:

`4 * sum_{d>b} W = sum_{d>b} (P(b,d) - P(b,d-b))`

and the symmetric `b>d` version.

Boundary arithmetic added:

- `eqPart_mul_add_eq`
- `eqBDPart_add_mul_eq`
- `eqPart_eqBDPart_two_mul_eq`

Important correction surfaced by formalization: `a = c` alone gives

`a * (b + d) = n`,

not `2ab = n`.  The equation `2ab = n` follows only on the intersection of
the two boundaries `a = c` and `b = d`.

Remaining work:

1. Turn the two strict-region `P`-step sums into the full telescope identity,
   including the cancellation between images and complements.
2. Evaluate the boundary sums over `eqPart` and `eqBDPart` into divisor sums.
3. Combine those boundary evaluations into the final Lahiri/Ramanujan
   `sigma_1 * sigma_3` identity.

Validation:

- `lake env lean QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean` passed.
- `rg -n "sorry|admit|axiom" QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`
  found no matches.
