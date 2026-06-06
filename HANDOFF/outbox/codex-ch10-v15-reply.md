Ch20 Liouville convolution update:

Worked in `QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`.

Verified/confirmed existing pieces:

- `liouvilleQ_eq_parts_union`
- `sum_liouvilleQ_eq_parts`

These already prove the partition

```lean
liouvilleQ n = (eqPart n ∪ gtPart n) ∪ ltPart n
```

and the corresponding `Finset.sum_union` split.

- The analogous `b/d` partition is also present:

```lean
liouvilleQ_eq_bd_parts_union
sum_liouvilleQ_eq_bd_parts
```

- Boundary equations are in the file:

```lean
eqPart_mul_add_eq        -- a = c gives a * (b + d) = n
eqBDPart_add_mul_eq      -- b = d gives (a + c) * b = n
eqPart_eqBDPart_two_mul_eq -- both boundaries give 2 * a * b = n
```

This is the precise Lean form: `a = c` alone gives `a * (b+d) = n`; the
`2*a*b = n` boundary is the common boundary `a=c` and `b=d`.

New work added:

- Fixed existing proof brittleness in the move/bijection block. The file now
  passes; the failing `omega` calls around `leftMove_mem_dGtBPart`,
  `rightMove_mem_bGtDPart`, inverse membership, and inverse-composition lemmas
  were replaced with explicit positivity/record-simplification proofs.

- Added direct bridge theorems from the move bijections to the P-step sums:

```lean
sum_dGtBPart_weightW_eq_sum_gtPart_leftMove_weightW
sum_bGtDPart_weightW_eq_sum_ltPart_rightMove_weightW

four_mul_sum_gtPart_leftMove_weightW_eq_sum_P_step
four_mul_sum_ltPart_rightMove_weightW_eq_sum_P_step
```

These combine the bijections with the proved P-step identities. For example,
the `gtPart` contribution after `leftMove` is now rewritten directly as the
sum over the `d > b` region, then as the `P(b,d)-P(b,d-b)` sum.

Verification:

```bash
lake env lean QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean
```

passes.

Remaining gap:

The actual telescoping collapse of

```lean
∑_{d>b region} (P(b,d) - P(b,d-b))
```

to explicit boundary sums is still not proved. The current file now has the
partition, bijective reindexing, P-step, and boundary equations in usable
theorem form; the next step is to formalize the repeated subtraction/telescope
over the `d` coordinate and identify exactly which boundary terms survive.
