## Chapter20 v20 reply

I created `QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`.

I did not complete the full Liouville telescope/boundary evaluation.  The new
file formalizes the mechanical scaffold needed for that proof and keeps it
independent of `Chapter20_Eisenstein.lean` so it can be checked directly.

Completed pieces:

- `sigmaPowZ`
- `sigma1Sigma3ConvZ`
- `sigmaPowZ_eq_sum_factorPairs_right_of_pos_le`
- `sigma1Sigma3FactorPairRightSplitSumZ`
- `sigma1Sigma3ConvZ_eq_factorPairRightSplitSumZ`

The factor-pair theorem uses the right factor as the divisor variable, so it
matches the Liouville weight `b*d^3`.

Four-tuple setup:

- `LQuad`
- `liouvilleBox`
- `liouvilleQ`
- `mem_liouvilleBox_iff`
- `mem_liouvilleQ_iff`

Swap symmetry:

- `swapQuad`
- `swapQuadEquiv`
- `swapQuad_mem_liouvilleQ_iff`
- `sum_swap_liouvilleQ`
- `two_mul_liouvilleBD3Sum_eq_liouvilleWSum`

This proves the clean formal version of

`2 * sum_Q b*d^3 = sum_Q b*d*(b^2+d^2)`.

Polynomial step:

- `liouvilleP`
- `liouvilleWBD`
- `liouvilleP_step_int`
- `liouvilleP_step_nat`

This proves

`P(b,d) - P(b,d-b) = 4*b*d*(b^2+d^2)`

with the Nat version using `Nat.cast_sub`.

Liouville transformations:

- `leftMove`
- `rightMove`
- `leftMove_mem_liouvilleQ`
- `rightMove_mem_liouvilleQ`

These prove that the two transformations from the prompt preserve membership
in `Q_n` under the side conditions `c < a` and `a < c`:

- `(a,b,c,d) -> (a-c,b,c,b+d)`
- `(a,b,c,d) -> (a,b+d,c-a,d)`

Sanity check:

- `factorPairRightSplitMatchesQ`
- `factorPairRightSplitMatchesQThrough8Check_true`

This executable check confirms through `n <= 8` that the right-factor
factor-pair split sum agrees with the `Q_n` sum weighted by `b*d^3`.  I kept
this bound small because the naive `Q_n` enumeration is quartic.

Remaining work:

1. Prove `factorPairRightSplitMatchesQ` for all `n` by reindexing the split
   sum over `k,a,b,c,d` into `liouvilleQ n`.
2. Partition `liouvilleQ n` by `a = c`, `a > c`, and `c > a`.
3. Use `leftMove`/`rightMove` as actual `Finset.sum_bij` bijections against
   the `d > b` / `b > d` regions.
4. Evaluate the boundary sums (`a = c` and `b = d`) into divisor sums.

Validation:

- `lake env lean QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean` passed.
- `rg -n "sorry|admit|axiom" QseriesFormalization/Pending/Chapter20_LiouvilleConvolution.lean`
  found no matches.
