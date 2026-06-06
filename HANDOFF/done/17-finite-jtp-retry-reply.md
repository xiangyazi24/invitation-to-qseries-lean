status: partial

diff summary:
- Added `finite_jacobi_triple_product_two`, a complete concrete verification of Chan Eq. 3.15 for `n = 2`.
- Added the main substitution infrastructure:
  - `triangular_succ_add`
  - `qPoch_succ_front`
  - `one_sub_div_qpow_succ`
  - `qPoch_substitute_div_qpow`
  - `qPoch_substitute_div_qpow_two_mul`
- The new `qPoch_substitute_div_qpow_two_mul` proves the product-side transformation used by Chan after substituting `z -> z / q^n` and splitting at `n`.

validation:
- `lake build`
- final line: `Build completed successfully (7908 jobs).`
- `rg -n "\b(sorry|axiom|native_decide)\b" QseriesFormalization/Chapter03.lean` returned no matches.

blocker:
- The remaining general theorem is blocked at the termwise reindexing of the q-binomial sum into `finiteJTPSummand`.
- The precise arithmetic subgoal needed for the q-exponent normalization is:

```lean
((((k : Int) - (n : Int)) * (((k : Int) - (n : Int)) - 1) / 2).toNat) + n * k =
  k * (k - 1) / 2 + triangular n
```

under `k ≤ 2 * n`, together with the matching Laurent monomial normalization

```lean
(-z : R) ^ n * (-z : R) ^ ((k : Int) - (n : Int)) = (-z : R) ^ k
```

using `z ≠ 0`.

The product-side Chan substitution is now proved; the unresolved part is only the bilateral-index sum algebra caused by `Int` division plus `.toNat` in `finiteJTPSummand`.
