Status: partial.

Touched only `QseriesFormalization/Chapter03.lean`.

Added the explicit `n = 3` finite Jacobi triple product check:

- `finite_jacobi_triple_product_three`

The proof follows the existing `n = 1`/`n = 2` style: unfold the finite
definitions with `norm_num`, clear the inverse of `z` using `field_simp [hz]`,
normalize the remaining constant `Int.toNat` exponents for `3` and `6`, then
finish by `ring_nf`.

I also tried the fresh direct arithmetic route for the original general
reindexing subgoal. The direct `omega`/`ring_nf` probes do not close it: the
blocker is still bridging the division-by-2 parity facts and `Int.toNat`
nonnegativity through the Nat/Int expression

```lean
((((k : Int) - (n : Int)) * (((k : Int) - (n : Int)) - 1) / 2).toNat) + n * k =
  k * (k - 1) / 2 + triangular n
```

No `axiom`, `sorry`, or `native_decide` was added to `Chapter03.lean`.

Validation:

- `lake build QseriesFormalization.Chapter03` passes.
- `lake build` passes. It reports the existing warning in `Chapter02.lean:98:8`
  that a declaration uses `sorry`; this is outside the touched file.
- `rg -n "sorry|axiom|native_decide" QseriesFormalization/Chapter03.lean`
  returns no matches.
