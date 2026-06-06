# Theorem 4.3 (Jacobi's identity) — strategy

**Statement**: `(q;q)_∞^3 = ∑_{n=0}^∞ (-1)^n (2n+1) q^{n(n+1)/2}` for `‖q‖ < 1`.

## Derivation (verified 2026-05-13)

Work with `Q : ℂ` satisfying `Q² = q`. The final wrapper uses
`Complex.exists_sq` to lift `q → Q`.

JTP at base `Q` and parameter `z`:
```
J(Q, z) := jacobiInfiniteProduct Q z = jacobiInfiniteSeries Q z
        = ∑_{n∈ℤ} z^n · Q^{n²}
        = ∏_{n≥1} (1 - Q^{2n})(1 + z Q^{2n-1})(1 + z⁻¹ Q^{2n-1}).
```

At `z = -Q`, both sides vanish (factor `(1 + z⁻¹ Q) = (1 - 1) = 0` for the
`n = 1` odd-pair, and pair-cancellation `n ↔ -n-1` on the series).

Differentiate in `z`, then evaluate at `z = -Q`.

### Series side derivative

```
dS/dz = ∑_{n∈ℤ} n · z^{n-1} · Q^{n²}.
dS/dz|_{z=-Q} = -Q⁻¹ · ∑_{n∈ℤ} n · (-1)^n · Q^{n(n+1)}
              = -Q⁻¹ · ∑_{n≥0} (2n+1) · (-1)^n · q^{n(n+1)/2}    (use Q² = q)
```
The last step pairs `n ↔ -n-1` in the bilateral sum: both have the same
exponent `n(n+1)`, and combined contribution is `(2n+1)(-1)^n`.

### Product side derivative

Factor out the vanishing `(1 + z⁻¹ Q)` from the `n = 1` term:
```
P(z) = (1 + z⁻¹ Q) · P_mod(z)
```
where `P_mod(z) = ∏_{n≥1}(1 - Q^{2n}) · ∏_{n≥1}(1 + z Q^{2n-1}) · ∏_{n≥2}(1 + z⁻¹ Q^{2n-1})`.

`P_mod(-Q)`:
- Even factor `∏(1 - Q^{2n}) = (Q²;Q²)_∞ = (q;q)_∞`.
- First odd `∏(1 + zQ^{2n-1})|_{z=-Q} = ∏(1 - Q^{2n}) = (q;q)_∞`.
- Second odd from `n≥2`: `∏_{n≥2}(1 - Q^{2n-2}) = ∏_{m≥1}(1 - Q^{2m}) = (q;q)_∞`.

So `P_mod(-Q) = (q;q)_∞^3`.

```
dP/dz|_{z=-Q} = d/dz(1 + z⁻¹ Q)|_{z=-Q} · P_mod(-Q) + 0
              = (-z⁻² Q)|_{z=-Q} · (q;q)_∞^3
              = -Q⁻¹ · (q;q)_∞^3.
```

### Conclusion

`dS/dz|_{z=-Q} = dP/dz|_{z=-Q}` (JTP) gives:
```
-Q⁻¹ · ∑_{n≥0} (2n+1)(-1)^n q^{n(n+1)/2} = -Q⁻¹ · (q;q)_∞^3.
```
Cancel `-Q⁻¹` (`Q ≠ 0` from `Q² = q` and `q ≠ 0`):
```
∑_{n≥0} (2n+1)(-1)^n q^{n(n+1)/2} = (q;q)_∞^3.   ∎
```

## Lean formalization plan

### Phase 1 — series-side derivative
1. `jacobiSeriesTermDeriv Q z n := n * z^(n-1) * Q^(n²)` (zpow over ℤ).
2. Show `Summable (fun n : ℤ => ‖jacobiSeriesTermDeriv Q z n‖)` for `‖Q‖ < 1` and `z ≠ 0`.
3. `HasDerivAt (fun z => jacobiInfiniteSeries Q z) (∑'_n jacobiSeriesTermDeriv Q z n) z` for `z ≠ 0`.
   - Termwise differentiation via `HasDerivAt.tsum` (Mathlib has variants).
4. Evaluate at `z = -Q`: arithmetic identity
   ```
   ∑'_{n∈ℤ} n (-Q)^(n-1) Q^(n²) = -Q⁻¹ · ∑_{n≥0} (2n+1)(-1)^n q^(n(n+1)/2)
   ```
   via pair-up `n ↔ -n-1` and Q² = q rewrite.

### Phase 2 — product-side derivative
5. Define `P_mod Q z := ∏'(1-Q^{2n}) · ∏'(1+zQ^{2n-1}) · ∏'_{n≥1}(1+z⁻¹Q^{2n+1})`
   (the odd₂ product shifted by one).
6. Show `jacobiInfiniteProduct Q z = (1 + z⁻¹ Q) · P_mod Q z` for `z ≠ 0`.
7. Evaluate `P_mod Q (-Q) = (q;q)_∞^3` using Q² = q and reindexing on each
   of the three sub-products.
8. `HasDerivAt (fun z => jacobiInfiniteProduct Q z)
        (-(-Q)⁻² Q · (q;q)_∞^3) (-Q)`
   from product-rule on `(1+z⁻¹Q) · P_mod Q z` at z=-Q, where
   `(1 + z⁻¹ Q)|_{z=-Q} = 0` makes the `P_mod` derivative term drop out.

### Phase 3 — combine
9. From JTP, the two functions `z ↦ S(Q,z)` and `z ↦ P(Q,z)` are equal on
   a neighborhood of `-Q`, so their derivatives agree at `-Q`.
10. Conclude `(q;q)_∞^3 = ∑_{n≥0} (2n+1)(-1)^n q^{n(n+1)/2}` after
    canceling `-Q⁻¹` on both sides.

### Phase 4 — Q-free wrapper
11. From `q ≠ 0`, `Complex.exists_sq q` gives `∃ Q, Q² = q`. Apply
    Phase 3.

## Estimated effort

Phases 1-2 are the heavy lift (analytic infrastructure for termwise
differentiation of `tsum`/`tprod` over `ℤ`). Probably 300-500 lines
of Lean. Phase 3 is the algebraic finale, ~50 lines. Phase 4 is a
one-line lift.

A pragmatic interim: prove the parameterized version
`jacobi_identity_at_Q (Q : ℂ) (hQ : ‖Q‖ < 1) (hQ0 : Q ≠ 0) :
  (q;q)_∞^3 = Jacobi sum` (taking `q := Q²` from hypothesis) and leave
the `exists_sq` wrapper for later.

## Phase 2 implementation notes (2026-05-13)

**Status**: Phase 1 fully proved. Phase 2 scaffolding (vanishing-factor derivative,
generic `hasDerivAt_mul_of_left_vanish`) committed. Core factorization theorem
`jacobiInfiniteProduct = (1 + z⁻¹·Q) * P_mod` was attempted but ran into Lean
elaboration timeouts. Diagnosis below.

### Gotcha: ℂ is CommMonoid but not CommGroup multiplicatively

`Multipliable.tprod_eq_zero_mul` (which extracts the `k=0` term of an infinite
product over ℕ) requires `[CommGroup G]`. This is because internally it uses
`multipliable_nat_add_iff` which uses `Equiv.mulRight (∏ i ∈ range k, f i)`.
**ℂ has no group inverse for 0, so this lemma does NOT directly apply.**

When trying to use it, Lean's elaborator searches for a `CommGroup ℂ` instance
indefinitely, producing whnf timeouts (200K, 1.6M, 4M heartbeats all insufficient).

### Workaround for shift extraction

Use `tprod_eq_zero_mul'` instead, which only requires
`Multipliable (fun n => f (n + 1))` (the shifted version):

```
theorem tprod_eq_zero_mul'
    {f : ℕ → M} (hf : Multipliable (fun n ↦ f (n + 1))) :
    ∏' b, f b = f 0 * ∏' b, f (b + 1)
```

`M : CommMonoid` only. ℂ works. To produce the shifted multipliability,
rebuild from `multipliable_one_add_of_summable` with a local proof of summability
of the shifted family (geometric decay `‖z‖ · ‖Q‖^(2k+3)`).

### Next steps for Phase 2

1. **Construct local summability**: For `Q, z : ℂ`, `‖Q‖ < 1`, prove
   `Summable fun k : ℕ => ‖z * Q^(2*(k+2) - 1)‖`. Geometric.
2. **Derive shifted multipliability**: Apply `multipliable_one_add_of_summable`.
3. **Apply `tprod_eq_zero_mul'`** to get the split.
4. **Compose three factors** via three `tprod_mul`s with multipliability witnesses
   from Ch02 (`multipliable_jacobiProductEvenFactor`, `multipliable_jacobiProductOddFactor`).
5. **Evaluate `P_mod(-Q)`**: needs evaluating each of the three tprods at `z = -Q`
   and matching with `(qPoch q q)^3`. The first/third sub-tprods both reindex to
   `(q;q)_∞` after substituting `z = -Q`. Heavy reindex work.
6. **Continuity of `P_mod` at `-Q`**: each sub-tprod is `tprod_continuous` on its
   convergence region. Use `Continuous.continuousAt`.
7. **Final**: apply `hasDerivAt_mul_of_left_vanish` with `g(z) = 1 + z⁻¹·Q`,
   `R(z) = P_mod(z)`, `x = -Q`. Combine with `hasDerivAt_oneAddInvMul_negQ`.

### Phase 3 series-side reindex

Independent of Phase 2 and can be worked in parallel:

```
dS/dz|_{z=-Q} = ∑'_{n : ℤ} n · (-Q)^{n-1} · Q^{n²}
              = -Q⁻¹ · ∑'_{n : ℤ} (-1)^n · n · Q^{n²+n}
              = -Q⁻¹ · ∑'_{n ≥ 0} (-1)^n · (2n+1) · Q^{n(n+1)}   [pair n ↔ -1-n]
              = -Q⁻¹ · ∑'_{n ≥ 0} (-1)^n · (2n+1) · q^{n(n+1)/2}   [q = Q²]
```

Steps:
1. Closed-form expansion of `jacobiSeriesT' Q n (-Q)`.
2. Pair `n` with `-1-n` (these together cover ℤ disjointly).
3. Show `(-1)^n · n + (-1)^(-1-n) · (-1-n) = (-1)^n · (2n+1)` and exponents agree.
4. Substitute `q = Q²` (using `Q^(2*k) = q^k`).
