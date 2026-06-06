# Ch15 logarithmic-derivative route status

I did not close `chan_theorem_11_7`.

What I verified:

- `QseriesFormalization/Pending/Chapter15_R_ODE.lean` still has exactly the existing blocker:

```lean
theorem chan_theorem_11_7_int_core_coeff (N : ℕ) : ...
```

and `lake env lean QseriesFormalization/Pending/Chapter15_R_ODE.lean` succeeds with the single warning:

```text
declaration uses 'sorry'
```

- The sign in the proposed shortcut should be corrected for the repo's normalization
  `rrcf_r = pentagonal014 / pentagonal023`:

```text
Dlog(rrcf_r).coeff n = - ∑_{d|n} d * legendre5 d
chan15LHSPS = 1 + 5 * Dlog(rrcf_r)
```

not `1 - 5 * Dlog(rrcf_r)`.  The `X^1` coefficient check is decisive:
`Dlog(rrcf_r)` has coefficient `-1`, so `1 + 5*Dlog(rrcf_r)` has coefficient
`-5`, matching `chan15LHSPS`.

The route remains mathematically viable:

1. Define `Theta(f) := X * (d⁄dX ℚ f)` and `Dlog(f) := Theta(f) * f⁻¹` for unit
   series.
2. Prove

```text
chan15LHSPS ℚ = 1 + 5 * Dlog(rrcf_r).
```

This is the missing formal bridge.  It requires an all-coefficients
log-derivative theorem for the AP product quotient

```text
(q,q^4,q^5;q^5)_∞ / (q^2,q^3,q^5;q^5)_∞.
```

Equivalently, one must prove that the AP product log derivative has the
divisor-sum coefficients filtered by residues `1,4` versus `2,3 mod 5`.

3. Differentiate the already proved
`QseriesFormalization.Pending.Ch13DeepIdentity.chan_theorem_11_5`:

```text
r^5 * B(v) = expand5(r) * A(v)
```

With `L := 1 + 5*Dlog(r)`, this gives

```text
L = Phi(v) * expand5(L)
Phi(t) = C(t)^4 / (A(t) * B(t))
```

using the polynomial identity

```text
A*B + t*A'*B - t*A*B' = C^4.
```

4. Use the already proved `chan_theorem_11_3_formal_ps` and
`chan_eq_12_37_cleared` to show the eta quotient

```text
M := (qPochInfPS ℚ)^5 / expand5(qPochInfPS ℚ)
```

satisfies the same recursion

```text
M = Phi(v) * expand5(M).
```

5. Prove uniqueness for unit series with constant coefficient `1` satisfying
`T = Phi(v) * expand5(T)`, then conclude `L = M`.

The missing Lean work is therefore not Dobbie/Sturm.  It is the formal
AP-product log-derivative bridge in step 2, plus the standard `Theta`/`Dlog`
calculus needed to differentiate Theorem 11.5.  I did not add new `sorry` or
axioms.
