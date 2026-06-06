# Ch15 Dlog infrastructure status

I did not close `chan_theorem_11_7`.

What I added in `QseriesFormalization/Pending/Chapter15_R_ODE.lean`:

- `formalDeriv : ℚ⟦X⟧ → ℚ⟦X⟧` with
  ```lean
  (formalDeriv f).coeff n = (n + 1 : ℚ) * f.coeff (n + 1)
  ```
  plus `formalDeriv_eq_derivative`, zero/one/X, add/sub/neg, and Leibniz.
- `thetaOp f := X * formalDeriv f` with
  ```lean
  (thetaOp f).coeff n = (n : ℚ) * f.coeff n
  ```
  plus add/sub/neg, product rule, and
  ```lean
  thetaOp (X^m) = C (m : ℚ) * X^m
  thetaOp (1 - X^m) = -C (m : ℚ) * X^m
  ```
- `formalDlog f := thetaOp f * f⁻¹`.
- The one-factor logarithmic derivative:
  ```lean
  formalDlog (1 - X^m) =
    -C (m : ℚ) * X^m * (1 - X^m)⁻¹
  ```
  and `IsUnit (1 - X^m)` for `0 < m`.
- Additivity on units:
  ```lean
  formalDlog (f * g) = formalDlog f + formalDlog g
  ```
  both with explicit `constantCoeff ≠ 0` hypotheses and with `IsUnit` hypotheses.

Validation:

```text
lake env lean QseriesFormalization/Pending/Chapter15_R_ODE.lean
```

passes, with the single existing warning:

```text
declaration uses 'sorry'
```

The remaining `sorry` is exactly:

```lean
theorem chan_theorem_11_7_int_core_coeff (N : ℕ) : ...
```

Exact reason it is still open:

The Dlog infrastructure proves the local calculus, but it does not prove the global Lambert/product identity. To use the Dlog route one still needs the all-coefficients AP-product logarithmic derivative bridge

```text
chan15LHSPS ℚ = 1 + 5 * formalDlog(rrcf_r)
```

equivalently, for every coefficient `N > 0`,

```text
[X^N] formalDlog(rrcf_r) = - ∑_{d | N} d * legendre5(d).
```

The repo defines

```lean
rrcf_r = pentagonal014SeriesPS ℚ * (pentagonal023SeriesPS ℚ)⁻¹
```

and has product/series identifications for the pentagonal factors, but it does not currently have a theorem allowing `formalDlog` to pass through the infinite AP products

```text
(q,q^4,q^5;q^5)_∞ / (q^2,q^3,q^5;q^5)_∞
```

and convert them into the residue-filtered divisor sum. That is a genuine infinite-product logarithmic-derivative theorem, not a consequence of the formal derivative rules alone.

Also, the direct eta quotient route is not a tautology:

```text
formalDlog(E^5/E5)
```

has the `5 ∤ m` unweighted Lambert coefficients, while `formalDlog(rrcf_r)` has the `χ₅(m)` signed coefficients. Thus `E^5/E5 = 1 + 5*formalDlog(rrcf_r)` remains the real content of Chan Theorem 11.7, not a formal consequence of Dlog calculus.

To close the theorem from here, one still needs one of:

1. a formal specialized Dobbie identity / two-variable Laurent constant-term argument leading to `chan_theorem_11_7_int_core_coeff`; or
2. the AP-product Dlog bridge above, then the Chan 11.5 / Eq. 12.37 recursion plus uniqueness route.

No new `sorry` or axioms were added.
