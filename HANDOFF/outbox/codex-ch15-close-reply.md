# Chan Theorem 11.7 close attempt

Target checked in the actual repo path:

```bash
lake env lean QseriesFormalization/Pending/Chapter15_R_ODE.lean
```

Result: PASS, with the expected single warning:

```text
QseriesFormalization/Pending/Chapter15_R_ODE.lean:140:8: warning: declaration uses 'sorry'
```

## What changed

I did not close the theorem unconditionally.  I isolated the remaining
mathematical blocker to an explicit all-`N` integer coefficient theorem:

```lean
theorem chan_theorem_11_7_int_core_coeff (N : ℕ) :
    (∑ ij ∈ Finset.antidiagonal N,
        (chan15LHSCoeffInt ij.1 : ℤ) *
          (if 5 ∣ ij.2 then (qPochInfPS ℤ).coeff (ij.2 / 5) else 0)) =
      ((qPochInfPS ℤ) ^ 5).coeff N := by
  sorry
```

The denominator-cleared `ℤ⟦X⟧` identity is proved from that coefficient theorem
by `ext N`, and the general theorem is now proved from the integer identity by
coefficient-cast naturality:

```lean
theorem map_chan15LHSPS_int (R : Type*) [CommRing R] :
    PowerSeries.map (Int.castRingHom R) (chan15LHSPS ℤ) = chan15LHSPS R

theorem chan_theorem_11_7_int_core :
    chan15LHSPS ℤ * (PowerSeries.expand 5 (by decide) (qPochInfPS ℤ)) =
      (qPochInfPS ℤ) ^ 5

theorem chan_theorem_11_7 (R : Type*) [CommRing R] :
    chan15LHSPS R * (PowerSeries.expand 5 (by decide) (qPochInfPS R)) =
      (qPochInfPS R) ^ 5
```

So the arbitrary-`CommRing` layer is no longer the blocker.  The only remaining
gap is the `ℤ⟦X⟧` Lambert/product identity itself.

## Exact blocker

The missing theorem is:

```text
1 - 5 * Σ χ₅(n) n X^n / (1 - X^n) = (q;q)_∞^5 / (q^5;q^5)_∞
```

or, denominator-cleared:

```lean
chan15LHSPS ℤ * expand 5 (qPochInfPS ℤ) = (qPochInfPS ℤ)^5
```

The existing 5th-root JTP infrastructure supplies product/root-of-unity and
Gaussian-period algebra, but it does not supply the central Lambert-series
identity.  In particular, `section83JTPProductPS_eq_rhs_pair14/23` and the
product collapse identify the relevant root-twisted products; they do not prove
Dobbie's two-variable partial-fraction identity or an all-coefficients divisor
sum theorem for this Lambert series.

To close `chan_theorem_11_7_int_core_coeff`, the next formal input must be one of:

1. a specialized Dobbie identity at `x = ζ`, `z = ζ^2`, including the
   residue-class collapse
   `ζ^j + ζ^(-j) - ζ^(2j) - ζ^(-2j) = δ * χ₅(j)`;
2. a direct coefficient theorem proving, for every `N`, that the divisor-sum
   coefficient defining `chan15LHSPS` matches the coefficient of
   `(qPochInfPS ℤ)^5 * (expand 5 (qPochInfPS ℤ))⁻¹`, equivalently the
   denominator-cleared convolution.

## Notes

The user-stated path `Pending/Chapter15_R_ODE.lean` does not exist in this
workspace; the file is `QseriesFormalization/Pending/Chapter15_R_ODE.lean`.
