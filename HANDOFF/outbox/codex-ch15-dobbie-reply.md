# Ch15 Dobbie identity attempt

I did not close `chan_theorem_11_7`.

Current Lean status:

```text
lake env lean QseriesFormalization/Pending/Chapter15_R_ODE.lean
```

passes with the existing warning:

```text
QseriesFormalization/Pending/Chapter15_R_ODE.lean:156:8: warning: declaration uses 'sorry'
```

The remaining unproved declaration is still:

```lean
theorem chan_theorem_11_7_int_core_coeff (N : ℕ) :
    (∑ ij ∈ Finset.antidiagonal N,
        (chan15LHSCoeffInt ij.1 : ℤ) *
          (if 5 ∣ ij.2 then (qPochInfPS ℤ).coeff (ij.2 / 5) else 0)) =
      ((qPochInfPS ℤ) ^ 5).coeff N := by
  sorry
```

What is already present and verified:

- `QseriesFormalization/Pending/RamanujanQuinticJTP.lean` has the formal fifth-root JTP product side:
  `section83JTPProductPS_eq_rhs_pair14`,
  `section83JTPProductPS_eq_rhs_pair23`,
  and `prod_scaleX_qPochInfPS_fifth_collapse_complex`.
- `QseriesFormalization/Chapter14_Thm116.lean` and
  `QseriesFormalization/Pending/Chapter16_MBI_Proof.lean` have the mod-5 AP product split
  `pentagonal014Series_mul_pentagonal023Series_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat`.
- The specialization algebra at `x = ζ`, `z = ζ^2` is consistent with the target:
  the product side collapses to `E(q)^5 / E(q^5)`, while the left side becomes
  `sqrt(5) * chan15LHSPS`.

The missing formal input is not the fifth-root product collapse. It is the
two-variable Dobbie partial-fraction/Lambert identity itself, or an equivalent
all-`N` coefficient theorem identifying the divisor-sum coefficients

```text
1 - 5 * Σ chi5(d) d q^d/(1 - q^d)
```

with the eta quotient

```text
(q;q)_∞^5 / (q^5;q^5)_∞.
```

No new `sorry`, `axiom`, or `admit` was added.
