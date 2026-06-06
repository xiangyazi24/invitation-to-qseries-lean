Done.

Implemented the all-degree Taylor bridge in `QseriesFormalization/Pending/RR_TaylorBridge.lean`.

Main new theorem:

```lean
theorem rrJInf_one_taylorCoeff_eq_rrGPS_coeff
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt (fun q : ℂ => rrJInf 1 q) p 0)
    (k : ℕ) :
    p.coeff k = (PowerSeries.map (algebraMap ℚ ℂ) rrGPS).coeff k
```

Also added:

```lean
theorem exists_rrJInf_one_taylor_coeffs_agree :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun q : ℂ => rrJInf 1 q) p 0 ∧
        ∀ n : ℕ, p.coeff n = (PowerSeries.map (algebraMap ℚ ℂ) rrGPS).coeff n
```

Proof structure:

- Proved the finite-term analytic/formal bridge for every `rrJTerm 1 · n`.
- Built the finite q-Pochhammer inverse from expanded geometric factors.
- Proved the tail estimate
  `rrJInf 1 q - ∑ n < N, rrJTerm 1 q n = O(‖q‖^N)` near `0`.
- For coefficient `k`, used `N = k + 1`; the tail has zero `k`-th Taylor coefficient, so the Taylor coefficient is the finite formal sum, which is exactly the `rrGPS` coefficient by definition.

Validation:

```bash
lake env lean QseriesFormalization/Pending/RR_TaylorBridge.lean
```

This passes. No new `sorry`.
