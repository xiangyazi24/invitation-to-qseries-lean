# codex-ch20-v4 reply

## Result

Proved the requested tau log-derivative recurrence in
`QseriesFormalization/Chapter20.lean`:

```lean
theorem ramanujanTau_log_derivative_recurrence (n : Nat) (hn : 2 ≤ n) :
    ((n : ℤ) - 1) * ramanujanTau ℤ n =
      -24 * ∑ k ∈ Finset.Icc 1 (n - 1),
        (Nat.divisorSum k id : ℤ) * ramanujanTau ℤ (n - k)
```

## What changed

- Imported `QseriesFormalization.Pending.Chapter15_FormalDeriv` for `thetaOp`.
- Added `Nat.divisorSum` locally, since this Mathlib snapshot does not provide
  `Nat.divisorSum`.
- Added finite-product logarithmic derivative infrastructure:
  - `divisorGeomPS`
  - `finiteDivisorSigmaPS`
  - `qPochFinitePS`
  - `thetaOp_qPochFinitePS`
- Passed from finite products to `etaPS` using the existing Chapter 19 low-degree
  coefficient stability theorem for `qPochInfPS`.
- Proved:
  - `thetaOp_etaPS_eq_neg_etaPS_mul_divisorSigmaPS`
  - `thetaOp_discriminantPS_eq`
  - `coeff_discriminantPS_mul_divisorSigmaPS`
  - `ramanujanTau_log_derivative_recurrence`

The final proof follows `Δ = X * etaPS^24`, applies `thetaOp`, expands the
formal Lambert series coefficient as `Nat.divisorSum`, and compares coefficients.

## Verification

Ran:

```bash
lake env lean QseriesFormalization/Chapter20.lean
```

Result: passed with no output.

Also ran:

```bash
rg -n "sorry|admit|axiom" QseriesFormalization/Chapter20.lean
```

Result: no matches.
