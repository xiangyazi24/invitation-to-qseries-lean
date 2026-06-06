# Eta S-transform attempt

Added `QseriesFormalization/Pending/EtaSTransform.lean`.

Validation:

```bash
lake env lean QseriesFormalization/Pending/EtaSTransform.lean
rg -n "sorry|axiom|admit" QseriesFormalization/Pending/EtaSTransform.lean
```

Result: the Lean file checks, and the grep returns no hits.

What is proved unconditionally:

- `theta2`, `theta3`, `theta4`, `thetaDelta` are defined.
- `theta3_S` uses Mathlib's Poisson-derived `jacobiTheta_S_smul`.
- `theta2_S` and `theta4_S` are proved from `jacobiTheta₂_functional_equation`.
- `theta_product_S` proves the product transform.
- `thetaDelta_S` proves
  `thetaDelta (S • τ) = τ^12 * thetaDelta τ`.

Eta is connected conditionally:

- `EtaPow24ThetaDeltaFormula` isolates the missing Jacobi product bridge
  `eta^24 = (theta2 * theta3 * theta4)^8 / 256`.
- `eta_pow_twenty_four_S_of_thetaDelta` proves the eta 24th-power S-transform
  from that bridge.
- `EtaSBranchFormula` isolates the analytic branch step from the 24th-power
  identity to the principal square-root eta S-transform.
- `eta_S_transform_of_thetaDelta_and_branch` packages the final conditional
  eta S-transform.

I did not insert an axiom or proof placeholder. The current Mathlib/repo gap is
not the theta S-transform; that part closes. The remaining work is to connect
Mathlib's `ModularForm.eta` to the theta-product discriminant and then prove
the global branch/root-of-unity argument.

One implementation detail: `theta4` is represented as `jacobiTheta₂ (1/2) τ`.
This is the two-variable theta-constant form equivalent to `theta3 (τ + 1)`;
the file does not spend proof effort on that equivalence because the S-transform
uses the two-variable functional equation directly.
