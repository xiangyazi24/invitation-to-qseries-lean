Ch20 Eisenstein / Ramanujan theta residual update:

Worked in `QseriesFormalization/Pending/Chapter20_Eisenstein.lean`.

What is now in the file:

- The residual series are named:
  - `residual3E4PS`
  - `residual2E6PS`
- The theta-log closure target is formalized:
  - `RamanujanThetaE4_of_residual3E4PS_theta_eq_mul`
  - `RamanujanThetaE6_of_residual2E6PS_theta_eq_mul`

These say that if one can prove, for some `C` with `C.coeff 0 = 0`,

```lean
thetaOp residual3E4PS = C * residual3E4PS
```

or the analogous `E6` statement, then the corresponding full Ramanujan theta
equation follows immediately by theta-log uniqueness.

- I also added/kept a constant-coefficient recurrence closure template:
  - `eq_zero_of_const_coeff_recurrence`
  - `RamanujanThetaE4_of_residual3E4_const_coeff_recurrence`
  - `RamanujanThetaE6_of_residual2E6_const_coeff_recurrence`

So a genuine finite-order homogeneous recurrence for the residual coefficients,
with nonzero leading coefficient and enough zero initial values, is also enough
to close the global theorem.

- The executable residual verification was extended from degree `100` to degree
  `500`:
  - `ramanujanThetaResidualCoeffZThrough500Check_true`
  - `ramanujanThetaResidual_coeff_zero_through_five_hundred`

- I fixed a brittle proof step in
  `ramanujanThetaE4ArithmeticIdentityAt_of_lahiri` by replacing `unfold ... at h`
  with explicit `change` statements.

Verification:

```bash
lake env lean QseriesFormalization/Pending/Chapter20_Eisenstein.lean
```

passes.

Status of the all-n proof:

Still open. I tried to follow the suggested "differentiate the residual/Ramanujan
equation" route. In formal terms, differentiating

```lean
residual3E4PS =
  3 * thetaOp E4 - (E2 * E4 - E6)
```

introduces `thetaOp (thetaOp E4)`. Eliminating that second derivative by
rewriting `3 * thetaOp E4 = E2 * E4 - E6 + residual3E4PS` just gives back a
tautology involving `thetaOp residual3E4PS`; it does not produce a closed
equation `thetaOp residual3E4PS = C * residual3E4PS`. To get such a recurrence
one still needs an additional non-circular arithmetic/modular input, e.g. a
proved Lahiri/Ramanujan sigma convolution identity for all `n`, a Sturm-type
bound, or a real recurrence for the residual coefficients.

The file now has the exact theorem hooks needed once that missing recurrence or
convolution identity is available.
