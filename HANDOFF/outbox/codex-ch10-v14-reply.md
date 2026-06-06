Ch20 Eisenstein / Lahiri convolution update:

Worked in `QseriesFormalization/Pending/Chapter20_Eisenstein.lean`.

What I proved/added:

- Added the direct Finset factor-pair expansion

```lean
lemma sigmaPowZ_eq_sum_factorPairs_of_pos_le
```

This rewrites `sigmaPowZ r k` as a bounded sum over factor pairs
`a*b = k`.

- Added the corresponding split convolution expansion

```lean
def sigma1Sigma3FactorPairSplitSumZ
theorem sigma1Sigma3ConvZ_eq_factorPairSplitSumZ
```

This rewrites the Lahiri LHS as a finite sum over `k,a,b,c,d` with
`a*b = k` and `c*d = n-k`.  This is the clean Finset version of the proposed
four-variable expansion.  I did not complete the harder collapse/telescoping
step from this split sum to the closed divisor expression on the RHS.

- Added the Lahiri difference series:

```lean
def lahiriSigma1Sigma3DiffCoeffZ
noncomputable def lahiriSigma1Sigma3DiffPS
```

and the bridge between zero difference and the Lahiri identity:

```lean
theorem lahiriSigma1Sigma3IdentityAt_of_diffCoeffZ_eq_zero
theorem diffCoeffZ_eq_zero_of_lahiriSigma1Sigma3IdentityAt
```

- Added the theta-recursive route for the difference series:

```lean
def lahiriSigma1Sigma3DiffThetaE2ResidualCoeffZ
theorem coeff_lahiriSigma1Sigma3DiffThetaE2Residual
theorem lahiriSigma1Sigma3Identity_all_of_diff_theta_eq
```

The last theorem says: if one proves

```lean
thetaOp lahiriSigma1Sigma3DiffPS =
  eisensteinE2PS * lahiriSigma1Sigma3DiffPS
```

then the Lahiri identity follows for all `n`.  This uses the existing
theta uniqueness lemma with `E2.coeff 0 = 1` and the checked zero coefficients
in degrees `0` and `1`.

- Finite checks added:

```lean
theorem lahiriSigma1Sigma3IdentityThrough500Check_true
theorem lahiriSigma1Sigma3Identity_through_five_hundred
theorem lahiriSigma1Sigma3DiffThetaE2ResidualThrough100Check_true
theorem lahiriSigma1Sigma3Diff_thetaE2_residual_coeff_zero_through_one_hundred
```

So Lahiri itself is now checked through `500`, and the proposed
`theta(diff)=E2*diff` residual is checked through `100`.

- While checking the file, I also fixed a brittle coefficient proof in the
mixed Eisenstein-discriminant coefficient expansion by adding
`coeff_mul_C_rat` and replacing the failing nat-cast rewrite steps.

Verification:

```bash
lake env lean QseriesFormalization/Pending/Chapter20_Eisenstein.lean
```

passes.

Status:

The full all-`n` Lahiri identity is still open.  The new Finset factor-pair
expansion is the right direct-combinatorial starting point, but the actual
telescoping/collapse over `a*b+c*d=n` is not yet proved.  The
`theta(diff)=E2*diff` route is now formalized conditionally and checked
finite-degree, but I did not find a non-circular proof of that global theta
equation.
