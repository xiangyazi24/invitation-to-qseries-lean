## Chapter20 v19 reply

I worked in `QseriesFormalization/Pending/Chapter20_Eisenstein.lean`.

I did not finish the all-`n` arithmetic proof.  What I did close is the
direct term-by-term expansion requested in this round, with no use of the
individual Ramanujan theta equations for `E4` or `E6`.

New mixed convolution coefficient layer:

- `sigmaConvCoeffZ`
- `sigmaTripleConvCoeffZ`
- `eisensteinDiscriminantLHSMixedCoeffZ`
- `eisensteinDiscriminantLHSThetaResidualMixedCoeffZ`

The expanded coefficient is:

`F_mixed(n) =
  720*sigma_3(n) + 1008*sigma_5(n)
  + 172800*(sigma_3*sigma_3)(n)
  + 13824000*(sigma_3*sigma_3*sigma_3)(n)
  - 254016*(sigma_5*sigma_5)(n)`.

The expanded theta residual is:

`((n : Int) - 1) * F_mixed(n)
  + 24 * (sigma_1 * F_mixed)(n)`.

This is exactly the coefficient form of

`thetaOp (E4^3 - E6^2) - E2 * (E4^3 - E6^2)`.

New proved coefficient bridges:

- `coeff_divisorSigmaPS_eq_sigmaPowZ`
- `coeff_sigmaConvCoeffZ`
- `coeff_sigmaTripleConvCoeffZ`
- `coeff_mul_natCast_rat`
- `coeff_mul_C_rat`
- `coeff_eisensteinDiscriminantLHS_eq_mixedCoeffZ`
- `convCoeffZ_eisensteinE2CoeffZ_left`
- `coeff_eisensteinDiscriminantLHSThetaResidual_mixedCoeffZ`

The important theorem is:

`coeff_eisensteinDiscriminantLHSThetaResidual_mixedCoeffZ`

which states that for every `n`,

`(thetaOp eisensteinDiscriminantLHS -
  eisensteinE2PS * eisensteinDiscriminantLHS).coeff n`

is the rational cast of the fully expanded mixed convolution residual above.

I also added the closure bridge:

- `eisensteinDiscriminantLHS_theta_eq_of_mixedResidualCoeffZ_eq_zero`
- `eisensteinE4_cubed_sub_eisensteinE6_squared_eq_1728_discriminantPS_of_lhs_mixedResidualCoeffZ`

So the remaining all-`n` task is now exactly:

`∀ n, eisensteinDiscriminantLHSThetaResidualMixedCoeffZ n = 0`.

This is a pure integer divisor-sum convolution identity involving
`sigma_1`, `sigma_3`, `sigma_5`, their binary convolutions, and the
`sigma_3*sigma_3*sigma_3` triple convolution.  Proving this directly still
appears to require a Lahiri/Liouville-type convolution theorem, not just
formal power-series algebra.

I kept the existing finite certificate
`eisensteinDiscriminantLHSThetaResidualCoeffZThrough100Check_true`; I did not
add a second `native_decide` theorem for the expanded mixed residual because
it duplicates the same computation and noticeably increases single-file
check time.

Validation:

- `lake env lean QseriesFormalization/Pending/Chapter20_Eisenstein.lean` passed.
- `rg -n "sorry|admit|axiom" QseriesFormalization/Pending/Chapter20_Eisenstein.lean`
  found no matches.
