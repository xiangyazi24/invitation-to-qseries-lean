Implemented the Ch15 coefficient extension in `QseriesFormalization/Pending/Chapter15_CoeffVerification.lean`.

What changed:
- Extended the `qPochInfPS` low-coefficient table through degree 20.
- Extended the raw Lambert-side table `chan15LambertCoeffLow` through degree 20.
- Extended the verified product/power coefficient table `chan15CoeffVerified` through degree 20.
- Generalized the coefficient verification lemmas from `n ≤ 10` to `n ≤ 20`.
- Kept `chan15_theorem_11_7_coeffs_zero_to_ten` and added:
  - `chan15_theorem_11_7_coeffs_zero_to_twenty`
  - `chan15_theorem_11_7_coeff_11` through `chan15_theorem_11_7_coeff_20`

Validation:
- `lake env lean QseriesFormalization/Pending/Chapter15_CoeffVerification.lean`
- `rg -n "\bsorry\b|\baxiom\b|\bnative_decide\b" QseriesFormalization/Pending/Chapter15_CoeffVerification.lean` returned no matches.
- `git diff --check -- QseriesFormalization/Pending/Chapter15_CoeffVerification.lean`
