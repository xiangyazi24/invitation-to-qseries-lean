Partial closed in `QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean`.

Closed:

- Bilateral theta analytic-to-formal bridge for both target RHS series:
  - `hasFPowerSeriesOnBall_pentagonal014Analytic`
  - `hasFPowerSeriesOnBall_pentagonal023Analytic`
- Supporting no-gap lemmas for both `014` and `023`:
  - integer exponent nonnegativity/coercion back from `toNat`
  - fiber-boundedness of each exponent level inside `Finset.Icc (-(n+1)) (n+1)`
  - complex sign bridge `negOnePowInt_complex_eq_zpow`
  - bilateral summability:
    - `summable_pentagonal014ThetaTerm`
    - `summable_pentagonal023ThetaTerm`
  - fiber regrouping:
    - `pentagonal014_fiber_tsum_eq_coeff_mul_pow`
    - `pentagonal023_fiber_tsum_eq_coeff_mul_pow`
  - coefficient Taylor `HasSum` forms:
    - `hasSum_pentagonal014Coeff_mul_pow`
    - `hasSum_pentagonal023Coeff_mul_pow`
  - radius bounds:
    - `one_le_pentagonal014SeriesFMLS_radius`
    - `one_le_pentagonal023SeriesFMLS_radius`

Not closed:

- `pentagonalProduct014PS R = pentagonal014SeriesPS R`
- `pentagonalProduct023PS R = pentagonal023SeriesPS R`

The remaining missing piece is the product-side `HasFPowerSeriesOnBall` /
infinite-product evaluation bridge for `pentagonalProduct014PS ℂ` and
`pentagonalProduct023PS ℂ`.

Validation:

- `lake env lean QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean`
- `rg -n "\b(sorry|axiom|admit|native_decide|sorryAx)\b" QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean` returned no matches.
- `#print axioms` for the two new `HasFPowerSeriesOnBall_*Analytic` theorems and the two new `HasSum_*Coeff_mul_pow` theorems reports only `[propext, Classical.choice, Quot.sound]`.
