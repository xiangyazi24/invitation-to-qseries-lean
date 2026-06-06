# TASK (codex/gpt-5.5): product-side analyticity → close the JTP product=series equalities

Extend `QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean` (namespace `JTPFormalPSPentagonal`).
Touch ONLY this file. Single-file `lake env lean` verify; 0 sorry/axiom/admit; no sorryAx.
Reply to `HANDOFF/outbox/codex-product-analyticity-reply.md`.

## The ONE remaining gap (everything else for the bridge is done in this file)
Already proven here: the SERIES-side analyticity (`HasFPowerSeriesOnBall` for the theta series,
radius≥1, Taylor `HasSum`), AND the analytic product=series identities
(`analytic_pentagonal014_eq_mod5_product`, `_023`).
MISSING: the PRODUCT-side `HasFPowerSeriesOnBall` for the formal AP triple products
`pentagonalProduct014PS ℂ`, `pentagonalProduct023PS ℂ` — i.e. that each formal product is the
Taylor expansion at 0 of its analytic infinite-product value on `‖q‖<1`.

## Goal
Prove `pentagonalProduct014PS ℂ = pentagonal014SeriesPS ℂ` and the `023` analogue, by:
1. product-side: `HasFPowerSeriesOnBall (fun q => analytic product) (pentagonalProduct014PS ℂ as FMLS) 0 1`;
2. combine with the proven analytic identity + the series-side `HasFPowerSeriesOnBall` and
   `HasFPowerSeriesAt`-uniqueness ⇒ the two formal FMLS are equal ⇒ the PowerSeries are equal.

## Template (CRUCIAL — reuse heavily)
`QseriesFormalization/Pending/JacobiCubeAnalyticToFormal.lean` proves exactly the product-side
`HasFPowerSeriesOnBall` for the STANDARD product `qPochInfPS` (= ∏(1-X^{n+1})) and lifts B2. Your
AP triple products `∏_n (1-X^{a+5n})(1-X^{b+5n})(1-X^{5n+5})` are products of the same shape of
factors (each `1 - X^k`), just over shifted arithmetic progressions. Mirror that file's
`hasFPowerSeriesOnBall_*` development for these AP products (multipliability on the ball, the
product is analytic, its Taylor coeffs are the formal-product coeffs). Ch19's `qPochInfPS`
analyticity / `tprod` lemmas + the `apFactorPS`/`qPochAPPS` objects already in THIS file help.

## Deliverable
Best: both equalities (this CLOSES the keystone → unblocks ASD eta-products + the MBI denominator
identity). Acceptable partial: the product-side `HasFPowerSeriesOnBall` lemma for one product.
Report exactly what closed. 0-sorry partial beats fake-complete.
