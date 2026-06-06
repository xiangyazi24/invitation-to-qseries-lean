# TASK (codex/gpt-5.5): close JTP product=series — reuse B2's EXACT template (cubeConvolution)

Extend `QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean` (namespace `JTPFormalPSPentagonal`).
Touch ONLY this file. Single-file verify; 0 sorry/axiom/admit; no sorryAx.
Reply to `HANDOFF/outbox/codex-product-analyticity-v2-reply.md`.

## The ONE missing lemma (everything else is done in this file)
```lean
HasFPowerSeriesOnBall pentagonal014ProductAnalytic
  (FormalMultilinearSeries.ofScalars ℂ (fun n => (pentagonalProduct014PS ℂ).coeff n)) 0 1
```
and the `023` analogue. Then combine with the ALREADY-PROVEN
`hasFPowerSeriesOnBall_pentagonal014ProductAnalytic_series` (analytic product has the THETA Taylor
series) via `HasFPowerSeriesAt`/`HasFPowerSeriesOnBall` uniqueness (`ofScalars_series_eq_iff`,
`Nontrivial ℂ`) ⇒ `(pentagonalProduct014PS ℂ).coeff n = pentagonal014SeriesPS coeff` ⇒
`pentagonalProduct014PS ℂ = pentagonal014SeriesPS ℂ`. (B2 does this final uniqueness step at the
END of `JacobiCubeAnalyticToFormal.lean` ~lines 285-300 — copy that structure.)

## DO NOT use `PowerSeries.aeval` (it needs `IsLinearTopology ℂ ℂ`, unavailable — dead end).
## Instead use B2's EXACT template:
In `QseriesFormalization/Pending/JacobiCubeAnalyticToFormal.lean`, the theorem
`hasFPowerSeriesOnBall_fAnalytic_cubeConvolution` (≈ lines 223–278) proves precisely
`HasFPowerSeriesOnBall fAnalytic cubeConvolutionSeries 0 1`, where `cubeConvolutionSeries` is
`ofScalars ℂ (fun n => (formal cube-convolution coeff : ℂ))` — i.e. the analytic product function
has Taylor series given by the FORMAL product's coefficients. It does this WITHOUT aeval: via the
`ofScalars_norm` radius/tail estimate + `ofScalars_apply_eq` + the partial-product convergence.
Mirror that lemma verbatim, substituting:
  fAnalytic              → pentagonal014ProductAnalytic
  cubeConvolutionSeries  → ofScalars ℂ (fun n => (pentagonalProduct014PS ℂ).coeff n)
The radius bound you need is the analogue of B2's `one_le_cubeConvolutionSeries_radius`; you already
have `one_le_pentagonal014SeriesFMLS_radius` for the theta side — make the matching one for the
formal-product-coeff side (the product coeffs are bounded similarly).

## Deliverable
Best: both product=series equalities (CLOSES the keystone). Acceptable: one, or just the
`HasFPowerSeriesOnBall ... (ofScalars product-coeff)` lemma. Report exactly what closed.
