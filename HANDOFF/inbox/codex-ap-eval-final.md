# TASK (codex/gpt-5.5): close the AP-product eval via tendsto_nhds_unique (LAST step)

Extend `QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean`. Touch ONLY this file.
Single-file verify; 0 sorry/axiom/admit; no sorryAx. Reply to `HANDOFF/outbox/codex-ap-eval-final-reply.md`.

## You have BOTH halves already (in this file). Only the limit-interchange remains.
- `tendsto_pentagonal014ProductAnalytic_partial`: the finite analytic partial products P_N(y) →
  `pentagonal014ProductAnalytic y` on ‖y‖<1.
- coeff stabilization: `(pentagonalProduct014PS ℂ).coeff k` = coeff k of the finite partial product
  over `range (k+1)` (and stable for larger N).

## The ONE lemma to prove
```lean
pentagonal014ProductAnalytic y = ∑' n : ℕ, y^n * ((pentagonalProduct014PS ℂ).coeff n)
```
(and 023). Then feed the existing `..._of_productCoeff_taylor` wrappers to get the unconditional
`pentagonalProduct014PS ℂ = pentagonal014SeriesPS ℂ`.

## Precise technique — `tendsto_nhds_unique`
Both of these sequences (indexed by N) converge to `pentagonal014ProductAnalytic y`:
1. `P_N(y)` (finite analytic partial product) — you have `tendsto_..._partial`.
2. `∑_{k=0}^{N} (formal coeff k) · y^k` (partial sums of the RHS tsum).
Show seq 2 also `Tendsto` to the analytic product, then `tendsto_nhds_unique` gives
`∑' = analytic product`. To link them: the finite partial product `P_N(y)` is a POLYNOMIAL whose
`y^k` coefficients (for k ≤ N) equal `(formal coeff k)` by stabilization; so
`P_N(y) = ∑_{k=0}^{deg P_N} (formal coeff k) y^k`, whose partial sums up to degree N agree with seq 2
up to a tail that → 0 (the formal-coeff series is summable on ‖y‖<1 — you have the radius bound).
Use `HasSum.tendsto_sum_nat` for the tsum's partial sums, `Filter.Tendsto.congr'`/eventually-eq for
the polynomial-vs-partial-sum match, and `tendsto_nhds_unique`. Alternatively: prove
`HasSum (fun n => (formal coeff n) y^n) (pentagonal014ProductAnalytic y)` directly and conclude.

## Mathlib helpers
`HasSum.tendsto_sum_nat`, `tendsto_nhds_unique`, `Filter.Tendsto.congr'`, `Filter.eventually_atTop`,
`Summable.hasSum`, `Finset.sum_range`, `Polynomial.eval`/`PowerSeries.coeff`-to-finite-sum.
Mirror Ch19's `eulerPentagonalInfiniteProduct_cube_eq_tsum_qpow_cubeConvolution` / Ch04
`eulerPentagonalInfiniteProduct_eq_tsum` for how an infinite product is shown to equal a tsum.

## Deliverable
Best: both eval lemmas + the two unconditional equalities (KEYSTONE CLOSED). Report exactly what closed.
