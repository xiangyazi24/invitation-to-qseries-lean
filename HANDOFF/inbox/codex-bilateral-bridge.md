# TASK (codex/gpt-5.5): close the JTP product=series formal-PS equalities (bilateral analytic→formal bridge)

Extend `QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean` (namespace `JTPFormalPSPentagonal`).
Touch ONLY this file. Single-file `lake env lean` verify (no `lake build`); 0 sorry/axiom/admit;
no sorryAx (re-elaborate from source). Reply to `HANDOFF/outbox/codex-bilateral-bridge-reply.md`.
This is the KEYSTONE unlock — partial genuine progress (0 sorry) beats fake-complete.

## Goal — close the two formal-PS equalities (currently open in this file)
```lean
pentagonalProduct014PS R = pentagonal014SeriesPS R
pentagonalProduct023PS R = pentagonal023SeriesPS R
```
(for `R = ℂ` suffices first; generalise to any CommRing R if the coefficients are integers, via map.)

## What's ALREADY in this file (REUSE)
- `pentagonalProduct014PS`, `pentagonalProduct023PS` (formal products) + their `_eq_tprod` forms.
- `pentagonal014SeriesPS`, `pentagonal023SeriesPS` (formal theta series) + coeff lemmas.
- `analytic_pentagonal014_eq_mod5_product`, `analytic_pentagonal023_eq_mod5_product`
  (the ANALYTIC identities `∏... = ∑...` over ℂ, already proven).

## Approach — mirror the B2 bridge EXACTLY
`QseriesFormalization/Pending/JacobiCubeAnalyticToFormal.lean` lifts an analytic product identity
to a `PowerSeries` identity via `HasFPowerSeriesOnBall` + formal/analytic Taylor-coefficient
uniqueness (`eq_formalMultilinearSeries` / `HasFPowerSeriesAt` uniqueness). Replicate that pattern:
1. Show each formal side (`pentagonalProduct014PS ℂ`, `pentagonal014SeriesPS ℂ`) is the formal
   Taylor series at 0 of the corresponding analytic function (the product / the theta sum), each
   `HasFPowerSeriesOnBall` on the unit ball (`‖q‖<1`).
2. The analytic functions are EQUAL by `analytic_pentagonal014_eq_mod5_product`.
3. Formal-PS Taylor coefficients of equal analytic functions agree ⇒ the two formal PS are equal.
The bilateral theta `∑_{k∈ℤ}` needs its summability/analyticity on `‖q‖<1` (it converges — the
exponents `(5k²∓3k)/2 → ∞`); set that up like the cube series in the B2 file.

## Why this is the keystone
Closing these feeds:
- the ASD eta-product identifications in `Chapter17_ASD_Mod5_Full`/`_Mod7_Full`
  (identify section components with `(q^10,q^15,q^25;q^25)` etc.), and
- (with the section dissection `(q;q) = product014·product023`) the MBI denominator identity
  `(E_0^5+11E_1^5+E_2^5)·E(q^25) = E(q^5)^6`.

## Deliverable
Best: both equalities. Acceptable partial: one equality, or the analyticity/`HasFPowerSeriesOnBall`
lemmas for the bilateral theta (the reusable hard part). Report exactly what closed.
