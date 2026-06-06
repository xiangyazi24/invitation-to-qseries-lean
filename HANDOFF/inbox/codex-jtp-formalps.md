# TASK (codex/gpt-5.5): Jacobi-triple-product specialisations as FORMAL power series

NEW file `QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean`. Touch ONLY this file
(do NOT edit any existing file or the import aggregators). Single-file `lake env lean` verify
(no `lake build`); 0 sorry/axiom/admit; no sorryAx. Reply to `HANDOFF/outbox/codex-jtp-formalps-reply.md`.
AMBITIOUS — partial genuine progress (0 sorry) beats fake-complete.

## Goal — the two pentagonal-AP JTP specialisations as formal power series (Hirschhorn 3.6.3)
Over `ℤ` (or any CommRing R), define the finite-product → formal-PS objects and prove:
```
(q, q^4, q^5 ; q^5)_∞  = ∑_{k∈ℤ} (-1)^k X^{(5k^2-3k)/2}        -- as elements of R⟦X⟧
(q^2, q^3, q^5 ; q^5)_∞ = ∑_{k∈ℤ} (-1)^k X^{(5k^2-k)/2}
```
where `(q^a, q^b, q^m ; q^m)_∞ := ∏_{n≥0}(1 - X^{a+mn})(1 - X^{b+mn})(1 - X^{mn+m})` as a formal PS
(define it as a `PowerSeries` multipliable product; or via the `qPochInfPS`-style partial-product limit
already used in Ch19). These are exactly the residue-shifted halves of Euler's pentagonal series
`(q;q)_∞ = ∑ (-1)^k X^{(3k^2-k)/2}` — note `(q,q^4,q^5;q^5)·(q^2,q^3,q^5;q^5) = (q;q)_∞`.

## Recommended approach
This is a Jacobi-triple-product specialisation. The repo ALREADY has:
- the ANALYTIC JTP `QseriesFormalization.PartI.Ch02.jacobiTripleProduct` (and Ch03 finite-JTP),
- the analytic↔formal Taylor-uniqueness BRIDGE pattern that closed B2 — study
  `QseriesFormalization/Pending/JacobiCubeAnalyticToFormal.lean` (it lifts an analytic product
  identity to a `PowerSeries` identity via `HasFPowerSeriesOnBall` + coefficient uniqueness).
Mirror that B2 bridge: instantiate the analytic JTP at the right `q,z` to get the analytic form of
each specialisation, then transfer to `R⟦X⟧` coefficientwise.
ALTERNATIVELY, a purely formal route: prove it as the residue-`{0,1,4}`/`{0,2,3}` dissection of the
Euler pentagonal series `(q;q)_∞` (the exponents `(3k^2-k)/2` split by residue mod 5) — this may be
simpler and avoids analysis. Try whichever is cleaner.

## Why this matters
Closing these unblocks the η-product identification stretch goals in
`Pending/Chapter17_ASD_Mod5_Full.lean` / `Chapter17_ASD_Mod7_Full.lean` (identifying the section
components with `(q^10,q^15,q^25;q^25)` etc.), completing the ASD congruences in η-quotient form.

## Deliverable (largest with 0 sorry)
Best: both specialisations. Acceptable partial: the `(q;q)_∞` pentagonal 5-dissection
`(q;q)_∞ = A_{0,1,4-part} · ... ` OR one of the two product identities. Report exactly what closed.
