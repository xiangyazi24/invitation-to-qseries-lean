# TASK (codex/gpt-5.5): MBI final lift — close most_beautiful_identity

Extend `QseriesFormalization/Pending/Chapter16_MBI_Proof.lean` (namespace `Ch16MBIProof`).
Touch ONLY this file. Single-file `lake env lean` verify (no `lake build`); 0 sorry/axiom/admit;
confirm no sorryAx (re-elaborate from source). Reply to `HANDOFF/outbox/codex-mbi-lift-reply.md`.

## You are ONE step from the full Most Beautiful Identity.
Already proven in this file (REUSE):
- `qPochInfPS_five_dissection`, (5.3.1), (5.3.2) full `E5_one_eq_neg_X_mul_expand_twentyfive_qPochInfPS`,
- `section5_four_qPochInfPS_pow_four_eq_neg_five_X_pow_four_expand_twentyfive_qPochInfPS_pow_four_rat`:
  `section5 4 ((qPochInfPS ℚ)^4) = -5 * X^4 * (expand 25 (qPochInfPS ℚ))^4`.

## Goal: prove `most_beautiful_identity`
`PowerSeries.mk (fun n => (partitionGenFun ℚ).coeff (5*n+4)) = 5 • ((expand 5 (qPochInfPS ℚ))^5 * (partitionGenFun ℚ)^6)`.

## The lift (from (qPoch)^4 to partitionGenFun = 1/(qPoch))
`partitionGenFun = (qPochInfPS)⁻¹`. Note `1/(q;q) = (q;q)^4 / (q;q)^5`, and over ℚ
`(q;q)^5`... is NOT `expand 5` (that's only mod 5). Instead use Hirschhorn's exact route:
`1/E = E^4/E^5`, and the 5-dissection of `E^5`'s denominator. Concretely, the cleanest formal path:
- Multiply the target by `(qPochInfPS ℚ)^6`: the identity is equivalent (since `partitionGenFun * qPochInfPS = 1`,
  see `Ch19.partitionGenFun_mul_qPochInfPS` or `coeff`/`PowerSeries.inv` lemmas) to
  `mk(fun n => (partitionGenFun ℚ).coeff (5n+4)) * (qPochInfPS ℚ)^6 = 5 • (expand 5 (qPochInfPS ℚ))^5`.
- Relate `mk(fun n => partitionGenFun.coeff (5n+4))` (a 5-section-then-compress of `1/E`) to the
  residue-4 section of `1/E`, and use `1/E = E^4 · (1/E^5)` with `E^5`'s residue structure +
  the proven residue-4 `(qPoch)^4` result. The `1/E^5 = 1/expand5(E)`-type Frobenius is mod-5 only;
  over ℚ you must instead use that `E(q)^5` and `E(q^5)` differ but the DISSECTION still extracts
  cleanly — follow Hirschhorn §5.4 exactly: `∑p(5n+4)q^{5n+4} = (E(q^25)/E(q^5)^6)·(residue-4 bracket)`,
  bracket = `5E_1^4 = 5q^4 E(q^25)^4`, giving `5q^4 E(q^25)^5/E(q^5)^6`; then `q^5→q` compress.

If the inverse/denominator bookkeeping is the blocker, prove the equivalent CLEARED-DENOMINATOR
form `mk(p(5n+4)) * (qPochInfPS ℚ)^6 = 5 • (expand 5 (qPochInfPS ℚ))^5` as the deliverable — that
IS the MBI modulo a unit, and is a complete result. State precisely what closed.
