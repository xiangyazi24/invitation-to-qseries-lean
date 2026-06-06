# TASK (codex/gpt-5.5): close the MBI bridge lemma (the last step of the Most Beautiful Identity)

Extend `QseriesFormalization/Pending/Chapter16_MBI_Proof.lean` (namespace `Ch16MBIProof`).
Touch ONLY this file. Single-file `lake env lean` verify (no `lake build`); 0 sorry/axiom/admit;
no sorryAx (re-elaborate from source). Reply to `HANDOFF/outbox/codex-mbi-bridge-reply.md`.
THIS IS AMBITIOUS — partial genuine progress (new lemmas, 0 sorry) beats a fake full claim.

## The single remaining bridge (proving it closes the full MBI via existing wrappers)
```lean
section5 ℚ 4 (partitionGenFun ℚ) * (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6
  = - PowerSeries.expand 25 (by decide) (qPochInfPS ℚ) * section5 ℚ 4 ((qPochInfPS ℚ)^4)
```
Once proved, feed it to `most_beautiful_identity_of_denominator_rationalization` (already in the
file) to obtain the unconditional `most_beautiful_identity`.

## Two possible routes (try the sections-only one FIRST — it may avoid heavy new infra)
ROUTE A (sections-only, preferred if it works): You already have, in this file:
 - `qPochInfPS_five_dissection`, (5.3.1) `E5 0 * E5 2 = -(E5 1)^2`,
 - (5.3.2) `E5 1 = -X * expand 25 (qPochInfPS)`,
 - the residue-4 collapse of `(qPoch)^4`.
 `partitionGenFun = (qPochInfPS)⁻¹` and `partitionGenFun * qPochInfPS = 1` (Ch19). Try to express
 `section5 4 (partitionGenFun) * (expand5 qPoch)^6` purely via the `E5` components and the
 multiplicative relation `(qPochInfPS)^5 vs expand5`, WITHOUT roots of unity. Key fact to find/derive:
 a relation between `(qPochInfPS)^5`, `expand 5 (qPochInfPS)`, and the `E5 i` over ℚ (NOT the mod-5
 Frobenius — an exact ℚ identity from the dissection). If `partitionGenFun·(qPoch)^5`-type
 bookkeeping closes it, great.

ROUTE B (roots of unity, if A fails): work in `(CyclotomicField 5 ℚ)⟦X⟧` (Mathlib
 `CyclotomicField`, `IsPrimitiveRoot`). Build the minimal lemma `∏_{j=0}^{4} subst(ζ^j) E = E(q^5)^?`-type
 product collapse following Hirschhorn §5.2 (5.2.3-5.2.4): `1/E(q) = ∏_{j=1}^4 E(ζ^j q) / D(q)` with
 `D(q) = E(q^5)^6/E(q^25)`. This needs a "substitute X ↦ ζ X" ring hom on power series and the product
 over the 5 roots. Substantial — only attempt if Route A is genuinely blocked, and report how far you got.

## Infrastructure
- This file's `E5`, `section5`/`isRes5_*`, the proven (5.3.1)/(5.3.2)/residue-4 lemmas.
- Ch19: `partitionGenFun`, `partitionGenFun_mul_qPochInfPS`/inverse lemmas, `qPochInfPS`, `expand`,
  `coeff_qPochInfPS_eq_pentagonalSign`. Mathlib: `PowerSeries`, `CyclotomicField`, `IsPrimitiveRoot`.
