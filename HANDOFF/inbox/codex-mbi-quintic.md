# TASK (codex/gpt-5.5): the Ramanujan quintic → the FULL Most Beautiful Identity (the last lemma)

Extend `QseriesFormalization/Pending/Chapter16_MBI_Proof.lean` (namespace `Ch16MBIProof`).
Touch ONLY this file. Single-file verify; 0 sorry/axiom/admit; no sorryAx.
Reply to `HANDOFF/outbox/codex-mbi-quintic-reply.md`. This is HARD (Hirschhorn §8.5/§9, the
"difficult and deep" identity); MULTIPLE ROUNDS / partial progress are expected and fine.

## The single remaining identity (gives the full MBI via existing wrappers)
Prove (over ℚ⟦X⟧), with `H := pentagonalProduct014PS ℚ`, `G := pentagonalProduct023PS ℚ`,
`E := qPochInfPS ℚ`, `P5 := PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)`:
```lean
ramanujanMod5ProductCoreThetaRat = E^11 / P5       -- i.e. equivalently:
ramanujanMod5ProductCoreThetaRat * P5 = E^11        -- THIS clean form (no division)
```
where `ramanujanMod5ProductCoreThetaRat = G^10 - 11*X*H^5*G^5 - X^2*H^10` (check exact def in file).
This is **Hirschhorn (8.5.6)**: `(q²,q³,q⁵;q⁵)¹⁰ − 11q(...)⁵(...)⁵ − q²(q,q⁴,q⁵;q⁵)¹⁰ = E(q)¹¹/E(q⁵)`.
Feeding it to the existing `..._product_core` / `most_beautiful_identity_of_*` wrappers closes the
unconditional `most_beautiful_identity`.

## Already proven you can USE (0 sorry)
- Factorisation `pentagonalProduct014_mul_..._eq_qPochInfPS_mul_expand_five_qPochInfPS_rat`:
  `H * G = E * P5`.  ⇒ `H^5 G^5 = (E P5)^5`.
- ℚ keystone (products = theta series), the five-dissection, (5.3.1) `E5 0·E5 2=-(E5 1)^2`,
  (5.3.2) `E5 1 = -X·expand 25 qPoch`, `expand_qPochAPPS`.

## Routes (try the most formal-PS-friendly)
ROUTE 1 (Hirschhorn §8.5 factorisation): (8.5.4)/(8.5.5) factor `core = (G^5 - β⁵X H^5)(G^5 - α⁵X H^5)`
where α,β are 5th-root-of-unity-related constants with `α⁵+β⁵ = 11`, `α⁵β⁵ = -1` (so the cross term
is -11X and the last is -X²·... ). Establishing the two factor identities `G^5 - cX H^5 = (E-form)`
needs cyclotomic (5th root) input — heavy; only if you build minimal `CyclotomicField 5` support.
ROUTE 2 (Gugg telescoping, §9): the product `∏_{k≥1} t_k` with `t_k = (1-q^k)^5/(1-q^{5k})` for
`k≡1,4 (mod5)`, `t_k = (1-q^{5k})/(1-q^k)^5` for `k≡2,3`, `t_k=1` for `k≡0`, telescopes to the
η-quotient `(q²,q³;q⁵)^5 / (q,q⁴;q⁵)^5`-type and yields (8.5.6). Mirror the keystone's qPochAPPS
infinite-product machinery.
ROUTE 3: try to reduce `core*P5 = E^11` directly using `H*G=E*P5` + the keystone + any further
formal-PS relations among `H^5, G^5, E, P5` you can derive; close residual by `ring`.

## Deliverable
Best: `core * P5 = E^11` ⇒ the unconditional `most_beautiful_identity` (Ramanujan's Most Beautiful
Identity, COMPLETE end-to-end). Acceptable: reduce it further / build a needed sub-identity / one of
the two §8.5 factors. Report EXACTLY what closed (do NOT overclaim — `#print axioms` will be checked).
