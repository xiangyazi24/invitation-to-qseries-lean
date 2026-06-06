# TASK round 6 (codex / gpt-5.5): EXECUTE the infinite fifth-root collapse (you diagnosed it; now WRITE it)

Round 5 correctly diagnosed the ONE missing lemma but produced no code. This round: WRITE THE PROOF.
Do NOT re-diagnose. If a tactic resists, report the exact tactic state — but produce code.

## Lemma 1 (the gap) — prove in RamanujanQuinticJTP.lean
```lean
theorem prod_scaleX_qPochInfPS_fifth_collapse_complex
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (∏ j : Fin 5, RamanujanQuintic.scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) *
      PowerSeries.expand 25 (by decide) (qPochInfPS ℂ) =
    (PowerSeries.expand 5 (by decide) (qPochInfPS ℂ)) ^ 6
```
**This is TRUE and the structure is fully worked out** — it is the N→∞ limit of the existing finite
collapse `RamanujanQuintic.prod_scaleX_qPochFinitePS_fifth_collapse` (RamanujanQuintic.lean:252), whose
RHS is `∏_{k<N} [if 5∣k+1 then (1-X^{k+1})^5 else 1-X^{5(k+1)}]`. Splitting the limit by the two cases:
- `5∣k+1` terms (k+1=5m): `∏_m (1-X^{5m})^5 = (expand5 qPochInf)^5 = E(q⁵)⁵`.
- `5∤k+1` terms: `∏_{5∤j}(1-X^{5j}) = E(q⁵)/E(q²⁵)` (all `j` minus the `5∣j` ones).
- product = `E(q⁵)⁵ · E(q⁵)/E(q²⁵) = E(q⁵)⁶/E(q²⁵)`, i.e. `·E(q²⁵) = E(q⁵)⁶`.  (numerically checkable)

**Proof strategy (pick the cleaner):**
(A) Coefficient-wise: `PowerSeries.ext`; the degree-N coefficient of each infinite product equals that
   of a finite truncation, so reduce to `prod_scaleX_qPochFinitePS_fifth_collapse` at truncation ≥ N
   plus the order/`expand` coefficient lemmas. OR
(B) tprod: establish `Multipliable` for `∏_j scaleX(ζ^j) qPochInf` (scaleX is a ring hom; reuse the
   existing multipliability of qPochInfPS factors), then `tprod_mul`/reindex to split into the
   `5∣` and `5∤` sub-products and identify each with `expand5/expand25 qPochInf` via reindexing
   `k ↦ 5k`. Reuse `quinticCyclotomic_qPochFinitePS_fifth_collapse` (RamanujanQuintic.lean:295) if it helps.

## Lemma 2 — identify with the Ch16 denominator core
```lean
theorem prod_scaleX_qPochInfPS_eq_E5DenominatorCore_complex
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    (∏ j : Fin 5, RamanujanQuintic.scaleX (ζ ^ (j : ℕ)) (qPochInfPS ℂ)) =
      PowerSeries.map (algebraMap ℚ ℂ) Ch16MBIProof.E5DenominatorCoreRat
```
(`E5DenominatorCoreRat` def at Chapter16_MBI_Proof.lean:1349 — match its factor structure.)

## Then close the MBI
Combine Lemma 1 + Lemma 2 via `PowerSeries.map_injective (algebraMap ℚ ℂ)` to get over ℚ:
`E5DenominatorCoreRat · expand25 qPoch = (expand5 qPoch)^6`. Run the existing Ch16 algebra
(`qPochInfPS_mul_E5RationalizerRat_eq_E5DenominatorCoreRat`:1487,
`section5_four_partitionGenFun_mul_E5DenominatorCoreRat`:1532) + the `hE0` bridge
(`E5_zero_eq_expand_compressedSection5_zero_qPochInfPS_rat`:2052) backward to discharge BOTH `hE0`
and `hfactor` of `RamanujanQuintic.most_beautiful_identity_of_compressed_E5_zero_bridge_and_factor_pair_product`,
yielding the unconditional `most_beautiful_identity`.

## Rules
- Edit ONLY `RamanujanQuinticJTP.lean`. NEVER `native_decide` (clean-3 axioms). NEVER `lake build`;
  verify `lake env lean QseriesFormalization/Pending/RamanujanQuinticJTP.lean`. 0 sorry/axiom/admit.
- PRODUCE CODE. If stuck on a specific tactic, paste the exact goal state. Reply to
  `HANDOFF/outbox/codex-mbi-collapse-reply.md`.
