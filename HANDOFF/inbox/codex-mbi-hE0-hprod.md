# TASK (codex/gpt-5.5): discharge hE0 + hprod → the FULL Most Beautiful Identity

Extend `QseriesFormalization/Pending/Chapter16_MBI_Proof.lean` (namespace `Ch16MBIProof`).
Touch ONLY this file. Single-file verify; 0 sorry/axiom/admit; no sorryAx.
Reply to `HANDOFF/outbox/codex-mbi-hE0-hprod-reply.md`.

## You are TWO formal-PS identities from the unconditional MBI.
Prove these (read exact defs of `compressedSection5`, `pentagonalProduct0xxPS`,
`ramanujanMod5ProductCoreCompressedRat` in the file), then apply
`most_beautiful_identity_of_compressed_E5_zero_bridge_and_product_core`:
```lean
hE0 : compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonalProduct014PS ℚ
        = PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) * pentagonalProduct023PS ℚ
hprod : (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 * ramanujanMod5ProductCoreCompressedRat
        = (qPochInfPS ℚ)^6 * (pentagonalProduct014PS ℚ)^5 * (pentagonalProduct023PS ℚ)^5
```

## KEY: use the keystone to turn products into theta series
`Pending/JTP_FormalPS_Pentagonal.lean`: `pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat`,
`pentagonalProduct023PS_eq_pentagonal023SeriesPS_rat` (over ℚ). Rewrite `pentagonalProduct0xxPS ℚ`
to the explicit theta series; then both hE0, hprod become identities among explicit theta series,
`qPochInfPS`, and `expand 5 qPoch`. Also available: this file's `qPochInfPS_five_dissection`
(qPoch = E5 0+E5 1+E5 2), (5.3.1) `E5 0·E5 2=-(E5 1)^2`, (5.3.2) `E5 1=-X·expand 25 qPoch`,
the rationalizer algebra; and `Pending/ASD_EtaProducts.lean` `expand_qPochAPPS` + the F/G η-products.

## Approach
- `hE0`: a residue/product relation — prove by coefficient matching over ℚ (mirror the ZMod-5
  proof `A0_eq_asd5FProductPS_zmod5` in ASD_EtaProducts: residue-section coeffs vs theta exponents,
  the pentagonal-exponent residue splits), or via the dissection + keystone + `ring`.
- `hprod`: the degree-6 identity. After rewriting the products to theta via the keystone, this is a
  finite formal-PS identity in `qPoch`, `expand5 qPoch`, and the two theta series; reduce using
  (5.3.1)/(5.3.2)/the five-dissection and close by `ring`/coefficient matching. This is Hirschhorn's
  degree-5 "surprising result" at the denominator level — the genuine deep core.

## Deliverable
Best: hE0 AND hprod ⇒ the unconditional `most_beautiful_identity` (THE PRIZE — Ramanujan's Most
Beautiful Identity, complete end-to-end). Acceptable: hE0 alone, or reducing hprod further with the
keystone substituted. Report exactly what closed. 0-sorry partial > fake-complete.
