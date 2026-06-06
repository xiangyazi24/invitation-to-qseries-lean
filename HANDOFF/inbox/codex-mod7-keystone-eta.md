# TASK (codex/gpt-5.5): mod-7 keystone + H,J,K η-products + ASD-7 η-quotients (mirror the COMPLETE mod-5 path)

NEW file `QseriesFormalization/Pending/JTP_FormalPS_Mod7.lean` (+ optionally a companion for the
ASD-7 connection). Touch ONLY your new file(s); do NOT edit existing files or aggregators.
Single-file verify; 0 sorry/axiom/admit; no sorryAx. Reply to `HANDOFF/outbox/codex-mod7-keystone-eta-reply.md`.

## The mod-5 path is COMPLETE — use it as your exact template
`Pending/JTP_FormalPS_Pentagonal.lean` (mod-5) and `Pending/ASD_EtaProducts.lean` together now give,
all 0 sorry: the formal AP-product `qPochAPPS`, the product=series keystone
`pentagonalProduct0xxPS_eq_pentagonal0xxSeriesPS_complex/_rat`, the analytic-formal bridge
(`tendsto`/dominated-convergence/`tendsto_nhds_unique`), `expand_qPochAPPS`, the η-product
identities F,G, and the ZMod-5 section identification `A0_eq_asd5FProductPS_zmod5` by coefficient
matching. MIRROR this entire chain for modulus 7.

## Goal (Hirschhorn §3.7)
1. mod-7 keystone: the pentagonal-AP products `(q^a,q^b,q^7;q^7)_∞ = theta` (formal-PS over ℂ then ℚ),
   the mod-7 analogues of the two mod-5 keystone identities. (The analytic JTP specialisations come
   from `Ch02.jacobiTripleProduct` / Ch03/Ch04 instantiated at the right q,z; derive them as the
   mod-5 file did its `analytic_pentagonal0xx_eq_mod5_product`.)
2. η-products `H,J,K` (mod 49): `(q^21,q^28,q^49;q^49)_∞ = ∑(-1)^k X^{(49k²-7k)/2}`,
   `(q^14,q^35,q^49;q^49) = ∑(-1)^k X^{(49k²-21k)/2}`, `(q^7,q^42,q^49;q^49) = ∑(-1)^k X^{(49k²-35k)/2}`
   (Hirschhorn 3.7.2), via `expand_qPochAPPS` (X↦X^7) on the mod-7 keystone — exactly like F,G from
   the mod-5 keystone.
3. (if time) ZMod-7 section identification: `(q;q)^3 ≡ H(q^7) - 3qJ(q^7) + 5q^3 K(q^7) (mod 7)`,
   identify the `ASD7 r` components (from `Chapter17_ASD_Mod7`) with H,J,K by coefficient matching
   (mirror `A0_eq_asd5FProductPS_zmod5`), discharging the ASD-7 η-quotient congruences.

## Deliverable (largest with 0 sorry)
Best: the full mod-7 chain through the ASD-7 η-quotient congruences. Acceptable: the mod-7 keystone
+ H,J,K η-product identities. Report exactly what closed. 0-sorry partial > fake-complete.
