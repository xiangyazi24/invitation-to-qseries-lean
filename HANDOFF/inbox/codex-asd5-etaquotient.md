# TASK (codex/gpt-5.5): complete the ASD mod-5 congruences in η-quotient form

Extend `QseriesFormalization/Pending/ASD_EtaProducts.lean` (namespace `ASDEtaProducts`) — or a new
file importing it + `Chapter17_ASD_Mod5_Full`. Touch ONLY your file(s) among those two; do NOT edit
`Chapter17_ASD_Mod5_Full.lean` itself, `Chapter16_MBI_Proof.lean`, or aggregators. Single-file verify;
0 sorry/axiom/admit; no sorryAx. Reply to `HANDOFF/outbox/codex-asd5-etaquotient-reply.md`.

## Now available (0 sorry)
- `ASD_EtaProducts`: `asd5FProductPS_eq_asd5FSeriesPS_complex` ((q¹⁰,q¹⁵,q²⁵;q²⁵)=F-theta),
  `asd5GProductPS_eq_asd5GSeriesPS_complex` ((q⁵,q²⁰,q²⁵;q²⁵)=G-theta), `expand_qPochAPPS`.
- `Chapter17_ASD_Mod5_Full`: the ASD mod-5 congruences in SECTION-component form
  (`partitionGenFun_mul_D5_sq_eq_S5_cube`, `section_S5_cube_*`, `partition_section_*`).

## Goal
Connect the two: identify the ASD-5 section components (the residue parts of `(q;q)³ mod 5`,
i.e. Hirschhorn's `F(q⁵) − 3qG(q⁵)` decomposition) with the F,G η-products just closed, yielding the
ASD mod-5 congruences `∑ p(5n+j) qⁿ ≡ (η-quotient in F,G,(q;q))` (Hirschhorn 3.6.7) — explicitly the
j=0..4 η-quotient forms, not just section form. The bridge: `(q;q)³ ≡ F(q⁵)−3qG(q⁵) (mod 5)` where
F,G now have the proven η-product forms.

## Deliverable
Best: the j=0,…,4 η-quotient congruences (esp. the clean `∑p(5n+4)qⁿ ≡ 0` and the `(q²,q³,q⁵;q⁵)`
ratio forms). Acceptable: the identification `F(q⁵)/G(q⁵)` = the ASD section components, or one
η-quotient congruence. Report exactly what closed. 0-sorry partial > fake-complete.
