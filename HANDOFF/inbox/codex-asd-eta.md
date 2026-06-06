# TASK (codex/gpt-5.5): ASD mod-5/7 η-product identification (now that the JTP keystone is closed)

NEW file `QseriesFormalization/Pending/ASD_EtaProducts.lean`. Touch ONLY this file. Single-file
verify; 0 sorry/axiom/admit; no sorryAx. Reply to `HANDOFF/outbox/codex-asd-eta-reply.md`.

## Context — the keystone is now available
`QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean` now proves (0 sorry):
- `pentagonalProduct014PS_eq_pentagonal014SeriesPS_complex` : `(q,q⁴,q⁵;q⁵)_∞ = ∑(-1)^k X^{(5k²-3k)/2}`
- `pentagonalProduct023PS_eq_pentagonal023SeriesPS_complex` : `(q²,q³,q⁵;q⁵)_∞ = ∑(-1)^k X^{(5k²-k)/2}`
plus the GENERAL formal AP-product machinery `qPochAPPS R r m`, `apFactorPS`, `multipliable_apFactorPS`,
`hasProd_qPochAPPS`, `tendsto_qPochAPPS_partial`, and the analytic→formal bridge technique
(finite-partial coeff stabilization + dominated-convergence/Tannery + `tendsto_nhds_unique`).

## Goal (Hirschhorn 3.6.5 / 3.7.2 — η-product forms of F,G,H,J,K)
Prove the formal-PS theta=product identities for the modulus-25 (and modulus-49) AP triple products
that appear in the ASD congruences:
- `F(q⁵) = (q¹⁰,q¹⁵,q²⁵;q²⁵)_∞ = ∑(-1)^k X^{(25k²-5k)/2}`  (3.6.5)
- `G(q⁵) = (q⁵,q²⁰,q²⁵;q²⁵)_∞ = ∑(-1)^k X^{(25k²-15k)/2}`  (3.6.5)
- (mod-7) `H,J,K = (q²¹,q²⁸,q⁴⁹;q⁴⁹), (q¹⁴,q³⁵,q⁴⁹;q⁴⁹), (q⁷,q⁴²,q⁴⁹;q⁴⁹)` theta forms (3.7.2)
These are the SAME kind of JTP-specialisation as the keystone, just modulus 25 (resp. 49) instead
of 5. REUSE the general `qPochAPPS` machinery + the keystone's analytic-formal bridge technique;
the analytic JTP specialisations come from Ch02/Ch03 `jacobiTripleProduct` (instantiate at the right
q,z). Mirror `JTP_FormalPS_Pentagonal.lean` structure exactly (it is your template for r,m≠(·,5)).

## Then (if time) connect to the ASD section components
`Chapter17_ASD_Mod5_Full` / `Chapter17_ASD_Mod7_Full` express the congruences via section
components; identifying those with F,G (resp H,J,K) completes the ASD congruences in η-quotient
form. State precisely what you connect.

## Deliverable (largest with 0 sorry)
Best: the F,G (mod-25) theta=product identities + (mod-7) H,J,K. Acceptable: the general
`qPochAPPS`-based theta=product lemma for ONE of these moduli, reusing the keystone technique.
Report exactly what closed. 0-sorry partial > fake-complete.
