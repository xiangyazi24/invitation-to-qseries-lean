# TASK (codex/gpt-5.5): full ASD mod-7 congruences (Hirschhorn §3.7), section-component form

NEW file `QseriesFormalization/Pending/Chapter17_ASD_Mod7_Full.lean`, importing committed
`QseriesFormalization.Pending.Chapter17_ASD_Mod7` (reuse `section7`/`ASD7`/`qPochInfPS_cube_decompose_mod_7`).
Touch ONLY this new file. Single-file verify; 0 sorry/axiom/admit; no sorryAx. Reply to
`HANDOFF/outbox/codex-asd-mod7-full-reply.md`.

## Goal (Hirschhorn §3.7, mirror the committed `Chapter17_ASD_Mod5_Full` for mod 7)
Over ZMod 7: `1/(q;q) = ((q;q)^3)^2 / (q;q)^7 ≡ (ASD7 0 + ASD7 1 + ASD7 3)^2 / (q^7;q^7)` (Frobenius
`(q;q)^7 = expand 7 qPoch`). Extract residues mod 7 to express
`mk (fun n => (partitionGenFun (ZMod 7)).coeff (7n+j))` in section-component form, including the
sanity case `∑ p(7n+5) qⁿ ≡ 0`. Follow EXACTLY the structure of `Chapter17_ASD_Mod5_Full.lean`
(study it: `partitionGenFun_mul_D5_sq_eq_S5_cube`, `section_kr`, the residue-convolution + Frobenius
bookkeeping) — adapt 5→7, cube→square (since (q;q)^6 = ((q;q)^3)^2 here, exponent 2 not 3).
Deliverable: the section-component congruences + `partition_section_5_eq_zero` (j=5 vanishing).
Skip the η-product identification (stretch). 0-sorry partial beats fake-complete.
