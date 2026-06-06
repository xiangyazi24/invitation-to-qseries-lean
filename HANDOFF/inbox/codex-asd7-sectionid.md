# TASK (codex/gpt-5.5): ASD-7 section identification + unconditional η-quotient congruences

NEW file `QseriesFormalization/Pending/ASD_Mod7_EtaQuotient.lean` importing
`Pending.JTP_FormalPS_Mod7`, `Pending.Chapter17_ASD_Mod7`, `Pending.ASD_EtaProducts` as needed.
Touch ONLY your new file. Single-file verify; 0 sorry/axiom/admit; no sorryAx.
Reply to `HANDOFF/outbox/codex-asd7-sectionid-reply.md`.

## The mod-5 analogue is COMPLETE — mirror it exactly for modulus 7
`Pending/ASD_EtaProducts.lean` did, for mod 5 (all 0 sorry): proved the ZMod-5 section
identifications `A0_eq_asd5FProductPS_zmod5 : A 0 = F`, `A1_eq...: A 1 = -3qG` by pure coefficient
matching (residue-triangular index splits ↔ pentagonal exponents), then discharged the conditional
bridges to get the UNCONDITIONAL `partition_section_{0..4}_eq_eta_product` congruences. DO THE SAME
for mod 7.

## Now available (0 sorry)
- `Pending/JTP_FormalPS_Mod7.lean`: the mod-7 keystone + H,J,K eta-product=theta identities
  (`asd7{H,J,K}ProductPS_eq_asd7{H,J,K}SeriesPS_complex/_rat`), `theta7` machinery.
- `Pending/Chapter17_ASD_Mod7.lean`: `qPochInfPS_cube_decompose_mod_7 : (qPoch ZMod 7)^3 =
  ASD7 0 + ASD7 1 + ASD7 3` and the `section7`/`ASD7` objects.
- `Chapter17_Mod7PerTermAnalysis`: mod-7 triangular/jacobiTripleSign residue lemmas.

## Goal (Hirschhorn §3.7)
1. ZMod-7 section identifications (coefficient matching, mirror `A0_eq_asd5FProductPS_zmod5`):
   `(q;q)^3 ≡ H(q^7) - 3qJ(q^7) + 5q^3 K(q^7) (mod 7)`, i.e. identify `ASD7 0 = H(q^7)`,
   `ASD7 1 = -3q·J(q^7)` (residue-1 part), `ASD7 3 = 5q^3·K(q^7)` (residue-3 part) over ZMod 7 —
   match the residue-r triangular indices to the H/J/K theta exponents with the signs (-1,-3,5).
2. Discharge the resulting bridges to get UNCONDITIONAL ASD mod-7 eta-quotient congruences for
   `∑ p(7n+j) qⁿ` (j=0..6), including the clean `∑ p(7n+5) qⁿ ≡ 0`.

## Deliverable (largest with 0 sorry)
Best: the section identifications + the unconditional ASD-7 eta-quotient congruences. Acceptable:
the ASD7 0 = H identification, or one congruence. Report exactly what closed. 0-sorry partial > fake.
