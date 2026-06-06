# TASK (codex/gpt-5.5): close A 0 = F, A 1 = -3qG over ZMod 5 (the final ASD-5 core)

Extend `QseriesFormalization/Pending/ASD_EtaProducts.lean` (namespace `ASDEtaProducts`).
Touch ONLY this file. Single-file verify; 0 sorry/axiom/admit; no sorryAx.
Reply to `HANDOFF/outbox/codex-asd5-sectionid-reply.md`.

## The remaining UNCONDITIONAL core (discharges all the conditional eta-quotient bridges)
Prove, over `ZMod 5`, the identifications of the ASD-5 section components with the F,G series:
```lean
-- A r := QseriesFormalization.Pending.ASDMod5.A r  = section5 (ZMod 5) r ((qPochInfPS (ZMod 5))^3)
-- (residue-r mod-5 section of jacobiThetaPS = (q;q)^3).
A 0 = asd5FSeriesPS (ZMod 5)
A 1 = -(3 : (ZMod 5)⟦X⟧) * X * (something) -- determine the EXACT form by coefficient analysis;
       Hirschhorn 3.6.4: (q;q)^3 ≡ F(q^5) - 3q G(q^5) (mod 5), so A 0 = F(q^5), A 1 = -3q·G(q^5)
       where F(q^5)=asd5FSeriesPS, and the G part is X·(asd5GSeriesPS shifted) — verify by coeffs.
```
(Read `Chapter17_ASD_Mod5.lean` for `A`'s exact def and the `asd5FSeriesPS`/`asd5GSeriesPS`
coeff lemmas `coeff_asd5FSeriesPS`/`coeff_asd5GSeriesPS` already in this file.)

## How — pure ZMod-5 coefficient matching (NOT analysis; like the mod-11 per-term proof)
For each n: `(A 0).coeff n = if n%5=0 then ((jacobiTripleSign n : ℤ):ZMod 5) else 0` (via
`coeff_section11`-style + `coeff_jacobiThetaPS`); and `(asd5FSeriesPS (ZMod 5)).coeff n` is given by
`coeff_asd5FSeriesPS`. Match them: the triangular numbers `T_j=j(j+1)/2` with `T_j≡0 (mod 5)` are
exactly `j≡0,4 (mod 5)`, and `T_j` then equals an F-exponent `(25k²-5k)/2`; the sign
`(-1)^j(2j+1) ≡ (-1)^k (mod 5)`. This is finite residue + exponent arithmetic (reuse the mod-5
triangular/jacobiTripleSign residue lemmas; `two_mul_triangular`; `decide` on ZMod-5 residues).

## Deliverable
Best: `A 0 = asd5FSeriesPS (ZMod 5)` AND `A 1 = -3q·G-form` ⇒ feed the existing
`partition_section_{0,1,2,3}_eq_eta_product_of_A0(_A1)` wrappers to get the UNCONDITIONAL ASD mod-5
eta-quotient congruences. Acceptable: just `A 0 = asd5FSeriesPS`. Report exactly what closed.
0-sorry partial > fake-complete.
