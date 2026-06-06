# TASK (codex/gpt-5.5): build toward the Ramanujan quintic core·P5 = E^11 (Hirschhorn §8.5/§8.6)

NEW file `QseriesFormalization/Pending/RamanujanQuintic.lean` (build infra here; the final
`core*P5=E^11` can be proved here too). Touch ONLY this new file. Single-file verify; 0 sorry/axiom/
admit; no sorryAx. Reply to `HANDOFF/outbox/codex-quintic-cyclotomic-reply.md`.
This is a DEDICATED multi-round effort (the "difficult and deep" identity) — partial genuine
progress (a working sub-module, 0 sorry) is the expected and valued outcome. Do NOT overclaim.

## Target (closes the MBI via the proven wrapper)
`ramanujanMod5ProductCoreThetaRat * (expand 5 (by decide) (qPochInfPS ℚ)) = (qPochInfPS ℚ)^11`
where `core = G^10 - 11*X*H^5*G^5 - X^2*H^10`, `H = pentagonalProduct014PS ℚ`,
`G = pentagonalProduct023PS ℚ` (read exact defs in `Chapter16_MBI_Proof.lean`). This is
Hirschhorn (8.5.6). It is NUMERICALLY TRUE (checked to degree 80) — you are proving a true identity.

## Known proof routes (all need 5th-root-of-unity infrastructure — build the minimal piece)
Hirschhorn §8.5/§8.6 factorises it as `(G^5 - β^5 X H^5)(G^5 - α^5 X H^5) = E^11/P5` where α,β are
related to a primitive 5th root ζ, with `α^5+β^5 = 11`, `α^5 β^5 = -1`. The factors come from
(8.6.1)/(8.6.2): `(q^10,q^15,q^25;q^25)_∞ - β(q^5,q^20,q^25;q^25)_∞ = E(q^5)·∏_k(1+βq^k+q^{2k})`.

## What to build (the reusable infrastructure)
1. A "scale the variable" ring hom on `PowerSeries`: `scaleX (c : R) : R⟦X⟧ →+* R⟦X⟧` sending
   `∑ aₙ Xⁿ ↦ ∑ aₙ cⁿ Xⁿ` (i.e. substitute `X ↦ c·X`). Prove it's a ring hom, commutes with
   `expand`, and `scaleX c (qPochInfPS R) = ∏(1 - cⁿ Xⁿ)` etc.
2. Over `R = CyclotomicField 5 ℚ` (Mathlib) with `ζ` a primitive 5th root (`IsPrimitiveRoot`):
   the product `∏_{j=0}^4 scaleX (ζ^j) (qPochInfPS R)` collapses to an `expand 5`-quotient
   (the residues mod 5 telescope) — this is the heart of (8.6.x).
3. Assemble the factor identities (8.6.1)/(8.6.2), multiply to get (8.5.6), then descend to ℚ
   (the symmetric functions α^5+β^5=11, α^5β^5=-1 are rational, so the final identity lives over ℚ).

## Infrastructure available
- `Pending/Chapter16_MBI_Proof.lean`: `H*G=E*P5` factorisation, the keystone (products=theta),
  the five-dissection, (5.3.1)/(5.3.2), `most_beautiful_identity_of_compressed_theta_clean_quintic`.
- `Pending/JTP_FormalPS_Pentagonal.lean`: `qPochAPPS`, `expand_qPochAPPS`, the keystone.
- Mathlib: `CyclotomicField`, `IsPrimitiveRoot`, `PowerSeries`, `Polynomial.cyclotomic`.

## Deliverable (largest with 0 sorry)
Best: `core*P5 = E^11` ⇒ feed the wrapper ⇒ unconditional `most_beautiful_identity`. Realistic:
the `scaleX` ring-hom module + the 5-root product collapse (the reusable core). Report EXACTLY what
closed; `#print axioms` will be verified. Partial 0-sorry infrastructure > fake-complete.
