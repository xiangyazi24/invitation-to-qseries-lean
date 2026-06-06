# TASK (codex/gpt-5.5): the §8.6 factor identity → core·P5 = E^11 → full MBI (the last cyclotomic piece)

Extend `QseriesFormalization/Pending/RamanujanQuintic.lean`. Touch ONLY this file. Single-file verify;
0 sorry/axiom/admit; no sorryAx. Reply to `HANDOFF/outbox/codex-quintic-8point6-reply.md`.
HARD/deep; partial 0-sorry progress valued; do NOT overclaim (#print axioms checked).

## All infrastructure is built (0 sorry) — only the §8.6 factor identity remains
You already have: `scaleX`, `prod_scaleX_qPochFinitePS_fifth_collapse`,
`quinticCyclotomic_qPochFinitePS_fifth_collapse`, `quintic_factor_pair_mul_eq_core`,
`clean_quintic_of_factor_pair_product`,
`most_beautiful_identity_of_compressed_E5_zero_bridge_and_factor_pair_product`.
So `core*P5=E^11` (hence the full MBI) follows once you supply the **two §8.6 factor identities** with
the right `α^5, β^5`.

## The concrete cyclotomic facts (use these — they make α^5,β^5 elementary)
Let `ζ` be a primitive 5th root of unity, and the two Gaussian PERIODS
`α = ζ + ζ^4`, `β = ζ^2 + ζ^3`. Then (PROVE these first, they are `ring`/`IsPrimitiveRoot`-level):
- `α + β = -1`, `α*β = -1`  (periods are roots of `x^2 + x - 1`, since `1+ζ+ζ^2+ζ^3+ζ^4=0`).
- Hence by Newton's identities (from `α^2 = -α+1`, `β^2 = -β+1`): `α^5 + β^5 = 11`, `α^5 β^5 = -1`.
  (Compute power sums p1=-1,p2=3,p3=-4,p4=7,p5=-11 → wait recompute with e1=-1,e2=-1; the agent
  should derive p5 directly by `ring` from α^2=-α+1: α^5 = α·(α^2)^2 = α(1-α)^2 = α(1-2α+α^2)
  = α(1-2α+1-α) = α(2-3α) = 2α-3α^2 = 2α-3(1-α) = 5α-3; so α^5=5α-3, β^5=5β-3,
  α^5+β^5=5(α+β)-6 = -5-6 = -11; α^5β^5=(5α-3)(5β-3)=25αβ-15(α+β)+9=25(-1)-15(-1)+9=-25+15+9=-1.
  NOTE: this gives α^5+β^5 = -11, so adjust signs/which root vs the spec's +11 by choosing the
  factor convention — match `quintic_factor_pair_mul_eq_core`'s exact α^5+β^5 hypothesis.)
- §8.6 factor: `(q^10,q^15,q^25;q^25)_∞ - β·(q^5,q^20,q^25;q^25)_∞ = E(q^5)·∏_k(1+β q^k+q^{2k})`,
  obtained by splitting `∏_{j} scaleX(ζ^j)(qPoch)` (your collapse) by residue mod 5 / the period
  structure. The product `∏(1+β q^k+q^{2k})` raised to the 5th power and combined gives the `H^5,G^5`
  factors; their product is `E^11/P5` (8.5.6) — and the α,β,ζ all cancel to leave a ℚ identity.

## Deliverable
Best: the §8.6 factor identities + `core*P5=E^11` ⇒ unconditional `most_beautiful_identity`
(Ramanujan's Most Beautiful Identity, COMPLETE — also closes Chan §13's deep identity & feeds §15).
Realistic: the period algebra (`α^5,β^5` values, the `x^2+x-1` facts) + one factor identity. Report
EXACTLY what closed.
