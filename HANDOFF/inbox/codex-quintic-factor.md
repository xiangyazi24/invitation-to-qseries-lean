# TASK (codex/gpt-5.5): use the scaleX/5th-root collapse → §8.6 factorisation → core·P5 = E^11 → full MBI

Extend `QseriesFormalization/Pending/RamanujanQuintic.lean` (namespace `RamanujanQuintic`).
Touch ONLY this file. Single-file verify; 0 sorry/axiom/admit; no sorryAx.
Reply to `HANDOFF/outbox/codex-quintic-factor-reply.md`. HARD; multiple rounds expected; partial
0-sorry progress is valued. Do NOT overclaim (#print axioms will be checked).

## Infrastructure you already built in THIS file (0 sorry) — build on it
- `scaleX (c) : R⟦X⟧ →+* R⟦X⟧` (X ↦ c·X) + `coeff_scaleX`, `scaleX_X/_X_pow/_oneSubXPow`,
  `scaleX_qPochFinitePS`, `scaleX_expand`.
- the 5th-root collapses `prod_scaleX_one_sub_X_pow_fifth`,
  `prod_scaleX_qPochFinitePS_fifth_collapse`, `quinticCyclotomic_qPochFinitePS_fifth_collapse`
  (∏_{j=0}^4 scaleX(ζ^j) (...) collapses to an expand-5 quotient).

## Goal — Hirschhorn §8.6 → §8.5 → (8.5.6)
Over `R = CyclotomicField 5 ℚ` with `ζ` a primitive 5th root:
1. §8.6 factor identities: `(q^10,q^15,q^25;q^25)_∞ - ζ^j·(q^5,q^20,q^25;q^25)_∞ =
   E(q^5)·∏_k(1+ζ^j q^k+q^{2k})` (the residue collapse of `∏ scaleX(ζ^{·}) qPoch` you have).
2. §8.5: multiply the relevant two factors `(G^5 - β^5 X H^5)(G^5 - α^5 X H^5)` (α^5,β^5 the
   symmetric pair with α^5+β^5=11, α^5β^5=-1) to get `core = G^10 - 11 X G^5 H^5 - X^2 H^10`,
   and the product equals `E^11/P5` (8.5.6). The symmetric functions are RATIONAL so the result
   descends to ℚ.
3. Conclude `ramanujanMod5ProductCoreThetaRat * (expand 5 (by decide) (qPochInfPS ℚ)) =
   (qPochInfPS ℚ)^11`, then apply
   `Ch16MBIProof.most_beautiful_identity_of_compressed_theta_clean_quintic` to close the
   unconditional `most_beautiful_identity` (in Chapter16_MBI_Proof, or re-state here and reference).

## Tools
- `Ch16MBIProof`: `H*G=E*P5` factorisation, keystone (products=theta), the clean-quintic wrapper.
- Mathlib `CyclotomicField`, `IsPrimitiveRoot`, `Polynomial.cyclotomic`, geometric-sum/`Finset.prod`.

## Deliverable
Best: `core*P5=E^11` ⇒ unconditional `most_beautiful_identity` (Ramanujan's Most Beautiful Identity,
COMPLETE). Realistic: the §8.6 factor identities or the descent to the two ℚ factors. Report EXACTLY
what closed; partial 0-sorry > fake.
