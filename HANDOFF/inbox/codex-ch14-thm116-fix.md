# TASK (codex / gpt-5.5): Ch14 Thm 11.6 — FIX the f-power bug, then prove it (Opus diagnosed + verified)

## BUG (Opus found, numerically verified)
Chan defines `A(q) = f(−q⁵)·G(q)²/H(q)`, so `A(q⁵) = f(−(q⁵)⁵)·G(q⁵)²/H(q⁵) = f(−q²⁵)·G(q⁵)²/H(q⁵)`.
Your `chan116A/B/C/D` used `fMinusQ5PS = expand 5 (qPochInfPS)` = f(−q⁵) — WRONG, must be
**`f(−q²⁵) = expand 25 (qPochInfPS ℂ)`**. With f(−q⁵): Thm 11.6 fails at q⁵ (LHS=2, RHS=1). With f(−q²⁵):
`chan116LHS = chan116RHS` (Thm 11.6) holds (Opus-verified, residual ~1e-12), and `chan116RHS·section83
= (qPoch)²` holds (~1e-15).

## Fix
Redefine the f-factor in `chan116A/B/C/D` from `expand 5` to `expand 25 (qPochInfPS ℂ)` (rename to
`fMinusQ25PS` for clarity). `chan116LHS_mul_section83_rhs_pair14` (already proven) is unaffected — keep it.

## Then prove Thm 11.6 = `chan116LHS = chan116RHS`
With the fix this is TRUE. Note (Opus): `section83_rhs_pair14 ζ` is the η-product — you already have
`RamanujanQuinticJTP.section83JTPProductPS_eq_rhs_pair14` giving
`section83JTPProductPS ζ = section83_rhs_pair14 ζ`, and `section83JTPProductPS ζ = (q;q)∞(ζq;q)∞(ζ⁻¹q;q)∞`.
So `section83 = (q;q)(ζq;q)(ζ⁻¹q;q)`, a UNIT (constant coeff 1). Therefore:
```
chan116RHS · section83 = (qPoch)²   ⟺   chan116RHS = (qPoch)²/section83 = (q;q)/((ζq;q)(ζ⁻¹q;q)) = chan116LHS
```
So Thm 11.6 ⟺ the blocker `chan116RHS · section83_rhs_pair14 ζ = (qPochInfPS ℂ)²`. Prove THAT (then
`chan116LHS = chan116RHS` follows by cancelling the unit `section83`, combined with your proven
`chan116LHS·section83 = (qPoch)²`).

Bounded deliverable (largest you CLOSE, 0 sorry): (1) the f-power fix; (2) the blocker
`chan116RHS · section83_rhs_pair14 ζ = (qPochInfPS ℂ)²` for primitive ζ — this is a product identity in
`f(−q²⁵), G(q⁵), H(q⁵)` and the pentagonal products; use `section83A = rrHDen(q⁵)·f(−q²⁵)`,
`section83B = rrGDen(q⁵)·f(−q²⁵)` (so `section83A = f(−q²⁵)/rrHAtQ5`, `section83B = f(−q²⁵)/rrGAtQ5`) and the
period coefficients `ζ+ζ⁻¹ = quinticPeriodAlpha`, `ζ²+ζ⁻² = quinticPeriodBeta`. (3) Conclude Thm 11.6 by
cancelling the unit. This is the deep Lost-Notebook identity — if the G/H/f product algebra resists, bank
the fix + partial and report the exact blocker.

## Rules
- Edit ONLY `Chapter14_Thm116.lean`. NEVER native_decide; NEVER lake build; verify `lake env lean
  QseriesFormalization/Chapter14_Thm116.lean`. 0 sorry/axiom/admit; clean-3 axioms.
- The corrected identity is Opus-verified to deg 60. Reply to `HANDOFF/outbox/codex-ch14-thm116-fix-reply.md`.
