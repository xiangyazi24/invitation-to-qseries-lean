# TASK (codex / gpt-5.5): prove hE0 → close Ch14 Thm 11.6 (Opus-verified, the path to Ch14 PASS)

## What's done
Ch14 f-power bug is fixed (chan116A/B/C/D use `fMinusQ25PS = expand 25`). Product rewrites are in:
`section83A = rrHDenAtQ5PS · fMinusQ25PS`, `section83B = rrGDenAtQ5PS · fMinusQ25PS`. The blocker
`chan116RHS · section83_rhs_pair14 ζ = (qPochInfPS ℂ)²` reduces (codex's own analysis) to the
**E0 5-dissection bridge**, which fires via `Ch16MBIProof.E5_zero_product_bridge_of_compressed`,
whose hypothesis is the unproven **hE0**:
```
hE0 : compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonalProduct014PS ℚ
        = PowerSeries.expand 5 (by decide) (qPochInfPS ℚ) * pentagonalProduct023PS ℚ
```

## hE0 is TRUE (Opus-verified numerically, residual 0 over degree 28)
Prove it. It is the **residue-0 component of the (q;q)∞ 5-dissection**. Leverage the existing MBI
machinery in `Chapter16_MBI_Proof.lean` (do NOT re-derive from scratch):
- `qPochInfPS_five_dissection` (the (q;q) = E0+E1+E2 section decomposition),
- the keystone AP-product factorisation
  `pentagonalProduct014_mul_pentagonalProduct023_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat`
  (`P014·P023 = qPoch·expand5 qPoch`),
- the surprising results (5.3.1) `E0·E2=−E1²`, (5.3.2) `E1=−qE(q²⁵)`, and the section/`IsRes5` calculus,
- `E5_zero_eq_expand_compressedSection5_zero_qPochInfPS_rat` (E5 0 = expand5(compressedSection5 0)).
Note (Opus): with the keystone `P014·P023 = qPoch·expand5(qPoch)`, hE0 is equivalent to
`E0c·P014² = qPoch·(expand5 qPoch)²` where `E0c = compressedSection5 0(qPoch)` — i.e. a pure
identity among the section-0 part and the pentagonal products. Find the cleanest route via the
section/AP machinery.

## Then close Ch14 (do it this round if hE0 closes)
hE0 (proven) → `E5_zero_product_bridge_of_compressed hE0` gives the E0 bridge → discharge the Ch14
blocker `chan116RHS · section83_rhs_pair14 ζ = (qPochInfPS ℂ)²` → combine with the proven
`chan116LHS_mul_section83_rhs_pair14` and cancel the unit `section83` → **Thm 11.6** `chan116LHS = chan116RHS`.

## Rules
- hE0 lives most naturally in `Chapter16_MBI_Proof.lean` (it's a Ch16-section identity); the Thm 11.6
  close in `Chapter14_Thm116.lean`. Edit those two files only (I wire Audit). Do NOT touch
  `RamanujanQuinticJTP.lean`/`QseriesFormalization.lean`/`Audit.lean`.
- NEVER native_decide; NEVER lake build; verify `lake env lean` on each edited file. 0 sorry/axiom/admit.
- hE0 is Opus-verified TRUE — if a Lean step resists, report the exact goal state, do NOT assume it as a
  hypothesis (that's the smuggling anti-pattern). Reply to `HANDOFF/outbox/codex-ch14-hE0-close-reply.md`.
