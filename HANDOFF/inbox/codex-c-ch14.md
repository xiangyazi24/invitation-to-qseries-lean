# TASK (codex / gpt-5.5): Ch14 Theorem 11.6 (Lost Notebook identity) — the verified §14 chapter-main
INDEPENDENT. Create ONLY new file `QseriesFormalization/Chapter14_Thm116.lean`. Do NOT touch
RamanujanQuinticJTP.lean / QseriesFormalization.lean / Audit.lean / other chapters (you MAY import
`Pending.RamanujanQuinticJTP` and `Chapter11` to reuse machinery).

VERIFIED Chan target (PDF p. for §11/§14): **Theorem 11.6** (the Lost Notebook identity proved in §14.1,
Andrews-Berndt top-10 #3). Let ζ = e^{2πi/5}. Then
```
(q;q)∞ / ((ζq;q)∞ (ζ⁻¹q;q)∞)
  = A(q⁵) − q(ζ+ζ⁻¹)² B(q⁵) + q²(ζ²+ζ⁻²) C(q⁵) − q³(ζ+ζ⁻¹) D(q⁵)
```
where (with f(−q)=(q;q)∞, and G,H the Rogers-Ramanujan functions G=1/((q;q⁵)(q⁴;q⁵)), H=1/((q²;q⁵)(q³;q⁵))):
A=f(−q⁵)·G²/H, B=f(−q⁵)·G, C=f(−q⁵)·H, D=f(−q⁵)·H²/G.

This is a **JTP-at-a-5th-root** identity, same flavour as the proven `RamanujanQuinticJTP.
section83JTPProductPS_eq_rhs_pair14/23` (those handle `(q;q)(ζq;q)(ζ⁻¹q;q)`; here the ζ-factors are in the
DENOMINATOR — reciprocal — and the RHS is the FULL 4-term period decomposition A,B,C,D rather than the
2-term pair). Reuse the η-period-collapse technique (`section83_triangular_tsum_period_collapse_of_ne_zero`
+ the Gaussian-period algebra `quinticPeriodAlpha/Beta`).

Bounded deliverable (largest you can CLOSE, 0 sorry): define A,B,C,D (G,H may need `Chapter11` truncations
or formal-PS RR-product defs), state Theorem 11.6, prove via the JTP-at-ζ collapse. If the reciprocal /
G,H-product layer blocks full closure, bank the well-defined pieces (the LHS=period-sum step) and report
the precise blocker. Make REAL progress; NO fake/sorry. NEVER native_decide; NEVER lake build; verify
`lake env lean QseriesFormalization/Chapter14_Thm116.lean`. 0 sorry/axiom/admit; clean-3 axioms.
Reply to HANDOFF/outbox/codex-c-ch14-reply.md.
