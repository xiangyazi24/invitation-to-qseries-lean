# TASK (codex / gpt-5.5): Ch14 crank generating function (Andrews–Garvan) — the §14 main result
INDEPENDENT. Do NOT touch RamanujanQuinticJTP.lean, QseriesFormalization.lean, Audit.lean, or files other
agents own. Create NEW file `QseriesFormalization/Chapter14_CrankGenFun.lean` (import Chapter14).

GOAL (Chan §14 main / Andrews–Garvan): the crank generating function
  ∑_{n≥0} ∑_{m} M(m,n) zᵐ qⁿ  =  (q;q)_∞ / ((zq;q)_∞ (z⁻¹q;q)_∞)
where M(m,n) = #{partitions of n with crank m}. Work in formal power series ℚ⟦X⟧ (or ℂ) where possible.
Bounded deliverable (pick the largest you can CLOSE with 0 sorry):
1. Define the formal crank generating function from the existing `crank` (Chapter14.lean).
2. Prove the product identity, OR if the full bilateral-z object is awkward in PowerSeries, prove the
   specialization at a concrete z / the coefficient form for small n, and state the general identity.
This is genuinely hard — make REAL progress and report EXACTLY what closes vs what blocks. NO fake/sorry.
NEVER native_decide; NEVER lake build; verify `lake env lean QseriesFormalization/Chapter14_CrankGenFun.lean`.
0 sorry/axiom/admit; clean-3 axioms. Reply to HANDOFF/outbox/codex-b-ch14-reply.md.
