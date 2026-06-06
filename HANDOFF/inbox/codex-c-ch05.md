# TASK (codex / gpt-5.5): Ch5 — close the INFINITE Boson-Fermion → JTP (extend committed finite work)
INDEPENDENT. EDIT your existing `QseriesFormalization/Chapter05_BosonFermion.lean` (already committed with
the finite-level results). Do NOT touch RamanujanQuinticJTP.lean / QseriesFormalization.lean / Audit.lean.

CONTEXT (already proven, 0 sorry, in that file): `Z(q,z)`, `finiteZ`, `finiteZ_eq_fermionicProductPartial`
(finite fermionic evaluation), `finiteZ_eq_sum_zpow_chargeEnergySectors` (finite bosonic charge-sector
decomposition), `fermionicProduct` (infinite form). Chan §5's main result is the **Boson-Fermion proof of
JTP**: the two infinite evaluations of `Z(q,z)` agree, giving JTP `∏(1-q^n)(1+zq^{n-1/2})(1+z^{-1}q^{n-1/2})
= ∑ z^k q^{k²/2}` (Chan's convention).

Bounded deliverable (largest you can CLOSE, 0 sorry):
1. Prove the infinite fermionic evaluation `Z = fermionicProduct` (summability over AdmissibleState +
   limit of `finiteZ_eq_fermionicProductPartial`).
2. Prove the infinite bosonic charge-sector sum and identify it with the JTP theta series.
3. Conclude JTP via Boson-Fermion (the §5-specific proof). If the summability/interchange is too heavy,
   close the fermionic side + state the bosonic side, and report the precise blocker.
Make REAL progress; report exactly what closes vs blocks. NO fake/sorry. NEVER native_decide; NEVER lake
build; verify `lake env lean QseriesFormalization/Chapter05_BosonFermion.lean`. 0 sorry/axiom/admit;
clean-3 axioms. Reply to HANDOFF/outbox/codex-c-ch05-reply.md.
