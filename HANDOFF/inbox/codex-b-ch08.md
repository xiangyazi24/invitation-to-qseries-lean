# TASK (codex / gpt-5.5): Ch8 Gaussian-polynomial side + Chan Thm 8.1 (finite Rogers–Ramanujan)
INDEPENDENT. Do NOT touch RamanujanQuinticJTP.lean, QseriesFormalization.lean, Audit.lean, or other agents' files.
Create NEW file `QseriesFormalization/Pending/Chapter08_Gaussian.lean` (import Pending.Chapter08_FiniteRR).

CONTEXT: `Pending/Chapter08_FiniteRR.lean` has `EFinite q a N` (= Chan's sum side E_{N+1}(a) = ∑_j q^{j²+aj}·gaussianBinom(N-j,j))
and `EFinite_recurrence`. MISSING (Chan Thm 8.1): the Gaussian-polynomial side
  D_n(a) = ∑_j (-1)^j q^{j(5j+1)/2 - 2aj} · gaussianBinom[n+a, ⌊(n+3a-5j)/2⌋]
and the finite identity E = D.
Bounded deliverable (largest you can CLOSE, 0 sorry):
1. Define `DFinite q a N` (the Gaussian-polynomial side).
2. Prove Chan Thm 8.1 (`EFinite = DFinite`) for a=0 and a=1 (matching the proven EFinite cases), via the
   shared second-order recurrence + base cases (uniqueness bridge — mirror how EFinite_recurrence is used).
NOTE: a≥2 has a known recurrence subtlety (`DFinite_recurrence_fails_a3_at_zero` in the existing file) — do
NOT claim general a; only a=0,1. Make real progress, report exactly what closes. NO fake/sorry.
NEVER native_decide; NEVER lake build; verify `lake env lean QseriesFormalization/Pending/Chapter08_Gaussian.lean`.
0 sorry/axiom/admit; clean-3 axioms. Reply to HANDOFF/outbox/codex-b-ch08-reply.md.
