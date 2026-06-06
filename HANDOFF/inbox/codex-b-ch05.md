# TASK (codex / gpt-5.5): Ch5 Boson–Fermion proof of JTP — the §5-specific content
INDEPENDENT. Do NOT touch RamanujanQuinticJTP.lean, QseriesFormalization.lean, Audit.lean, or other agents' files.
Create NEW file `QseriesFormalization/Chapter05_BosonFermion.lean` (import Chapter05).

CONTEXT: Chapter05.lean has the Borcherds fermion-sea setup: `AdmissibleState`, `charge`, `energy`, `vacuum`,
`charge_eq_zero_iff`. Chan §5's DISTINCT content is the Boson–Fermion proof of JTP: the partition function
`Z(q,z) = ∑_{states} z^{charge} q^{energy}` evaluated two ways (fermionic product over modes vs bosonic
charge-sector sum) gives JTP. (The JTP *result* is already in Ch02/Ch03 — this task is the §5 METHOD.)
Bounded deliverable (largest you can CLOSE, 0 sorry):
1. Define `Z(q,z)` over AdmissibleStates.
2. Prove the fermionic evaluation (product over single-mode occupations) and/or the bosonic charge-sector
   decomposition; aim toward `Z = (product form) = (charge-sector sum)` = JTP.
This is large/combinatorial (no new theory needed). Make REAL progress, report EXACTLY what closes vs blocks.
If the full Z=Z is out of reach, bank the well-defined pieces (Z def + one evaluation). NO fake/sorry.
NEVER native_decide; NEVER lake build; verify `lake env lean QseriesFormalization/Chapter05_BosonFermion.lean`.
0 sorry/axiom/admit; clean-3 axioms. Reply to HANDOFF/outbox/codex-b-ch05-reply.md.
