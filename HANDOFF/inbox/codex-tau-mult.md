# TASK (codex / gpt-5.5): τ(14),τ(15) + two new multiplicativity instances (Ch20)

INDEPENDENT bonus. Another agent edits RamanujanQuinticJTP.lean — do NOT touch it, nor
QseriesFormalization.lean, Audit.lean, Chapter20.lean, or Chapter20_TauValues.lean. Create a NEW file
`QseriesFormalization/Chapter20_TauMult.lean` (import Chapter20 and Chapter20_TauValues).

Mirror the existing `ramanujanTau_thirteen` / `ramanujanTau_ten_eq` proof style exactly:
1. `ramanujanTau_fourteen : ramanujanTau R 14 = 401856`
2. `ramanujanTau_fifteen  : ramanujanTau R 15 = 1217160`
3. Multiplicativity (coprime args), mirroring `ramanujanTau_ten_eq`:
   - `ramanujanTau_fourteen_eq : ramanujanTau ℤ 14 = ramanujanTau ℤ 2 * ramanujanTau ℤ 7`
     (check: (-24)·(-16744) = 401856 ✓)
   - `ramanujanTau_fifteen_eq  : ramanujanTau ℤ 15 = ramanujanTau ℤ 3 * ramanujanTau ℤ 5`
     (check: 252·4830 = 1217160 ✓)
(τ(7) = -16744 is `ramanujanTau_seven` in Chapter20.)

NEVER native_decide (keep clean-3 axioms; use decide/the same tactic as ramanujanTau_eight, maxHeartbeats 0 if needed).
NEVER lake build; verify `lake env lean QseriesFormalization/Chapter20_TauMult.lean`. 0 sorry/axiom/admit;
fresh #print axioms = [propext, Classical.choice, Quot.sound]. If τ(15) is too slow, do τ(14)+its
multiplicativity and report the cutoff. Reply to HANDOFF/outbox/codex-tau-mult-reply.md.
