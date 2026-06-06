# TASK (codex / gpt-5.5): extend Ramanujan τ values + a new multiplicativity instance (Ch20)

## Independent bonus task — no conflict
Two other agents are editing `RamanujanQuinticJTP.lean` and have finished `Chapter14_CrankN14.lean`.
You must NOT touch `RamanujanQuinticJTP.lean`, `QseriesFormalization.lean`, or `Audit.lean`.
Create a NEW file only.

## Goal
`Chapter20.lean` currently proves `ramanujanTau R n` for n=0..8 (`ramanujanTau_zero..eight`) and the
multiplicativity instance τ(6)=τ(2)·τ(3). Extend the ladder.

Create `QseriesFormalization/Chapter20_TauValues.lean` (import `QseriesFormalization.Chapter20`),
mirroring the existing `ramanujanTau_eight` proof style exactly (`unfold ramanujanTau discriminantPS`
+ the established coefficient computation tactic — copy whatever `ramanujanTau_seven/eight` use):
1. Prove `ramanujanTau_nine .. ramanujanTau_thirteen` with the OEIS A000594 values:
   - τ(9) = -113643
   - τ(10) = -115920
   - τ(11) = 534612
   - τ(12) = -370944
   - τ(13) = -577738
   (state them generically over `R` like the existing ones, or over ℤ if the existing pattern does so —
   match `ramanujanTau_eight` exactly.)
2. Prove a NEW multiplicativity instance at coprime (2,5):
   `ramanujanTau_ten_eq : ramanujanTau ℤ 10 = ramanujanTau ℤ 2 * ramanujanTau ℤ 5`
   (since gcd(2,5)=1; check: (-24)·4830 = -115920 = τ(10) ✓). Mirror the existing `ramanujanTau_six`
   multiplicativity proof.

## Notes
- If `native_decide`/`decide` on the degree-12/13 coefficient is too slow, use `set_option
  maxHeartbeats 0` (or the same tactic `ramanujanTau_eight` uses) — match the existing proof method.
- NEVER `lake build`. Verify single-file: `lake env lean QseriesFormalization/Chapter20_TauValues.lean`.
- 0 sorry/axiom/admit; fresh `#print axioms` clean. If a value's computation is infeasible in
  reasonable time, prove as many as you can (τ(9)..τ(k)) and report the cutoff honestly.
- Reply to `HANDOFF/outbox/codex-tau-extend-reply.md` with theorem names + `#print axioms`.
