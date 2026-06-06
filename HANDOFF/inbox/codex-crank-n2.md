# TASK (codex / gpt-5.5): crank surjectivity mod 5, n=2 case (partitions of 14)

## Independent bonus task — must NOT conflict with the in-flight quintic work
A separate agent is editing `QseriesFormalization/Pending/RamanujanQuinticJTP.lean`. You must
NOT touch that file, nor `QseriesFormalization.lean`, nor `QseriesFormalization/Audit.lean`
(I wire those). Create a NEW file only.

## Goal
Extend the Dyson–Garvan crank surjectivity-mod-5 ladder to **n = 2** (`14 = 5·2 + 4`):
prove that the cranks of partitions of 14 cover all residues `{0,1,2,3,4}` mod 5.
This follows the EXACT pattern of the already-proven cases:
- `Chapter14_CrankN4.lean` — n=0 (`crank_n4_surjective_mod_five`)
- `Chapter14_CrankN9.lean` — n=1 (`crank_n9_surjective_mod_five`)

## What to do
Create `QseriesFormalization/Chapter14_CrankN14.lean` (import `QseriesFormalization.Chapter14`,
and `Chapter14_CrankN9` if helpful), mirroring `Chapter14_CrankN9.lean` exactly:
1. Define 5 partitions of 14 whose cranks hit all 5 residues mod 5. Suggested witnesses
   (verify the crank values yourself — `crank` def + the `1 ∈ parts ? μ−ω : largest` rule):
   - `[14]`            → crank 14 ≡ 4
   - `[13,1]`          → `1 ∈ parts`, ω=1, μ=1 ⇒ crank 0
   - `[12,2]`          → largest 12 ≡ 2
   - `[11,3]`          → largest 11 ≡ 1
   - `[8,3,3]`         → largest 8 ≡ 3
   (Use `decide` for `parts_sum`/membership, same as the n=9 file.)
2. Compute each `crank … = …` (mirror `crank_partitionNineEightOne` etc., `if_pos/if_neg` +
   `crankOnes`/`crankMu`/`crankLargest` via `decide`).
3. State and prove `crank_n14_surjective_mod_five`: the image of `crank` over partitions of 14
   covers `{0,1,2,3,4}` mod 5 (mirror `crank_n9_surjective_mod_five`'s final statement form).

## Rules
- NEVER `lake build`. Verify single-file: `lake env lean QseriesFormalization/Chapter14_CrankN14.lean`.
- 0 sorry/axiom/admit; fresh `#print axioms` clean.
- Reply to `HANDOFF/outbox/codex-crank-n2-reply.md` with the theorem name and `#print axioms`.
