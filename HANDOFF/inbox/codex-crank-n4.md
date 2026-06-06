# TASK (codex / gpt-5.5): crank surjectivity mod 5, n=4 (partitions of 24)
INDEPENDENT bonus. Do NOT touch RamanujanQuinticJTP.lean, QseriesFormalization.lean, Audit.lean. NEW file only.
Mirror Chapter14_CrankN19.lean EXACTLY for n=4: 24 = 5·4+4. Create Chapter14_CrankN24.lean.
5 partitions of 24 covering residues {0,1,2,3,4} mod 5 (suggested: [24]→4, [23,1]→0, [22,2]→2, [21,3]→1,
[18,3,3]→3 — VERIFY each crank), prove crank_n24_surjective_mod_five mirroring crank_n19_surjective_mod_five.
NEVER native_decide; NEVER lake build; verify lake env lean QseriesFormalization/Chapter14_CrankN24.lean.
0 sorry/axiom/admit; clean-3 axioms. Reply to HANDOFF/outbox/codex-crank-n4-reply.md.
