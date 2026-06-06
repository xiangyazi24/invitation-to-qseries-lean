# TASK (codex / gpt-5.5): crank surjectivity mod 5, n=3 case (partitions of 19)

INDEPENDENT bonus task. Do NOT touch RamanujanQuinticJTP.lean, QseriesFormalization.lean, or
Audit.lean. Create a NEW file only.

Mirror `QseriesFormalization/Chapter14_CrankN14.lean` (the n=2 case, just merged) EXACTLY, but for
n=3: `19 = 5·3 + 4`. Create `QseriesFormalization/Chapter14_CrankN19.lean`.
Define 5 partitions of 19 whose cranks cover all residues {0,1,2,3,4} mod 5 (suggested:
[19]→4, [18,1]→0 (1∈parts, ω=1, μ=1), [17,2]→2, [16,3]→1, [13,3,3]→3 — VERIFY each crank yourself),
compute each crank (if_pos/if_neg + crankOnes/crankMu/crankLargest via decide), and prove
`crank_n19_surjective_mod_five` mirroring `crank_n14_surjective_mod_five`.

NEVER lake build; verify `lake env lean QseriesFormalization/Chapter14_CrankN19.lean`.
0 sorry/axiom/admit; fresh #print axioms clean. Reply to HANDOFF/outbox/codex-crank-n3-reply.md.
