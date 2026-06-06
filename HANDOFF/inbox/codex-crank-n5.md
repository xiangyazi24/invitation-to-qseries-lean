# TASK (codex): crank surjectivity mod 5, n=5 (partitions of 29)
INDEPENDENT bonus. Do NOT touch RamanujanQuinticJTP.lean, QseriesFormalization.lean, Audit.lean. NEW file only.
Mirror Chapter14_CrankN24.lean for n=5: 29 = 5·5+4. Create Chapter14_CrankN29.lean.
5 partitions of 29 covering residues {0,1,2,3,4} mod 5 (suggested [29]→4,[28,1]→0,[27,2]→2,[26,3]→1,[23,3,3]→3, VERIFY),
prove crank_n29_surjective_mod_five mirroring crank_n24_surjective_mod_five.
NEVER native_decide; NEVER lake build; verify lake env lean QseriesFormalization/Chapter14_CrankN29.lean.
0 sorry/axiom/admit; clean-3 axioms. Reply to HANDOFF/outbox/codex-crank-n5-reply.md.
