# batch50 — Ch18 positive t-core examples, performance-safe

Goal: add small positive examples for `IsTCoreByHooks`, such as showing
`[3,2,1]`, `[4,2]`, and `[2,2,1,1]` are `6`-cores or `7`-cores by hook lengths.

Context:
- Read `QseriesFormalization/Chapter18.lean`.
- The useful general theorem already exists:
  `isTCoreByHooks_of_hookLength_lt`.
- Concrete hook-length equalities for `[3,2,1]`, `[4,2]`, and `[2,2,1,1]`
  already exist.

Important performance warning:
- Do not add a large theorem that repeatedly runs
  `norm_num [FerrersCell, PartI.Ch05.FerrersCell, hookLength, armLength, legLength]`
  under variables `r c`. A previous attempt made `Chapter18` elaborate for many
  minutes and consume large memory.
- First test any exhaustive-cell proof in a tiny isolated lemma.
- Prefer using the already-proved concrete hook-length equalities after proving
  the finite cell cases.

Deliverable:
- Touch only `QseriesFormalization/Chapter18.lean`.
- No `sorry`, no `axiom`, no `native_decide`.
- Build only:
  `lake build QseriesFormalization.Chapter18`
- Run:
  `rg -n "sorry|axiom|native_decide" QseriesFormalization/Chapter18.lean`
- Write a short reply to `HANDOFF/outbox/batch50-ch18-positive-core-examples-reply.md`.
