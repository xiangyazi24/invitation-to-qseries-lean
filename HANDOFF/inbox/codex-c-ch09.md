# TASK (codex / gpt-5.5): Ch9 Bailey's lemma (Chan Thm 9.1/9.2) — verified target
INDEPENDENT. Create ONLY new file `QseriesFormalization/Chapter09_BaileyLemma.lean` (import Chapter09).
Do NOT touch RamanujanQuinticJTP.lean / QseriesFormalization.lean / Audit.lean / other chapters.

VERIFIED Chan target (PDF): **Theorem 9.1 (Bailey's lemma):** given a Bailey pair (a,b), `Lb = M·Da`,
i.e. `(Da, Lb)` is again a Bailey pair. Proof = Lemma 9.1 (`LM = MD` as operators on sequences) + `b = Ma`.
**Theorem 9.2:** `L²b = M·D²a`, then applied to prove the first Rogers-Ramanujan identity (third RR proof).
Chapter09.lean already has `IsBaileyPairUpTo`, finite preservation to N=7.

Bounded deliverable (largest you can CLOSE, 0 sorry):
1. Define the operators `L`, `M`, `D` on sequences (per Chan §9 / Def 9.2) and the Bailey-pair relation.
2. Prove **Lemma 9.1** (`L∘M = M∘D`) and **Theorem 9.1** (`Lb = M·Da`), then **Theorem 9.2**.
3. If reachable, apply to the first RR identity (Chan's "third proof"). If the infinite-sum analytic
   layer blocks the RR application, bank the algebraic Bailey lemma (Thm 9.1/9.2) and report.
Make REAL progress; report exactly what closes vs blocks. NO fake/sorry. NEVER native_decide; NEVER lake
build; verify `lake env lean QseriesFormalization/Chapter09_BaileyLemma.lean`. 0 sorry/axiom/admit;
clean-3 axioms. Reply to HANDOFF/outbox/codex-c-ch09-reply.md.
