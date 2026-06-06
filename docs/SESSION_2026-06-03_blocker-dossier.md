# Session 2026-06-03 — audit status + precise remaining blockers

## Verified status: 17/20 PASS, audit-clean

`lake env lean QseriesFormalization/Audit.lean` (2026-06-03, HEAD 54fa0e4):
**338 `#print axioms` results, all `{propext, Classical.choice, Quot.sound}`** —
0 `sorryAx`, 0 `ofReduceBool`/`trustCompiler`, 0 errors. The 17 PASS chapters
genuinely pass the mechanical audit (no hidden sorry, no native_decide pollution).

PASS (17): Ch01–09, 11–14, 16–19. (Ch11/12/13 wired via Chan_Theorem_11_1,
Chapter13_Thm113, Chan_Theorem_11_4, Chapter13_DeepIdentity — all sorry-free, clean-3.)
AUX / open (3): **Ch10, Ch15, Ch20.**

## Ch15 — the Dobbie-Wronskian wall (2 days, 30 commits, never closed)

`Chapter15_WronskianIndependent.lean` (created 2026-06-01, 30 commits to 06-03)
reduces Chan §15 / Thm 11.7 (the RRCF differential equation `(q;q)^5/(q^5;q^5) =
1 − 5∑χ₅(n)n qⁿ/(1−qⁿ)`) to ONE `sorry`:
`pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff` on the `5∣4N+1` branch.
Everything else (Jacobi `qPochInfPS⁶ = jacobiThetaPS²`, the coeff bridges, the
`thetaOp` log-derivative lemmas, the iff-reductions, `eq_of_coeff_zero_eq_of_thetaOp_eq_rat`)
is proved. Routes tried and blocked: Sturm/valence bound (Mathlib lacks it),
backward recurrence (structurally blocked), theta-log ODE (circular), 5-string
coefficient grouping (no clean Z/5 orbit).

**The irreducible crux = Dobbie's identity** `A·B + 5(B·θA − A·θB) = P⁶`,
A = f(−q,−q⁴), B = f(−q²,−q³), P = (q;q)_∞, θ = q d/dq. chan1's exact reduction:

```
∑_{x≡7, y≡9 (mod 10),  x²+y²=40N+10} (−1)^{(x+y+4)/10}·(x²−y²)/8
   =   ∑_{u,v>0 odd,  u²+v²=8N+2} (−1)^{(u+v−2)/2}·u·v          (= dobbie_shell_identity N)
```

The natural Gaussian map (2−i): `u=(2x−y)/5, v=(x+2y)/5`, `x²+y²=5(u²+v²)`, but the
weight `(x²−y²)/8 → (3u²+8uv−3v²)/8 ≠ uv` — **no termwise bijection**; cancellation
is global. This is genuine Dobbie/Winquist theta-identity content. NOT a transcription
gap. Non-grind paths: (a) formalize Dobbie's original 1962 two-variable theta identity
and specialize; (b) build a Gaussian-integer / sum-of-two-squares layer for the shell
identity. Both are real sub-projects.

Full designs: `docs/chatgpt-designs-2026-06-03/chan1-Ch15-wronskian-route.md`,
`chan3b-Ch15-dlog-formalization.md`, and `HANDOFF/outbox/codex-ch15-wronskian-jacobi-reply.md`.

## Ch10 — tenth-order mock theta Eq 10.15 (multi-week)

chan2's decomposition: LHS = `Θ₉²H₀₀ − 2Θ₉Θ₁H₁₀ + Θ₁²H₁₁`, each `H` a finite
combination of nine `f_{2,3,2}` Hecke kernels. Bankable partial = that decomposition.
Hard remainder = the `f_{2,3,2}` Appell–Lerch evaluation (Hickerson–Mortenson / 1ψ1).
Design: `docs/chatgpt-designs-2026-06-03/chan2-Ch10-f232-decomposition.md`.

## Ch20 — full Ono Thm 20.1 (blocked)

Needs modular-forms-mod-ℓ machinery (half-integral weight Hecke) absent from Mathlib.
m=5,7,11 cases done; the universal statement (all primes ≥5) is not formalizable now.

## Bottom line

All three open chapters are blocked on research-level content (theta/Winquist
identity, Appell–Lerch mock-theta kernel, modular forms mod ℓ) that current Mathlib
cannot support without major new infrastructure. Verified deliverable: **17/20,
audit-clean**, with every remaining crux precisely isolated.
