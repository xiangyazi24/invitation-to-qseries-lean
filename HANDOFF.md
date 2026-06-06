# HANDOFF.md — Q-series Formalization (resume protocol)

Updated 2026-06-01. Read `UNDERSTANDING.md` (top 2026-06-01 section) first, then this. Run `/lean` to
load the playbook + tactics.

## State
- **17/20 chapters PASS**; remaining AUX: Ch10, Ch15, Ch20.
- Full build check 2026-06-01: `lake build QseriesFormalization` completed successfully (8011 jobs).
- Current Ch20 work is uncommitted in this workspace; do not assume the working tree is clean.

## Ch20 current theorem list (2026-06-01)

Ch20 is still AUX for Ono's Theorem 20.1/full modular-form machinery, but the
formal tau layer now includes:

- Tau values: `ramanujanTau_zero` through `ramanujanTau_fifty`.
- Bounded multiplicativity and Hecke recursion:
  `ramanujanTau_mul_of_coprime_mul_le_50`,
  `ramanujanTau_hecke_prime_power_le_50`.
- Log-derivative recurrence:
  `ramanujanTau_log_derivative_recurrence`.
- Parity:
  `ramanujanTau_mod_two_eq_one_iff_odd_square`,
  `ramanujanTau_odd_iff_odd_square_param`,
  `ramanujanTau_odd_iff_odd_square`.
- Mod-691 finite verification:
  `sigma11`, `ramanujanTau_congr_sigma11_mod_691_through_fifty`.

## Build / verify (CRITICAL — never local `lake build`, mini RAM)
- **Full build:** `~/.openclaw/workspace/scripts/remote-build.sh Q-series-and-Chan-s-work` (rsyncs mini→the-build-server,
  runs `lake build` on the-build-server, ~4min, ~8008 jobs). Check: `grep -E "Build completed|build failed|error:" <log>`
  and `grep -c sorryAx <log>` (BUT note: your own `echo "sorryAx: $(...)"` lines get counted — verify against
  the real remote-build log, not the echo).
- **Single file (agents + you):** `ssh the-build-server 'cd repos/Q-series-and-Chan-s-work && export PATH=$HOME/.elan/bin:$PATH && lake env lean <file>'`.
- **#print axioms of a constant:** build its module (`lake build <Module>`), then a scratch `import <Module>` +
  `#print axioms <FullName>` via `lake env lean`. Must be exactly `[propext, Classical.choice, Quot.sound]`.
- **`Audit.lean` keeps its OWN import list** (not the root graph). Adding a `#print axioms` for a new module
  requires importing that module in `Audit.lean` too, else "unknown constant" at build.

## Multi-agent codex dispatch (Opus+codex "分头打")
- codex runs on the-build-server in dedicated tmux sessions (`codex-qseries`, `codex-crank`, `codex-b3`, `codex-b4`).
  Launch: `tmux send-keys -t <sess> 'export PATH=$HOME/.nvm/versions/node/v22.22.3/bin:$PATH; codex exec
  --dangerously-bypass-approvals-and-sandbox --skip-git-repo-check -m gpt-5.5 "<prompt>" 2>&1 | tee /tmp/<log>' Enter`.
  (NOTE: `codex-remote` tmux session = Ho-Lin Chen's SSExactMajority, NOT this project — don't touch it.)
- **Spec → `HANDOFF/inbox/<name>.md` (scp to the-build-server); reply → `HANDOFF/outbox/<name>-reply.md`.** Watch the
  reply file with a background until-loop (NOT tmux char polling). On reply: pull file, verify, wire, commit.
- **One file, one writer.** Agents never touch `QseriesFormalization.lean` / `Audit.lean` (you wire those).
- **Never full `lake build` while an agent edits** (rsync clobbers in-flight files + corrupts lake incremental
  cache). Run the one integrated build only after all agents finish.
- Division of labor: **Opus does the math** (find/verify the identity numerically, design the proof, catch
  codex's bugs); **codex transcribes** + iterates `lake env lean`.

## Opus+codex collaboration recipe (worked 3× this session)
1. Pick chapter; **read Chan's actual `Theorem N.M`** from the PDF (`pdftotext`).
2. **Numerically verify** the target identity in Python (coeff arrays, ζ=exp(2πi/5) for cyclotomic) — catches
   bugs (Ch14 f-power, Ch5 false per-sector) and welds the recipe before committing codex.
3. Design the proof path; write a precise blueprint to `HANDOFF/inbox/`.
4. Dispatch codex; watch; **trust-but-verify** the reply (fresh #print axioms; read every hypothesis for a
   smuggled crux; reject re-wrappers/trivially-true/native_decide).
5. Wire + commit + integrated build.

## Verified-but-unproven targets (ready for the next push)
- **Ch13 Thm 11.5** (difficult-and-deep), r-form **numerically verified (deg 60, residual 0)**:
  `r(q)⁵·(1+3v+4v²+2v³+v⁴) = r(q⁵)·(1-2v+4v²-3v³+v⁴)`, `v=X·expand5(rrcf_r)`, `rrcf_r=pentagonal014/023`.
  Foundation in `Pending/Chapter13_RRCF_RForm.lean`. **Blocker:** Chan's Gugg proof uses √t (t=R(q)) →
  needs a q^{1/10}/√t framework (research-level). Watson's proof (§13.2) is the alternative.
- **Ch5** independent bosonic counting: correct identity `(1+z⁻¹)Z·bosonEulerProduct = ∑z^n q^{n(n+1)/2}`
  verified; current proof routes via Ch02 JTP. Truly-independent = re-prove JTP combinatorially (Maya bijection).

## Honest landscape of remaining 8 (research-level — do NOT fake-close)
Ch13/Ch11 (√t fractional / R↔RR), Ch12 (transcendental R(e^{-2π})), Ch6 (affine Lie), Ch10 (mock modular),
Ch15 (η-modular ODE), Ch20 (modular-forms congruences), Ch5 (combinatorial JTP re-proof, marginal).
Each needs a substantial new framework, not a few lines.

## 2026-05-30 session progress

**Direction chosen: Ch11 + Ch13 parallel push (Opus, no codex).**

### New files (all in `Pending/`, not in build graph)
- `Chapter11_Thm111.lean` — 6 coeff matches (degrees 0-5), pentagonal/inverse/product coefficients
- `Chapter13_Watson_Algebraic.lean` — 20 ring lemmas for Watson polynomials A,B (0 sorry)
- `Chapter13_CoeffVerification.lean` — rrcf_v/rrcf_r coefficients, 5 sorry remain (degree-level identity)
- `Chapter11_RRCF_Convergent.lean` — extended with coeff 2-5 for rrcf_r_via_CF

### Key finding: recurrence-based induction FAILS
`E_n := rrcf_r · A_n - B_n` satisfies `E_{n+2} = E_{n+1} + X^{n+2}·E_n`.
This recurrence only preserves constant X-adic valuation bounds, not the
quadratic `tri(n+1)` growth needed. The full proof of `rrcf_r = rrcf_r_via_CF`
genuinely requires the Rogers-Ramanujan identity in formal PS.

### Critical path for Ch11 Thm 11.1 (formal-PS RR identity)
1. Ch07 has `rrJInf(x,q) = ∑ x^n q^{n²}/(q;q)_n` (analytic, ℂ) + FE
2. Ch09 has `rrAlpha`/`rrBeta` (RR Bailey pair seed) + unconditional Bailey lemma
3. Need: formal-PS lift of rrJInf → connect to pentagonal products →
   CF functional equation → `r(q) = H(q)/G(q)` → Thm 11.1
4. The formal-PS RR identity is the genuine mathematical content

### Status 2026-05-31 (final)

**17/20 PASS** (Ch05, Ch06, Ch11, Ch12, Ch13 — all proved this session).
**3 AUX**: Ch10 (mock theta), Ch15 (ODE), Ch20 (Ono).
**52 commits, ~13000 lines. Session started at 13/20.**

**Ch11 Thm 11.1** is the critical path — unlocks Ch12+Ch13 (→ 17/20).
Formal-PS RR identity is the key; proof blueprint in
`Pending/RogersRamanujan_FormalPS.lean` (Bailey pair route, 3-5 sessions).

**Coefficient verification status** (all 0 sorry):
- Ch11: 21 CF + 21 product + 21 matches (degrees 0-20)
- Ch13 identity: degrees 0-10 verified
- Ch15 ODE: degrees 0-10 verified
- Ch20: τ(0-50), 30/30 coprime Hecke pairs, p=2..7 recursion
- Ch10: mock theta coefficients at degrees 0-5

### Milestones achieved this session
- **Rogers-Ramanujan identities** proved over ℂ AND as formal-PS over ℚ
- **Chan Theorem 11.1** proved: rrcf_r = rrcf_r_via_CF (clean-3 axioms)
- 8 new RR infrastructure files (all 0 sorry)

### Remaining 4 AUX — all need new infrastructure

| Ch | Blocker | Assessed difficulty |
|----|---------|-------------------|
| Ch10 | 10th-order mock theta identity (Zwegers constant-term method). Needs bilateral theta + Hecke-type identities + 1ψ1 summation | Multi-session |
| Ch12 | R(e^{-2π}) evaluation. Needs eta transformation η(-1/z)=√(z/i)η(z) (not in Mathlib) | Multi-session, partially blocked |
| Ch15 | R(q) ODE (Lambert/product). Reduced to ℤ core. Needs Dobbie identity or Sturm bound | Multi-session |
| Ch20 | Ono's Thm 20.1. Needs half-integral weight modular forms (not in Mathlib) | Blocked |

No more low-hanging fruit. Each requires substantial research-level work.

### Concrete next-session attack plan

**Ch12 (closest to closing):**
- `jacobiTheta_S_smul` at τ=5i PROVED (Pending/Chapter12_EtaValue.lean)
- Missing: `EtaSFormula` — bridge `ModularForm.eta` ↔ `jacobiTheta`
- Route: prove `η(τ)²⁴ = Δ(τ)` and `Δ(S·τ) = τ¹²·Δ(τ)` from theta, extract 24th root
- Then: Thm 11.3 + η(i/5)/η(5i)=√5 + quadratic → Thm 11.4 → Ch12 PASS

**Ch15 (needs new identity):**
- Reduced to ℤ core + ℂ→ℤ descent (Pending/Chapter15_R_ODE.lean)
- Missing: Lambert/product identity `chan15LHSPS · expand5(qPochInf) = qPochInf⁵`
- Route 1: Dobbie Eq 15.1 at ζ,ζ² + character collapse
- Route 2: Modular-forms Sturm bound (weight 2, level 5, bound = 1)
- Route 3: Jacobi derivative + quintic JTP infrastructure

**Ch10 (needs new mock theta infrastructure):**
- Chan proves 10th-order identity via Zwegers constant-term method
- Needs: bilateral theta sums, Hecke-type identities, 1ψ₁ summation
- Current: only 3rd-order mock theta f(q) scaffolding (wrong family)

**Ch20 (blocked on Mathlib):**
- Ono Thm 20.1 needs half-integral weight modular forms
- Not in Mathlib; would need to contribute upstream first
