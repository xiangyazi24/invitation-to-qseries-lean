# Q-Series Formalization — Audit Cleanup Plan

Durable worklist for clearing the remaining unfinished items found in
`PLAYBOOK_AUDIT.md`. Multi-agent parallel execution: one codex agent per
chapter on the-build-server, plus Claude subagents for research/prep.

**Last updated: 2026-05-24.**

## DONE this session (2026-05-23 / 05-24) — all 0 sorry / 0 axiom, build 7993, 0 sorryAx
**Ramanujan partition congruences (Hirschhorn Ch.3) — the headline sweep:**
- ✅ **mod-5/7/11**: `ramanujan_{5,7,11}_dvd_p_*` (all three classical congruences).
- ✅ **ASD mod-5** (§3.6): full η-quotient congruences `partition_section_{0..4}_eq_eta_product`
  via `A0=F`, `A1=-3qG` (`ASD_EtaProducts`).
- ✅ **ASD mod-7** (§3.7): full η-quotient congruences `partition_section_{0..6}_eq_eta_product`
  via `ASD7_0=H, ASD7_1=-3qJ, ASD7_3=5q³K` (`ASD_Mod7_EtaQuotient`).

**The keystone + its cascade (the session's structural unlock):**
- ✅ **JTP pentagonal-AP keystone** (`JTP_FormalPS_Pentagonal`): formal-PS product=series for
  `(q,q⁴,q⁵;q⁵)`, `(q²,q³,q⁵;q⁵)` (bilateral analytic→formal bridge — took ~6 rounds).
- ✅ **mod-5 F,G η-products** (3.6.5) + **mod-7 keystone + H,J,K η-products** (3.7.2)
  (`JTP_FormalPS_Mod7`), via `expand_qPochAPPS` (X↦X⁵, X↦X⁷).
- ✅ AP-product factorisation `product014·product023 = qPoch·expand5 qPoch`.

**Other chapters:**
- ✅ **Ch05** MISLABELED→AUX: JTP re-export. ✅ **Ch06** MISLABELED→AUX: Macdonald A₁.
- ✅ **Ch08**: Thm 8.1 (finite RR) for a=0,1 + a≥2 limitation counterexamples.
- ✅ **Ch20** τ-parity; **Ch14** crank n=1; mod-3 sign identity; `(q;q)³ mod 2` indicator.

**ONLY remaining hard core in this sweep:** the **MBI** (Ch16) is reduced to the **Ramanujan
quintic** product identity `core = G¹⁰ − 11·X·H⁵G⁵ − X²H¹⁰` (a degree-5 modular equation, related
to the Rogers-Ramanujan continued fraction `R(q)⁵`). All MBI wrappers + the factorisation are
proven; only this quintic is open. It is a genuine dedicated-effort identity, NOT an incremental
round. (Agent once overclaimed MBI closure — caught by `#print axioms`; it is NOT closed.)

## Reusable infrastructure (for the parallel agents)
- **B2**: `JacobiCubeAnalyticToFormal.qPochInfPS_pow_three_eq_jacobiThetaPS` : `(qPoch R)^3 = jacobiThetaPS R`.
- **Frobenius**: `Ch19.PowerSeries.expand_eq_pow_zmod p hp f : expand p f = f^p` over `ZMod p`.
- **Euler pentagonal**: `Ch19.coeff_qPochInfPS_eq_pentagonalSign`, `coeff_qPochInfPS_pow_p_in_ZMod_p`.
- **Section calculus** (mod-11; generalizable): `Pending/Chapter17_Hirschhorn_Mod11.lean` —
  `section11`, `IsRes`, `section11_add`, `isRes_mul/pow`, `JTerm` normal form,
  degree-k residue extraction pattern.
- **Combination certificate trick**: prove a char-p polynomial identity via integer
  factorisation `LHS−RHS = p·Q` (computed by a Python script) + `CharP` — see
  `scripts/hirschhorn_mod11_*.py` and `Chapter17_Hirschhorn_Combination.lean`.
- **JTP (analytic)**: `Ch02.jacobiTripleProduct`; **quintuple/finite-JTP**: `Ch03`, `Ch04`.
- **Cyclotomic / scaleX module** (`Pending/RamanujanQuintic.lean`, 2026-05-24): `scaleX (X↦cX)`
  PowerSeries ring hom + the 5th-root product collapse + factor-pair algebra + Gaussian-period
  algebra (`α=ζ+ζ⁴, β=ζ²+ζ³` roots of `x²+x−1`, `α⁵=5α−3`). Reusable for any cyclotomic q-series.

## ★★★ MBI CLOSED UNCONDITIONALLY (2026-05-25, build 8001, clean-3 axioms) ★★★
**Ramanujan's Most Beautiful Identity is FULLY PROVEN** (no hypotheses):
`RamanujanQuinticJTP.most_beautiful_identity : ∑ p(5n+4)qⁿ = 5·(q⁵;q⁵)⁵/(q;q)⁶`.
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (no sorryAx, no native_decide). The final
step (round 6): `prod_scaleX_qPochInfPS_fifth_collapse_complex` (the infinite fifth-root collapse,
lifted from the finite `prod_scaleX_qPochFinitePS_fifth_collapse` via `tprod` over `Fin 5 × ℕ`:
`5∣k+1` fiber → `E(q⁵)⁵`, other residues → `E(q⁵)/E(q²⁵)`) + `prod_scaleX_qPochInfPS_eq_E5DenominatorCore_complex`
+ `map_injective ℂ→ℚ`, discharging both `hE0` and `hfactor`. Prerequisite (round 4): the §8.3 factor
identities (8.3.1)/(8.3.2) via JTP-at-η period collapse. **This also settles the §8.6 "difficult and
deep" identity (= Chan §13) and the R(q)⁵ relation feeding Chan §15.** Ch16 → PASS.

### (historical) earlier frontier note — §8.3 factor identities CLOSED unconditionally; MBI 2 obligations away
**MAJOR UPDATE (2026-05-25, build 7998, clean-3 axioms):** the §8.6/§8.3 factor identities — the deep
crux that resisted 4 rounds — are now **PROVEN UNCONDITIONALLY** via the JTP-at-η route (Hirschhorn
§8.3): the book's "easy" proof = Jacobi Triple Product specialized at a primitive 5th root of unity ζ,
RHS regrouped by residue mod 5 (the Gaussian-period collapse, Hirschhorn 8.3.5). Key theorems in
`Pending/RamanujanQuinticJTP.lean` (0 sorry/axiom):
- `section83_triangular_tsum_period_collapse_of_ne_zero` — the η-period collapse
  `∑_{n∈ℤ}(−ζ)ⁿqⁿ⁽ⁿ⁺¹⁾ᐟ² = (1−ζ⁻¹)(A+βqB)` (residue-split, verified numerically to machine precision)
- `hasFPowerSeriesOnBall_section83JTPProductAnalytic_rhs_pair14/23` — dominated-convergence transfer
- `section83JTPProductPS_eq_rhs_pair14/23` — **the unconditional (8.3.1)/(8.3.2)**:
  `(q;q)∞(ζq;q)∞(ζ⁻¹q;q)∞ = expand5(pentagonal023) + (ζ²+ζ³)·X·expand5(pentagonal014)` (and ζ² → α).
Plus all round-1/2 infra: book α/β reconciliation (`bookAlpha⁵+bookBeta⁵=11`), the 5th-power linear
collapse `prod_sub_scaled_primitive_fifth_powerSeries`, book-period core factorization.

**The unconditional `most_beautiful_identity` now needs only TWO obligations** (round 5 in progress):
1. `hE0`: `compressedSection5 0 (qPoch)·pentagonal014 = expand5(qPoch)·pentagonal023` — likely
   assemblable from `E5_zero_eq_expand_compressedSection5_zero_qPochInfPS_rat` + the dissection.
2. `hfactor`: `core·E(q⁵)=E(q)¹¹` via the §8.5 5th-power chain off the §8.3 identities (q↔q⁵ base
   reconciliation through `expand` ring hom).
**Payoff when closed: MBI (Ch16) + Chan §13 deep identity + Chan §15 R(q) all unlock at once.**

## Tier 1 — parallel codex wave 1 (2026-05-24) — DONE, integrated (build 7987 OK, 0 sorryAx)
| # | Chapter | Result | File | Status |
|---|---------|--------|------|--------|
| 1 | Ch17 §3.6 | `qPochInfPS_cube_decompose_mod_5` + re-derived `5∣p(5n+4)` | `Pending/Chapter17_ASD_Mod5.lean` | ✅ DONE |
| 2 | Ch17 §3.7 | `qPochInfPS_cube_decompose_mod_7` (mod-7 cube dissection) | `Pending/Chapter17_ASD_Mod7.lean` | ✅ DONE |
| 3 | Ch08 | `EFinite_recurrence` (Chan Eq 8.2 finite RR recurrence) | `Pending/Chapter08_FiniteRR.lean` | 🟡 partial (recurrence; full identity open) |
| 4 | Ch16 | MBI partial: `qPochInfPS_five_dissection`, `(5.3.1) E0·E2=−E1²`, `(5.3.2)` support half | `Pending/Chapter16_MBI_Proof.lean` | 🟡 partial (full MBI open: E1 sign reindexing + assembly) |

### Wave 2 (2026-05-24) — DONE, integrated (build 7988 OK, 0 sorryAx)
- **MBI** (`Chapter16_MBI_Proof`): closed Hirschhorn **(5.3.2) FULLY** —
  `E5_one_eq_neg_X_mul_expand_twentyfive_qPochInfPS` (`E_1 = −q·E(q²⁵)`) via
  `pentagonalSign(25m+1) = −pentagonalSign m`, plus `E5_bracket_collapse_rat`.
  **Remaining for full MBI:** the (5.2.6) residue-4 coefficient extraction + final assembly.
- **Ch08** (`Chapter08_FiniteRR`): `DFinite` Gaussian-poly side + base cases +
  `second_order_recurrence_unique` + `EFinite_eq_DFinite_*_of_recurrence` (Thm 8.1 reduced
  to the `DFinite` recurrence). **Remaining:** the `DFinite` floor-index reindexing recurrence.
- **ASD-5 full** (`Chapter17_ASD_Mod5_Full`): section-component form of the mod-5
  congruences (`partitionGenFun_mul_D5_sq_eq_S5_cube`, `section_S5_cube_*`,
  `partition_section_4_eq_zero`). **Remaining (stretch):** identify `A 0/A 1` with the
  η-products (3.6.5) — needs a JTP formal-PS coefficient lemma.

### Wave 3 (2026-05-24) — DONE, integrated (build 7989 OK, 0 sorryAx)
- **Ch08** (`Chapter08_FiniteRR`): **Chan Thm 8.1 CLOSED for a=0 and a=1** unconditionally
  (`EFinite_eq_DFinite_a0`, `EFinite_eq_DFinite_a1`) — both finite Rogers-Ramanujan cases —
  via `DFinite_recurrence_of_a_le_one` (zero-extended integer-bottom Gaussian Pascal) + the
  uniqueness bridge. (General `Nat a` recurrence still open — the `a>1` integer-exponent case.)
- **ASD-7 full** (`Chapter17_ASD_Mod7_Full`, NEW): section-component mod-7 congruences
  (`partitionGenFun_mul_D7_eq_S7_sq`, `section_S7_sq_*`, `partition_7n_plus_5_eq_zero_mod_7`).
- **MBI** (`Chapter16_MBI_Proof`): residue-4 of `(qPoch)^4` collapsed —
  `section5_four_qPochInfPS_pow_four_eq_neg_five_X_pow_four_expand_twentyfive_qPochInfPS_pow_four_rat`
  `= -5 X^4 (expand 25 qPoch)^4`. **Remaining for full MBI:** lift this from `(qPoch)^4` to
  `partitionGenFun` (the `1/(q;q)` residue-4 extraction) → `most_beautiful_identity`.

### Wave 4 (2026-05-24) — MBI reduced to ONE bridge lemma (conditional, integrated)
`Chapter16_MBI_Proof`: full MBI now holds CONDITIONALLY via
`most_beautiful_identity_of_denominator_rationalization` / `_iff_cleared_denominator`.
The **single remaining bridge** (Hirschhorn 5.2.6 denominator rationalization):
```
section5 ℚ 4 (partitionGenFun ℚ) * (expand 5 qPoch)^6
  = - expand 25 qPoch * section5 ℚ 4 ((qPoch)^4)
```
This is the hard cyclotomic step (needs 5th-root-of-unity power-series machinery the repo
lacks — `1/E = ∏_{j=1}^4 E(ζ^j q) / ∏_{j=0}^4 E(ζ^j q)`, denominator `= E(q⁵)⁶/E(q²⁵)`).
4 agents reduced the MBI to exactly this; closing it needs new roots-of-unity infrastructure.
**Status: conditional MBI is the honest deliverable; bridge documented for a future
roots-of-unity-equipped attempt.**

### KEYSTONE status (2026-05-24): bilateral analytic→formal bridge — multi-session wall
Both MBI and ASD-η-products reduce to closing the JTP product=series equalities
`pentagonalProduct0xxPS = pentagonal0xxSeriesPS`. Over 4 focused agent-rounds this was reduced to:
- ✅ series-side `HasFPowerSeriesOnBall` + radii + Taylor `HasSum` (theta side)
- ✅ analytic product = analytic theta (Ch04 JTP specialisations, reindexed)
- ✅ analytic product has the theta Taylor expansion on the ball
- ✅ conditional equalities `..._of_productCoeff_taylor`
- ❌ STILL OPEN: the formal-product↔analytic-Taylor link, i.e. the AP-product analogue of B2's
  `eulerPentagonalInfiniteProduct_cube_eq_tsum_qpow_cubeConvolution` (analytic AP product =
  tsum of the formal-product coefficients). `PowerSeries.aeval` is a dead end (`IsLinearTopology
  ℂ ℂ` unavailable). Closing it = re-deriving B2's full product-evaluation chain for the AP
  products — a genuine multi-session infrastructure module, not a few-round close.
**Recommendation: bank the milestone; the keystone is a deliberate multi-session investment.**

### Remaining open (genuinely need new machinery / external sources)
- MBI bridge lemma (above) — 5th-root-of-unity power series.
- Ch08 general `a` (in flight: `codex-ch08-general`).
- ASD-5/7 η-product identification — JTP formal-PS coefficient lemma.
- Ch13 `∑qᵏ²/(q;q)ₖ²` (not in Hirschhorn), Ch10 mock theta (not in Hirschhorn),
  Ch12 RRCF value, Ch15 R(q) ODE — external sources / convergence / VOA.

### Tier 1b — MBI (dispatched 2026-05-24, codex-4)
| # | Chapter | Target | Agent | File | Status |
|---|---------|--------|-------|------|--------|
| 1b | Ch16 | Most Beautiful Identity `∑p(5n+4)qⁿ = 5 E(q⁵)⁵/E(q)⁶` | codex-4 | `Pending/Chapter16_MBI_Proof.lean` | dispatched |

**MBI roadmap (Hirschhorn §§5.1–5.4, confirmed by research subagent):** dissect
`E = E_0 + E_1 + E_2` by exponent residue mod 5; prove the two surprising formal
identities **(5.3.1) `E_0·E_2 = −E_1²`** and **(5.3.2) `E_1 = −q·E(q²⁵)`**; the residue-4
GF equals `(E(q²⁵)/E(q⁵)⁶)(E_0²E_2² − 3E_0E_1²E_2 + E_1⁴)`, whose bracket collapses to
`5E_1⁴ = 5q⁴E(q²⁵)⁴` ⟹ MBI. Second proof in §6.3 (degree-5 modular eq); 7-analogue §7.3.

## Tier 2 — queued (NEED EXTERNAL SOURCES — not in Hirschhorn)
Research subagent (2026-05-24) confirmed Hirschhorn's book has NO mock-theta content
("mock" appears 0×) and NO `∑ qᵏ²/(q;q)ₖ²` closed form.
| # | Chapter | Target | Notes |
|---|---------|--------|-------|
| 4 | Ch13 | "deep identity" `∑ qᵏ²/(q;q)ₖ²` | NOT in Hirschhorn. Need Chan §13's actual statement (check Chan PDF) / Slater list. Hirschhorn's "deep" identity is instead the RRCF relation `v⁵ = u·(1−2u+4u²−3u³+u⁴)/(1+3u+4u²+2u³+u⁴)` (§15.7) — possibly Chan §13's real content. CLARIFY before dispatch. |
| 5 | Ch10 | mock theta `f(q)` | NOT in Hirschhorn. Use Watson (1936) / Andrews–Gordon–McIntosh. Needs mock-modular framework; hardest. |
| 6 | Ch12 | RRCF evaluation `R(e^{-2π}) = …` | needs CF convergence + special value |
| 7 | Ch15 | differential equation for `R(q)` (Thm 15.1) | needs VOA / Milas |

## Tier 3 — AUX deepening / higher congruences
| # | Chapter | Target | Notes |
|---|---------|--------|-------|
| 8 | Ch09 | general (infinite) Bailey transform / Bailey's Lemma | finite N≤7 done |
| 9 | Ch11 | RRCF convergence `R_trunc q n → R(q)` | α/β algebra done |
| 10 | Ch14 | crank general equidistribution (all n, mod 5/7/11) | n=0,1 surjectivity done; Fintype(Partition) not `decide`-able |
| 11 | Ch20 | full modularity of Δ(τ), Hecke action on τ | beyond Mathlib |
| 12 | — | higher congruences: Watson `p(25n+24)≡0 mod 25`, `p(49n+47) mod 49` | small cases native_decide'd |

## Execution rules (multi-agent safety)
1. Each agent edits ONLY its own new Pending file. Never touch
   `QseriesFormalization.lean`, `Audit.lean`, or another agent's chapter.
2. Verify with single-file `lake env lean <file>` (does not write oleans → no mutual clobber).
3. The orchestrator (Zinan) does NOT run `remote-build.sh` (full-tree rsync) while any
   codex agent is editing on the-build-server — it would revert their working tree.
4. Integration (module-graph wiring + Audit `#print axioms` + full build) happens only
   after agents finish, when the-build-server is free.
5. Trust-but-verify every closure: `#print axioms` under FRESH oleans (a stale mid-run
   olean can show a phantom `sorryAx`).
