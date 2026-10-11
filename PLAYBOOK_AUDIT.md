# Status against the book — Q-series formalization

**Last revised:** 2026-10-11, Lean 4.28.0, Mathlib `v4.28.0`.

This file replaces the May 2026 per-chapter audit, whose verdicts (13 PASS / 7 AUX,
"Ch10 AUX", "Ch13 statement only", "Ch15 stub, not in main build") no longer describe
the library. The earlier text remains in the git history.

## What each check establishes

| Check | Establishes | Does not establish |
|---|---|---|
| Full build of `QseriesFormalization` (includes `Audit.lean`, `AuditExercises.lean`) | every module in the root closure compiles; no `sorry`/`admit` warnings | that statements match the book |
| `#print axioms` lines in the audit modules | the axioms each listed declaration depends on | non-vacuity, statement fidelity |
| Comment-aware token scan | no `sorry`, `admit` or custom `axiom` anywhere in `QseriesFormalization/`; 264 `native_decide` tokens (228 in root-imported modules, 36 outside it; 48 of the 228 inside `example`s) | which results depend on `native_decide`: only `#print axioms` shows that (`Lean.ofReduceBool`) |
| Fidelity review (this file, README table "Scope of the formalized results") | the relation of each headline Lean statement to the book statement | — |

## Per-chapter status

"Full" means the chapter-main result of the book is formalized with a statement
that matches it. "Narrower" means a proved result exists whose statement is weaker
or of a different kind than the book's; the gap is stated.

| Ch | Book result | Lean | Status |
|---|---|---|---|
| 1 | partitions, generating function, values of `p(n)` up to 54 | `Ch01.coeff_partitionGenFun`, `partitionGenFun_eq_euler_product`, `Chapter01_PartitionCount*` | full |
| 2 | Jacobi triple product (analytic) | `Ch02.jacobiTripleProduct` | full |
| 3 | q-binomial theorem, finite JTP | `qBinomialTheorem_chanForm`, `finite_jacobi_triple_product` | full |
| 4 | Euler pentagonal theorem, quintuple product, Jacobi identity | `Chapter04*.lean` | full |
| 5 | JTP (book proves it by the Boson–Fermion route) | `Ch05JTP.jacobi_triple_product`, `bosonFermion_JTP` | full for the theorem; the proof route differs from the book's |
| 6 | Macdonald identities (book proves `t = 2`) | `Ch06Macdonald.macdonald_A1_identity` | full relative to what the book proves |
| 7 | Rogers–Ramanujan identities | `rogersRamanujan_first/second` | full |
| 8 | Thm 8.1, `a = 0, 1` | `chan_theorem_8_1_a0/a1` | full (book states `a = 0, 1` only) |
| 9 | Bailey lemma, Thm 9.1, 9.2 | `Ch09.theorem91`, `theorem92` | full; the Rogers–Ramanujan application through the Bailey chain is not separately wired |
| 10 | tenth-order mock theta identity, Eq. 10.15 | `Ch10Bridge.chan1015` (primary route); `Chapter10_HM` second route up to `hm23ChangeZIdentity` | full via the primary route; the second route stops before re-deriving Eq. 10.15 |
| 11 | Thm 11.1 (continued fraction = product) | `Pending/Chan_Theorem_11_1.lean`: equality in `ℚ⟦X⟧` of the X-adic limit of the convergents with the product | narrower: formal power series only; no analytic `|q| < 1` statement |
| 12 | Thm 11.4: `R(e^{-2π}) = √((5+√5)/2) − (1+√5)/2` | `Pending/Chan_Theorem_11_4.lean`: the value of the product quotient at `e^{-2π/5}` | narrower: product form of `R`; not tied to the continued fraction |
| 13 | Thm 11.5 (`R(q)^5` vs `R(q^5)`) | `Pending/Chapter13_DeepIdentity.lean` | narrower: identity of formal series for the product form `r`, not for the analytic continued fraction |
| 14 | Thm 11.6 (Lost Notebook identity), cranks | `Ch14Thm116.chan116_theorem_11_6`; crank bookkeeping | full for Thm 11.6; the crank theory beyond finite cases and generating-function bookkeeping is not formalized |
| 15 | Thm 11.7, differential equation for `R(q)` | `Ch15RODE.chan_theorem_11_7` (Eq. 15.8) and restatements in `Chapter15_Hirschhorn` | narrower: Lambert-series identity (Eq. 15.8) over any commutative ring; the differential equation for the function `R(q)` is not stated |
| 16 | Most Beautiful Identity | `RamanujanQuinticJTP.most_beautiful_identity` | full |
| 17 | Ramanujan congruences mod 5, 7, 11 | `ramanujan_5/7/11_dvd_*`, ASD eta-quotient forms | full for the three classical congruences |
| 18 | hook lengths, t-cores | staircase and hook framework | narrower: Thm 18.1 (t-core characterization) is not proved |
| 19 | formal power series framework | `Chapter19.lean` | full |
| 20 | Ono's theorem, modular forms excursus | `Chapter20_Ono.lean` (`m = 5, 7, 11`), τ values, parity, small Hecke instances | narrower: Ono's theorem for all primes `m ≥ 5` is not formalized |

## Modules outside the root closure

25 of the 174 library files are not imported by `QseriesFormalization.lean`, so the full
build neither compiles them nor audits them: `BaileyqPS`, `Chapter01_PartitionCount55`,
`Chapter01_PentagonalSignBundle`, `Chapter09_n7_common`, `Chapter11_RRBridge`,
`Chapter20_TauExtend`, `Chapter20_TauMult`, `Chapter20_TauValues`, and under `Pending/`:
`Chapter12_EtaValue`, `Chapter13_CoeffVerification`, `Chapter14_CrankResidue`,
`Chapter15_DobbieFromJTP`, `Chapter15_Wronskian`, `Chapter15_WronskianBridge`,
`Chapter16_MBI` (statement stubs), `Chapter17_NestedModArithmetic`,
`Chapter20_Eisenstein`, `Chapter20_LiouvilleConvolution`, `Chapter20_Mod691`,
`Chapter20_TauMod691Proof`, `DobbieIdentity`, `RR_BaileyPairSeed`, `RR_FiniteJTPAtOne`,
`Ramanujan1Psi1`, `Watson_Mod25_SmallCases`. None contains a `sorry`; 36 `native_decide`
tokens sit in these files. They are retained as development material and are not part of
any claim above.
