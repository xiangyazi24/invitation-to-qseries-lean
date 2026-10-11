# A Lean 4 Formalization of *An Invitation to q-Series*

A machine-checked formalization, in Lean 4 + Mathlib, of the chapter-main theorems of
Hei-Chi Chan's *An Invitation to q-Series: From Jacobi's Triple Product to Ramanujan's
"Most Beautiful Identity"* (World Scientific, 2011) — from the definition of a partition
through Euler's pentagonal number theorem, the Jacobi triple product, the Rogers–Ramanujan
identities and continued fraction, Ramanujan's partition congruences, up to the tenth-order
mock theta identity that closes the book's hardest chapter.

## Scale and verification status

| | |
|---|---|
| Lean source | **258,052 lines** across 174 files (`QseriesFormalization/`) |
| Theorems and lemmas | about 27,600 (line-initial `theorem`/`lemma` declarations) |
| Audit | `QseriesFormalization/Audit.lean` (374 `#print axioms` lines) and `QseriesFormalization/AuditExercises.lean` (957 lines, one per theorem of `Exercises.lean`); both are imported by the root module and run by the full build |
| Axiom discipline | each `#print axioms` line reports `[propext, Classical.choice, Quot.sound]` except the lines that depend on `native_decide` (see the next row and the release notes) |
| `sorry`, `admit`, custom `axiom` | none in the library (comment-aware scan of all 174 files) |
| `native_decide` | **264 tokens** in the library: 228 in modules imported by the root, 36 in modules outside it. Of the 228, 48 sit in `example`s (which do not enter any axiom set) and 180 in `theorem`s; the audit decides which results depend on it (`Lean.ofReduceBool` in the `#print axioms` output) |

## Scope of the formalized results

Several results are narrower than the corresponding statement in the book. Each
is wired into the root module and the audit, and each is described here exactly.

| Book item | What the Lean result proves | Not proved |
|---|---|---|
| Thm 11.1 (continued fraction equals product) | `Pending/Chan_Theorem_11_1.lean`: in `ℚ⟦X⟧`, the X-adic limit of the convergents of `1/(1+X/(1+X^2/(1+…)))` equals `(X,X^4,X^5;X^5)_∞ / (X^2,X^3,X^5;X^5)_∞` | any statement for a complex `q` with `|q| < 1`: convergence of the continued fraction and its identification with the analytic product |
| Thm 11.4 (`R(e^{-2π})`) | `Pending/Chan_Theorem_11_4.lean`: the product quotient `q·P₀₁₄(q⁵)/P₀₂₃(q⁵)` at `q = e^{-2π/5}` equals `√((5+√5)/2) − (1+√5)/2` | that this product is the value of the continued fraction (needs the analytic form of Thm 11.1) |
| Thm 11.5 (`R(q)^5` vs `R(q^5)`) | `Pending/Chapter13_DeepIdentity.lean`: `r^5·(1+3v+4v²+2v³+v⁴) = r(q⁵)·(1−2v+4v²−3v³+v⁴)` in `ℚ⟦X⟧`, with `r = R·q^{-1/5}` the product form and `v = X·r(q⁵)` | an analytic statement, or one about the continued fraction function |
| Thm 11.7 (differential equation) | `Pending/Chapter15_R_ODE.lean`: Eq. 15.8, `1 − 5Σ(n\|5) n qⁿ/(1−qⁿ)` times `(q⁵;q⁵)_∞` equals `(q;q)_∞⁵`, as formal series over any commutative ring | the differential equation `5q·d/dq·ln R(q) = η⁵(τ)/η(5τ)` for the function `R(q)` |
| Ch18 | hook-length and staircase-partition framework | Thm 18.1 (characterization of t-cores) |
| Ch20 Thm 20.1 (Ono) | the cases `m = 5, 7, 11` (from Ramanujan's congruences), plus τ-function values, parity and small Hecke instances | Ono's theorem for all primes `m ≥ 5` |
| Ch6 | Macdonald identity for `t = 2` (the case the book proves) | general odd `t` (stated, not proved, in the book) |

`Pending/Chapter11_Thm111.lean` is an earlier check of the same Thm 11.1 identity
through degree 20 and is superseded by `Chan_Theorem_11_1.lean`.
`Exercises.lean` collects exercise-style wrappers of chapter theorems; it is not a
claim that every exercise of the book is formalized.

## Quick start

Requires [elan](https://github.com/leanprover/elan) (the toolchain in `lean-toolchain` is
installed automatically).

```bash
lake exe cache get        # fetch prebuilt Mathlib oleans
lake build QseriesFormalization   # builds everything, including the audit modules, which print all axiom sets
```

The audit output lists, for every headline theorem, the exact axioms it depends on.
To check a single result:

```lean
import QseriesFormalization.Pending.Chapter10_Bridge
#print axioms QseriesFormalization.Pending.Ch10Bridge.chan1015
-- [propext, Classical.choice, Quot.sound]
```

## Highlights

| Topic (book chapter) | Result | Where |
|---|---|---|
| Partitions, explicit values | `p(12)=77`, `p(13)=101` via the Euler-pentagonal recurrence on formal power series | `Chapter01_*` |
| Euler's pentagonal number theorem | combinatorial (Franklin's involution) **and** formal-power-series proofs | `Chapter04_FranklinPentagonal.lean`, `Pending/JTP_FormalPS_Pentagonal.lean` |
| Jacobi triple product | analytic over ℂ and as a formal Laurent identity via AP-Pochhammer products | `Chapter03/04`, `Pending/Chapter10_HM.lean` (`jLaurent_eq_tripleProductInf`) |
| Rogers–Ramanujan identities | both identities, Schur's 1917 proof | `Chapter07*` |
| Rogers–Ramanujan continued fraction | golden-ratio values; the Lambert-series form (Eq. 15.8) of the differential equation via **Dobbie's identity** (Gaussian-integer strings over ℤ[i]); formal-series continued fraction = product (Thm 11.1); the identity for `R(q)^5` and the value at `e^{-2π}` for the product form (see the scope table) | `Chapter11.lean`, `Pending/Chapter15_WronskianIndependent.lean`, `Pending/Chapter15_R_ODE.lean` |
| Ramanujan congruences, ∀n | `5∣p(5n+4)`, `7∣p(7n+5)`, `11∣p(11n+6)` via a k-section operator over `(ZMod p)⟦X⟧`; Ono-style infinite families | `Chapter17*`, `Chapter20_Ono.lean` |
| Ramanujan's τ | initial values, multiplicativity instances, parity | `Chapter20*` |
| t-cores, hook lengths | staircase partition theory | `Chapter18*` |
| **Tenth-order mock theta identity** (Chan Eq. 10.15) | `chan1015`, proved by the book's own route: constant-term decoupling + Zwegers' lemma + Hickerson's lemma + diagonal collapse, on a two-variable Hahn-series foundation ordered q-adically first | `Pending/Chapter10_TwoVar.lean`, `Pending/Chapter10_Bridge.lean` |

A second, independent route to the mock theta identity, via Hickerson–Mortenson
Appell–Lerch reductions, is in `Pending/Chapter10_HM.lean`. It formalizes the formal JTP, the
Riemann theta relation, cross-modulus bridges, the partial-fraction expansion and the
change-of-z theorem (`hm23ChangeZIdentity`, now closed with a core-axioms proof). The last
step of that route, which would re-derive Eq. 10.15 from the Appell–Lerch side, is **not**
formalized: the theta-correction cleared residual was removed from the library rather than
proved, and `chan1015` does not use it. Eq. 10.15 is therefore proved by the primary route
only.

## Repository structure

- `QseriesFormalization/ChapterNN*.lean` — per-chapter developments.
- `QseriesFormalization/Pending/` — large self-contained campaigns (the Chapter 10 mock theta
  files, the Chapter 15 Dobbie/Wronskian files, analytic-to-formal bridges).
- `QseriesFormalization/Audit.lean`, `QseriesFormalization/AuditExercises.lean` — import the
  audited modules and run `#print axioms` on each listed declaration. They report axioms only;
  statement fidelity is the table "Scope of the formalized results" above.
- `docs/chatgpt-designs-*/` — the mathematical design documents produced during the
  formalization (kept as a record of the method).
- `HANDOFF/` — working artifacts of the multi-agent formalization process (dispatch notes and
  reports), kept for provenance.
- `PLAYBOOK_AUDIT.md` — per-chapter status against the book.

## Notes

- File names were normalized to content-true names for this release (e.g. the Franklin-involution
  development, which proves Chan §4 content, lives in `Chapter04_FranklinPentagonal.lean`).
  A few internal namespace names retain historical numbering where renaming would add no clarity.

## Method

The formalization was carried out by a human–AI team: mathematical designs from a reasoning
model, Lean transcription by code-generation agents under a strict verify-before-claim
contract (numerical oracles before formalization; `#print axioms` from rebuilt binaries after),
orchestrated and audited end to end. Three false intermediate claims were caught by
machine-verified counterexamples during the project and corrected before they could enter the
library. Two accounts of the process:

- [Mock Theta, Two Roads, and Three Counterexamples](https://infsup.com/math/mock-theta-two-roads-and-three-counterexamples/)
- [Formalizing An Invitation to q-Series: Twenty Chapters in Lean 4](https://infsup.com/math/formalizing-an-invitation-to-q-series-twenty-chapters-in-lean-4/)

## License

Apache License 2.0 (see `LICENSE`). Copyright © 2026 Xiang Huang.
