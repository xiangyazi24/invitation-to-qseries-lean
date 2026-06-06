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
| Lean source | **255,073 lines** across 173 files |
| Theorems and lemmas | 26,504 |
| Definitions | 1,151 |
| Audit | `QseriesFormalization/Audit.lean`: 8,012 modules compile with zero errors, **351 `#print axioms` checks** |
| Axiom discipline | every audited theorem depends only on `[propext, Classical.choice, Quot.sound]` (one documented exception, see *Caveats*) |

No `sorry`, no custom axioms, no `native_decide` in any audited result.

## Quick start

Requires [elan](https://github.com/leanprover/elan) (the toolchain in `lean-toolchain` is
installed automatically).

```bash
lake exe cache get        # fetch prebuilt Mathlib oleans
lake build QseriesFormalization.Audit   # builds everything + runs all #print axioms checks
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
| Euler's pentagonal number theorem | combinatorial (Franklin's involution) **and** formal-power-series proofs | `Chapter05.lean`, `Pending/JTP_FormalPS_Pentagonal.lean` |
| Jacobi triple product | analytic over ℂ and as a formal Laurent identity via AP-Pochhammer products | `Chapter03/04`, `Pending/Chapter10_HM.lean` (`jLaurent_eq_tripleProductInf`) |
| Rogers–Ramanujan identities | both identities, Schur's 1917 proof | `Chapter07*` |
| Rogers–Ramanujan continued fraction | golden-ratio values; the differential equation via **Dobbie's identity** (Gaussian-integer strings over ℤ[i]) | `Chapter11.lean`, `Pending/Chapter15_WronskianIndependent.lean`, `Pending/Chapter15_R_ODE.lean` |
| Ramanujan congruences, ∀n | `5∣p(5n+4)`, `7∣p(7n+5)`, `11∣p(11n+6)` via a k-section operator over `(ZMod p)⟦X⟧`; Ono-style infinite families | `Chapter17*`, `Chapter20_Ono.lean` |
| Ramanujan's τ | initial values, multiplicativity instances, parity, mod-691 | `Chapter20*` |
| t-cores, hook lengths | staircase partition theory | `Chapter18*` |
| **Tenth-order mock theta identity** (Chan Eq. 10.15) | `chan1015`, proved by the book's own route: constant-term decoupling + Zwegers' lemma + Hickerson's lemma + diagonal collapse, on a two-variable Hahn-series foundation ordered q-adically first | `Pending/Chapter10_TwoVar.lean`, `Pending/Chapter10_Bridge.lean` |

A second, independent route to the mock theta identity via Hickerson–Mortenson Appell–Lerch
reductions is ~80% complete in `Pending/Chapter10_HM.lean` (the formal JTP, the Riemann theta
relation, cross-modulus bridges, and a fully formal partial-fraction expansion are finished and
audited; the final Finset assembly of the change-of-z theorem is documented and numerically
verified but not yet closed).

## Repository structure

- `QseriesFormalization/ChapterNN*.lean` — per-chapter developments.
- `QseriesFormalization/Pending/` — large self-contained campaigns (the Chapter 10 mock theta
  files, the Chapter 15 Dobbie/Wronskian files, analytic-to-formal bridges).
- `QseriesFormalization/Audit.lean` — the single source of truth for what is verified: imports
  every audited module and runs `#print axioms` on each headline.
- `docs/chatgpt-designs-*/` — the mathematical design documents produced during the
  formalization (kept as a record of the method).
- `HANDOFF/` — working artifacts of the multi-agent formalization process (dispatch notes and
  reports), kept for provenance.
- `PLAYBOOK_AUDIT.md` — audit conventions and known file-labeling caveats.

## Caveats (documented honestly)

- One pentagonal-coefficient lemma (`coeff_qPochInfPS_int_eq_pentagonalSign`) still routes
  through a legacy `native_decide` dependency and therefore carries `Lean.ofReduceBool`. It is
  flagged in `Audit.lean`, quarantined from everything else, and scheduled for replacement.
- Two files carry historical names that do not match their content (`Chapter05.lean` holds
  Franklin-involution material that is Chan §4 content; `Chapter15.lean` holds q-calculus
  material, while Chan §15's actual chapter-main lives in `Pending/Chapter15_*.lean`).
  See `PLAYBOOK_AUDIT.md`.

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
