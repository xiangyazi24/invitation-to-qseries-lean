# TASK (codex / gpt-5.5): Chapter 8 — finite Rogers–Ramanujan (Chan Thm 8.1)

## Output file (yours only)
Create `QseriesFormalization/Pending/Chapter08_FiniteRR.lean`.
Do NOT edit `QseriesFormalization.lean`, `Audit.lean`, `Chapter08.lean`, or other files.

## Hard constraints (playbook)
0 `sorry`/`axiom`/`admit`, no weakened statements. Verify ONLY single-file:
```
cd ~/repos/Q-series-and-Chan-s-work
export NVM_DIR=~/.nvm; source ~/.nvm/nvm.sh; nvm use 22 >/dev/null
~/.elan/bin/lake env lean QseriesFormalization/Pending/Chapter08_FiniteRR.lean
```
Do NOT run full `lake build` (other agents edit the same tree concurrently).
Confirm no `sorryAx` (re-elaborate from source). Summary to
`HANDOFF/outbox/codex-ch08-finiteRR-reply.md`.

## Context
`QseriesFormalization/Chapter08.lean` already has the **sum side**
`D_partialSum q a N = Σ_{n=0}^N q^{n²+an}/(q;q)_n` (= Chan's `E_n(a)`), with its
`_succ` recursion. Chan §8 (Andrews/Schur finite Rogers–Ramanujan) Theorem 8.1 is
the identity between this sum and a **Gaussian-polynomial (q-binomial) side**
`D_n(a) = Σ_j (−1)^j q^{j(5j+1)/2 − 2aj} · [ n+a ; ⌊(n+3a−5j)/2⌋ ]_q`, satisfying the
same second-order q-difference recurrence; equality follows by matching base cases
+ the shared recurrence.

## Deliverable (choose the largest you can close with 0 sorry)
Working over a field `R` (mirror `Chapter08.lean`'s `variable {R : Type*} [Field R]`):
1. **Recurrence for the sum side**: prove the second-order q-difference relation that
   `D_partialSum`/`E_n(a)` satisfies (Chan eq for `E`). This is finite algebra.
2. **Gaussian-polynomial side**: define `D_n(a)` via `Nat`-indexed q-binomial
   coefficients (use Mathlib `Nat.choose`-analogue / `Polynomial.gaussianBinomial`
   if available, else define the q-binomial `[n;k]_q = (q;q)_n/((q;q)_k (q;q)_{n-k})`),
   and prove it satisfies the SAME recurrence + base cases.
3. **Thm 8.1**: conclude `E_n(a) = D_n(a)` by induction on the shared recurrence.

If the full identity is too large, the **recurrence (1) alone is an acceptable
deliverable** — state and prove it cleanly. Document in the reply exactly what closed.

## Reusable infrastructure
- `Basic.lean`: `qPochhammer`, `natSum`, `qPoch`.
- Mathlib q-binomial / Gaussian binomial lemmas (search `gaussianBinomial`, `qPochhammer`).
- `Chapter08.lean` `D_partialSum_succ`, the `_N` closed forms (sanity checks).
