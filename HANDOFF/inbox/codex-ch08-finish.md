# TASK (codex / gpt-5.5): FINISH Chapter 8 finite Rogers–Ramanujan (Chan Thm 8.1)

## File (extend the existing committed file — keep what's there, add lemmas)
`QseriesFormalization/Pending/Chapter08_FiniteRR.lean` (namespace `QseriesFormalization.PartII.Ch08`).
Do NOT touch other files. Verify single-file:
```
cd ~/repos/Q-series-and-Chan-s-work
export NVM_DIR=~/.nvm; source ~/.nvm/nvm.sh; nvm use 22 >/dev/null
~/.elan/bin/lake env lean QseriesFormalization/Pending/Chapter08_FiniteRR.lean
```
Do NOT run full `lake build`. 0 sorry/axiom/admit; no phantom `sorryAx`. Reply to
`HANDOFF/outbox/codex-ch08-finish-reply.md`.

## Already proven (REUSE)
- `EFinite q a N = Σ_j q^{j²+aj} · [N-j choose j]_q` (Chan's finite sum side `E_{N+1}(a)`).
- `EFinite_zero`, `EFinite_one`.
- `EFinite_recurrence : EFinite q a (N+2) = EFinite q a (N+1) + q^{N+a+1}·EFinite q a N`  (Chan Eq 8.2).
- `EFinite_chan_eq_8_2_of_two_le` (one-based wrapper).

## What to close
1. **Gaussian-polynomial (alternating-sum) side** `DFinite q a N`, Chan's
   `D_n(a) = Σ_j (−1)^j q^{j(5j+1)/2 − 2aj} · [ n+a ; ⌊(n+3a−5j)/2⌋ ]_q`
   (finite alternating sum of Gaussian binomials; use the same q-binomial `[·;·]_q`
   you already use in `EFinite`). Define it cleanly for `Nat` indices.
2. Prove `DFinite` satisfies the **same recurrence** `D(N+2) = D(N+1) + q^{N+a+1}·D(N)`
   and the same **base cases** `D(0)`, `D(1)` as `EFinite`.
3. **Thm 8.1**: conclude `EFinite q a N = DFinite q a N` for all `N`, by strong
   induction on `N` using the shared recurrence + base cases.

If step 1's Gaussian-binomial bookkeeping (the floor `⌊(n+3a−5j)/2⌋`) is too heavy,
an acceptable alternative deliverable: prove the **uniqueness** lemma "any two sequences
satisfying the order-2 recurrence with matching `N=0,1` values are equal", and apply it
to reduce Thm 8.1 to checking `DFinite` satisfies the recurrence + base cases. Report
precisely what closed. Partial 0-sorry beats fake-complete.

## Infrastructure
- `Basic.lean`: `qPochhammer`, `natSum`, `qPoch`; Mathlib `gaussianBinomial` / q-binomial lemmas.
- The existing `EFinite_*` lemmas above.
