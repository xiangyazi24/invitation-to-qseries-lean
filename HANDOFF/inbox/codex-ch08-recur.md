# TASK (codex/gpt-5.5): close the DFinite recurrence → Chan Thm 8.1

Extend `QseriesFormalization/Pending/Chapter08_FiniteRR.lean` (namespace `QseriesFormalization.PartII.Ch08`).
Touch ONLY this file. Single-file verify; 0 sorry/axiom/admit; no sorryAx. Reply to
`HANDOFF/outbox/codex-ch08-recur-reply.md`.

## Already proven (REUSE)
- `EFinite`, `EFinite_recurrence` (Chan Eq 8.2).
- `DFinite` (Gaussian-poly alternating side), `DFinite_zero_two`/`DFinite_one_two` base cases.
- `second_order_recurrence_unique`, `EFinite_eq_of_recurrence`,
  `EFinite_eq_DFinite_*_of_recurrence` (Thm 8.1 reduced to the DFinite recurrence).

## Goal
Prove `DFinite_recurrence : DFinite q a (N+2) = DFinite q a (N+1) + q^(N+a+1) * DFinite q a N`
(the floor-index reindexing of the alternating Gaussian-binomial sum), then combine with
`EFinite_eq_DFinite_*_of_recurrence` to conclude **Chan Thm 8.1**: `EFinite q a N = DFinite q a N`.
Key tool: the Pascal-type q-binomial recurrences `[n+1;k]_q = [n;k]_q + q^? [n;k-1]_q` (two forms),
applied termwise with care on the floor index `⌊(n+3a-5j)/2⌋`. If the general `a` is too hard,
closing it for `a = 0` and `a = 1` (the cases the bridge needs) is an acceptable deliverable.
