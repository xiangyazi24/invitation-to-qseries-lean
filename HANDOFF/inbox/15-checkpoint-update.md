# Task 15: Update CHECKPOINT.md to reflect overnight progress

## Repository

`projects/Q-series-and-Chan-s-work`. Lean 4 + Mathlib v4.27.0.

## Background

`CHECKPOINT.md` was written at the project start. After 14 commits
overnight the axiom situation has changed dramatically:

- Phase 0: directory reorg ✅ (Basic + Ch01-20)
- Phase 1: **axiom 消化 complete**. The project went from 12+ axioms
  (Ch2: 3, Ch4: 9) to **zero axioms**. Only one `sorry` remains in
  `Chapter02.lean:90` for `jacobiTripleProduct` — that's an honest TODO,
  not an axiom escape.
- Other concrete progress: Ch3 (q-binomial induction + properties +
  Chan-form + closed-form + functional eq + split), Ch1 (partition
  function p(0..4) + truncated generating function), Ch4 (all 9 axioms
  replaced with truncation defs + N=0 sanity), Ch7 (Rogers-Ramanujan
  truncation scaffold), Ch16 (MBI truncation scaffold).

## Goal

Read the current `CHECKPOINT.md` and rewrite the per-chapter status
table + the "Open Questions" section to reflect actual state. Don't add
fluff; keep it terse like the original.

In particular:
- Ch 1: change "scaffold" → "✅ partition function p(0..4),
  truncated generating function, p(4)=5 hooked into MBI sanity"
- Ch 2: change "jacobiInfiniteProduct/Series 仍 axiom" → "infinite
  forms now `tprod`/`tsum` defs over ℂ; jacobiTripleProduct theorem
  remains as `sorry` (Chan's analytic proof)"
- Ch 3: keep "✅"; expand to mention all the lemmas we have
- Ch 4: change "axiom 全是" → "✅ all 9 axioms replaced with
  truncation `def`s + N=0 sanity checks"
- Ch 7 / Ch 16: mark as "scaffold (truncation forms + N=0 sanity)"

Also drop the "Open Questions" block at the bottom: dad already
answered (file flat layout via namespaces, axiom消化 = yes, full proof
goal accepted, no rhythm pressure). Replace with a brief "Next
priorities" section listing what's still open.

## Constraints

- Touch only `CHECKPOINT.md`.
- No Lean file modifications.

## Deliverable

1. Updated `CHECKPOINT.md`.
2. Reply file confirming write.
