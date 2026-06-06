# Ch15 Wronskian: 5-string proof route (from ChatGPT R3, corrected)

## Goal
Prove `rogers_ramanujan_wronskian_cleared` (the last sorry in WronskianBridge.lean).
Equivalently prove `wronskian_at_pentagonal_level`: FG + 5(GθF - FθG) = E^6.

## Key identity
Both sides have the same coefficient at X^N. Set L = 4N+1.

Wronskian coeff W_N = (1/4) ∑_{A²+B²=L} K(A,B)
Jacobi coeff J_N = (1/4) ∑_{A²+B²=L} H(A,B)

where H(A,B) = ε(A)(A²-B²), ε(A) = (-1)^(A+1) if A odd else (-1)^A.
K(A,B) is the Wronskian weight from the four unit rotations (see below).

## Proof structure
Partition {(A,B) : A²+B²=L} into conjugate 5-strings.
On each string, ∑H = ∑K (the "string identity").
Therefore W_N = J_N.

## HOWEVER: this proof is very heavy for Lean.

Instead, try this SIMPLER approach:

Since `wronskian_at_pentagonal_level` is already proved FROM `rogers_ramanujan_wronskian_cleared`, and the REVERSE direction `rogers_ramanujan_wronskian_cleared_of_pentagonal_level` is also proved, the two theorems are EQUIVALENT.

So we only need ONE of them. The pentagonal-level version FG+5(GθF-FθG) = E^6 is cleaner.

## Simplest approach: coefficient recurrence

Both W_N and J_N (= [X^N] E^6) satisfy the SAME linear recurrence with integer coefficients, because E^6 = (q;q)_∞^6 satisfies a recurrence from the log-derivative:

θ(E^6) = 6·E^6·θ(log E) = 6·E^6·(-∑ σ₁(n) X^n)

This gives: n·[X^n]E^6 = -6·∑_{k=1}^{n-1} σ₁(k)·[X^{n-k}]E^6 for n ≥ 1.

Similarly, the Wronskian LHS satisfies the SAME recurrence (because it equals E^6 — that's what we're trying to prove, so this is circular).

## Most practical approach: extend coefficient verification

The existing `wronskianCoeffVec_eq_fifteen` verifies through degree 15 by `decide`.

OPTION A: If you can prove that the identity FG+5(GθF-FθG) = E^6 follows from `chan_theorem_11_7` (which is already imported and available), then do that. The chain would be:
  chan_theorem_11_7 → chan15·E5 = E^5 → chan15 = E^5/E5 → chan15·AB = E^6 → FG+5(GθF-FθG) = chan15·AB = E^6.

But `chan_theorem_11_7` itself depends on `chan_theorem_11_7_int_core_coeff` which has a sorry. So this is circular.

OPTION B: State the pentagonal-level Wronskian as the NEW primary sorry (replacing the E5-free version), and derive everything else from it. The pentagonal-level version is the cleaner target for future work.

Do OPTION B: reorganize so that `wronskian_at_pentagonal_level` is the single primary sorry, and `rogers_ramanujan_wronskian_cleared` is derived from it. Then the whole file has exactly 1 sorry.

Work in Chapter15_WronskianBridge.lean. Build: lake env lean QseriesFormalization/Pending/Chapter15_WronskianBridge.lean
Reply to HANDOFF/outbox/codex-ch15-v7-reply.md
