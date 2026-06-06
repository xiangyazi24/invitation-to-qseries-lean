# Task: Ch10 — 10th-order mock theta infrastructure

## Context

You are working in `~/repos/Q-series-and-Chan-s-work/`, a Lean 4 + Mathlib v4.27 formalization.

Ch10 is currently AUX. The existing `Chapter10.lean` has mock theta f(q) values at N=0..13 (3rd-order). Chan §10 discusses 10th-order mock theta functions φ and ψ.

Existing Pending files:
- `Chapter10_MockTheta_PS.lean` — formal PS definitions for φ, ψ
- `Chapter10_TenthOrder.lean` — 10th-order scaffolding

## Your task

Work in `QseriesFormalization/Pending/Chapter10_TenthOrder.lean` and/or new files `Chapter10_*.lean`. Do NOT touch files outside `Pending/`.

### Step 1: Read the existing files

Read `Chapter10_MockTheta_PS.lean` and `Chapter10_TenthOrder.lean` to understand what's already defined.

### Step 2: Define the 10th-order mock theta functions as formal PS

If not already done, define:
```lean
-- φ(q) = ∑_{n≥0} q^{n(n+1)/2} / (q,q^2;q^2)_n
-- ψ(q) = ∑_{n≥0} q^{(n+1)(n+2)/2} / (q,q^2;q^2)_n
```

These are partial-fraction-style series. In formal PS, define them via truncated convolution (like `tauEtaPowVec` in Chapter20).

### Step 3: Verify coefficients

Compute φ and ψ coefficients through degree 10-15 and verify against known OEIS values.

### Step 4: State Chan's 10th-order identity

From Chan §10, the key identity relates φ, ψ to the Rogers-Ramanujan products. State it precisely as a `sorry` theorem.

### Step 5: 1ψ1 summation (Ramanujan's bilateral sum)

If time permits, state and begin proving:
```lean
-- ₁ψ₁(a;b;q;z) = (q,b/a,az,q/(az);q)∞ / (b,q/a,z,b/(az);q)∞
```
This is the key analytic tool for the 10th-order proof.

## Key files to read

- `QseriesFormalization/Chapter10.lean` — existing mock theta
- `QseriesFormalization/Pending/Chapter10_*.lean` — existing Pending work
- `QseriesFormalization/Pending/Ramanujan1Psi1.lean` — if it exists, ₁ψ₁ infrastructure
- `QseriesFormalization/Chapter19.lean` — qPochInfPS, partitionGenFun

## Build command

```bash
export PATH=$HOME/.elan/bin:$PATH
cd ~/repos/Q-series-and-Chan-s-work
lake env lean QseriesFormalization/Pending/Chapter10_TenthOrder.lean
```

## Rules

- No sorry in final committed code (sorry stubs OK during development)
- No axiom, no native_decide
- Reply to `HANDOFF/outbox/codex-ch10-mock-theta-reply.md` when done
