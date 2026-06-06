# Task: Ch20 — Commit tau consolidation + extend Hecke/multiplicativity

## Context

You are working in `~/repos/Q-series-and-Chan-s-work/`, a Lean 4 + Mathlib v4.27 formalization.

Ch20 has uncommitted changes that consolidate τ values from three separate files into Chapter20.lean using a truncated convolution framework (`tauEtaPowStep`/`tauEtaPowVec`/`tauEtaPowCoeffZ`). This computes τ(0)..τ(50) via repeated convolution of Euler pentagonal coefficients.

## Your task

### Step 1: Build and verify the current uncommitted changes

```bash
export PATH=$HOME/.elan/bin:$PATH
cd ~/repos/Q-series-and-Chan-s-work
lake env lean QseriesFormalization/Chapter20.lean
```

If it builds clean, good. If there are errors, fix them.

### Step 2: Verify the separate files are now redundant

Check that `Chapter20_TauExtend.lean`, `Chapter20_TauMult.lean`, `Chapter20_TauValues.lean` have had their content absorbed into the main `Chapter20.lean`. If so, verify the main build still works without them (they should not be imported by any main-graph file).

### Step 3: Extend τ values and Hecke checks

Using `ramanujanTau_succ_eq_tauEtaPowCoeffZ`, prove:
- All coprime-factor multiplicativity pairs up to 50:
  `τ(a·b) = τ(a)·τ(b)` for coprime a,b with a·b ≤ 50
- Prime-power Hecke recursion:
  `τ(p^(k+1)) = τ(p)·τ(p^k) - p^11·τ(p^(k-1))` for p ∈ {2,3,5,7}, pk ≤ 50
- τ parity pattern through 50

### Step 4: State Ch20 main targets

From Chan §20, state as `sorry`:
- Ono's Theorem 20.1 (conditional on half-integral weight modular forms)
- Any additional τ congruences or bounds that follow from coefficient verification

## Key files to read

- `QseriesFormalization/Chapter20.lean` — main file (has uncommitted changes)
- `QseriesFormalization/Chapter20_TauExtend.lean` — being absorbed
- `QseriesFormalization/Chapter20_TauMult.lean` — being absorbed
- `QseriesFormalization/Chapter20_TauValues.lean` — being absorbed
- `QseriesFormalization/Chapter19.lean` — qPochInfPS, pentagonalSign

## Build command

```bash
export PATH=$HOME/.elan/bin:$PATH
cd ~/repos/Q-series-and-Chan-s-work
lake env lean QseriesFormalization/Chapter20.lean
```

For full build (only after all work is done):
```bash
lake build QseriesFormalization
```

## Rules

- No sorry in final code
- No axiom, no native_decide  
- set_option maxHeartbeats 0 is OK for heavy native computation
- Reply to `HANDOFF/outbox/codex-ch20-tau-consolidation-reply.md` when done
