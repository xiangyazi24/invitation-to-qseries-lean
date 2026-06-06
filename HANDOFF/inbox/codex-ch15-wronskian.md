# Task: Ch15 Wronskian identity — bridge chan15LHSPS to pentagonal products via thetaOp

## Context

You are working in `~/repos/Q-series-and-Chan-s-work/`, a Lean 4 + Mathlib v4.27 formalization.

The main sorry blocking Ch15 is in `QseriesFormalization/Pending/Chapter15_Hirschhorn.lean:157`:
```lean
theorem chan_theorem_11_7_rat :
    chan15LHSPS ℚ * PowerSeries.expand 5 (qPochInfPS ℚ) = (qPochInfPS ℚ) ^ 5 := by
  ext N
  by_cases hN : N ≤ 20
  · exact chan15_theorem_11_7_coeff_low ℚ N hN
  · push_neg at hN
    sorry
```

## Mathematical target

Chan Theorem 11.7 is equivalent to the Rogers-Ramanujan Wronskian (denominator-cleared form):

```
A · B + 5 · (B · θ(A) - A · θ(B)) = E⁴ · A² · B²
```

where:
- `A = pentagonal014SeriesPS R` — `∑_{k∈ℤ} (-1)^k X^((5k²-3k)/2)` — the `(q,q⁴;q⁵)∞` series
- `B = pentagonal023SeriesPS R` — `∑_{k∈ℤ} (-1)^k X^((5k²-k)/2)` — the `(q²,q³;q⁵)∞` series
- `E = qPochInfPS R` — Euler `(q;q)∞`
- `θ = thetaOp` — Euler's theta operator `X d/dX`

The bridge: `E = A · B · E₅` where `E₅ = expand 5 (qPochInfPS R)`, so:
```
chan15LHSPS · E₅ = E⁵
⟺ E₅² · (A·B + 5·(B·θA - A·θB)) = E⁶
⟺ A·B + 5·(B·θA - A·θB) = E⁴·A²·B²  [using E = A·B·E₅]
```

## Your task

Work in a NEW file `QseriesFormalization/Pending/Chapter15_Wronskian.lean`. Do NOT touch any existing file.

### Step 1: State the Wronskian target

```lean
theorem rogers_ramanujan_wronskian_cleared (R : Type*) [CommRing R] :
    pentagonal014SeriesPS R * pentagonal023SeriesPS R +
      5 * (pentagonal023SeriesPS R * thetaOp (pentagonal014SeriesPS R) -
           pentagonal014SeriesPS R * thetaOp (pentagonal023SeriesPS R)) =
    (qPochInfPS R) ^ 4 * (pentagonal014SeriesPS R) ^ 2 * (pentagonal023SeriesPS R) ^ 2 := by
  sorry
```

### Step 2: Verify coefficients

Using the existing `pentagonal014Coeff`/`pentagonal023Coeff` + `coeff_thetaOp` + `pentagonalSign`, compute both sides coefficientwise through degree 20+ and prove equality. Follow the pattern in `Chapter15_CoeffVerification.lean`.

### Step 3: Bridge to chan15LHSPS

Prove that `chan15LHSPS` equals the Wronskian form divided by `E₅²`, i.e., show:
```lean
chan15LHSPS R * expand5(E) = E₅² * (A·B + 5·(B·θA - A·θB)) / E₅²
```
This needs the factorization `E = A · B · E₅` and the Leibniz rule for thetaOp.

## Key files to read

- `QseriesFormalization/Pending/Chapter15_FormalDeriv.lean` — thetaOp and properties
- `QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean` — pentagonal014/023 definitions
- `QseriesFormalization/Pending/Chapter15_CoeffVerification.lean` — coefficient verification pattern
- `QseriesFormalization/Pending/Chapter15_Hirschhorn.lean` — current sorry location
- `QseriesFormalization/Chapter19.lean` — qPochInfPS, pentagonalSign

## Build command

```bash
export PATH=$HOME/.elan/bin:$PATH
cd ~/repos/Q-series-and-Chan-s-work
lake env lean QseriesFormalization/Pending/Chapter15_Wronskian.lean
```

## Rules

- No sorry in final code (sorry stubs OK during development, track them)
- No axiom, no native_decide
- Clean-3 axioms: `[propext, Classical.choice, Quot.sound]`
- Reply to `HANDOFF/outbox/codex-ch15-wronskian-reply.md` when done
