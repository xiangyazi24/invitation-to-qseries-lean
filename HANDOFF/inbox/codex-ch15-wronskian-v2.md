# Task: Ch15 Wronskian — close the 3 sorries in Chapter15_WronskianBridge.lean

## Context

You are working in `~/repos/Q-series-and-Chan-s-work/`, a Lean 4 + Mathlib v4.27 formalization.

The previous round correctly proved that the Wronskian identity is FALSE for
`pentagonal014/023SeriesPS` (which include E5). The correct target uses E5-free
products defined in `QseriesFormalization/Pending/Chapter15_WronskianBridge.lean`.

**Read that file first** — it has the correct definitions, 3 sorry targets, and
the full proof chain documented.

## The 3 sorries to close

### Sorry 1: `rogers_ramanujan_wronskian_cleared` (line ~99)

```
rrProductA ℚ * rrProductB ℚ +
  5 * (rrProductB ℚ * thetaOp (rrProductA ℚ) -
       rrProductA ℚ * thetaOp (rrProductB ℚ)) =
(qPochInfPS ℚ) ^ 4 * (rrProductA ℚ) ^ 2 * (rrProductB ℚ) ^ 2
```

where:
- `rrProductA = qPochAPPS 1 5 * qPochAPPS 4 5` (E5-free)
- `rrProductB = qPochAPPS 2 5 * qPochAPPS 3 5` (E5-free)

**Approach**: Coefficient verification. Both sides are in ℚ⟦X⟧. Compute
coefficients of both sides to degree N using truncated convolution (follow the
`tauEtaPowVec` pattern from Chapter20.lean). Prove equality coefficientwise
using `decide` or `interval_cases`.

The left side needs: coefficients of rrProductA, rrProductB (from qPochAPPS
convolution), thetaOp (multiply by index), Cauchy product.

The right side needs: qPochInfPS^4 coefficients (from pentagonalSign convolution),
rrProductA^2, rrProductB^2 (Cauchy product).

If you can verify through degree 20, that's a good start. Through degree 1 suffices
by the Sturm bound for weight-2 level-5 modular forms, but we don't have the
modular forms machinery, so higher degree is better.

### Sorry 2: `chan15LHSPS_eq_qPochInfPS_pow4_mul_rrProducts` (line ~117)

```
chan15LHSPS ℚ = (qPochInfPS ℚ) ^ 4 * rrProductA ℚ * rrProductB ℚ
```

This says chan15 = E^4 * A * B. **Approach**: Coefficient verification again.
The LHS is `chan15LHSCoeffInt` (Lambert divisor sum). The RHS is E^4 * A * B
(convolution of pentagonal^4 with rrProduct coefficients).

### Sorry 3: `wronskian_at_pentagonal_level` (line ~158)

```
pentagonal014SeriesPS ℚ * pentagonal023SeriesPS ℚ +
  5 * (pentagonal023SeriesPS ℚ * thetaOp (pentagonal014SeriesPS ℚ) -
       pentagonal014SeriesPS ℚ * thetaOp (pentagonal023SeriesPS ℚ)) =
(qPochInfPS ℚ) ^ 6
```

This is `P14*P23 + 5*(P23*θP14 - P14*θP23) = E^6`. **Approach**: follows
from Sorry 1 via Leibniz rule (thetaOp_mul) and E5 cancellation.

## Key infrastructure already available

- `coeff_thetaOp`: `(thetaOp f).coeff n = f.coeff n * n`
- `thetaOp_mul`: `thetaOp (f * g) = f * thetaOp g + g * thetaOp f`
- `pentagonal014SeriesPS_mul_pentagonal023SeriesPS_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat`
- `pentagonalProduct014PS_eq_pentagonal014SeriesPS_rat`
- `coeff_qPochInfPS_eq_pentagonalSign`
- `tauEtaPowVec`/`tauEtaPowStep` pattern in Chapter20.lean

## Build

```bash
export PATH=$HOME/.elan/bin:$PATH
lake env lean QseriesFormalization/Pending/Chapter15_WronskianBridge.lean
```

## Rules

- Edit ONLY `Chapter15_WronskianBridge.lean`. Do not create new files.
- No sorry, no axiom, no native_decide in final code
- Reply to `HANDOFF/outbox/codex-ch15-wronskian-v2-reply.md`
