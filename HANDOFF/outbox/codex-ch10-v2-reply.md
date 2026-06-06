# Ch10 v2 report

## Files changed

- `QseriesFormalization/Pending/Chapter10_TenthOrder.lean`

## Coefficient verification extended

Extended the tenth-order mock theta coefficient certificates to degree 25:

- `mockThetaPhiCoeffList_twentyfive`
  - `[1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26, 31, 34, 40, 46, 52, 60, 68, 76, 87, 98]`
- `mockThetaPsiCoeffList_twentyfive`
  - `[0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16, 18, 20, 24, 26, 30, 36, 40, 44, 52, 58]`

## Chan Eq. (10.15) RHS coefficients

Added computable integer coefficient infrastructure for the RHS:

- `chan1015EtaCoeffZ`
- `etaAtPowerCoeffZ`
- `convCoeffVecZ`
- `coeffVecOfFnZ`
- `powCoeffVecZ`
- `coeffFromVecZ`
- `unitInvCoeffAuxZ`
- `unitInvCoeffVecZ`
- `chan1015PentagonalCoeffZ`
- `chan1015RHSCoeffVec`
- `chan1015RHSCoeff`
- `chan1015RHSCoeffList`

The RHS computation follows:

```text
- (Q^3;Q^3)_inf^5 * ((Q^6;Q^6)_inf^2)^-1 * pentagonal_factor
```

using truncated convolution for products and the standard recursive inverse
for unit power series.

## LHS/RHS check through degree 15

Added:

- `squareWindow`, used to shrink the `k,l` loops in `chan1015LHSCoeff`
- `chan1015LHSCoeffList`
- `#guard chan1015LHSCoeffList 15 == chan1015RHSCoeffList 15`

The common coefficient list is:

```text
[-1, 0, 0, 6, 0, 0, -12, 0, 0, 7, 0, 0, 1, 0, 0, 6]
```

## Validation

Commands run:

```bash
export PATH=$HOME/.elan/bin:$PATH
lake env lean QseriesFormalization/Pending/Chapter10_TenthOrder.lean
lake env lean QseriesFormalization/Pending/Ramanujan1Psi1.lean
rg -n "sorry|axiom|native_decide" QseriesFormalization/Pending/Chapter10_TenthOrder.lean
```

Results:

- `Chapter10_TenthOrder.lean` passes.
- `Ramanujan1Psi1.lean` still passes.
- No `sorry`, `axiom`, or `native_decide` occurs in the edited Ch10 file.
