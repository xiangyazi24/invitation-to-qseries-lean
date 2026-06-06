# Ch10 mock theta infrastructure report

## Files changed

- `QseriesFormalization/Pending/Chapter10_TenthOrder.lean`

## What was added

- Added truncated-convolution coefficient infrastructure for Chan/Ramanujan tenth-order
  mock theta functions:
  - `tenthOrderPhiShift`
  - `tenthOrderPsiShift`
  - `oddQPochInvMulStep`
  - `oddQPochInvCoeffVec`
  - `oddQPochInvCoeff`
  - `mockThetaPhiCoeffNat`
  - `mockThetaPsiCoeffNat`
  - `mockThetaPhiCoeffVec`
  - `mockThetaPsiCoeffVec`
  - `mockThetaPhiCoeffList`
  - `mockThetaPsiCoeffList`

- Rebased the formal PS definitions on those coefficient functions:
  - `mockThetaPhiPS : ℚ⟦X⟧`
  - `mockThetaPsiPS : ℚ⟦X⟧`
  - `[simp] coeff_mockThetaPhiPS`
  - `[simp] coeff_mockThetaPsiPS`

- Kept explicit formal summand definitions:
  - `mockThetaPhiSummandPS n = X^(n(n+1)/2) * (oddQPochPS (n+1))⁻¹`
  - `mockThetaPsiSummandPS n = X^((n+1)(n+2)/2) * (oddQPochPS (n+1))⁻¹`

- Added coefficient certificates through degree 15:
  - `mockThetaPhiCoeffList_fifteen`
    - `[1, 2, 2, 3, 4, 4, 6, 7, 8, 10, 12, 14, 16, 20, 22, 26]`
  - `mockThetaPsiCoeffList_fifteen`
    - `[0, 1, 1, 2, 2, 2, 4, 4, 4, 6, 7, 8, 10, 11, 12, 16]`

- Added a theorem-sized target wrapper for Chan Eq. (10.15):
  - `chan1015IdentityStatement_iff`

## Convention note

The handoff text mentions `(q,q^2;q^2)_n`, but the Chan/Ramanujan/OEIS tenth-order
`φ` and `ψ` coefficient sequences use the odd denominator
`(q;q^2)_{n+1} = (1-q)(1-q^3)...(1-q^(2n+1))`.

I kept that convention because it matches:

- OEIS A053281: https://oeis.org/A053281
- OEIS A053282: https://oeis.org/A053282

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
- No `sorry`, `axiom`, or `native_decide` occurs in the edited Lean file.
