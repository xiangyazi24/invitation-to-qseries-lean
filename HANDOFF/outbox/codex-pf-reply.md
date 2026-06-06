# codex-pf reply

Created:

- `QseriesFormalization/Pending/Chapter10_PF.lean`

Did not touch or import `QseriesFormalization/Pending/Chapter10_HM.lean`.

## What is proved

The new file is self-contained relative to the allowed stable imports:

- `Mathlib`
- `QseriesFormalization.Chapter03`
- `QseriesFormalization.Pending.JTP_FormalPS_Pentagonal`
- `QseriesFormalization.Chapter19`

Closed lemmas:

- local `qPochPF`, `jCoeffPF`, `pfNumExpPF`;
- coefficient-level lex/annulus branch for `(1 - q^k u)^{-1}`;
- `denom_mul_branchInvCoeffAtPF`: the branch coefficients satisfy
  `(1 - q^k u) * branchInv(k) = 1` coefficientwise;
- `thetaMulPFConstCoeffPF_eq_jacobiCubeCoeffPF`: after multiplying by the
  coefficient-definition theta `j(u;q)`, the `u^0` coefficient of the PF side
  is the Jacobi cube coefficient
  `∑_h (-1)^h (2h+1) q^(h(h+1)/2)`.

## Exact remaining blocker

I did **not** prove the full localized-ring theorem

`j(u;q) * PF(u;q) = (q;q)_∞^3`

as a Hahn-series equality.

The missing upstream input is exactly the formal Jacobi cube identity

`(qPochInfPS R)^3 = jacobiThetaPS R`.

`Chapter19` defines `jacobiThetaPS` but explicitly leaves this formal cube
identity as future B2 work. The unconditional proof appears to live in a
pending analytic-to-formal bridge outside the allowed import set, so I did not
import it.

## Verification

Ran:

```bash
lake env lean QseriesFormalization/Pending/Chapter10_PF.lean
```

It passed.

## #print axioms

```text
'QseriesFormalization.Pending.Chapter10PF.qPochPF_eq_qPochInfPS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.jCoeffPF_of_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.jCoeffPF_of_ne_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.branchInvCoeffPF_nonneg' depends on axioms: [propext]
'QseriesFormalization.Pending.Chapter10PF.branchInvCoeffPF_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.branchInvCoeffAtPF_zero_of_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.branchInvCoeffAtPF_sub_cancel_of_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.branchInvCoeffAtPF_sub_cancel_of_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.denom_mul_branchInvCoeffAtPF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.thetaMulPFConstCoeffPF_eq_jacobiCubeCoeffPF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.firstBranchMultiplicityPF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

