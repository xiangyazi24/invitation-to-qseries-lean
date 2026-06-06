# codex-fixstmt reply

Edited `QseriesFormalization/Pending/Chapter10_HM.lean`.

## Statement fix

The false unconditional HM2.3 cleared/PF statements now require
`hm23Nonsingular a z0 z1`:

- `appellNumeratorLaurent_PF_changeOfZ_coeff_mapDown`
- `hm23PartialFractionExpansionPF`
- `hm23ResidueCancellationCoefficientAlgebra`
- `hm23ClearedThetaIdentity`

`hm23ChangeZIdentity` now passes its existing `hreg` into
`hm23ClearedThetaIdentity`.  `ch10_classical_theta_bridge` exposes the corrected
conditional cleared theorem:

```lean
∀ a z0 z1 : ℤ,
  hm23Nonsingular a z0 z1 →
    hm23ClearedThetaLHS a z0 z1 = hm23ClearedThetaRHS a z0 z1
```

## Map-down progress

Closed the denominator/nonzero and branch-coefficient layer:

- `geomInvCoeff_eq_branchInvCoeffAtPF_ediv`
- `appellNumeratorPFBranchCoeff`
- `appellNumeratorCoeff_eq_PFBranchCoeff`
- `appellDenomExp_ne_zero_of_jLaurent_ne_zero`
- `hm23Nonsingular_appellDenomExp_z0_ne_zero`
- `hm23Nonsingular_appellDenomExp_z1_ne_zero`

The remaining HM2.3 map-down gap is isolated as:

```lean
theorem hm23PFBranchMapDown_coeff_residual
    (hPF :
      Chapter10PF.thetaMulPFSeriesCoeffPF =
        Chapter10PF.qPochInfPSCubeUPowerCoeffPF)
    (a z0 z1 e : ℤ) (_hreg : hm23Nonsingular a z0 z1)
    (_hnum0 : ∀ E : ℤ,
      appellNumeratorCoeff a z0 E = appellNumeratorPFBranchCoeff a z0 E)
    (_hnum1 : ∀ E : ℤ,
      appellNumeratorCoeff a z1 E = appellNumeratorPFBranchCoeff a z1 E) :
    ...
```

This is the remaining support/summation transport after rewriting the HM
finite-window numerator coefficients into the PF branch convention.

## T_ij nonsingularity

Added clean numeric witnesses for all nine specializations:

- `hmF232Terms_T00_hm23Nonsingular`
- `hmF232Terms_T01_hm23Nonsingular`
- `hmF232Terms_T02_hm23Nonsingular`
- `hmF232Terms_T10_hm23Nonsingular`
- `hmF232Terms_T11_hm23Nonsingular`
- `hmF232Terms_T12_hm23Nonsingular`
- `hmF232Terms_T20_hm23Nonsingular`
- `hmF232Terms_T21_hm23Nonsingular`
- `hmF232Terms_T22_hm23Nonsingular`

Each proof unfolds the concrete HM term list and discharges the four mod-90
conditions by `norm_num [hm23DeltaBase]`.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passed with exactly the two expected `sorry` warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:4375:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:4874:8: warning: declaration uses 'sorry'
```

Forbidden-token grep for `native_decide`, `admit`, `axiom`, and `opaque`
returned no matches.

## #print axioms

```text
'QseriesFormalization.Pending.Ch10HM.geomInvCoeff_eq_branchInvCoeffAtPF_ediv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appellNumeratorCoeff_eq_PFBranchCoeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23PFBranchMapDown_coeff_residual' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appellNumeratorLaurent_PF_changeOfZ_coeff_mapDown' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23PartialFractionExpansionPF' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23DeltaToBase_eq_changeZ' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.ch10_classical_theta_bridge' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

All nine `hmF232Terms_Tij_hm23Nonsingular` theorems report only:

```text
[propext, Classical.choice, Quot.sound]
```
