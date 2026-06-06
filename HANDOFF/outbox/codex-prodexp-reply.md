# codex prodexp reply

Status: partial, bankable product expansion committed.

Edited only `QseriesFormalization/Pending/Chapter10_HM.lean` for Lean code.

## Added

General bounded-below Laurent convolution:

```lean
theorem lcoeff_mul_eq_sum_Icc_of_coeff_zero_lt
theorem lcoeff_mul_eq_zero_of_lt_add_lower
```

HM-side level-90 product expansions:

```lean
theorem lcoeff_two_jLaurent_90_eq_coeff_sum
theorem lcoeff_three_jLaurent_90_eq_coeff_sum
theorem lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_coeff_sum
theorem lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_window_sum
```

The final theorem expands

```lean
lcoeff
  (appellNumeratorLaurent a z * jLaurent w₁ 90 *
    jLaurent w₂ 90 * jLaurent w₃ 90) e
```

into the finite nested convolution over the Appell numerator coefficient
window and the three `jCoeff` coefficient windows.

Also added the raw PF coefficient extraction from `hPF`:

```lean
theorem thetaMulPFRawCoeffPF_eq_qPochInfPSCubeUPowerCoeffPF_coeff_of_hPF
```

This uses `Chapter10PF.thetaMulPFRawCoeffPF_eq_thetaMulPFCoeffPF` and a
coefficient projection of `hPF`.

## Remaining gap

`hm23PFBranchMapDown_coeff_residual` is still the true open step.  The new
HM-side theorem expands each four-factor product, and the raw PF bridge now
extracts raw coefficients from `hPF`; the missing piece is the reindexing
that combines the two expanded HM products

```lean
appellNumeratorLaurent a z1 * jLaurent z0 90 *
  jLaurent (a + z0) 90 * jLaurent (a + z1) 90

appellNumeratorLaurent a z0 * jLaurent z1 90 *
  jLaurent (a + z0) 90 * jLaurent (a + z1) 90
```

into the exact `Chapter10PF.thetaMulPFRawCoeffPF` family, with the remaining
theta factors and the `Qpow z0` shift aligned to the RHS coefficient.  I did
not replace this with a renamed sorry and did not touch `Chapter10_PF.lean`,
the collapse residual, `redJ`, the bridge lemmas, `jLaurent_riemann`, or
`jLaurent_eq_tripleProductInf`.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passed with the two pre-existing warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:4638:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:5137:8: warning: declaration uses 'sorry'
```

Forbidden-token grep in `Chapter10_HM.lean`:

```text
3373:def hm23Nonsingular (a z0 z1 : ℤ) : Prop :=
4653:  sorry
5140:  sorry
```

## #print axioms

Source-pipe check, avoiding stale `.olean`:

```text
'QseriesFormalization.Pending.Ch10HM.lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_window_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.thetaMulPFRawCoeffPF_eq_qPochInfPSCubeUPowerCoeffPF_coeff_of_hPF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23PFBranchMapDown_coeff_residual' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
