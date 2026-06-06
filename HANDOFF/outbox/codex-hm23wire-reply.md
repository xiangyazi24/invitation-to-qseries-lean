# codex-hm23wire reply

Read `HANDOFF/inbox/codex-hm23wire.md`.

## Result

Edited only `QseriesFormalization/Pending/Chapter10_HM.lean` for Lean code.

Progress made:

- Imported the stable PF module:
  `QseriesFormalization.Pending.Chapter10_PF`.
- Proved the first concrete map-down bridge from HM's one-variable branch
  convention to the PF branch coefficients:

```lean
theorem geomInvCoeff_mul_eq_branchInvCoeffAtPF
    (d m : ℤ) (hd : d ≠ 0) :
    geomInvCoeff d (d * m) =
      (Chapter10PF.branchInvCoeffAtPF d (d * m) m : ℚ)

theorem geomInvCoeff_mul_eq_branchInvCoeffPF
    (d m : ℤ) (hd : d ≠ 0) :
    geomInvCoeff d (d * m) =
      (Chapter10PF.branchInvCoeffPF d m : ℚ)
```

- Rewired `hm23PartialFractionExpansionPF` so it no longer directly contains
  a `sorry`.  It now proves the Laurent equality coefficientwise from the
  isolated PF specialization residual, passing in the proved theorem
  `Chapter10PF.thetaMul_PF_eq_qPochInfPS_pow_three`.

## Remaining gap

One honest HM2.3 residual remains:

```lean
theorem appellNumeratorLaurent_PF_changeOfZ_coeff_mapDown
    (hPF :
      Chapter10PF.thetaMulPFSeriesCoeffPF =
        Chapter10PF.qPochInfPSCubeUPowerCoeffPF)
    (a z0 z1 e : ℤ) :
    lcoeff
      (((appellNumeratorLaurent a z1 * jLaurent z0 90 -
              appellNumeratorLaurent a z0 * jLaurent z1 90) *
            jLaurent (a + z0) 90 * jLaurent (a + z1) 90) -
          Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
            jLaurent (a + z0 + z1) 90) e = 0
```

This is the remaining summation/support map-down from the proved two-variable
PF coefficient family to the existing one-variable `QLaurent` coefficient
model for `appellNumeratorLaurent`.  The branch-level `geomInvCoeff` vs PF
branch compatibility is now proved above it.

I did not touch `jLaurent_riemann`, `jLaurent_eq_tripleProductInf`, the four
bridge lemmas, or `theta_correction_denominator_cleared_residual`.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passed with the two expected warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:4274:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:4439:8: warning: declaration uses 'sorry'
```

Forbidden-token grep:

```text
3293:def hm23Nonsingular (a z0 z1 : ℤ) : Prop :=
4285:  sorry
4442:  sorry
```

The `def : Prop` is pre-existing.  The two `sorry`s are the new PF map-down
residual and the pre-existing theta-correction residual.

## #print axioms

```text
'QseriesFormalization.Pending.Ch10HM.appellNumeratorLaurent_PF_changeOfZ_coeff_mapDown' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23PartialFractionExpansionPF' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.thetaMul_PF_eq_qPochInfPS_pow_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
