# codex-collapse2 reply

## Result

Partial, with real narrowing of the theta collapse.

Edited only `QseriesFormalization/Pending/Chapter10_HM.lean`.

`theta_correction_cleared_product_identity` is no longer a naked `sorry`.
It now follows from a single denominator-cleared residual:

```lean
theorem theta_correction_denominator_cleared_residual :
    thetaCorrectionMod90DenominatorProduct *
      (E6Laurent ^ 2 * thetaCorrectionLaurent + E3Laurent ^ 5 * jLaurent 12 15) = 0
```

The multiplier is the raw product of the four mod-90 denominator factors
`[18, z, a+18, a+z]` for each of the 30 nonzero HM 2.3 correction entries,
in `T_ij` table order.  I proved the denominator product is nonzero via:

```lean
theorem jLaurent_90_ne_zero_of_emod_ne_zero (a : ℤ) (hmod : a % 90 ≠ 0) :
    jLaurent a 90 ≠ 0

theorem thetaCorrectionMod90DenominatorProduct_ne_zero :
    thetaCorrectionMod90DenominatorProduct ≠ 0
```

So the public theorem is now proved by cancelling this nonzero denominator
product from the residual.

## Riemann Rewrite Sequence

No `jLaurent_riemann (A,B,C,D)` rewrite was successfully applied in the final
proof.

Remaining exact gap:

```lean
theta_correction_denominator_cleared_residual
```

This is the finite residual that still needs the explicit Riemann-addition
rewrite chain after the raw mod-90 denominators have been cleared.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passed with exactly two `sorry` warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:3869:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:3997:8: warning: declaration uses 'sorry'
```

`scripts/ch10_hm_verify.py` passed, including HM 2.3 samples, all shifted
`T_ij` checks, Chan combination, and the theta-correction Delta sum through
`Q^44`.

Forbidden-token grep reports only the existing denominator-condition Prop and
the two remaining honest `sorry`s:

```text
2889:def hm23Nonsingular (a z0 z1 : ℤ) : Prop :=
3875:  sorry
4000:  sorry
```

## Axioms

```text
'QseriesFormalization.Pending.Ch10HM.jLaurent_riemann' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_denominator_cleared_residual' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_cleared_product_identity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_product_identity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_eval' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
