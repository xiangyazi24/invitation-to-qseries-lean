# Ch10 theta-correction reply

Status: partial.  I added the Laurent-level theta-correction target and
isolated the remaining product identity as one explicit `sorry`.

## Lean changes

Edited only:

- `QseriesFormalization/Pending/Chapter10_HM.lean`

Added:

- `hm23DeltaBase := -30`
- `hm23DeltaToBase`
- `hmTermThetaCorrection`, `hmTermsThetaCorrection`,
  `hmF232ThetaCorrection`
- `TijThetaCorrection`, `H00ThetaCorrection`, `H10ThetaCorrection`,
  `H01ThetaCorrection`, `H11ThetaCorrection`
- `thetaCorrectionLaurent`
- `etaLaurent`, `E3Laurent`, `E6Laurent`
- `theta_correction_product_identity`
- `theta_correction_eval`
- conditional Laurent-level assembly `chan1015_hm_laurent`

The remaining formal gap is exactly:

```lean
theorem theta_correction_product_identity :
    thetaCorrectionLaurent =
      -(E3Laurent ^ 5) * (E6Laurent ^ 2)⁻¹ * jLaurent 12 15 := by
  sorry
```

## Numeric verification

I did not edit `scripts/ch10_hm_verify.py` because the task also said to edit
only `Chapter10_HM.lean`.  I ran a temporary Python check importing the existing
verifier and computing the Delta-only correction.

Important: with the current Lean/Python HM table, where `T02` and `T10` use
`ell=2`, the handoff's requested base `z0=18` does **not** numerically verify.
The base `z0=-30` does verify, and the Appell base contribution is zero.

```text
Delta Corr with z0=-30 vs -E3^5*E6^-2*j(12,15) through Q^44: OK
  nonzero=[(0, -1), (3, 6), (6, -12), (9, 7), (12, 1), (15, 6), (18, -4), (21, -14), (24, 18), (27, -18), (33, 13), (36, 28), (39, -18), (42, -8)]
Base contribution with z0=-30 through Q^44: zero
Delta Corr with z0=+18 vs -E3^5*E6^-2*j(12,15) through Q^44: FAIL
  first diffs=[(0, 3, -1), (3, 2, 6), (9, -1, 7), (12, 9, 1), (15, 2, 6), (24, 30, 18), (33, 5, 13), (36, 36, 28)]
Base contribution with z0=+18 through Q^44: nonzero
  first base coeffs=[(0, -4, 0), (3, 4, 0), (9, 8, 0), (12, -8, 0), (15, 4, 0), (24, -12, 0), (33, 8, 0), (36, -8, 0)]
```

Existing full verifier still passes:

```text
Checking HM Def. 0.1 quotient bridge j(z,90)*m(a,z)=numerator
m(+36,+18): OK
m(+36,+12): OK
m(+21,-12): OK
m(-9,+18): OK
m(+6,-24): OK
m(-39,+30): OK
m(+21,+42): OK
Checking HM Theorem 2.3 change-of-z through Q^44
a=+36, z0=+12, z1=+18: OK
a=+21, z0=-12, z1=+18: OK
a=-9, z0=+18, z1=-18: OK
a=+6, z0=-24, z1=+24: OK
a=+36, z0=-30, z1=+30: OK
Checking shifted T_ij HM table against direct f_{2,3,2} through Q^44
T00: OK
T01: OK
T02: OK
T10: OK
T11: OK
T12: OK
T20: OK
T21: OK
T22: OK
Chan combination vs -E3^5*E6^-2*j(12,15) through Q^44: OK
```

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
lake build QseriesFormalization.Pending.Chapter10_HM
python3 scripts/ch10_hm_verify.py
rg -n "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|opaque|def .*: Prop" \
  QseriesFormalization/Pending/Chapter10_HM.lean
```

Lean and the targeted module build pass.  The only new proof hole is
`theta_correction_product_identity`; no `native_decide`, `admit`, `axiom`, or
`opaque` was added.  The existing `def : Prop` wrappers for HM 2.3 remain:

```text
363:def hm23Nonsingular (a z0 z1 : ℤ) : Prop :=
371:def hm23ClearedThetaIdentity (a z0 z1 : ℤ) : Prop :=
398:def hm23ChangeZIdentity (a z0 z1 : ℤ) : Prop :=
850:  sorry
```

## Axioms

```text
'QseriesFormalization.Pending.Ch10HM.theta_correction_eval' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_product_identity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.chan1015_hm_laurent' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appell_cancel' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ChangeZIdentity_of_cleared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Not closed

I did not add an unconditional `chan1015 : chan1015LHSPS = chan1015RHSPS`.
Those objects live in `Chapter10_TenthOrder.lean`, and there is still no formal
bridge from that PowerSeries target to the Laurent HM combination in this file.
The current assembly theorem is therefore conditional on the missing HM
decomposition rewrite.
