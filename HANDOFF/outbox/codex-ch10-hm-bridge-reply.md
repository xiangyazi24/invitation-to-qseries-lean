# Ch10 HM bridge reply

## Commits

- `84d545d ch10: verify HM Appell-Lerch identities`
  - Extends `scripts/ch10_hm_verify.py`.
  - Adds Def. 0.1 quotient bridge checks `j(z,90)*m(a,z)=numerator`.
  - Adds HM Theorem 2.3 theta-quotient numerical checks.
- `e90a374 ch10: define HM Appell-Lerch quotient`
  - Renames the old functional-equation normal form to `appellMFE`.
  - Defines public `appellM` as the HM Def. 0.1 quotient:
    `jLaurent z 90 ⁻¹ * appellNumeratorLaurent a z`.
  - Adds coefficient extraction for the Def. 0.1 numerator:
    `geomInvCoeff`, `appellNumeratorCoeff`, `appellNumeratorLaurent`.
  - Adds clean theorem `appellM_eq_hmDef01`.
  - Adds `JOneLaurent`, `hm23ThetaQuotient`, and the exact Prop
    `hm23ChangeZIdentity`.

## Important correction

The old `appellM` normal form cannot be bridged to HM Def. 0.1 as an equality:
it is independent of `z`, while the genuine quotient is not.  Numeric check before
editing gave, for example:

```text
genuine m(Q^36,Q^90,Q^18) coefficient at Q^18 = -1
old functional-equation normal form coefficient at Q^18 = 0
```

So I did not prove a false bridge.  The file now keeps the old object as
`appellMFE` and makes `appellM` the genuine quotient.

## Numeric verification

Command:

```bash
python3 scripts/ch10_hm_verify.py
```

Output:

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
T00: sign=+1, C= 1, X=18, Y=18, ell=+1, nonzero<=44 direct= 3, HM= 3: OK
T01: sign=-1, C= 5, X=27, Y=24, ell=+1, nonzero<=44 direct= 4, HM= 4: OK
T02: sign=+1, C=11, X=36, Y=30, ell=+2, nonzero<=44 direct= 3, HM= 3: OK
T10: sign=-1, C= 5, X=24, Y=27, ell=+2, nonzero<=44 direct= 4, HM= 4: OK
T11: sign=+1, C=12, X=33, Y=33, ell=+1, nonzero<=44 direct= 3, HM= 3: OK
T12: sign=-1, C=21, X=42, Y=39, ell=+1, nonzero<=44 direct= 4, HM= 4: OK
T20: sign=+1, C=11, X=30, Y=36, ell=+1, nonzero<=44 direct= 3, HM= 3: OK
T21: sign=-1, C=21, X=39, Y=42, ell=+1, nonzero<=44 direct= 4, HM= 4: OK
T22: sign=+1, C=33, X=48, Y=48, ell=+1, nonzero<=44 direct= 3, HM= 3: OK
Chan combination vs -E3^5*E6^-2*j(12,15) through Q^44: OK
```

## Lean validation

Commands:

```bash
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
lake build QseriesFormalization.Pending.Chapter10_HM
rg -n "native_decide|\bsorry\b|\badmit\b|^\s*axiom\b|opaque" \
  QseriesFormalization/Pending/Chapter10_HM.lean scripts/ch10_hm_verify.py
```

Result:

```text
warning: QseriesFormalization/Pending/Chapter10_HM.lean:685:8: declaration uses 'sorry'
Build completed successfully.

QseriesFormalization/Pending/Chapter10_HM.lean:683:not imported by `Audit.lean`.  It is the only `sorry` in this file.
QseriesFormalization/Pending/Chapter10_HM.lean:686:  sorry
```

No `native_decide`, `admit`, `axiom`, or `opaque`.

## Axioms

After refreshing the module olean:

```text
'QseriesFormalization.Pending.Ch10HM.appellM_eq_hmDef01' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.coeff_appellNumeratorLaurent' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.coeff_appellM' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ThetaQuotient' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ChangeZIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hmF232Laurent_T02' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appell_cancel' depends on axioms: [sorryAx]
```

## Remaining proof status

- DEF-0.1 bridge: closed at the public-definition level by making `appellM`
  the genuine quotient and proving `appellM_eq_hmDef01`.
- HM Theorem 2.3: RHS and exact identity proposition are formalized and
  numerically checked, but the full formal theta-quotient proof is not proved.
  I did not add a fake theorem or a second `sorry`.
- `appell_cancel` remains the one isolated `sorry`, not imported by Audit.
