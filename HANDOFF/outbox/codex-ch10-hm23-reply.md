# Ch10 HM 2.3 reply

Status: partial.  I did not close `hm23ChangeZIdentity` as the requested real
theorem.  The existing `hm23ChangeZIdentity` is still the old `def : Prop`.

## Commits

- `a55ec36 ch10: add Chan HM Laurent combination`
  - Adds actual Laurent definitions for `thetaOneLaurent`, `thetaNineLaurent`,
    `TijLaurent`, `H00Laurent`, `H10Laurent`, `H01Laurent`, `H11Laurent`, and
    `chan1015HCombinationLaurent`.
  - Adds clean unfold/symmetric-combination lemmas.
- `9decc7c ch10: add HM change-of-z cleared bridge`
  - Adds `hm23Nonsingular`.
  - Adds cleared denominator target `hm23ClearedThetaIdentity`.
  - Proves the clean algebra bridge
    `hm23ChangeZIdentity_of_cleared`:
    nonzero denominators plus the cleared theta-addition identity imply the HM
    Theorem 2.3 theta quotient formula.

## Numeric verification

Command:

```bash
python3 scripts/ch10_hm_verify.py
```

Result: all existing checks pass, including HM Theorem 2.3 nonsingular samples
through `Q^44`:

```text
a=+36, z0=+12, z1=+18: OK
a=+21, z0=-12, z1=+18: OK
a=-9, z0=+18, z1=-18: OK
a=+6, z0=-24, z1=+24: OK
a=+36, z0=-30, z1=+30: OK
Chan combination vs -E3^5*E6^-2*j(12,15) through Q^44: OK
```

I also checked a totalized Python model matching the current Lean convention
that singular inverses are zero.  The no-hypothesis formula fails at singular
parameters; first failures found:

```text
(-36, -6, 0): coeff Q^42 differs, lhs=1 rhs=0
(-36, 0, 6): coeff Q^36 differs, lhs=1 rhs=0
```

No failures were found among the sampled non-singular triples.  This matters
because the current Lean `LaurentSeries` field inverse is total (`0⁻¹=0`), while
HM's analytic statement excludes the poles of `m(x,q,z)`.

## Lean validation

Commands:

```bash
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
lake build QseriesFormalization.Pending.Chapter10_HM
rg -n "native_decide|\bsorry\b|\badmit\b|^\s*axiom\b|opaque|def .*: Prop" \
  QseriesFormalization/Pending/Chapter10_HM.lean scripts/ch10_hm_verify.py
```

Lean succeeds, with the existing isolated `appell_cancel` warning:

```text
warning: QseriesFormalization/Pending/Chapter10_HM.lean:793:8: declaration uses 'sorry'
Build completed successfully.
```

The grep result is:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:363:def hm23Nonsingular (a z0 z1 : ℤ) : Prop :=
QseriesFormalization/Pending/Chapter10_HM.lean:371:def hm23ClearedThetaIdentity (a z0 z1 : ℤ) : Prop :=
QseriesFormalization/Pending/Chapter10_HM.lean:397:def hm23ChangeZIdentity (a z0 z1 : ℤ) : Prop :=
QseriesFormalization/Pending/Chapter10_HM.lean:791:not imported by `Audit.lean`.  It is the only `sorry` in this file.
QseriesFormalization/Pending/Chapter10_HM.lean:794:  sorry
```

So the requested `hm23ChangeZIdentity` conversion is not done.

## Axioms

After refreshing the module olean:

```text
'QseriesFormalization.Pending.Ch10HM.appellM_eq_hmDef01' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ChangeZIdentity_of_cleared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.H00Laurent_unfold' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.chan1015HCombinationLaurent_symmetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ThetaQuotient' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ChangeZIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appell_cancel' depends on axioms: [sorryAx]
```

`appell_cancel` remains the one isolated `sorryAx` and is not imported by
`Audit.lean`.

## Remaining exact target

The new clean bridge reduces HM 2.3 to:

```lean
hm23ClearedThetaIdentity a z0 z1
```

with four nonzero theta denominator hypotheses.  Expanding that definition:

```lean
appellNumeratorLaurent a z1 * jLaurent z0 90 *
      jLaurent (a + z0) 90 * jLaurent (a + z1) 90 -
    appellNumeratorLaurent a z0 * jLaurent z1 90 *
      jLaurent (a + z0) 90 * jLaurent (a + z1) 90 =
  Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
    jLaurent (a + z0 + z1) 90
```

This is the pure Jacobi theta-addition identity still needing proof.
