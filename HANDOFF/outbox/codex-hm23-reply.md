# codex-hm23 reply

Edited only `QseriesFormalization/Pending/Chapter10_HM.lean`.

## Status

- Replaced the top-level `hm23ClearedThetaIdentity` `sorry` with a PF-route scaffold.
- Added `hm23PartialFractionExpansionPF` as the single new HM2.3 analytic blocker.
- Proved the residue-cancellation coefficient algebra from PF:
  `hm23ResidueCancellationCoefficientAlgebra`.
- Proved the cleared identity from the coefficient algebra:
  `hm23ClearedThetaIdentity_of_residueCancellationCoefficientAlgebra`.
- Left the proved `jLaurent_eq_tripleProductInf` untouched.
- Left `theta_correction_cleared_product_identity` untouched.

## Remaining Blocker

`hm23PartialFractionExpansionPF` is still `sorry`.  It is the localized PF/PF'
specialization for `x=Q^a`, `z_i=Q^z_i`, `q=Q^90`, using the valuation-compatible
inverse branches already encoded by `geomInvCoeff`.

Once this theorem is proved, `hm23ClearedThetaIdentity` has no direct `sorry`.

## Verification

Command:

```bash
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

Output:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:2797:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:2870:8: warning: declaration uses 'sorry'
```

These are `hm23PartialFractionExpansionPF` and the pre-existing
`theta_correction_cleared_product_identity`.

Forbidden-token check on the edited Lean file:

```text
1817:def hm23Nonsingular (a z0 z1 : ℤ) : Prop :=
2803:  sorry
2873:  sorry
```

The `def : Prop` hit is pre-existing; no new `native_decide`, `axiom`,
`admit`, or `opaque` was introduced.

## #print axioms

```text
'QseriesFormalization.Pending.Ch10HM.hm23PartialFractionExpansionPF' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ResidueCancellationCoefficientAlgebra' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity_of_residueCancellationCoefficientAlgebra' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ChangeZIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_cleared_product_identity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
