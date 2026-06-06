# Ch10 assemble reply

Status: partial, but the isolated `appell_cancel` `sorry` is gone.

## Commit

- `17334df ch10: prove elementary Appell cancellation`
  - Replaces the old `HMExpr` syntax-tree crux with a Laurent-ring elementary
    coefficient table.
  - Adds six raw Appell coefficients for the common bases
    `M(-39,18)`, `M(-24,18)`, `M(-9,18)`, `M(6,18)`, `M(21,18)`,
    and `M(36,18)`.
  - Proves the reductions using `J0=0`, `J15=J3`, `J12=J6`, and
    `Theta1 = J9 - 2*Q*J3`, then proves `appell_coeffs_zero` and
    parameterized `appell_cancel`.

## Important limitation

The requested design file
`docs/chatgpt-designs-2026-06-03/chan2-Ch10-APPELL-CANCEL-elementary.md`
is not present in this checkout.  I used the handoff summary plus the existing
HM table in `Chapter10_HM.lean`.

I did not prove the full `hm23ClearedThetaIdentity`.  It remains the exact
formal sublemma:

```lean
hm23ClearedThetaIdentity a z0 z1
```

expanded as:

```lean
appellNumeratorLaurent a z1 * jLaurent z0 90 *
      jLaurent (a + z0) 90 * jLaurent (a + z1) 90 -
    appellNumeratorLaurent a z0 * jLaurent z1 90 *
      jLaurent (a + z0) 90 * jLaurent (a + z1) 90 =
  Qpow z0 * JOneLaurent ^ 3 * jLaurent (z1 - z0) 90 *
    jLaurent (a + z0 + z1) 90
```

No axiom, fake theorem, or `def : Prop` proof dodge was added for this.

## Validation

```bash
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
lake build QseriesFormalization.Pending.Chapter10_HM
python3 scripts/ch10_hm_verify.py
rg -n "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|opaque" \
  QseriesFormalization/Pending/Chapter10_HM.lean
```

Results:

- Lean single-file check passed.
- Module build passed.
- Numerical verifier passed through `Q^44`.
- Grep found no `sorry`, `admit`, `native_decide`, `axiom`, or `opaque` in
  `Chapter10_HM.lean`.

## Axioms

```text
'QseriesFormalization.Pending.Ch10HM.appell_cancel' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appell_coeffs_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ChangeZIdentity_of_cleared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

