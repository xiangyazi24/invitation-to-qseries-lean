# codex split bridge reply

Status: partial.  The split is implemented and the easy theta dissection is now
proved clean-3, but I did not honestly close HM 2.3.  The file currently has
two explicit `sorry`s: HM 2.3 cleared theta addition and the big collapse
product identity.

## Commit

- `8fe4d20 ch10: split theta bridge and prove dissection`

## Closed cleanly

- Split the old aggregate `ch10_classical_theta_bridge` into named theorems.
- Proved the cubic dissection:

```lean
thetaOneLaurent_dissection :
  thetaOneLaurent = thetaNineLaurent - 2 * Qpow 1 * jLaurent 3 18
```

The proof is coefficient-level: expand `jCoeff`, split the `n`-sum into the
three residue classes mod 3, reindex `n = 3m`, `n = 3m - 1`, and
`n = 1 - 3m`, and use the existing finite-window/root-bound lemmas.

- Proved the nonzero side condition:

```lean
E6Laurent_sq_ne_zero : E6Laurent ^ 2 ≠ 0
```

This uses `jLaurent_ne_zero_of_pos_lt 6 18`.

## Still open

```lean
hm23ClearedThetaIdentity :
  ∀ a z0 z1,
    hm23ClearedThetaLHS a z0 z1 = hm23ClearedThetaRHS a z0 z1
```

This is still a `sorry`.  I could not derive it from the current file's
foundation: `appellNumeratorLaurent` has only the coefficient definition and
coefficient simp theorem, while the file does not yet have the general
coefficient/product bridge needed to expand
`appellNumeratorLaurent * jLaurent * jLaurent * jLaurent` and match it to the
JTP product side.

The intended isolated collapse is also still a `sorry`:

```lean
theta_correction_cleared_product_identity :
  E6Laurent ^ 2 * thetaCorrectionLaurent =
    -(E3Laurent ^ 5) * jLaurent 12 15
```

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passes with exactly the two `sorry` warnings.

```text
python3 scripts/ch10_hm_verify.py
```

passes through `Q^44`, including HM 2.3 sample checks, the shifted `T_ij`
table, Chan combination, and the weighted theta-correction delta sum.

Grep:

```text
1026:def hm23Nonsingular (a z0 z1 : ℤ) : Prop :=
2006:  sorry
2035:  sorry
```

No `native_decide`, `admit`, `axiom`, or `opaque`.

## Source-level `#print axioms`

Re-elaborated the source with `#print axioms` appended, not from stale olean:

```text
'QseriesFormalization.Pending.Ch10HM.thetaOneLaurent_dissection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.E6Laurent_sq_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_cleared_product_identity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.ch10_classical_theta_bridge' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

