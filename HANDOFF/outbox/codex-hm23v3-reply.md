# codex hm23 v3 reply

Status: partial, with one precisely isolated `sorry`.

## Commit

- `c564efd ch10: isolate HM theta bridge`

## What changed

Edited only `QseriesFormalization/Pending/Chapter10_HM.lean`.

- Replaced the old `def hm23ClearedThetaIdentity ... : Prop` surface with:
  - `hm23ClearedThetaLHS : QLaurent`
  - `hm23ClearedThetaRHS : QLaurent`
  - `theorem hm23ClearedThetaIdentity (a z0 z1) :
      hm23ClearedThetaLHS a z0 z1 = hm23ClearedThetaRHS a z0 z1`
- Replaced the old `def hm23ChangeZIdentity ... : Prop` surface with:
  - `theorem hm23ChangeZIdentity_of_cleared`, still pure algebra and no `sorryAx`.
  - `theorem hm23ChangeZIdentity (a z0 z1) (hreg : hm23Nonsingular a z0 z1)`.
- Connected `appell_cancel` to real `jLaurent` factors via:
  - `thetaOneLaurent_dissection`
  - `jLaurent_0_18_eq_zero`
  - `jLaurent_15_18_eq_3_18`
  - `jLaurent_12_18_eq_6_18`
  - `appell_cancel_jLaurent`

## Single remaining bridge

The only `sorry` is concentrated in:

```lean
theorem ch10_classical_theta_bridge :
    (∀ a z0 z1 : ℤ,
        hm23ClearedThetaLHS a z0 z1 = hm23ClearedThetaRHS a z0 z1) ∧
      thetaOneLaurent = thetaNineLaurent - 2 * Qpow 1 * jLaurent 3 18 ∧
        (E6Laurent ^ 2 ≠ 0 ∧
          E6Laurent ^ 2 * thetaCorrectionLaurent =
            -(E3Laurent ^ 5) * jLaurent 12 15)
```

This isolates the missing analytic-to-formal/JTP stabilization content:
HM 2.3 cleared theta addition, the `j(Q;Q²)` cubic dissection, and the
already-existing theta-correction product collapse.  The previous standalone
`theta_correction_cleared_product_identity` `sorry` now derives from this one
bridge, so the file has exactly one `sorry`.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passed with the single warning:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:1495:8: warning: declaration uses 'sorry'
```

```text
lake build QseriesFormalization.Pending.Chapter10_HM
```

passed with the same single warning.

```text
python3 scripts/ch10_hm_verify.py
```

passed.  HM 2.3 samples, the shifted `T_ij` table, Chan combination, and the
weighted theta-correction delta sum all checked through `Q^44`.

Grep:

```text
1026:def hm23Nonsingular (a z0 z1 : ℤ) : Prop :=
1507:  sorry
```

No `native_decide`, `admit`, `axiom`, or `opaque`.  The only remaining
`def : Prop` is the nonsingularity condition, not a theorem surrogate.

## Axioms

```text
'QseriesFormalization.Pending.Ch10HM.ch10_classical_theta_bridge' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ChangeZIdentity_of_cleared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ChangeZIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.thetaOneLaurent_dissection' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_cleared_product_identity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appell_cancel' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_0_18_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_15_18_eq_3_18' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_12_18_eq_6_18' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appell_cancel_jLaurent' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
