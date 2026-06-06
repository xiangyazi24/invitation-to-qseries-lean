# codex-pfasm reply

Read `HANDOFF/inbox/codex-pfasm.md`.

## Result

Closed the PF assembly in `QseriesFormalization/Pending/Chapter10_PF.lean`.

New main theorems:

```lean
theorem thetaMulPFUnifiedCoeffPF_nonconstant_vanish
    (N : ℕ) {z : ℤ} (hz : z ≠ 0) :
    thetaMulPFUnifiedCoeffPF N z = 0

theorem thetaMulPFCoeffPF_eq_jacobiCubeCoeffPF_ite (N : ℕ) (z : ℤ) :
    thetaMulPFCoeffPF N z = if z = 0 then jacobiCubeCoeffPF N else 0

theorem thetaMul_PF_eq_jacobiCube :
    thetaMulPFSeriesCoeffPF = jacobiCubeUPowerCoeffPF
```

The final theorem is the cleared HM (1.3) coefficient-family statement:
the `u^0` coefficient is the Jacobi-cube `q`-series, and every nonzero
`u^z` coefficient vanishes.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_PF.lean
```

passed with no output.

Forbidden-token grep on `Chapter10_PF.lean` found no matches for
`native_decide`, `axiom`, `admit`, `opaque`, `sorry`, or `def .*: Prop`.

## Axioms

```text
'QseriesFormalization.Pending.Chapter10PF.thetaMul_PF_eq_jacobiCube' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.thetaMulPFCoeffPF_eq_jacobiCubeCoeffPF_ite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.thetaMulPFCoeffPF_nonconstant_vanish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
