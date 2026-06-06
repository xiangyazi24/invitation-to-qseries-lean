# codex-pfbridge reply

Read `HANDOFF/inbox/codex-pfbridge.md`.

## Result

Edited only `QseriesFormalization/Pending/Chapter10_PF.lean` for code.

Closed the PF-to-real-series bridge:

```lean
theorem jCoeffPF_eq_jacobiThetaCoeffPF (N : ℕ) (r : ℤ) :
    jCoeffPF N r = jacobiThetaCoeffPF N r

theorem branchInvCoeffPF_eq_branchInvCoeffAtPF (k m : ℤ) :
    branchInvCoeffPF k m = branchInvCoeffAtPF k (k * m) m

theorem jacobiCubeCoeffPF_eq_jacobiTripleSign (N : ℕ) :
    jacobiCubeCoeffPF N = QseriesFormalization.PartIV.Ch19.jacobiTripleSign N

theorem jacobiCubeSeriesPF_eq_qPochInfPS_pow_three :
    jacobiCubeSeriesPF = (QseriesFormalization.PartIV.Ch19.qPochInfPS ℤ) ^ 3

theorem thetaMul_PF_eq_qPochInfPS_pow_three :
    thetaMulPFSeriesCoeffPF = qPochInfPSCubeUPowerCoeffPF
```

The final theorem is the upgraded coefficient-family series identity:
`j(u;q) * PF(u;q)` has `u^0` coefficient `(qPochInfPS ℤ)^3` and all
nonzero `u`-coefficients vanish.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_PF.lean
```

passed with no output.

Forbidden-token grep on `Chapter10_PF.lean` found no matches for
`native_decide`, `axiom`, `admit`, `opaque`, `sorry`, or `def .*: Prop`.

## Axioms

```text
'QseriesFormalization.Pending.Chapter10PF.jCoeffPF_eq_jacobiThetaCoeffPF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.branchInvCoeffPF_eq_branchInvCoeffAtPF' depends on axioms: [propext,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.jacobiCubeSeriesPF_eq_qPochInfPS_pow_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.thetaMul_PF_eq_qPochInfPS_pow_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
