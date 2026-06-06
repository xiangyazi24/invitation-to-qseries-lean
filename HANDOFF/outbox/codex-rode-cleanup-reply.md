# codex-rode-cleanup reply

Closed the redundant `R_ODE` sorry:

- `QseriesFormalization.Pending.Ch15RODE.chan15CoreCoeff_pentagonal_identity`
- route: `Ch15RODE.chan15LHSPS_eq_apSigmaLambertFactor_rat` identifies the Chan
  Lambert side with `Ch15WronskianIndependent.apSigmaLambertFactor`; then
  `Ch15WronskianIndependent.quintupleProduct_log_derivative_identity` plus the
  AP-sigma eta-quotient equivalences gives the rational product identity;
  finally `PowerSeries.map_injective (Int.castRingHom ℚ)` descends to the
  integral coefficient identity.

Validation:

```text
lake env lean QseriesFormalization/Pending/Chapter15_R_ODE.lean
lake build QseriesFormalization.Pending.Chapter15_R_ODE
git diff --check
rg -n "sorry" QseriesFormalization/Pending/Chapter15_R_ODE.lean
```

Final `#print axioms`:

```text
'QseriesFormalization.Pending.Ch15RODE.chan15LHSPS_eq_apSigmaLambertFactor_rat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch15RODE.chan15CoreCoeff_pentagonal_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch15RODE.chan_theorem_11_7_int_core_coeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch15RODE.chan_theorem_11_7_int_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch15RODE.chan_theorem_11_7' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Referenced `WronskianIndependent` endpoints:

```text
'QseriesFormalization.Pending.Ch15WronskianIndependent.pentagonalWronskianCoeff_eq_jacobiThetaSquareCoeff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch15WronskianIndependent.wronskian_at_pentagonal_level' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch15WronskianIndependent.quintupleProduct_log_derivative_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch15WronskianIndependent.quintupleLogFactor_eq_etaQuotient_iff_apSigmaLambertFactor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch15WronskianIndependent.apSigmaLambertFactor_eq_etaQuotient_iff_mul_expandFive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

No `native_decide` is used in the new all-`N` closure path.
