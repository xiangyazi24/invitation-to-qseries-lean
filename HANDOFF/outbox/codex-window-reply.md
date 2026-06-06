# codex window reply

Status: not closed.

Commit:

```text
8f82d6b proof: add HM23 Gamma window bridge
```

Edited `QseriesFormalization/Pending/Chapter10_HM.lean` only for code.

Proved/added:

```lean
appellNumeratorPFBranchCoeff_eq_sum_Gamma
hm23GammaWindowFourFactorSum
lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_Gamma_window_sum
```

This closes the first two layers of the requested bridge:

1. The four-factor Appell/theta product coefficient is expanded through the
   existing convolution formula.
2. The Appell PF branch coefficient is rewritten into a finite `Gamma` window
   using `hm23_branchInvCoeffAtPF_eq_sum_Gamma`.

I also replaced the direct `sorry` in
`hm23PFBranchMapDown_coeff_residual` by a proved reduction to the smaller
finite-window theorem:

```lean
hm23GammaWindowDifference_residual
```

The remaining HM2.3 gap is now exactly the finite `Gamma` window difference:

```lean
hm23GammaWindowFourFactorSum a z1 z0 (a + z0) (a + z1) e -
hm23GammaWindowFourFactorSum a z0 z1 (a + z0) (a + z1) e -
lcoeff (Qpow z0 * JOneLaurent ^ 3 *
  jLaurent (z1 - z0) 90 * jLaurent (a + z0 + z1) 90) e = 0
```

This is still the source/coord collapse plus Phi/PF projection layer.  I did
not close the finite source-set bridge to
`Chapter10PF.thetaMulPFRawCoeffPF`.

Validation:

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passed with the two current `sorry` warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:5340:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:5906:8: warning: declaration uses 'sorry'
```

Forbidden-token grep in `Chapter10_HM.lean`:

```text
3373:def hm23Nonsingular (a z0 z1 : ℤ) : Prop :=
5349:  sorry
5909:  sorry
```

Source-pipe `#print axioms`:

```text
'QseriesFormalization.Pending.Ch10HM.hm23GammaWindowDifference_residual' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23PFBranchMapDown_coeff_residual' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
