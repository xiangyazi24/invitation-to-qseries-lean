# codex sumbij reply

Status: not closed.

I did not replace `hm23PFBranchMapDown_coeff_residual` with a renamed sorry.
The remaining gap is still the finite-Icc fivefold reindex from the expanded
HM numerator/theta product windows to the PF raw coefficient family.

What I added in `QseriesFormalization/Pending/Chapter10_HM.lean`:

- `coeff_qPochInfPS_pow_three_rat_eq_intCast`
- `lcoeff_JOneLaurent_pow_three_of_not_dvd`
- `hm23_thetaMulPFRawCoeffPF_rat_eq_JOneCoeff_of_hPF`

These close the RHS/PF projection side: `hPF` now gives the raw PF coefficient
as a rational coefficient of `JOneLaurent^3` at `u=0`, and zero for `u≠0`.
They do not yet perform the HM-side fivefold finite-window transport.

Validation:

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

Result: typechecks, with the two pre-existing sorry warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:4953:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:5452:8: warning: declaration uses 'sorry'
```

`#print axioms`:

```text
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

Exact remaining blocker:

Formalize the finite sum transport:

1. Expand both four-factor HM product coefficients with
   `lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_window_sum`.
2. Rewrite numerator coefficients using `hnum0`/`hnum1`.
3. Apply `Finset.sum_bij`/`sum_nbij` for `hm23Psi1_*` and `hm23Psi0_*`,
   carrying the finite Icc window bounds or enlarging to a common finite
   support box.
4. Use `hm23Phi_*`, `hm23Ncoord`, and the residual sign lemmas pointwise.
5. Identify the resulting inner finite sum with
   `Chapter10PF.thetaMulPFRawCoeffPF N z`, then apply
   `hm23_thetaMulPFRawCoeffPF_rat_eq_JOneCoeff_of_hPF`.

The hard missing Lean object is step 5's exact equality between the transported
HM-side finite support and `thetaMulPFRawCoeffPF`; no existing lemma in
`Chapter10_HM.lean` or `Chapter10_PF.lean` currently states it.
