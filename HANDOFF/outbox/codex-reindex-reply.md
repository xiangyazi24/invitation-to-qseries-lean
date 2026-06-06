# codex reindex reply

Status: not closed.

I executed the blueprint as far as the mechanically isolated algebra and RHS
scaling bridges.  The remaining open point is still the actual finite-Icc
fivefold summation reindex from the two HM product expansions into
`Chapter10PF.thetaMulPFRawCoeffPF`.

## Commits

- `9c43800 docs: add HM23 reindex algebra lemmas`
- `0ac8234 docs: align HM23 residual coordinates`
- `23a3906 docs: add HM23 JOne scaling bridge`

## Added in `QseriesFormalization/Pending/Chapter10_HM.lean`

- `hmTri`, `two_mul_hmTri`
- Term-1 Psi algebra:
  `hm23Psi1_m`, `hm23Psi1_p`, `hm23Psi1_z`, `hm23Psi1_N`,
  inverse lemmas, exponent identity, sign identity.
- Term-2 Psi algebra:
  `hm23Psi0_m`, `hm23Psi0_p`, `hm23Psi0_z`, `hm23Psi0_r`,
  `hm23Psi0_N`, inverse lemmas, exponent identity, sign identity.
- Phi algebra:
  `hm23Phi_quadratic_preservation`,
  `hm23Phi_parity_preservation`.
- Shared `(m,p,z,r,k)` coordinate bridge:
  `hm23Ncoord`,
  `hm23Psi1_N_eq_Ncoord`,
  `hm23Psi0_N_eq_Ncoord`,
  residual-sign coordinate lemmas,
  `hm23Psi0_D_coord`.
- RHS scaling:
  `hm23_continuous_expand`,
  `hm23_expand_qPochInfPS_eq_qPochAPPS_rat`,
  `JOneLaurent_eq_expand_qPochInfPS`,
  `lcoeff_JOneLaurent_pow_three_mul90`.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passes with the two existing warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:4891:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:5390:8: warning: declaration uses 'sorry'
```

## #print axioms

Source-pipe check, avoiding stale `.olean`:

```text
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23PFBranchMapDown_coeff_residual' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.lcoeff_JOneLaurent_pow_three_mul90' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The target theorem `hm23PFBranchMapDown_coeff_residual` is therefore not
closed yet.
