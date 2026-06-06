# codex fiber reply

Status: not closed.

I did not replace `hm23GammaWindowDifference_residual`, and I did not add
axioms/admit/native_decide/opaque or a renamed `sorry`.

Committed Lean milestones:

- `8a093bb proof: add HM23 gamma straddle lemma`
  - Added `hm23Gamma_eq_heaviside`.
  - Added `hm23Gamma_sub_eq_straddle`.
- `9ebb84c proof: align HM23 raw PF branch term`
  - Added `negOnePowIntQ_eq_negOnePowIntPF_cast`.
  - Added `hm23Ncoord_pf_raw_remainder`.
  - Added `hm23_thetaMulPFRawBranchTermPF_rat_eq_coord`, aligning
    `thetaMulPFRawBranchTermPF` with the `(m,p,z,r,k)` coordinate exponent
    and residual sign under `N = hm23Ncoord ...`.
- `a241652 proof: express HM23 gamma difference as cutoffs`
  - Added `hm23Gamma_sub_eq_cutoff`.
  - Added `hm23Gamma_coord_sub_eq_cutoff`, using `hm23Nonsingular` to remove
    the zero-denominator cases.

The remaining gap is the actual finite fiber telescope:

```text
sum over (r,k) with N = hm23Ncoord m p z r k
  (-1)^(z+p-m+1-k)
  * (Gamma(D1(r),k) - Gamma(D0(z+p-r+1-k),k))
= thetaMulPFRawCoeffPF N z
```

After the committed cutoff lemma this reduces to the integer core

```text
sum_{h,K} (-1)^(h-z)
  * (1_{K <= h + A} - 1_{K <= B})
  * 1_{triInt(h-z) + K*z = N}
= thetaMulPFUnifiedCoeffPF N z
```

for arbitrary integer cutoffs `A,B`.  Numerical checks over many random
`a,z0,z1,m,p,z,N` confirm this is the right telescope shape, but I did not
complete the Lean proof or the source-window bridge from
`hm23GammaWindowFourFactorSum` into that fiber sum.

Validation:

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

Result: success, with the two pre-existing `sorry` warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:5505:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:6071:8: warning: declaration uses 'sorry'
```

Source-level `#print axioms`:

```text
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
