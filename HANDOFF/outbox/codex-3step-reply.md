# codex 3step reply

Status: not closed.

I did not prove the requested exact three lemmas
`hm23Term1_transport`, `hm23Term2_transport`, and
`hm23Difference_assembly` in the requested `lcoeff` form.  I avoided naming a
weaker theorem with those final names.

Committed support work:

```text
ad69a79 proof: add HM23 transport cores
```

Added in `QseriesFormalization/Pending/Chapter10_HM.lean`:

```lean
hm23Gamma
hm23Gamma_eq
hm23_branchInvCoeffAtPF_eq_sum_Gamma

HM23Psi1Source
HM23Psi0Source
HM23Coord

hm23Psi1Coord
hm23Psi1SourceOfCoord
hm23Psi1SourceOfCoord_left_inv
hm23Psi0Coord
hm23Psi0SourceOfCoord
hm23Psi0SourceOfCoord_left_inv

hm23TermOutExp
hm23Term1SourceExp
hm23Term2SourceExp
hm23Term1SourceSummand
hm23Term2SourceSummand
hm23Term1CoordSummand
hm23Term2CoordSummand

hm23Term1_transport_core
hm23Term2_transport_core
```

The two `_core` lemmas are the actual one-`Finset.sum_bij'` Psi transports on
finite source sets.  They use the existing exponent/sign/Ncoord algebra and
prove the pointwise source-to-`(m,p,z,N,r,k)` summand transport.  They do not
yet connect the concrete
`lcoeff_appellNumeratorLaurent_mul_three_jLaurent_90_eq_window_sum` nested
windows to those finite source sets.

The remaining exact blocker is the missing support/window bridge:

1. Expand the four-factor `lcoeff` product.
2. Rewrite the Appell branch via `hm23_branchInvCoeffAtPF_eq_sum_Gamma`.
3. Collapse the `E,E1,E2` convolution windows to a finite source set over
   `(r,k,i,j,l)` / `(s,k,h,j,l)`, with zero outside the support.
4. Apply the committed `_core` transport.
5. Only then can the Phi difference assembly and `hPF` projection be applied.

Validation:

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

Result: typechecks, with the two pre-existing warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:5265:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:5764:8: warning: declaration uses 'sorry'
```

Forbidden-token grep:

```text
5280:  sorry
5767:  sorry
```

`#print axioms` from a source-pipe check:

```text
'QseriesFormalization.Pending.Ch10HM.hm23_branchInvCoeffAtPF_eq_sum_Gamma' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23Term1_transport_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23Term2_transport_core' depends on axioms: [propext,
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
