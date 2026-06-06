# codex-step2 reply

Status: not closed.  I did not edit `QseriesFormalization/Pending/Chapter10_HM.lean`; replacing the target by a new level-90 `sorry` would be rename-and-sorry rather than a proof.

## What I checked

I reconstructed the denominator-cleared residual numerically from `scripts/ch10_hm_verify.py`, then applied the committed bridges:

- `J_3_18_bridge`
- `J_6_18_bridge`
- `J_9_18_bridge`
- `J_3_9_pow5_J_3_15_bridge`

with `K = jLaurent 90 270`.

After `thetaOneLaurent_dissection`, normalization by `jLaurent_shift`/`jLaurent_symm`, denominator clearing, and bridge replacement, the common factor of the 31-term residual is:

```text
Q^-1030 *
J3^3 * J6^10 * J9^8 * J12^11 * J15^2 *
J18^42 * J21^4 * J24^14 * J27^4 * J30^7 *
J33^2 * J36^11 * J39^7 * J42^8 * J45
```

where `Ja = jLaurent a 90`.

The remaining core splits by explicit `K` degree:

```text
- Q^4 *
  J3^6 J6^3 J9^4 J12^5 J15^6 J18^3 J21^6 J24^4
  J27^5 J30^5 J33^6 J36 J39^6 J42^5 J45^2
+ K^48 * P30 = 0
```

`P30` is the 30-term correction polynomial produced by the bridge rewrite.  The key obstruction is that the single RHS term is in explicit `K^0`, while every correction term is in explicit `K^48`.

Explicitly:

```text
P30 =
- J6 J9^2 J15 J18 J21^3 J24 J27^3 J30 J33 J36 J39^2 J42 J45
+ J9^4 J18 J21 J24 J27^6 J30^2 J36 J42 J45^2
- 4 Q J3 J9^2 J15 J18 J21^2 J24 J27^4 J30^2 J33 J36 J39 J42 J45
- 2 Q J9^3 J12^2 J18 J21 J24 J27^3 J30^3 J36 J39 J42^2 J45
+ Q J9^3 J12 J15 J21^3 J24 J27^3 J30 J33 J36^2 J39 J42 J45
+ Q J9^3 J12^2 J21 J24^3 J27^3 J30^2 J36^2 J39 J42 J45
+ 4 Q J3 J6 J15^2 J18 J21^4 J24 J27 J30 J33^2 J36 J39^3 J42
- Q^3 J9^5 J12 J18 J27^4 J30 J36 J39 J42^2 J45^3
+ Q^3 J9^3 J12^2 J18 J21 J24^3 J27^3 J30 J39 J42^3 J45
- Q^4 J9^3 J12 J15^2 J18 J21^2 J27^3 J30 J33 J36 J39 J42^2 J45
- Q^4 J3 J9^3 J15 J18 J21 J24 J27^3 J30^2 J33^2 J36 J39 J42 J45
- Q^4 J3 J9^3 J12 J15 J21 J24 J27^3 J30 J36^2 J39^3 J42 J45
+ 4 Q^4 J3 J9^3 J12 J15 J18 J21 J27^2 J30 J33 J36 J39^2 J42^2 J45^2
- Q^6 J3 J9^2 J12 J15 J18 J21^2 J24 J27^3 J30^2 J33^2 J36 J39 J45
- Q^6 J3 J9^2 J12 J15 J18 J21^3 J24 J27^3 J33 J36 J39 J42^2 J45
+ Q^6 J3 J6 J9^2 J12 J18 J21^2 J27^3 J30 J33^2 J36 J39^2 J42 J45
- 4 Q^7 J3^2 J6 J12 J15 J18 J21^3 J27 J30 J33^3 J36 J39^3 J42
- Q^7 J6^2 J9^3 J18 J21 J24^2 J27^3 J30^2 J36 J39 J42^2 J45
+ Q^7 J6^2 J9^3 J12 J21 J24 J27^3 J30^2 J36^2 J39 J42^2 J45
+ 4 Q^7 J3^2 J9 J12 J15^2 J21^3 J24 J30 J33^2 J36^2 J39^3 J42
+ Q^9 J9^3 J12^3 J18 J21 J24^2 J27^3 J30^3 J39 J42 J45
- Q^12 J9^5 J12^2 J18 J24 J27^5 J36 J39 J42 J45^2
- Q^13 J3 J6 J9^3 J15 J18 J21^2 J24 J27^3 J30 J36 J39^2 J42 J45
+ Q^13 J6^2 J9^3 J12^2 J18 J21 J27^3 J30 J36 J39 J42^3 J45
- Q^15 J6^2 J9^3 J12 J18 J21 J24^3 J27^3 J30^2 J39 J42 J45
+ 4 Q^16 J3 J6^2 J9 J12 J15 J18 J21^2 J24^3 J27 J30^2 J33 J39^2 J42
- Q^18 J9^6 J12 J18 J21 J24^2 J27^4 J30 J36 J45^2
+ Q^19 J3^2 J6 J9^3 J12 J18 J21 J27^3 J30 J33 J36 J39^2 J42 J45
- Q^21 J6^2 J9^3 J12^3 J18 J21 J24 J27^3 J30 J39 J42^2 J45
+ 4 Q^22 J3 J6^2 J9 J12^3 J15 J18 J21^2 J24 J27 J30 J33 J39^2 J42^2
```

## Riemann search

I searched Riemann-at-90 relations after the bridge rewrite.  Local hits exist inside the `K^48` correction component.  One example:

```text
(A,B,C,D) = (30,18,-9,-12)

J9 J18 J27 J42
  = J6 J21 J30 J39 + Q^6 J3 J12 J21 J42
```

The search found local two-term matches in the `K^48` component, but none can touch the unique `K^0` term.  This is structural: `jLaurent_riemann (M=90)` rewrites only products of `jLaurent _ 90`; multiplying such a relation by any monomial preserves the explicit power of `K = jLaurent 90 270`.  Therefore a finite sequence of `jLaurent_riemann (M=90)` rewrites plus `ring_nf` cannot cancel a `K^0` monomial against `K^48` monomials unless an additional bridge/extraction identity relates explicit powers of `K` to level-90 theta products.

Exact Riemann sequence used in Lean:

```text
none
```

Smallest honest remaining gap I can isolate is the K-split level-90 identity above:

```text
Q^4 *
  J3^6 J6^3 J9^4 J12^5 J15^6 J18^3 J21^6 J24^4
  J27^5 J30^5 J33^6 J36 J39^6 J42^5 J45^2
=
K^48 * P30
```

Closing this needs either:

- a K-extraction/refinement layer, e.g. rewriting `Ja = K * P_a * P_{90-a}` and proving the resulting AP/additive identity, or
- a Riemann theory formulated for the normalized ratios with the common `K` factor divided out.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passed with the two existing warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:4225:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:4353:8: warning: declaration uses 'sorry'
```

```text
python3 scripts/ch10_hm_verify.py
```

passed, including HM Def. 0.1 samples, HM 2.3 samples, all nine shifted `T_ij` rows, Chan combination through `Q^44`, and the weighted Delta-sum theta correction through `Q^44`.

## Axioms

```text
'QseriesFormalization.Pending.Ch10HM.theta_correction_denominator_cleared_residual' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_riemann' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.J_3_18_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.J_6_18_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.J_9_18_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.J_3_9_pow5_J_3_15_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_90_270_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
```
