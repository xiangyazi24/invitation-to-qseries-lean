# codex-linsolve reply

Verdict: `NOT_IN_SPAN`.

I did not close `theta_correction_denominator_cleared_residual`.  The remaining
`sorry` is the same theorem, now annotated as the honest residual gap.

## Linear-algebra check

I modeled each term as a basis vector

```text
(coefficient) * Q^q * K^k * Π J_a^e_a
```

with `K = jLaurent 90 270`, `J_a = jLaurent a 90`, and atom order

```text
J3,J6,J9,J12,J15,J18,J21,J24,J27,J30,J33,J36,J39,J42,J45
```

The reduced residual is exactly the level-90 identity from `codex-step2`:

```text
Q^4 *
  J3^6 J6^3 J9^4 J12^5 J15^6 J18^3 J21^6 J24^4
  J27^5 J30^5 J33^6 J36 J39^6 J42^5 J45^2
=
K^48 * P30
```

The exact `P30` term table is:

```text
(-1,  0, [0,1,2,0,1,1,3,1,3,1,1,1,2,1,1])
( 1,  0, [0,0,4,0,0,1,1,1,6,2,0,1,0,1,2])
(-4,  1, [1,0,2,0,1,1,2,1,4,2,1,1,1,1,1])
(-2,  1, [0,0,3,2,0,1,1,1,3,3,0,1,1,2,1])
( 1,  1, [0,0,3,1,1,0,3,1,3,1,1,2,1,1,1])
( 1,  1, [0,0,3,2,0,0,1,3,3,2,0,2,1,1,1])
( 4,  1, [1,1,0,0,2,1,4,1,1,1,2,1,3,1,0])
(-1,  3, [0,0,5,1,0,1,0,0,4,1,0,1,1,2,3])
( 1,  3, [0,0,3,2,0,1,1,3,3,1,0,0,1,3,1])
(-1,  4, [0,0,3,1,2,1,2,0,3,1,1,1,1,2,1])
(-1,  4, [1,0,3,0,1,1,1,1,3,2,2,1,1,1,1])
(-1,  4, [1,0,3,1,1,0,1,1,3,1,0,2,3,1,1])
( 4,  4, [1,0,3,1,1,1,1,0,2,1,1,1,2,2,2])
(-1,  6, [1,0,2,1,1,1,2,1,3,2,2,1,1,0,1])
(-1,  6, [1,0,2,1,1,1,3,1,3,0,1,1,1,2,1])
( 1,  6, [1,1,2,1,0,1,2,0,3,1,2,1,2,1,1])
(-4,  7, [2,1,0,1,1,1,3,0,1,1,3,1,3,1,0])
(-1,  7, [0,2,3,0,0,1,1,2,3,2,0,1,1,2,1])
( 1,  7, [0,2,3,1,0,0,1,1,3,2,0,2,1,2,1])
( 4,  7, [2,0,1,1,2,0,3,1,0,1,2,2,3,1,0])
( 1,  9, [0,0,3,3,0,1,1,2,3,3,0,0,1,1,1])
(-1, 12, [0,0,5,2,0,1,0,1,5,0,0,1,1,1,2])
(-1, 13, [1,1,3,0,1,1,2,1,3,1,0,1,2,1,1])
( 1, 13, [0,2,3,2,0,1,1,0,3,1,0,1,1,3,1])
(-1, 15, [0,2,3,1,0,1,1,3,3,2,0,0,1,1,1])
( 4, 16, [1,2,1,1,1,1,2,3,1,2,1,0,2,1,0])
(-1, 18, [0,0,6,1,0,1,1,2,4,1,0,1,0,0,2])
( 1, 19, [2,1,3,1,0,1,1,0,3,1,1,1,2,1,1])
(-1, 21, [0,2,3,3,0,1,1,1,3,1,0,0,1,2,1])
( 4, 22, [1,2,1,3,1,1,2,1,1,1,1,0,2,2,0])
```

Enumeration over the residue grid `A,B,C,D ∈ {0,3,...,87}` gave:

```text
residual terms: 31
K-degree distribution: {0: 1, 48: 30}
enumerated instances: 810000
zero canonical instances: 277104
unique nonzero relation vectors: 38704
all relation terms have K-degree zero: True
```

The exact obstruction is the `K`-graded block split.  Riemann-90 relations do
not mention `K`; multiplying a relation by any monomial preserves the explicit
`K` degree.  Therefore a Riemann-only linear combination decomposes by explicit
`K` degree.

After projecting to explicit `K^0`, the residual is the single nonzero term

```text
- Q^4 *
  J3^6 J6^3 J9^4 J12^5 J15^6 J18^3 J21^6 J24^4
  J27^5 J30^5 J33^6 J36 J39^6 J42^5 J45^2
```

Taking the leading `Q^4` coefficient after evaluating the level-90 theta
atoms gives a dual row of the linear system: every Riemann column maps to `0`,
while the residual maps to `-1`.  Gaussian elimination therefore contains the
inconsistent row

```text
0 = -1
```

So the residual is not in the Riemann-90 span.  A closure proof needs another
product/refinement identity relating the explicit `K^48` block to the `K^0`
block; Riemann alone cannot supply it.

## Lean edits

Edited only:

```text
QseriesFormalization/Pending/Chapter10_HM.lean
```

The edit is a comment on the existing residual theorem explaining the
not-in-span verdict.  I did not touch the bridges, `jLaurent_riemann`,
`jLaurent_eq_tripleProductInf`, or the HM 2.3 PF `sorry`.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passed with the two existing warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:4225:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:4361:8: warning: declaration uses 'sorry'
```

Forbidden-token grep after the edit:

```text
3245:def hm23Nonsingular (a z0 z1 : ℤ) : Prop :=
4231:  sorry
4364:  sorry
```

The `def ... : Prop` and both `sorry`s are pre-existing; I did not add a new
one.

## Axioms

```text
'QseriesFormalization.Pending.Ch10HM.theta_correction_denominator_cleared_residual' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_cleared_product_identity' depends on axioms: [propext,
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
'QseriesFormalization.Pending.Ch10HM.hm23PartialFractionExpansionPF' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
