# codex-normalize reply

Status: partial, with the `K` obstruction removed formally.

Edited source file only:

```text
QseriesFormalization/Pending/Chapter10_HM.lean
```

## Lean changes

Added the normalized level-90 atom:

```lean
noncomputable def redJ (a : ℕ) : QLaurent :=
  qPochAPLaurent a 90 * qPochAPLaurent (90 - a) 90
```

Proved both requested bridges:

```lean
theorem redJ_eq_qPochAPLaurent (a : ℕ) :
    redJ a = qPochAPLaurent a 90 * qPochAPLaurent (90 - a) 90

theorem jLaurent_eq_JOne_mul_redJ (a : ℕ) (ha0 : 0 < a) (ha90 : a < 90) :
    jLaurent (a : ℤ) 90 = jLaurent 90 270 * redJ a
```

Recorded the normalized LHS product and the normalized `P30` table as
`thetaCorrectionNormalizedLHSRedJ` and
`thetaCorrectionNormalizedP30Rows`.

Added degree lemmas:

```lean
thetaCorrectionNormalizedLHSRedJ_totalDegree
thetaCorrectionNormalizedP30_term01_totalDegree
...
thetaCorrectionNormalizedP30_term30_totalDegree
```

So the K-degree bookkeeping is now explicit in Lean:

```text
LHS: 67
RHS: 48 + 19 = 67 for every P30 row
```

I did not touch the proved bridges, `jLaurent_riemann`,
`jLaurent_eq_tripleProductInf`, or
`appellNumeratorLaurent_PF_changeOfZ_coeff_mapDown`.

## Normalized Span Verdict

The old `K^0`/`K^48` obstruction is gone after `J_a = K * redJ a`.

I did not find a normalized Riemann certificate.  Search results:

```text
unique normalized M=90 Riemann base relations: 1394
anchored Macaulay system: 32862 columns, 29981 rows, rank 16358 mod 1000003
anchored target remainder: nonzero, 58 rows

bounded reachable closure [-10,40]: 150032 rows, 222160 cols, rank 100731, remainder 56
bounded reachable closure [-20,60]: 150114 rows, 218344 cols, rank 99562, remainder 54
bounded reachable closure [-40,80]: 150313 rows, 218158 cols, rank 99570, remainder 54
```

This is not a full mathematical non-span proof for the entire Riemann ideal;
it is a precise “certificate not found” verdict for the tested normalized
Macaulay systems.  The residual remains the single honest `sorry`.

As a consistency check, the normalized AP-product identity evaluates to zero
through `Q^300`.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passed with exactly the two expected `sorry` warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:4295:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:4634:8: warning: declaration uses 'sorry'
```

```text
python3 scripts/ch10_hm_verify.py
```

passed all HM Def. 0.1, HM 2.3, shifted `T_ij`, Chan combination, and
theta-correction checks through `Q^44`.

Forbidden-token grep reports only the pre-existing Prop definition and the two
honest `sorry`s:

```text
3314:def hm23Nonsingular (a z0 z1 : ℤ) : Prop :=
4306:  sorry
4637:  sorry
```

## Axioms

```text
'QseriesFormalization.Pending.Ch10HM.jLaurent_eq_JOne_mul_redJ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.thetaCorrectionNormalizedLHSRedJ_totalDegree' depends on axioms: [propext]
'QseriesFormalization.Pending.Ch10HM.thetaCorrectionNormalizedP30_term30_totalDegree' depends on axioms: [propext]
'QseriesFormalization.Pending.Ch10HM.theta_correction_denominator_cleared_residual' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_cleared_product_identity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_riemann' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23PartialFractionExpansionPF' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
