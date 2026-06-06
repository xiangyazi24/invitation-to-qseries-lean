# codex-mapdown reply

I did not close `appellNumeratorLaurent_PF_changeOfZ_coeff_mapDown`.

The current all-integer statement is false at singular parameters.  A concrete
counterexample is `(a,z0,z1) = (0,0,1)`.  In that case the left cleared product
has a `jLaurent 0 90` factor, while the right product is
`JOneLaurent^3 * jLaurent 1 90 * jLaurent 1 90`, whose factors are nonzero.

Lean check used:

```lean
example :
    (((appellNumeratorLaurent 0 1 * jLaurent 0 90 -
              appellNumeratorLaurent 0 0 * jLaurent 1 90) *
            jLaurent (0 + 0) 90 * jLaurent (0 + 1) 90) -
          Qpow 0 * JOneLaurent ^ 3 * jLaurent (1 - 0) 90 *
            jLaurent (0 + 0 + 1) 90) ≠ 0 := by
  simp only [zero_add, sub_zero]
  rw [jLaurent_zero 90 (by norm_num)]
  simp only [mul_zero, zero_mul, Qpow_zero, one_mul]
  rw [zero_sub]
  apply neg_ne_zero.mpr
  refine mul_ne_zero (mul_ne_zero ?hJ3 ?hj1a) ?hj1b
  · exact pow_ne_zero 3 (by
      unfold JOneLaurent
      exact jLaurent_ne_zero_of_pos_lt 90 270 (by norm_num) (by norm_num))
  · exact jLaurent_ne_zero_of_pos_lt 1 90 (by norm_num) (by norm_num)
  · exact jLaurent_ne_zero_of_pos_lt 1 90 (by norm_num) (by norm_num)
```

This means the coefficientwise theorem cannot be proved as stated.  The next
honest fix is to add the appropriate nonsingularity hypothesis to the PF
map-down / cleared HM2.3 layer, or change the singular Appell numerator
convention so the cleared identity remains valid at zero theta factors.

Validation:

```text
lake env lean /tmp/counter_nonzero.lean
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

The source check still passes with the two pre-existing `sorry` warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:4295:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:4634:8: warning: declaration uses 'sorry'
```

`#print axioms` from a direct source compile:

```text
'QseriesFormalization.Pending.Ch10HM.appellNumeratorLaurent_PF_changeOfZ_coeff_mapDown' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23PartialFractionExpansionPF' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Chapter10PF.thetaMul_PF_eq_qPochInfPS_pow_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
