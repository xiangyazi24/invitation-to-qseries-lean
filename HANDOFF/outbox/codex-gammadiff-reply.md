# codex gammadiff reply

Status: not closed.

Edited Lean source:

- `QseriesFormalization/Pending/Chapter10_HM.lean`

Added two proved PF-raw coordinate lemmas:

```lean
hm23Ncoord_eq_pf_raw_exponent
hm23_residual_sign_eq_pf_raw_sign
```

These identify the transported coordinate exponent/sign with the PF raw
variables

```text
theta index      z + p - r + 1
denominator idx  r - m + k
branch power     r - p - 1
```

I did not close `hm23GammaWindowDifference_residual`.  The remaining hard
sub-step is the genuine finite telescoping/support bridge: the pointwise Gamma
difference is not equal to a PF raw branch term; it agrees only after summing
over the finite `(r,k)` fiber.  That fiber identity still has to be proved.

Validation:

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

Result: passes, with the two existing `sorry` warnings now at:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:5365:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:5931:8: warning: declaration uses 'sorry'
```

`#print axioms` from source re-elaboration:

```text
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
