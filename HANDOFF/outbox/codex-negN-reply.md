# codex negN reply

Status: not closed.

I verified the negative-`N` direction numerically before editing:

- Canonical integer-core fibers: no failures for `N=-8..-1`, `z=-8..8`.
- Random arbitrary cutoff fibers: no failures in 300 small random negative-`N` samples.
- Random HM-coordinate cutoff fibers from sampled `(a,z0,z1,m,p,z)`: no failures in 300 small random negative-`N` samples.
- User-style source example found with `a=z0=z1=-20`, `r=k=-10`, `i=-22`, `j=-24`, `l=-1`, giving `m=14`, `p=-35`, `z=2`, `N=-2`, `A=-36`, `B=-48`; the integer-core fiber sum was `0`.
- A broader random check over 2000 samples also found arbitrary cutoff fibers matching the canonical fiber for `N=-20..40`.

Edited `QseriesFormalization/Pending/Chapter10_HM.lean` only for Lean source. Added proved negative-`N` canonical integer-core infrastructure:

```lean
hm23IntegerCoreSummandInt
hm23IntegerCoreSummandInt_of_nat
hm23IntegerCoreCanonical_pos_term_zero_of_neg
hm23IntegerCoreCanonical_neg_term_zero_of_neg
hm23IntegerCoreCanonicalSumInt
hm23IntegerCoreCanonicalSumInt_eq_zero_of_neg
hm23IntegerCoreCanonicalSumInt_of_nat
```

The new vanishing theorem is clean:

```text
'QseriesFormalization.Pending.Ch10HM.hm23IntegerCoreCanonicalSumInt_eq_zero_of_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Remaining blocker:

```lean
hm23GammaWindowDifference_residual
```

is still the original `sorry`. The next missing Lean layer is the finite source/coord support closure plus arbitrary-cutoff-to-canonical fiber invariance. Numerically the arbitrary cutoff invariance is true, but I did not finish the formal `Finset` proof or the final residual assembly.

Validation:

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passes, with the two existing `sorry` warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:6907:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:7473:8: warning: declaration uses 'sorry'
```

Requested source-level `#print axioms`:

```text
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
