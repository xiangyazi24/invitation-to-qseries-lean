# codex intcore reply

Status: not closed.

I did not replace `hm23GammaWindowDifference_residual` with a renamed sorry,
and I did not touch `Chapter10_PF.lean` or the forbidden bridge/collapse files.

Closed and committed in `QseriesFormalization/Pending/Chapter10_HM.lean`:

- `5b7a9ca proof: add HM23 integer core canonical telescope`
  - `hm23IntegerCoreSummand`
  - `hm23IntegerCoreCanonical_pos_inner`
  - `hm23IntegerCoreCanonical_neg_inner`
  - `hm23IntegerCoreCanonicalSum`
  - `hm23IntegerCoreCanonical_eq_thetaMulPFCoeffPF`
  - `hm23IntegerCoreCanonical_eq_unified`
- `87e6890 proof: align HM23 gamma fiber with integer core`
  - `hm23_linear90_pos_iff_cutoff`
  - `hm23Ncoord_eq_integer_core_exponent`
  - `hm23_integer_core_sign_eq_coord`
  - `hm23Gamma_coord_sub_eq_integer_core_cutoff`
- `8199c62 proof: package HM23 fiber core summand`
  - `hm23_coord_fiber_term_eq_integerCoreSummand`

What is now proved:

```lean
hm23IntegerCoreCanonical_eq_unified
  (N : ℕ) (z : ℤ) :
  hm23IntegerCoreCanonicalSum N z =
    Chapter10PF.thetaMulPFUnifiedCoeffPF N z
```

and the pointwise HM fiber term with
`N = hm23Ncoord m p z r k` is identified with the corresponding
`hm23IntegerCoreSummand` using the actual denominator cutoffs.

Remaining blocker:

```lean
hm23GammaWindowDifference_residual
```

still needs the source-window bridge:

```text
hm23GammaWindowFourFactorSum
  -> finite source windows in (r,k,i,j,l)/(s,k,h,j,l)
  -> shared (m,p,z,N,r,k) fiber sum
  -> integer-core summand theorem above
```

The pointwise algebra and the PF-side canonical integer telescope are now
proved; the missing step is the finite nested-window support collapse and
summation reindexing.

Validation:

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passes, with the two existing warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:5906:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:6472:8: warning: declaration uses 'sorry'
```

Forbidden-token grep:

```text
rg -n "\\bnative_decide\\b|\\badmit\\b|\\bopaque\\b|^\\s*axiom\\b" QseriesFormalization/Pending/Chapter10_HM.lean
```

returns no matches.

Source-level `#print axioms`:

```text
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

