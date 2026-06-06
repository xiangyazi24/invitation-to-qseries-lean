# codex support reply

Status: not closed.

I did not replace `hm23GammaWindowDifference_residual` with a renamed theorem,
and I did not touch the collapse residual, redJ, bridge files,
`jLaurent_riemann`, `jLaurent_eq_tripleProductInf`, or `Chapter10_PF.lean`.

Edited `QseriesFormalization/Pending/Chapter10_HM.lean` only for Lean code.

Proved support pieces:

```lean
hm23Gamma_ne_zero_iff_of_ne
hm23Gamma_mul_nonneg

appellNumeratorCoeffLower_le_exp_add_denom_mul_of_Gamma_ne_zero
appellNumeratorExp_add_denom_mul_mem_window_of_Gamma_ne_zero

hm23Term1SourceExp_phi_eq_term2SourceExp
hm23Term2SourceExp_phi_eq_term1SourceExp

hm23Psi1_phi_mem_Psi0WindowSourceSet_of_Gamma_ne_zero
hm23Psi0_phi_mem_Psi1WindowSourceSet_of_Gamma_ne_zero
```

These prove the opposite Appell/source-window side: if the transported opposite
Gamma term is nonzero, the Phi image lands in the opposite concrete
`hm23Psi*WindowSourceSet`.

Blocker found while checking the requested PF window statement:

The local claim "nonzero transported Gamma term implies
`0 <= hm23Ncoord` / PF Nat window" is false for the current definitions.
A concrete integer instance satisfying the source sigma windows and active
equations has negative `Ncoord`:

```text
a = -20, z0 = -20, z1 = -20
r = -10, k = -10, i = -7, j = -5, l = -5
E = 15450, E1 = 2660, E2 = 1550, E3 = 1550, e = 21210
D1 = appellDenomExp a z1 r = -1030
D0 = appellDenomExp a z0 (i-k) = 140
Gamma(D1,k) = -1, Gamma(D0,k) = 0
m = -5, p = -20, z = 2
hm23Ncoord m p z r k = -2
```

The same data satisfies the concrete source window inequalities:

```text
appellNumeratorCoeffLower a z1 <= E
E <= e - (jCoeffLower z0 90 + (jCoeffLower (a+z0) 90 + jCoeffLower (a+z1) 90))
jCoeffLower z0 90 <= E1
jCoeffLower (a+z0) 90 <= E2
r/i/j/l/k are all inside their corresponding concrete windows
```

So the remaining HM2.3 residual cannot be closed by only the stated local
integer-inequality support lemma.  It needs an additional cancellation/reindex
step for negative-`Ncoord` transported terms, or a corrected support statement
with stronger hypotheses.

Validation:

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passes, with the two existing `sorry` warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:6703:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:7269:8: warning: declaration uses 'sorry'
```

Forbidden-token grep:

```text
rg -n "\bnative_decide\b|\badmit\b|\bopaque\b|^\s*axiom\b" QseriesFormalization/Pending/Chapter10_HM.lean
```

returns no matches.

Source-piped `#print axioms`:

```text
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
