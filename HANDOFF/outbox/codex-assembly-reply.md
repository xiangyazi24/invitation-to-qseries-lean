# codex assembly reply

Status: not closed.

I did not replace `hm23GammaWindowDifference_residual` with a renamed theorem,
and I did not touch the collapse residual, redJ, bridges,
`jLaurent_riemann`, `jLaurent_eq_tripleProductInf`, or `Chapter10_PF.lean`.

What is now proved in `QseriesFormalization/Pending/Chapter10_HM.lean`:

- Flattened the concrete `hm23GammaWindowFourFactorSum` into an eight-coordinate
  finite sigma index:
  - `HM23GammaWindowSigma`
  - `hm23GammaWindowSigmaSet`
  - `hm23GammaWindowSigmaSummand`
  - `hm23GammaWindowFourFactorSum_eq_sigma`
- Added the window-to-source maps and injectivity on the active guard filter:
  - `hm23GammaWindowSigmaToPsi1`
  - `hm23GammaWindowSigmaToPsi0`
  - `hm23GammaWindowSigmaToPsi1_injOn`
  - `hm23GammaWindowSigmaToPsi0_injOn`
- Added source exponent decomposition lemmas:
  - `jExp90_eq_hmTri`
  - `appellNumeratorExp_eq_hmTri`
  - `hm23Term1SourceExp_eq_window_parts`
  - `hm23Term2SourceExp_eq_window_parts`
- Proved the source-set bridge for both Gamma windows:
  - `hm23GammaWindowSigmaSummand_eq_term1Source`
  - `hm23GammaWindowSigmaSummand_eq_term2Source`
  - `hm23Psi1WindowSourceSet`
  - `hm23Psi0WindowSourceSet`
  - `hm23GammaWindowFourFactorSum_eq_Psi1Source`
  - `hm23GammaWindowFourFactorSum_eq_Psi0Source`

Remaining exact blocker:

After the new source bridge, the next step is the support/Phi transport from
the two concrete finite source sets to the common `(m,p,z,N,r,k)` fibers.  The
repository currently has the `jExp` window lemmas, but I could not find an
existing Appell/Gamma window-support lemma proving that every nonzero
transported Gamma term lands in the opposite Appell window and then in the PF
raw/canonical fiber window.  That support lemma is needed before the already
proved `_core` transports and integer-core canonical telescope can be applied
honestly.

Validation:

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
```

passes, with the two remaining warnings:

```text
QseriesFormalization/Pending/Chapter10_HM.lean:6309:8: warning: declaration uses 'sorry'
QseriesFormalization/Pending/Chapter10_HM.lean:6875:8: warning: declaration uses 'sorry'
```

`#print axioms`:

```text
'QseriesFormalization.Pending.Ch10HM.hm23ClearedThetaIdentity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```
