# Ch15 JTP logarithmic-derivative attempt

I did not close `chan_theorem_11_7` unconditionally.

## Added

- `QseriesFormalization/Pending/Chapter15_FormalDeriv.lean`
  - `formalDeriv`, as a wrapper around `PowerSeries.derivative`.
  - `thetaOp f := X * formalDeriv f`.
  - coefficient theorem:
    ```lean
    (thetaOp f).coeff n = f.coeff n * (n : R)
    ```
  - derivation rules:
    ```lean
    thetaOp_add
    thetaOp_sub
    thetaOp_mul
    thetaOp_pow
    thetaOp_C_mul
    thetaOp_X_mul
    ```
  - `thetaDlog` plus multiplication/power rules under nonzero constant-coefficient
    hypotheses.

- `QseriesFormalization/Pending/Chapter15_DobbieFromJTP.lean`
  - `thetaOp_section83_pair14`
  - `thetaOp_section83_pair23`
  - expanded theta forms of the two §8.3 RHS identities
  - `thetaOp_fifth_root_collapse_complex`
  - expanded theta form of the fifth-root collapse
  - `chan_theorem_11_7_from_current_core`, which only repackages the existing
    `Ch15RODE.chan_theorem_11_7`.

## Verification

Passed:

```bash
lake env lean QseriesFormalization/Pending/Chapter15_FormalDeriv.lean
lake env lean QseriesFormalization/Pending/Chapter15_DobbieFromJTP.lean
lake build QseriesFormalization.Pending.Chapter15_DobbieFromJTP
```

Also checked:

```bash
lake env lean QseriesFormalization/Pending/Chapter15_R_ODE.lean
```

This still passes with the existing warning:

```text
QseriesFormalization/Pending/Chapter15_R_ODE.lean:156:8: warning: declaration uses 'sorry'
```

`#print axioms` confirms the distinction:

```text
Ch15FormalDeriv.thetaOp_mul
  depends on [propext, Classical.choice, Quot.sound]

Ch15DobbieFromJTP.chan_theorem_11_7_from_current_core
  depends on [propext, sorryAx, Classical.choice, Quot.sound]
```

## Blocker

The requested route is not closed by just applying `thetaOp` to the listed JTP
identities.

The key mismatch is that:

- `section83JTPProductPS z` is the constant-twist product
  `(q, zq, z⁻¹q; q)_∞`, whose factors are `(1 - z X^n)`.
- `prod_scaleX_qPochInfPS_fifth_collapse_complex` is the variable-rescale
  product `∏ E(ζ^j X)`, whose factors are `(1 - ζ^{j n} X^n)`.

Their logarithmic derivatives have different root-of-unity weights.  The
formal derivative layer is now available, but the remaining missing theorem is
still the all-coefficients Lambert/product bridge:

```lean
theorem chan_theorem_11_7_int_core_coeff (N : ℕ) : ...
```

Equivalently, one must still prove that the derivative algebra extracted from
the §8.3 identities gives the exact series

```text
1 - 5 * Σ χ₅(d) d q^d/(1-q^d)
```

or replace that step with a formal specialized Dobbie partial-fraction identity.
