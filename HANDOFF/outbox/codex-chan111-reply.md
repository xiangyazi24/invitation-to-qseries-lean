Done.

Added `QseriesFormalization/Pending/Chan_Theorem_11_1.lean`.

Main theorem:

```lean
theorem QseriesFormalization.Pending.chan_theorem_11_1 :
    Ch13RRCF.rrcf_r = Ch11RRCFConvergent.rrcf_r_via_CF
```

Key proof path:

- Defined shifted Rogers-Ramanujan formal series
  `J_m = Σ_n X^(n^2 + m*n)/(X;X)_n` as `rrJShiftPS m`.
- Proved `rrJShiftPS 0 = rrGPS` and `rrJShiftPS 1 = rrHPS`.
- Proved the formal functional equation
  `rrJShiftPS m = rrJShiftPS (m+1) + X^(m+1) * rrJShiftPS (m+2)`.
- Proved the cleared-convergent error identity:
  `J_1*A_n - J_0*B_n = (-1)^(n+1) * X^tri(n) * J_(n+2)`.
- Divided by the units `rrGPS` and `rrcf_APS n` to get
  `X^tri(n) ∣ (rrHPS * rrGPS⁻¹ - rrcf_RPS n)`.
- Took `n = k` coefficientwise, using `coeff_rrcf_r_via_CF`, to prove
  `rrcf_r_via_CF = rrHPS * rrGPS⁻¹`.
- Finished with `RRFinalAssembly.rogersRamanujan_ratio_formal`.

Validation:

```bash
lake env lean QseriesFormalization/Pending/Chan_Theorem_11_1.lean
lake build QseriesFormalization.Pending.Chan_Theorem_11_1
rg -n "sorry|admit|axiom" QseriesFormalization/Pending/Chan_Theorem_11_1.lean
```

`lake env lean` and module build both pass. The `rg` check returns no
matches in the new file.

Axiom audit:

```lean
#print axioms QseriesFormalization.Pending.chan_theorem_11_1
```

Output:

```text
[propext, Classical.choice, Quot.sound]
```
