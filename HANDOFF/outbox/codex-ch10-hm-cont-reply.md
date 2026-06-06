# Ch10 HM continuation reply

## Commits

- `ff98f77 ch10: add HM Laurent m semantics`
  - Adds `ℚ⸨X⸩` layer (`QLaurent`), coefficient extraction `lcoeff`, monomials `Qpow`, and finite coefficient extraction for `jLaurent`.
  - Adds Laurent-valued Appell-Lerch functional-equation normal form `appellM` with:
    - `appellM_period_z : appellM a (z + 90) = appellM a z`
    - `appellM_shift_a : appellM (a + 90) z = 1 - Qpow a * appellM a z`
    - `appellM_inversion : appellM a z = Qpow (-a) * appellM (-a) (-z)`
- `cdbeed7 ch10: specialize HM f232 Laurent table`
  - Adds `hmTermLaurent`, `hmTermsLaurent`, and `hmF232Laurent`.
  - Completes the nine verified HM `T_ij` term rows, including the `ell = 2` nonsingular choices for `T02` and `T10`.
  - Adds nine Laurent-specialized table theorems `hmF232Laurent_T00` through `hmF232Laurent_T22`.

## Validation

Commands run:

```bash
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
lake build QseriesFormalization.Pending.Chapter10_HM
python3 scripts/ch10_hm_verify.py
rg -n "native_decide|\bsorry\b|\badmit\b|^\s*axiom\b|opaque" QseriesFormalization/Pending/Chapter10_HM.lean
```

Lean result:

```text
warning: QseriesFormalization/Pending/Chapter10_HM.lean:592:8: declaration uses 'sorry'
Build completed successfully.
```

The grep finds only the isolated `appell_cancel` crux:

```text
590:not imported by `Audit.lean`.  It is the only `sorry` in this file.
593:  sorry
```

No `native_decide`, `admit`, `axiom`, or `opaque`.

Numeric verifier remains OK through `Q^44`:

```text
T00 OK, T01 OK, T02 OK, T10 OK, T11 OK, T12 OK, T20 OK, T21 OK, T22 OK
Chan combination vs -E3^5*E6^-2*j(12,15) through Q^44: OK
```

## Axioms

Spot-check after refreshing the module olean:

```text
'QseriesFormalization.Pending.Ch10HM.coeff_jLaurent' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appellM_period_z' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appellM_shift_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appellM_inversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hmF232Laurent_T02' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hmF232Laurent_T10' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.hmF232Laurent_T22' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appell_cancel' depends on axioms: [sorryAx]
```

## Notes

- `appellM` is currently a genuine Laurent-valued functional-equation normal form.  The HM Def. 0.1 quotient-series bridge is still future work; it should prove that the nonsingular Appell-Lerch quotient specializes to this normal form.
- `QseriesFormalization.lean` and `Audit.lean` remain untouched.
- Existing untracked file left untouched: `HANDOFF/inbox/codex-ch10-hm-start.md`.
