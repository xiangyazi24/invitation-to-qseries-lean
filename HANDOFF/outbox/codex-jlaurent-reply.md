# jLaurent foundation reply

Completed the coefficient-reindexing layer in `QseriesFormalization/Pending/Chapter10_HM.lean`.

## Commits

- `b593b6c ch10: add Qpow coefficient product lemma`
- `1074884 ch10: prove jLaurent symmetry`
- `9c946cb ch10: prove jLaurent shift`
- `ced51d3 ch10: prove jLaurent boundary zeros`

## Lemmas

- `lcoeff_Qpow_mul`
- `jCoeff_symm`, `jLaurent_symm`
- `jShiftExp`, `jCoeff_shift`, `jLaurent_shift`, `jLaurent_shift_one`
- `jLaurent_zero`, `jLaurent_period_zero`, `jLaurent_self_zero`, `jLaurent_neg`

The `jLaurent` theorems assume `0 < b`, matching the Laurent-series support condition.

## Validation

```bash
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
lake build QseriesFormalization.Pending.Chapter10_HM
python3 scripts/ch10_hm_verify.py
rg -n "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|opaque" QseriesFormalization/Pending/Chapter10_HM.lean
```

Results:

- Lean single-file check passed.
- Lake module build passed.
- `scripts/ch10_hm_verify.py` passed.
- No `admit`, `native_decide`, `axiom`, or `opaque`.
- Existing unrelated `sorry` remains at `theta_correction_cleared_product_identity` (`Chapter10_HM.lean:1256`); this run did not attempt HM 2.3 or the theta collapse.

## Axioms

```text
'QseriesFormalization.Pending.Ch10HM.lcoeff_Qpow_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jCoeff_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jCoeff_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_shift_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_period_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_self_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
```
