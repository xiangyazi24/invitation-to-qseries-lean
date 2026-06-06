# codex jTP bridge reply

## Commit

- `f671b5b ch10: add finite JTP bridge lemmas`

## What closed

Edited only `QseriesFormalization/Pending/Chapter10_HM.lean` for the Lean layer.

Added the finite `jLaurent`/JTP bridge:

- `Qpow_ne_zero`, `Qpow_inv`, `Qpow_inv_mul`
- `Qpow_pow_nat`, `Qpow_zpow`, `negOnePowIntQ_cast_zpow`, `neg_Qpow_zpow`
- `jTermLaurent`
- `jFiniteProductLaurent`
- `jTripleProductPartialLaurent`
- `jFiniteJTPSummand_Qpow`
- `finiteJTPRHS_Qpow_eq_natSum_jTerm`
- `jFiniteProductLaurent_eq_finiteJTPRHS`
- `jTripleProductPartialLaurent_eq_qPochhammer_mul_finiteJTPRHS`

This reuses the repository theorem
`QseriesFormalization.PartI.Ch03.finite_jacobi_triple_product` with
`q = Qpow b`, `z = Qpow a`; the second q-Pochhammer factor is normalized by
`Qpow_inv_mul : (Qpow a)⁻¹ * Qpow b = Qpow (b-a)`.

Added denominator/unit bridge lemmas for HM 2.3 quotient manipulation:

- `jExpTwice_pos_of_ne_zero_of_pos_lt`
- `jExp_ne_zero_of_ne_zero_of_pos_lt`
- `jCoeff_zero_of_pos_lt`
- `jLaurent_ne_zero_of_pos_lt`
- `jLaurent_isUnit_of_ne_zero`
- `jLaurentRatio`, `jLaurentRatio_isUnit`
- `jLaurentRatio_mul_den`, `den_mul_jLaurentRatio`
- `jLaurent_four_product_ne_zero`

The normalized product range is explicit: for `0 < a < b`, `jLaurent a b`
has constant coefficient `1`, so denominator nonzero/unit facts are available.
Arguments outside the product range should first use the existing
`jLaurent_shift`/`jLaurent_symm` lemmas.

## Numeric self-check

Ran the existing verifier:

```text
python3 scripts/ch10_hm_verify.py
```

All checks passed, including HM 2.3 sample change-of-z checks and the theta
correction through `Q^44`.

Also checked the product bridge numerically before editing:

- Direct product `j(a,b)` matched for normalized samples including
  `(12,15)`, `(1,2)`, `(9,18)`, `(90,270)`, `(12,90)`, `(18,90)`, `(30,90)`,
  `(24,18)`.
- Non-normalized cases such as `j(39,18)` require shift normalization first;
  normalized product checks passed for `(39,18)`, `(24,18)`, `(42,18)`,
  `(-24,90)`, `(-12,90)`, `(42,90)`, `(120,90)`.

## Validation

```text
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
lake build QseriesFormalization.Pending.Chapter10_HM
rg -n "native_decide|\bsorry\b|\badmit\b|^\s*axiom\b|opaque|def .*: Prop" \
  QseriesFormalization/Pending/Chapter10_HM.lean
```

Lean and module build pass. The only `sorry` warning is the pre-existing
`theta_correction_cleared_product_identity`; no new `sorry`, `admit`,
`native_decide`, `axiom`, or `opaque` was added. The existing `def : Prop`
items are the prior HM 2.3 proposition wrappers.

## Axioms

```text
'QseriesFormalization.Pending.Ch10HM.Qpow_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.Qpow_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.Qpow_zpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.neg_Qpow_zpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jFiniteJTPSummand_Qpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.finiteJTPRHS_Qpow_eq_natSum_jTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jFiniteProductLaurent_eq_finiteJTPRHS' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jTripleProductPartialLaurent_eq_qPochhammer_mul_finiteJTPRHS' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jCoeff_zero_of_pos_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_ne_zero_of_pos_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurentRatio_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurentRatio_mul_den' depends on axioms: [propext, Classical.choice, Quot.sound]
'QseriesFormalization.Pending.Ch10HM.jLaurent_four_product_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No new theorem depends on `sorryAx`.

## Remaining boundary

I did not assert a fake infinite-product equality
`jLaurent = (Q^b;Q^b)_∞(Q^a;Q^b)_∞(Q^(b-a);Q^b)_∞`. The repo still needs the
general analytic-to-formal/infinite-product coefficient-stabilization bridge
for that exact statement. This run closes the finite JTP partial-product bridge
and the HM denominator/unit manipulation layer without adding axioms or sorries.
