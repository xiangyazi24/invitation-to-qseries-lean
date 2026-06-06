# Ch10 grind reply

Status: partial.  I completed the requested numeric Corr verification and
aligned the Lean theta-correction base to `z0 = 18`.  I did not honestly close
the cleared theta-product identity or the PowerSeries/Laurent bridge.

## Commits

- `c2046c1 chore: verify chapter 10 theta correction`
  - Extended `scripts/ch10_hm_verify.py` to compute Corr directly as the
    weighted HM 2.3 Delta-sum with base `18`.
  - Confirmed Corr equals `-E3^5 * E6^-2 * j(12,15)` through `Q^44`.
- `3c2d30c ch10: align theta correction base`
  - Changed `hm23DeltaBase` from `-30` to `18`.
  - Replaced the quotient-form `theta_correction_product_identity` sorry with
    the precise cleared crux:
    `E6Laurent^2 * thetaCorrectionLaurent = -E3Laurent^5 * jLaurent 12 15`,
    plus the needed `E6Laurent^2 ≠ 0` division side condition.
  - `theta_correction_eval` now follows from that single cleared crux.

## Numeric pass

Command:

```bash
python3 scripts/ch10_hm_verify.py
```

Relevant new output:

```text
Corr weighted Delta-sum vs -E3^5*E6^-2*j(12,15) through Q^44: OK
Corr terms off 3Z through Q^44: none
Corr nonzero coefficients through Q^44:
[(0, -1), (3, 6), (6, -12), (9, 7), (12, 1), (15, 6), (18, -4), (21, -14), (24, 18), (27, -18), (33, 13), (36, 28), (39, -18), (42, -8)]
```

The earlier `z0=18` failure recorded in `codex-ch10-theta-reply.md` was a
truncation artifact: the direct Delta quotient must be computed to a higher
internal `HIGH` before negative prefactors shift terms into degrees `0..44`.

## Lean validation

Commands:

```bash
lake env lean QseriesFormalization/Pending/Chapter10_HM.lean
lake build QseriesFormalization.Pending.Chapter10_HM
rg -n "\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|opaque" \
  QseriesFormalization/Pending/Chapter10_HM.lean scripts/ch10_hm_verify.py
```

Results:

```text
warning: QseriesFormalization/Pending/Chapter10_HM.lean:845:8: declaration uses 'sorry'
Build completed successfully
QseriesFormalization/Pending/Chapter10_HM.lean:852:  sorry
```

No `native_decide`, `admit`, `axiom`, or `opaque` was added.

## Axioms

After refreshing the module olean:

```text
'QseriesFormalization.Pending.Ch10HM.theta_correction_cleared_product_identity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_eval' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.theta_correction_product_identity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.chan1015_hm_laurent' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'QseriesFormalization.Pending.Ch10HM.appell_cancel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Not closed

The current repository state contradicts the handoff premise:
`hm23ClearedThetaIdentity` is not proved; it is still only a `Prop` definition,
and the previous outbox explicitly says it was not closed.  The file also does
not contain proved Laurent-level `j` symmetry/shift lemmas connecting the
coefficient-defined `jLaurent` to the product algebra needed for the cleared
theta identity.

I did not add `chan1015 : chan1015LHSPS = chan1015RHSPS`.  The formal
PowerSeries objects live in `Chapter10_TenthOrder.lean`, while the HM object is
currently a separate Laurent expression with no proved bridge from
`chan1015LHSPS` to `chan1015HCombinationLaurent`.  Adding `chan1015` would have
required another unproved bridge theorem, so I left the exact missing crux
visible instead of hiding it.
