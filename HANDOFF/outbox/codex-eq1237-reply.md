Status: closed, no `sorry`.

Added `QseriesFormalization/Pending/Chapter13_Eq1237.lean`.

Main theorem:

```lean
QseriesFormalization.Pending.Ch13Eq1237.chan_eq_12_37_cleared
```

It proves the cleared formal-power-series form over `ℚ⟦X⟧`:

```lean
(qPochInfPS ℚ)^6 *
    (pentagonal014SeriesPS ℚ)^5 *
    (pentagonal023SeriesPS ℚ)^5 =
  (PowerSeries.expand 5 (by decide) (qPochInfPS ℚ))^6 *
    ((pentagonal023SeriesPS ℚ)^10 -
      (11 : ℚ⟦X⟧) * PowerSeries.X *
        (pentagonal014SeriesPS ℚ)^5 * (pentagonal023SeriesPS ℚ)^5 -
      PowerSeries.X^2 * (pentagonal014SeriesPS ℚ)^10)
```

Route:

- used `RamanujanQuinticJTP.E5DenominatorCoreRat_mul_expand_twentyfive_qPochInfPS`;
- used `PartIII.Ch14Thm116.E5_zero_product_bridge_expanded_rat`;
- derived the expanded mod-5 product-core bridge;
- pulled it back through injectivity of `PowerSeries.expand 5`;
- rewrote `pentagonalProduct014/023PS` to `pentagonal014/023SeriesPS`.

Auxiliary theorem exposed:

```lean
QseriesFormalization.Pending.Ch13Eq1237.chan_eq_12_37_product_core
```

which is the direct `ramanujanMod5ProductCoreThetaRat` packaging:

```lean
(expand 5 qPochInfPS)^6 * ramanujanMod5ProductCoreThetaRat =
  qPochInfPS^6 * pentagonal014SeriesPS^5 * pentagonal023SeriesPS^5
```

Validation:

```bash
lake env lean QseriesFormalization/Pending/Chapter13_Eq1237.lean
rg -n "sorry|axiom|admit" QseriesFormalization/Pending/Chapter13_Eq1237.lean
```

Result: Lean check succeeds; `rg` returns no matches.

I did not add the `1/rrcf_r^5 - 11 - rrcf_r^5 = .../(X*...)` form because the
right side has an explicit `X` denominator and is naturally Laurent rather
than an ordinary formal power series. The cleared identity is the formal-PS
statement.
