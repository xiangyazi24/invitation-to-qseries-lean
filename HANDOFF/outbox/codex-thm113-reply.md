Implemented `QseriesFormalization/Pending/Chapter13_Thm113.lean`.

Main theorem:
- `QseriesFormalization.Pending.Ch13Thm113.chan_theorem_11_3_formal_ps`

Statement proved:
```lean
(PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ))^2 -
    PowerSeries.X *
      PowerSeries.expand 5 (by decide) (pentagonal023SeriesPS ℚ) *
      PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ) -
    PowerSeries.X^2 *
      (PowerSeries.expand 5 (by decide) (pentagonal014SeriesPS ℚ))^2 =
  qPochInfPS ℚ * PowerSeries.expand 5 (by decide) (qPochInfPS ℚ)
```

Proof route:
- Uses `section83JTPProductPS_eq_rhs_pair14/23`.
- Multiplies the two period RHS factors and uses
  `quinticPeriod_sum` / `quinticPeriod_mul` to get
  `A^2 - X*A*B - X^2*B^2`.
- Proves the corresponding fifth-root product collapse for
  `constQPochInfPS`, giving
  `section83JTPProductPS ζ * section83JTPProductPS (ζ^2)
    = qPochInfPS ℂ * expand5(qPochInfPS ℂ)`.
- Descends the complex identity to `ℚ⟦X⟧` via `PowerSeries.map_injective`.

Validation:
```bash
lake env lean QseriesFormalization/Pending/Chapter13_Thm113.lean
rg -n "sorry|admit|axiom" QseriesFormalization/Pending/Chapter13_Thm113.lean
```

The Lean check passed. The grep found no `sorry`, `admit`, or `axiom`.
