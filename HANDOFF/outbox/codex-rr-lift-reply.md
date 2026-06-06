Status: not closed.

Added `QseriesFormalization/Pending/RR_LiftToFormalPS.lean` with a no-sorry
algebraic descent layer:

- `map_pentagonal023SeriesPS_rat_complex`
- `rogers_ramanujan_G_formal_of_complexification`
- `rogers_ramanujan_G_formal_of_complex_identity`

The last theorem proves that if the complexified formal identity

```lean
PowerSeries.map (algebraMap ℚ ℂ) rrGPS * qPochInfPS ℂ =
  pentagonal023SeriesPS ℂ
```

is available, then the desired rational identity

```lean
rrGPS * qPochInfPS ℚ = pentagonal023SeriesPS ℚ
```

follows by `PowerSeries.map_injective`, `map_qPochInfPS`, and the
`ℚ → ℂ` naturality of `pentagonal023SeriesPS`.

Validation:

```bash
lake build QseriesFormalization.Pending.RR_LiftToFormalPS
rg -n "sorry|admit|axiom" QseriesFormalization/Pending/RR_LiftToFormalPS.lean
```

The build passes.  The `rg` check returns no matches in the new file.
The build still reports the pre-existing four `sorry` declarations in
`Pending/RogersRamanujan_FormalPS.lean`, because that file is imported for
`rrGPS`; the new lift file does not introduce any.

I did not add a theorem named `rogers_ramanujan_G_formal`, because the only
currently available theorem with the target statement is
`RogersRamanujanFormalPS.rogersRamanujan_G_alt`, and it depends on `sorryAx`.
Wrapping it would be a fake proof.

Remaining blocker:

Need the actual Taylor bridge for `rrGPS`, namely a no-sorry proof that
`PowerSeries.map (algebraMap ℚ ℂ) rrGPS` is the formal coefficient series of
`q ↦ rrJInf 1 q` near `0` (or directly that
`PowerSeries.map (algebraMap ℚ ℂ) rrGPS * qPochInfPS ℂ` is the coefficient
series of `q ↦ rrJInf 1 q * qPochhammer_inf q`).  The `pentagonal023` side
already has the required `HasFPowerSeriesOnBall` infrastructure in
`Pending/JTP_FormalPS_Pentagonal.lean`, and `qPochInfPS` already has the
analytic coefficient bridge in `Chapter19_JacobiTripleSignChar.lean`.
