# codex-asd-eta reply

Created `QseriesFormalization/Pending/ASD_EtaProducts.lean`.

Closed, with 0 `sorry`/`axiom`/`admit`:

- `ASDEtaProducts.expand_qPochAPPS`: formal AP-products commute with `PowerSeries.expand`, so `(X^r;X^m)_∞` expands to `(X^(sr);X^(sm))_∞`.
- `ASDEtaProducts.asd5FProductPS_eq_asd5FSeriesPS_complex`:
  `(q^10,q^15,q^25;q^25)_∞` equals the expanded `pentagonal023` theta series, i.e. the `F(q^5)` theta side `∑ (-1)^k X^((25k^2 - 5k)/2)`.
- `ASDEtaProducts.asd5GProductPS_eq_asd5GSeriesPS_complex`:
  `(q^5,q^20,q^25;q^25)_∞` equals the expanded `pentagonal014` theta series, i.e. the `G(q^5)` theta side `∑ (-1)^k X^((25k^2 - 15k)/2)`.

This reuses `JTP_FormalPS_Pentagonal.lean` by applying `X ↦ X^5` to the two closed mod-5 formal JTP identities.

Not closed in this pass:

- The mod-49 `H,J,K` identities need a mod-7 base JTP formal bridge or a direct analogue of the pentagonal template.
- No connection was made to `Chapter17_ASD_Mod5_Full` / `Chapter17_ASD_Mod7_Full` section components.

Verification:

- `~/.elan/bin/lake env lean QseriesFormalization/Pending/ASD_EtaProducts.lean`
- `rg -n "\bsorry\b|\baxiom\b|\badmit\b|native_decide|sorryAx" QseriesFormalization/Pending/ASD_EtaProducts.lean` returned no matches.
- Re-elaborated from source with `#print axioms` for the two final F/G theorems and `expand_qPochAPPS`; dependencies were only `[propext, Classical.choice, Quot.sound]`.
