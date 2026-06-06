Closed the full ASD-5 section identification core in
`QseriesFormalization/Pending/ASD_EtaProducts.lean`.

Added coefficient-matching proofs over `ZMod 5`:

- `A0_eq_asd5FSeriesPS_zmod5 : A 0 = asd5FSeriesPS (ZMod 5)`
- `A0_eq_asd5FProductPS_zmod5 : A 0 = asd5FProductPS (ZMod 5)`
- `A1_eq_asd5GShiftedSeriesPS_zmod5 :
  A 1 = -(3 : (ZMod 5)⟦X⟧) * X * asd5GSeriesPS (ZMod 5)`
- `A1_eq_asd5GShiftedProductPS_zmod5 : A 1 = asd5GShiftedProductPS`

Method: pure coefficient matching.  The residue-0 triangular indices split as
`j = 5a` and `j = 5a - 1`, matching `pentagonal023Exp (-a)` and
`pentagonal023Exp a`.  The residue-1 triangular indices split as
`j = 5a + 1` and `j = 5a - 2`, matching `pentagonal014Exp (-a)` and
`pentagonal014Exp a`, with the expected `-3` factor.

Verification:

- `lake env lean QseriesFormalization/Pending/ASD_EtaProducts.lean`
- `rg -n "sorry|admit|axiom|sorryAx" QseriesFormalization/Pending/ASD_EtaProducts.lean`
- `#print axioms` for the four new public theorems: no `sorryAx`; only
  `propext`, `Classical.choice`, and `Quot.sound`.
