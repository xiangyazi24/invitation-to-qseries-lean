Implemented the tau mod-2 parity theorem in
`QseriesFormalization/Chapter20.lean`.

Added the Chapter 20 proof path:

- imports the formal Jacobi cube identity from
  `Pending.JacobiCubeAnalyticToFormal`;
- proves over `ZMod 2` that `discriminantPS = X * expand 8 jacobiThetaPS`;
- reads coefficients via `PowerSeries.coeff_expand` and
  `jacobiTripleSign_triangular`;
- converts the `ZMod 2` result back to integer parity.

New public theorems:

- `ramanujanTau_mod_two_eq_one_iff_odd_square`
- `ramanujanTau_odd_iff_odd_square_param`
- `ramanujanTau_odd_iff_odd_square`

Verification:

- `lake env lean QseriesFormalization/Chapter20.lean` passed.
- `rg -n "sorry|admit|axiom" QseriesFormalization/Chapter20.lean` returned no matches.
