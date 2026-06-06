# codex-mod7-keystone-eta reply

Created `QseriesFormalization/Pending/JTP_FormalPS_Mod7.lean`.

Closed, with 0 `sorry`/`axiom`/`admit`/`sorryAx` in the new file:

- Formal mod-7 AP products:
  - `mod7Product034PS = (q^3,q^4,q^7;q^7)_∞`
  - `mod7Product025PS = (q^2,q^5,q^7;q^7)_∞`
  - `mod7Product016PS = (q,q^6,q^7;q^7)_∞`
- Analytic JTP specialisations via `PartI.Ch02.jacobiTripleProduct`, including the
  formal analytic-to-coefficient bridge:
  - `mod7Product034PS_eq_theta7SeriesPS_complex`
  - `mod7Product025PS_eq_theta7SeriesPS_complex`
  - `mod7Product016PS_eq_theta7SeriesPS_complex`
- Rational forms:
  - `mod7Product034PS_eq_theta7SeriesPS_rat`
  - `mod7Product025PS_eq_theta7SeriesPS_rat`
  - `mod7Product016PS_eq_theta7SeriesPS_rat`
- Mod-49 eta products from `X ↦ X^7`:
  - `asd7HProductPS_eq_asd7HSeriesPS_complex`
  - `asd7JProductPS_eq_asd7JSeriesPS_complex`
  - `asd7KProductPS_eq_asd7KSeriesPS_complex`
  - and the corresponding `_rat` versions.

The H/J/K theta sides are defined as expanded series:

- `H(q^7)`: `∑ (-1)^k X^((49k^2 - 7k)/2)`
- `J(q^7)`: `∑ (-1)^k X^((49k^2 - 21k)/2)`
- `K(q^7)`: `∑ (-1)^k X^((49k^2 - 35k)/2)`

Not closed in this pass:

- The optional `ZMod 7` section identification
  `(q;q)^3 ≡ H(q^7) - 3qJ(q^7) + 5q^3K(q^7) (mod 7)`.
- No eta-quotient rewrite of `Chapter17_ASD_Mod7_Full` section congruences yet.

Verification:

- `lake env lean QseriesFormalization/Pending/JTP_FormalPS_Mod7.lean`
- `rg -n "sorry|admit|axiom|sorryAx" QseriesFormalization/Pending/JTP_FormalPS_Mod7.lean` returned no matches.
