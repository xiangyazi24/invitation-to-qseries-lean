# codex-eta-bridge reply

Modified `QseriesFormalization/Pending/Chapter12_EtaValue.lean`.

What now compiles:
- Kept the Mathlib theta specialization:
  `jacobiTheta (I / 5) = (sqrt 5 : ℂ) * jacobiTheta (5 * I)`.
- Isolated the exact local eta S-transform at `τ = 5i`:
  - `EtaSFormulaAtTau5Raw`
  - `EtaSFormulaAtTau5`
  - `eta_S_raw_at_tau5_of_eta_S`
  - `eta_S_at_tau5_of_raw`
- Added local quotient forms requiring only the raw `τ = 5i` eta S-transform,
  not the full global eta S-transform:
  - `eta_i_div_five_eq_sqrt_five_mul_eta_five_i_of_eta_S_at_tau5_raw`
  - `eta_i_div_five_div_eta_five_i_eq_sqrt_five_of_eta_S_at_tau5_raw`
- Added the cube/root-branch algebra bridge:
  `eta_S_at_tau5_of_cube_and_positive`.
  This proves that an eta³ S-transform at `τ = 5i`, plus positive-real branch
  information for the two eta values, is enough to recover the desired eta
  identity itself.

Validation:
- `lake env lean QseriesFormalization/Pending/Chapter12_EtaValue.lean`

Exact remaining gap:
- I did not find a Mathlib theorem proving Dedekind eta's S-transform, even at
  one point.  `DedekindEta.lean` currently exposes eta's product definition,
  nonvanishing, differentiability, and log-derivative facts, but no modular
  transformation theorem.
- The likely route is still:
  1. prove `eta^3` at `τ = 5i` via `jacobiTheta₂'_functional_equation`;
  2. connect `jacobiTheta₂' ((τ+1)/2) τ` to
     `2*pi*I*(eulerPentagonalInfiniteProduct (qParam 1 τ))^3`;
  3. prove eta values at `I/5` and `5I` lie on the positive real branch.
- Step 2 is mathematically supported by the existing Chapter 4 Jacobi identity,
  but the concrete bridge to Mathlib's `jacobiTheta₂'` is not currently in the
  repository. Step 3 is also not present as a reusable positivity theorem for
  the eta product on the imaginary axis.
