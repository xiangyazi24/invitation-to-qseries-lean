# Ch12 eta value reply

Created `QseriesFormalization/Pending/Chapter12_EtaValue.lean`.

What is closed:
- Specialized Mathlib `jacobiTheta_S_smul` at `τ = 5i`:
  `jacobiTheta (I / 5) = (sqrt 5 : ℂ) * jacobiTheta (5 * I)`.
- Recorded the definitional bridge from `ModularForm.eta` to this repo's
  Euler product:
  `eta z = qParam 24 z * eulerPentagonalInfiniteProduct (qParam 1 z)`.
- Proved the exact Chapter 12 eta quotient from a single isolated hypothesis
  `EtaSFormula`:
  `eta (I / 5) / eta (5 * I) = (sqrt 5 : ℂ)`.

Validation:
- `lake env lean QseriesFormalization/Pending/Chapter12_EtaValue.lean`

Remaining blocker:
- In Mathlib v4.27, `Mathlib.NumberTheory.ModularForms.DedekindEta` provides
  `ModularForm.eta`, `eta_ne_zero`, and differentiability, but no eta
  S-transform theorem.  The unconditional Ch12 eta quotient still requires
  proving `EtaSFormula`, likely via the theta derivative/triple-product bridge.
