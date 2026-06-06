# TASK (codex/gpt-5.5): the AP-product analytic evaluation (THE keystone gap)

Extend `QseriesFormalization/Pending/JTP_FormalPS_Pentagonal.lean`. Touch ONLY this file.
Single-file `lake env lean` verify; 0 sorry/axiom/admit; no sorryAx.
Reply to `HANDOFF/outbox/codex-ap-product-eval-reply.md`.

## The ONE remaining lemma (closes the whole keystone)
The AP-product analogue of B2's `Ch19.eulerPentagonalInfiniteProduct_cube_eq_tsum_qpow_cubeConvolution`:
```lean
-- on ‖y‖ < 1:
pentagonal014ProductAnalytic y = ∑' n : ℕ, y^n * ((pentagonalProduct014PS ℂ).coeff n)
```
and the `023` analogue. (LHS = the analytic infinite product; RHS = tsum of the FORMAL product's
coefficients.) Then feed it to the CONDITIONAL wrappers already in this file
(`pentagonalProduct014PS_eq_pentagonal014SeriesPS_complex_of_productCoeff_taylor` etc.) to obtain
the unconditional `pentagonalProduct014PS ℂ = pentagonal014SeriesPS ℂ` (and 023). That CLOSES the
keystone ⇒ unblocks ASD η-products + (separately) the MBI denominator identity.

## How — reuse the formal↔partial machinery ALREADY in this file
You already proved: `multipliable_apFactorPS`, `hasProd_qPochAPPS`, `tendsto_qPochAPPS_partial`
(formal product = limit of finite partial products, coefficientwise). And the analytic product
`pentagonal014ProductAnalytic` is the analytic limit of the SAME finite partial products on ‖y‖<1.
So: (a) the formal product's coeff n = coeff n of a finite partial product (for the product over
enough factors — exponents grow, so low coeffs stabilise); (b) the analytic finite partial product
evaluated at y = the polynomial sum ∑ (finite-product coeff) y^k; (c) take limits on both sides
(analytic: product converges on ‖y‖<1; formal-coeff side: the tsum converges by the radius bound
`one_le_pentagonal014SeriesFMLS_radius`-style summability you already have for the product coeffs).
This is exactly B2's `eulerPentagonalInfiniteProduct_cube_eq_tsum_qpow_cubeConvolution` strategy,
specialised to these AP products. Study how Ch19 proves that cube lemma and mirror it.

## Deliverable
Best: both equalities (keystone closed). Acceptable: the analytic-eval lemma for one product, or
the partial-product coeff-stability bridge. Report exactly what closed. 0-sorry partial > fake.
