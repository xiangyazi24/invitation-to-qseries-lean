# TASK round 3 (codex / gpt-5.5): the η-period-collapse — the LAST blocker for (8.3.1)/(8.3.2)

## Excellent round-2 work — the product side is DONE
Round 2 closed (0 sorry, committed) the genuinely hard product-side analytic→formal transfer:
`hasFPowerSeriesOnBall_section83JTPProductAnalytic_productCoeff_small` plus the conditional
bridges `section83JTPProductPS_eq_rhs_pair14_of_rhs_taylor` / `..._pair23_...`. These say: once
the RHS Taylor expansion is supplied, `eq_formalMultilinearSeries` closes the factor identity.

## The ONLY remaining blocker (this round's sole deliverable)
Prove the two RHS η-period-collapse Taylor expansions:
```lean
HasFPowerSeriesOnBall (section83JTPProductAnalytic ζ)       (section83RhsPair14FMLS ζ) 0 1
HasFPowerSeriesOnBall (section83JTPProductAnalytic (ζ ^ 2)) (section83RhsPair23FMLS ζ) 0 1
```
where (recall your own defs):
- `section83JTPProductAnalytic z q = (q;q)∞ · (zq;q)∞ · (z⁻¹q;q)∞`  (the (8.3.4) LHS product)
- `section83RhsPair14 = section83A + C(quinticPeriodBeta ζ)·X·section83B`  (= `A + (ζ²+ζ³)qB`)
- `section83RhsPair23 = section83A + C(quinticPeriodAlpha ζ)·X·section83B`  (= `A + (ζ+ζ⁴)qB`)
- `section83A = expand 5 (pentagonal023SeriesPS)` = A = `(q¹⁰,q¹⁵,q²⁵;q²⁵)∞`
- `section83B = expand 5 (pentagonal014SeriesPS)` = B = `(q⁵,q²⁰,q²⁵;q²⁵)∞`

This is Hirschhorn (8.3.4)→(8.3.5)→(8.3.6): the JTP at a 5th root of unity, RHS bilateral sum
regrouped by residue `k mod 5` using `ηᵏ+⋯+η⁻ᵏ ∈ {1,α,0,−α,−1}`.

## Two candidate routes — pick whichever closes
### Route A — invoke the existing infinite analytic JTP (preferred if convention matches)
The repo HAS the full infinite 2-variable analytic JTP:
`PartI.Ch02.jacobiTripleProduct (q z : ℂ) (hq : ‖q‖<1) (hz : z≠0) : jacobiInfiniteProduct q z =
jacobiInfiniteSeries q z`, where `jacobiInfiniteSeries q z` is the symmetric `∑_{n∈ℤ} zⁿ q^{n²}`
(see `HasSum (fun n:ℤ => z^n q^(n^2)) (jacobiInfiniteSeries q z)`, Chapter03.lean ~line 441) and
`jacobiInfiniteProduct q z = ∏ jacobiProductNatFactor q z n`.
**WARNING — convention:** Ch02 uses the `q²`-base / `q^{n²}` symmetric form; your
`section83JTPProductAnalytic` is the base-`q` triangular `(q,zq,z⁻¹q;q)∞` form with `q^{k(k+1)/2}`.
You must reparametrize (Ch02 `q ↦ q^{1/2}` style, or match `jacobiProductNatFactor` to your
`constQFactorAnalytic` triple) and align the `z` argument. Identify
`section83JTPProductAnalytic ζ q` with `jacobiInfiniteProduct` at the right `(q,z)`, so by Ch02 JTP
it equals `∑_{n∈ℤ} ζⁿ q^{tri(n)}`; then regroup the sum by `n mod 5` (Gaussian-period collapse,
which you already built: `quinticPeriod_pair14_five_mul_add_*`) into `A + (ζ²+ζ³)qB`, and show that
series' FMLS equals `section83RhsPair14FMLS`.

### Route B — reuse the keystone product=series (avoids re-deriving JTP)
`section83A/B` are `expand 5` of `pentagonal023/014SeriesPS`, and the keystone already proves
`pentagonalProduct014/023PS = pentagonal014/023SeriesPS` (product=theta). The base-`q` η-product
`(q,ζq,ζ⁻¹q;q)∞` factors over `k mod 5`; grouping the `ζ^{±}` factors by residue and using your
`quinticQuadraticFactor` / `section83_pair*_residue_*_local_factor` lemmas may let you rewrite the
analytic η-product directly in terms of the `q⁵`-base pentagonal products (=A,B via keystone),
giving `A + (ζ²+ζ³)qB` without invoking Ch02's JTP. Then transfer to FMLS as in round 2.

## Rules
- Edit ONLY `RamanujanQuinticJTP.lean`. Do NOT touch `QseriesFormalization.lean`/`Audit.lean`.
- NEVER `lake build`. Verify `lake env lean QseriesFormalization/Pending/RamanujanQuinticJTP.lean`.
- 0 sorry/axiom/admit; fresh `#print axioms` clean. If still blocked, name the precise sub-lemma.
- If you close the two `HasFPowerSeriesOnBall` lemmas, IMMEDIATELY chain through the existing
  `section83JTPProductPS_eq_rhs_pair14/23_of_rhs_taylor` to get the unconditional (8.3.1)/(8.3.2),
  then 5th-power + `prod_sub_scaled_primitive_fifth_powerSeries` + multiply → discharge `hfactor`
  in `RamanujanQuintic.clean_quintic_of_factor_pair_product` → state the UNCONDITIONAL MBI.
- Reply to `HANDOFF/outbox/codex-quintic-jtp-round3-reply.md`.
