# TASK round 2 (codex / gpt-5.5): the actual JTP-at-η application → (8.3.1)/(8.3.2)

## What round 1 already did (DO NOT redo — it's committed in RamanujanQuinticJTP.lean)
All the SURROUNDING algebra is closed, 0 sorry: book α/β reconciliation
(`bookAlpha/bookBeta`, `bookPeriod_pow_five_sum : bookAlpha^5+bookBeta^5=11`), the η² local
residue factors, `prod_sub_scaled_primitive_fifth_powerSeries`
(`∏ⱼ (A − C(μʲc)B) = A^5 − C(c^5)B^5`), and `quintic_factor_pair_mul_eq_core_of_book_periods`.

**The ONE thing still open is the actual analytic content: the factor identities (8.3.1)/(8.3.2).**
Round 1 stopped exactly here. This round must close THIS, not add more algebra.

## The single deliverable
The two formal-PS identities (over ℂ, or over ℚ(ζ₅)):
```
(8.3.2):  E(q) · ∏_{k≥1}(1 + bookBeta·q^k + q^{2k}) = A − bookAlpha·q·B
(8.3.1):  E(q) · ∏_{k≥1}(1 + bookAlpha·q^k + q^{2k}) = A − bookBeta·q·B
```
where `A = (q^10,q^15,q^25;q^25)_∞`, `B = (q^5,q^20,q^25;q^25)_∞`, `E(q)=(q;q)_∞=qPochInfPS`.
(In the file these RHS objects may be `section83A`, `section83B`.)

## The ONLY viable route — generalize the keystone's transfer, do NOT attack the product directly
These ARE the Jacobi Triple Product `(z^{-1}q, zq, q; q)_∞ = ∑_{k∈ℤ}(−1)^k z^k q^{k(k+1)/2}`
specialized at `z = η` (resp `z = η²`), a primitive 5th root of unity:
- LHS factor regroups: `(1−η^{-1}q^k)(1−ηq^k) = 1 − (η+η^{-1})q^k + q^{2k} = 1 + bookBeta·q^k + q^{2k}`
  (since `η+η^{-1} = −bookBeta`). Times `(1−q^k)` gives `E(q)·∏(1+bookBeta q^k+q^{2k})`.
- RHS bilateral sum, regrouped by residue of `k mod 5` using the period collapse
  `η^k+⋯+η^{-k} ∈ {1,bookAlpha,0,−bookAlpha,−1}` (Hirschhorn (8.3.5)), becomes `A − bookAlpha·q·B`.

**The repo has NO free-`z` formal-PS JTP.** The keystone
`JTP_FormalPS_Pentagonal` proves product=series ONLY for the q^5-base triple products via the
analytic→formal transfer template (study it EXACTLY):
```
pentagonalProduct014PS_eq_pentagonal014SeriesPS_complex_of_productCoeff_taylor   -- JTP_FormalPS_Pentagonal.lean:1422
  uses: HasFPowerSeriesAt … .eq_formalMultilinearSeries  (both product-analytic & series share one FMLS)
        hasFPowerSeriesOnBall_pentagonal014ProductAnalytic_productCoeff   -- the hard dominated-convergence lemma
        pentagonal014ProductAnalytic / pentagonal014ProductCoeffFMLS / pentagonal014SeriesFMLS
```
**Your job:** build the analogous transfer for the **z=η product** `∏(1−η^{-1}q^k)(1−ηq^k)(1−q^k)`
and the theta series `A − bookAlpha·q·B`. Concretely, EITHER:
1. (preferred, reusable) Build a general 2-variable formal-PS JTP `twoVarJTP_PS (z : ℂ)` by
   GENERALIZING the keystone's `productAnalytic`/`ProductCoeffFMLS`/`eq_formalMultilinearSeries`
   pipeline from the fixed pentagonal case to a free unit `z` (the dominated-convergence /
   Tannery bound is uniform on `‖q‖ < r` for fixed `z` on the unit circle); then substitute
   `z = η`, `z = η²` and apply the period collapse. OR
2. (narrower) Directly mirror the keystone's three analytic lemmas for the specific η-product,
   reusing `Chapter03.jacobiTripleProduct_of_gaussianWeightedTail_dominated` /
   `jacobiTripleProduct_of_gaussianWeightedTail_tendsto` (the analytic 2-var JTP, params q,z, z≠0).

This is genuinely hard analytic work (the keystone's `productCoeff` lemma is the model). Spend
the effort on the dominated-convergence/FMLS-uniqueness core; the period-collapse RHS bookkeeping
is already done in `RamanujanQuintic`/`RamanujanQuinticJTP`. DO NOT just add more algebraic
scaffolding — the deliverable is the two product=theta identities themselves.

## Then (if (8.3.1)/(8.3.2) close): chain to the quintic
With (8.3.1)/(8.3.2) closed, raise to 5th power, apply
`prod_sub_scaled_primitive_fifth_powerSeries` (the conjugate collapse over μ=η), multiply the two,
use `bookAlpha^5+bookBeta^5=11`, `(bookAlpha·bookBeta)^5=−1` to get the A,B-core, then bridge
A=scaleX5(G or H)/B to `quinticProductCore` and discharge `hfactor` in
`RamanujanQuintic.clean_quintic_of_factor_pair_product` → unconditional MBI.

## Rules (unchanged)
- Edit ONLY `RamanujanQuinticJTP.lean` (you may add a new helper file if cleaner, but then say so).
  Do NOT touch `QseriesFormalization.lean`/`Audit.lean` (I wire those).
- NEVER `lake build`. Verify: `lake env lean QseriesFormalization/Pending/RamanujanQuinticJTP.lean`.
- 0 sorry/axiom/admit; fresh `#print axioms` clean. NO overclaiming — if (8.3.1)/(8.3.2) don't
  fully close, say so precisely and report what analytic sub-lemma blocked you.
- Reply to `HANDOFF/outbox/codex-quintic-jtp-round2-reply.md`.
