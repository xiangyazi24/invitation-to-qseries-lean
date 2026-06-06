# TASK (codex / gpt-5.5): close the Ramanujan clean quintic via JTP-at-η (Hirschhorn §8.3 route)

## Context — why this spec exists
The Most Beautiful Identity is FULLY reduced (0 sorry/axiom, build 7994) to ONE
unconditional lemma: the `hfactor` hypothesis of
`RamanujanQuintic.clean_quintic_of_factor_pair_product`, i.e. the **clean quintic**
```
(G⁵ − βX·H⁵)(G⁵ − αX·H⁵) · expand 5 (qPochInfPS ℚ) = (qPochInfPS ℚ)^11
```
with `H = pentagonal014SeriesPS ℚ = (q,q⁴,q⁵;q⁵)∞`,
`G = pentagonal023SeriesPS ℚ = (q²,q³,q⁵;q⁵)∞`, and `α+β=11, αβ=−1`.
By `quintic_factor_pair_mul_eq_core` this LHS = `core·E(q⁵)` where
`core = G¹⁰ − 11X·G⁵H⁵ − X²·H¹⁰`. So you must prove `core·E(q⁵) = E(q)¹¹`
(= Hirschhorn (8.4.3)/(8.5.6), the "difficult and deep" identity). Numerically
verified to degree 80.

**4 previous rounds FAILED because they attacked the infinite product directly.
DO NOT do that. Follow the book's "easy" route below.**

## The book's route (Hirschhorn §8.3 → §8.5), which we missed

### Step 1 — the factor identities (8.3.1)/(8.3.2), "easy to establish" via JTP at a 5th root of unity
Let `η = primitive 5th root of unity`, `α = (1+√5)/2`, `β = (1−√5)/2` (so `η+η⁻¹=−β`,
`η²+η⁻²=−α`, and α,β are the Gaussian periods already built in this file:
`quinticPeriodAlpha`/`quinticPeriodBeta`, with `α+β=1, αβ=−1` — NOTE the book's α,β here
satisfy `x²−x−1`, i.e. `α+β=1`; the quintic factor pair uses the symmetric pair `α⁵,β⁵`
with `α⁵+β⁵`-type relations — keep the two conventions straight, see `neg_quinticPeriod_pow_five_*`).

The 2-variable Jacobi Triple Product (1.7.5)/(8.3.4):
```
(a⁻¹q, aq, q; q)∞ = ∑_{k≥0} (−1)ᵏ (aᵏ + a^{k−1} + ⋯ + a⁻ᵏ) q^{k(k+1)/2}
```
Set `a = η` (resp `a = η²`). Two things happen:
- **LHS product regroups**: `(1−η⁻¹qⁿ)(1−ηqⁿ) = 1 − (η+η⁻¹)qⁿ + q²ⁿ = 1 + βqⁿ + q²ⁿ`,
  so `(η⁻¹q,ηq,q;q)∞ = ∏ₙ(1+βqⁿ+q²ⁿ)(1−qⁿ) = E(q)·∏ₙ(1+βqⁿ+q²ⁿ)`.
- **RHS coefficient collapses** by residue mod 5 (Hirschhorn (8.3.5)):
  `ηᵏ+⋯+η⁻ᵏ ∈ {1, α, 0, −α, −1}` for `k ≡ {0,1,2,3,4} (mod 5)`, giving the 5-dissected theta
  `(q¹⁰,q¹⁵,q²⁵;q²⁵)∞ − αq(q⁵,q²⁰,q²⁵;q²⁵)∞ =: A − αqB`.
Hence (8.3.6)/(8.3.7) ⇒ (8.3.2)/(8.3.1):
```
E(q)·∏ₙ(1+βqⁿ+q²ⁿ) = A − αqB        (8.3.6 = 8.3.2)
E(q)·∏ₙ(1+αqⁿ+q²ⁿ) = A − βqB        (8.3.7 = 8.3.1)
```
where `A = (q¹⁰,q¹⁵,q²⁵;q²⁵)∞`, `B = (q⁵,q²⁰,q²⁵;q²⁵)∞`.

This RHS collapse `ηᵏ+⋯+η⁻ᵏ → {1,α,0,−α,−1}` is exactly the Gaussian-period algebra
already in this file. The `(1−η⁻¹qⁿ)(1−ηqⁿ)=1+βqⁿ+q²ⁿ` regroup is `scaleX`/`apFactorPS` level.

### Step 2 — 5th powers + η-collapse → (8.5.4)/(8.5.5)
Raise (8.3.1)/(8.3.2) to the 5th power and use the 5th-root product collapse
`∏_{j=0}^{4} (scaleX ηʲ · ∏(1+α qⁿ+q²ⁿ)) → ∏(1+α q⁵ⁿ+q¹⁰ⁿ)`-style. You ALREADY HAVE this:
`prod_scaleX_qPochFinitePS_fifth_collapse`, `quinticCyclotomic_qPochFinitePS_fifth_collapse`,
`scaleX_period_pair14/23_qPochFinitePS`. The book result is (8.5.4)/(8.5.5):
```
A⁵ − α⁵q⁵B⁵ = E(q)E(ηq)⋯E(η⁴q) · ∏(1+α q⁵ⁿ+q¹⁰ⁿ)⁵ ... (η-collapsed form)
```

### Step 3 — multiply (8.5.4)·(8.5.5) = (8.4.3) = clean quintic
`(A⁵ − α⁵q⁵B⁵)(A⁵ − β⁵q⁵B⁵) = A¹⁰ − (α⁵+β⁵)q⁵A⁵B⁵ + (αβ)⁵q¹⁰B¹⁰`. With α,β roots of
`x²−x−1`: `α⁵+β⁵ = 11`, `(αβ)⁵ = (−1)⁵ = −1`. So this `= A¹⁰ − 11q⁵A⁵B⁵ − q¹⁰B¹⁰` = the
core in A,B. Equate with the E-product side ⇒ `core·E(q⁵)=E(q)¹¹` (8.4.3).

### Step 4 — bridge A,B ↔ H=014/G=023
`A = (q¹⁰,q¹⁵,q²⁵;q²⁵) = scaleX 5` applied to `(q²,q³,q⁵;q⁵) = G`; similarly
`B = scaleX 5 (H)`. Reconcile the A,B-core with the `quinticProductCore ℚ H G`
expected by `clean_quintic_of_factor_pair_product` (watch the X-power / `expand` vs `scaleX`
bookkeeping — A,B live in q⁵, the core target is in q).

## Deliverable (largest with 0 sorry/axiom/admit)
NEW file `QseriesFormalization/Pending/RamanujanQuinticJTP.lean`, importing
`RamanujanQuintic`, `JTP_FormalPS_Pentagonal`, Ch16 MBI, the 2-variable JTP (Ch02/Ch03).
DO NOT edit other files or `QseriesFormalization.lean`/`Audit.lean`.
Prioritize:
1. **Step 1 first** — the factor identities (8.3.1)/(8.3.2) as formal-PS identities. This is
   the genuinely new unlock; even closing JUST these two unconditionally is major progress.
2. Then Steps 2–4 to discharge `hfactor` and produce an UNCONDITIONAL
   `most_beautiful_identity` (no hypotheses).
Report partial honestly — say exactly which of (8.3.1)/(8.3.2)/(8.5.4)/(8.5.5)/(8.4.3) are
closed and which remain. NO fake completion; verify with fresh `#print axioms`.

## Infra inventory (use, don't rebuild)
- `RamanujanQuintic.lean`: `scaleX`, `coeff_scaleX`, `scaleX_qPochFinitePS`, `scaleX_expand`,
  `prod_scaleX_qPochFinitePS_fifth_collapse`, `quinticCyclotomic_qPochFinitePS_fifth_collapse`,
  `quintic_factor_pair_mul_eq_core`, `quintic_factor_pair_mul_eq_core_of_gaussian_periods`,
  `quinticPeriodAlpha/Beta`, `neg_quinticPeriod_pow_five_sum/mul`,
  `scaleX_period_pair14/23_qPochFinitePS`, `section86_pair14_residue_{one..four}_local_factor`,
  `clean_quintic_of_factor_pair_product`, `most_beautiful_identity_of_compressed_E5_zero_bridge_and_factor_pair_product`.
- `JTP_FormalPS_Pentagonal.lean`: `qPochAPPS`, `pentagonalProduct014/023PS`,
  `pentagonal014/023SeriesPS`, `*_eq_pentagonal*SeriesPS_complex/_rat` (product=series).
- 2-variable analytic JTP: `Chapter03.finite_jacobi_triple_product`,
  `Chapter03.jacobiTripleProduct_of_gaussianWeightedTail_*` (q,z params, z≠0);
  `Chapter02.jacobiTripleProduct_q_zero`. Analytic→formal transfer template:
  `Pending/JacobiCubeAnalyticToFormal.lean` (B2), `Chapter19_B2_FromCubeConvolution`.
- `Ch16MBIProof`: `compressedSection5`, `ramanujanMod5ProductCoreThetaRat`,
  `most_beautiful_identity_of_compressed_theta_clean_quintic`, `qPochInfPS_five_dissection`.

## Build / verify (CRITICAL)
- NEVER `lake build` (rsync clobbers in-flight edits + mini RAM). Single-file:
  `scp` your new file to the-build-server, then `lake env lean QseriesFormalization/Pending/RamanujanQuinticJTP.lean`.
- 0 sorry / 0 axiom / 0 admit; confirm no `sorryAx` in fresh elaboration.
- Reply to `HANDOFF/outbox/codex-quintic-jtp-at-eta-reply.md` with the exact theorem names
  closed and `#print axioms` output for the top result.
