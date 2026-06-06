# Work Log — q-series Formalization

## 2026-05-13 — Quintuple Product Identity closed end-to-end

`quintupleProduct_identity` is now fully proved (Chan Theorem 4.4 /
equation (2.12)). Closed the last three sorries inside
`quintuple_theta_kernel_eval` plus the dead Route B sorry.

Route A is the active proof path; Route B (uniform-tail bridge through
`tendsto_qPoch_qsix_mul_combinedMonomialSum`) is deleted as dead.

Key sub-results introduced:

- **`qpoch_q4_residue_split`** (Ch04 ~line 3800).
  Identity `(∏'_{m} 1 - q^(12m+4)) · (∏'_{m} 1 - q^(12m+8)) · (∏'_{m} 1 - q^(12m+12))
  = ∏'_{m} 1 - q^(4m+4)`. Proof avoids the `Nat.divModEquiv 3` →
  `Multipliable.tprod_prod` path (which times out at 1.6M heartbeats due
  to the `tprod_prod` `T0Space`/`CompleteSpace` class-search chain) by
  proving the exact finite identity
  `∏_{m∈range N} f₄ · ∏_{m∈range N} f₈ · ∏_{m∈range N} f₁₂
   = ∏_{m∈range (3N)} f_full` by induction on `N`, taking limits on both
  sides, and concluding via `tendsto_nhds_unique`. (ChatGPT collab gave
  this tactic; otherwise we'd have been stuck on the heartbeat ceiling.)

- **`jacobiInfiniteSeries_qsq_iterate_int`** (Ch04 ~line 3895).
  ℤ-iterated form of `Ch02.jacobiInfiniteSeries_qsq_mul`:
  `JTP(q, q^(2n) · z) = q^(-(n·n)) · z^(-n) · JTP(q, z)` for `n : ℤ`.
  Direct reindex via `(Equiv.addRight n).tsum_eq` — single equiv shift
  of the bilateral series, no induction needed.

- **`hI0`/`hI2`** (inside `quintuple_theta_kernel_eval`).
  Residue evaluations
  `I(3n)   = (-1)^n · q^(-(6n²+2n))      · P`,
  `I(3n+2) = (-1)^(n+1) · q^(-(6n²+10n+4)) · P`,
  for `n : ℤ`. Each is proved by:
    1. `hI_eq_jtp`: rewrite `I(k)` as `JacobiInfiniteSeries (q^6) (-q^(-(4k+2)))`.
    2. Reformat the argument as `(q^6)^(2k') · (-q^(±2))` for appropriate `k'`
       (`k' = -n` for `hI0`, `-(n+1)` for `hI2`).
    3. Apply `jacobiInfiniteSeries_qsq_iterate_int` to factor out the shift.
    4. Identify the base point as `P`: `hI0_eq_P` for `JTP(q^6, -q⁻²) = P`,
       and `hI_neg1_eq_P` for `JTP(q^6, -q²) = P`, both routed through
       `qpoch_q4_residue_split` after a Nat-pow form of `hfactor`.
    5. Simplify `(q^6)^(-(n²))·(-q^(±2))^n` via `mul_zpow` + `zpow_mul`.

- **`hsplit`** (inside `quintuple_theta_kernel_eval`).
  Mod-3 partition identity
  `∑'_{k∈ℤ} (-1)^k · z^k · q^(k²) · I(k) = P · ∑'_{n∈ℤ} quintupleProductSeriesTerm q z n`.
  Proof:
    1. Define `A`, `B` matching the two summands of `quintupleProductSeriesTerm`
       (so `qpsterm n = A n - B n`), both summable as JTP series at `q^3` base.
    2. Compute `F(3n) = P·A n`, `F(3n+1) = 0`, `F(3n+2) = P·(-B(-n-1))`
       (algebraic via `hI0`/`hI1`/`hI2`).
    3. Build `HasSum` on each coset, compose via `HasSum.sum` along the
       disjoint-union equiv `ℤ ⊕ (ℤ ⊕ ℤ) ≃ ℤ` (built from
       `(Int.divModEquiv 3).trans prodFin3ToSum`).
    4. Transfer to `HasSum F (S_a + 0 + S_c)` via `Equiv.hasSum_iff`,
       conclude `∑' F = P · (∑' A + ∑' (-B)) = P · ∑' qpsterm`.

- **Dead Route B removed**: `eventually_norm_qPoch_mul_quintupleCombinedMonomialTail_le`
  + `uniform_tail_qPoch_mul_quintupleCombinedMonomial`
  + `tendsto_qPoch_qsix_mul_combinedMonomialSum` deleted.
  Upstream `qPoch_qsix_mul_quintupleCombinedMonomial*` definitions and
  `tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomial*` theorems retained
  as scaffolding (in case useful for future bridges).

Collab notes: ChatGPT-webapp bridge was used for two tactic-level
sub-problems (the partial-product trick on `qpoch_q4_residue_split` and
the HasSum-decomposition structure on `hsplit`). Bridge plugin's
`textContent` was stripping newlines from code blocks; fixed by
changing to `innerText` in `~/repos/chatgpt-bridge/extension/content.js`
(reload required to take effect).

Stats: ~320 lines added, 7 commits, 0 sorries remaining in Chapter04.

## 2026-05-07

### Batch 66 — Ch09 q-PS kernel definitions + j=n boundary + conditional general Bailey lemma

- Added definitions:
  - `baileyKernelSum a q ρ₁ ρ₂ n j`: the inner sum from
    `BaileyTransformBeta_of_pair_double_sum` over `k ∈ filter (j ≤ ·) (range (n+1))`.
  - `baileyKernelTarget a q ρ₁ ρ₂ n j`: the q-Pfaff–Saalschütz right-hand side
    `(ρ₁;q)_j (ρ₂;q)_j (aq/(ρ₁ρ₂))^j /
       ((aq/ρ₁;q)_j (aq/ρ₂;q)_j (q;q)_(n-j) (aq;q)_(n+j))`.
- Proved boundary case `baileyKernelSum_eq_target_n`:
  for `j = n`, the filter `(range (n+1)).filter (n ≤ ·) = {n}` and the
  resulting single-term simplification reduces (via `simp [div_div]`) to
  `baileyKernelTarget`.
- Added `BaileyTransform_preserves_pair_general`: the structural Bailey
  preservation theorem, taking
  `hkernel : ∀ j ∈ range (n+1),
     baileyKernelSum a q ρ₁ ρ₂ n j = baileyKernelTarget a q ρ₁ ρ₂ n j`
  as an explicit hypothesis. Proof composes
  `BaileyTransformBeta_of_pair_double_sum` (Batch 65),
  `BaileyBeta_transformAlpha_eq` (Batch 64), and `hkernel` pointwise via
  `Finset.sum_congr` + `ring`. No `sorry`, no `axiom`.
- Validation: `lake build QseriesFormalization.Chapter09` →
  `Built QseriesFormalization.Chapter09 (459s)`, 7886 jobs, no errors,
  no warnings, no sorry, no axiom.
- Net effect: the entire structural side of Bailey's lemma is now
  formalized end-to-end. The single remaining analytic input is the
  q-Pfaff–Saalschütz (Jackson) summation
  `baileyKernelSum n j = baileyKernelTarget n j` for `1 ≤ j ≤ n - 1`.
  The j = n case is unconditional; j = 0 is itself an instance of the
  q-Saalschütz formula (not a base case) and is the next attack target.

### Batch 65 — Ch09 triangular Fubini swap for the Bailey expansion

- Proved `BaileyTransformBeta_of_pair_double_sum`: the central re-indexing
  step in Bailey's lemma. Under `IsBaileyPairUpTo a q α β n`,

      BaileyTransformBeta a q ρ₁ ρ₂ β n =
        ∑ j ∈ range (n + 1),
          α j *
            ∑ k ∈ (range (n + 1)).filter (· ≥ j),
              baileyTransformCoeff a q ρ₁ ρ₂ n k /
                (qPochhammer q (k - j) * qPoch (a * q) q (k + j))

- Proof structure (the codex `c754eda` attempt failed at all four steps,
  including a misuse of `Finset.sum_comm` on a non-rectangular sum):
  1. `BaileyTransformBeta_of_pair` rewrites the LHS as
     `∑ k, coeff(n,k) * ∑ j ∈ range (k+1), BaileyTerm a q α k j`.
  2. Pull `coeff(n,k)` and `α j` together into one named integrand
     `F k j = coeff(n,k) * α j / ((q;q)_(k-j) * (aq;q)_(k+j))`.
  3. Replace each inner `range (k + 1)` by
     `(range (n + 1)).filter (· ≤ k)` so the inner Finset is fixed.
  4. Apply Fubini on the rectangle `range (n+1) × range (n+1)` via
     `simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]`.
  5. Re-fold the resulting indicator sum back into a `filter`,
     factor `α j` out of each inner sum, and discharge by `ring`.
- Validation: `lake build QseriesFormalization.Chapter09` →
  `Built QseriesFormalization.Chapter09 (516s)`, 7886 jobs, no errors,
  no warnings, no sorry, no axiom. Chapter09 7782 → 7847 lines (+65).
- This is the structural Fubini step needed before the q-Pfaff–Saalschütz
  kernel evaluation. Together with `BaileyBeta_transformAlpha_eq`, the
  general Bailey-pair preservation theorem now reduces cleanly to the
  pointwise q-PS kernel identity `baileyKernelSum n j = baileyKernelTarget n j`.

### Batch 64 — Ch09 restore Bailey bridge lemmas (sorry-free)

- Restored two bridge lemmas reverted in Batch 62, this time test-first:
  - `BaileyTransformBeta_of_pair`: under
    `IsBaileyPairUpTo a q α β n`, rewrites
    `BaileyTransformBeta a q ρ₁ ρ₂ β n` as
    `∑ k, baileyTransformCoeff(n,k) * ∑ j ∈ range (k+1), BaileyTerm a q α k j`
    by collapsing `β k = BaileyBeta a q α k` via `Finset.sum_congr` and
    `BaileyBeta_eq_sum`. (Codex's prior version had `.symm` in the wrong
    direction; removed.)
  - `BaileyBeta_transformAlpha_eq`: explicit `Finset.sum` form of
    `BaileyBeta a q (BaileyTransformAlpha ρ₁ ρ₂ α) n`, unfolding
    `BaileyTransformAlpha` and `BaileyTerm` via `simp` (no remaining
    open goal — codex's prior version stopped at `simp only` and left
    the residual unsolved).
- Validation: `lake build QseriesFormalization.Chapter09` →
  `Built QseriesFormalization.Chapter09 (515s)`, 7886 jobs, no errors,
  no warnings. Chapter09 7760 → 7782 lines (+22).
- These are the two pre-q-PS structural rewrites needed to state and
  attack the general preservation theorem; the remaining gap is the
  double-sum swap and the q-Pfaff–Saalschütz kernel identity itself.

### Batch 63 — Ch07 Rogers–Ramanujan functional equation `J(x) − J(xq) = xq · J(xq²,N−1)`

- Defined the generalized Rogers–Ramanujan partial sum
  `rrJ x q : Nat → R` (Chan §7.1) by `rrJ x q 0 = 1` and
  `rrJ x q (n+1) = rrJ x q n + xⁿ⁺¹ q^{(n+1)²} / (q;q)_{n+1}`.
- Bridge lemmas: `rrJ_zero`, `rrJ_succ`, `rrJ_eq_natSum`,
  `rrJ_one_eq_lhsTrunc_zero`, `rrJ_q_eq_lhsTrunc_one`,
  `rrJ_connects_to_lhsTrunc`.
- Termwise identity: `rrJTermDiff_eq` —
  `xⁿ q^{n²} (1 − qⁿ) / (q;q)_n = x · q · (xq²)^{n−1} q^{(n−1)²} / (q;q)_{n−1}`
  for `n ≥ 1`, after simplifying via `qPochhammer_succ`.
- Closed-form base cases verified: `rrJ_functional_eq_zero`,
  `rrJ_functional_eq_one`, `rrJ_functional_eq_two`.
- General theorem: `rrJ_functional_eq` — for all `N` and all `x q`
  with `qPochhammer q m ≠ 0` for `m ≤ N+1`,
  `rrJ x q (N+1) − rrJ (xq) q (N+1) = xq · rrJ (xq²) q N`. Proof by
  induction on `N` using `rrJ_succ_diff` and `rrJTermDiff_succ_eq_xq_shifted`.
- Validation: `lake build QseriesFormalization.Chapter07` →
  `Build completed successfully (7886 jobs)`. `rg -n "sorry|axiom"
  QseriesFormalization/Chapter07.lean` → no matches.
- This is the structural input that turns the existing finite
  `rogersRamanujanLHSTrunc` truncations into the Chan §7.1 functional
  equation; downstream Ch07 work can now factor the Rogers–Ramanujan
  identity through `rrJ` instead of opening the partial sums by hand.

### Batch 62 — Ch09 General Bailey framework: revert broken section, restore 0-sorry

- Prior commit `c754eda` ("Ch09: general Bailey lemma framework + double-sum
  swap infrastructure") landed without a clean `lake build` and broke the
  project's 0-sorry / 0-error baseline. Pre-existing errors:
  `BaileyTransformBeta_of_pair` (`.symm` direction, `Finset.sum_comm` on a
  non-double-sum), `BaileyTransformBeta_of_pair_double_sum` (orphan `open
  Finset in` before doc comment), `baileyKernelSum_eq_target_zero` (typeclass
  metavar from premature `simp`), `baileyKernelSum_eq_target_n` (`simp` no
  progress), and `BaileyTransform_preserves_pair_general` (`sorry`).
- Reverted everything in the `GeneralBaileyLemma` section after
  `baileyTransformCoeff`. Kept only the verifiable bridge layer:
  - `natSum_eq_sum_range'`
  - `BaileyBeta_eq_sum`
  - `BaileyTransformBeta_eq_sum`
  - `baileyTransformCoeff` (noncomputable def)
  - `BaileyTransformBeta_eq_sum_coeff` (proof:
    `rw [BaileyTransformBeta_eq_sum]; simp only [baileyTransformCoeff]`)
- Validation: `lake build QseriesFormalization.Chapter09` →
  `Built QseriesFormalization.Chapter09 (435s)`, 7886 jobs, no errors,
  no warnings. `rg -n "sorry|axiom" QseriesFormalization/Chapter09.lean` →
  no matches.
- Net: Chapter09 7883 → 7760 lines (–123). The double-sum swap, kernel
  identity, and general preservation theorem are deferred to a future batch
  and must be developed test-first.

## 2026-04-30

### Phase 0 — directory reorganization (Zinan, completed)
- Created `Basic.lean` housing partition / triangular / pentagonal /
  qPochhammer / natSum / gaussianBinom (root namespace
  `QseriesFormalization`).
- Renamed `Chapter1.lean..Chapter4.lean` → `Chapter01.lean..Chapter04.lean`,
  re-namespaced under `QseriesFormalization.PartI.ChNN`.
- Created stubs `Chapter05.lean..Chapter20.lean` (each in their respective
  `PartI/PartII/PartIII/PartIV.ChNN` sub-namespace).
- Updated `QseriesFormalization.lean` (root) and `Exercises.lean` import lists.
- `lake build` clean (7908 jobs).
- Commit: see `git log` for "Phase 0: reorganize into Basic.lean +
  Chapter01-20.lean stubs".

### Phase 1 — digesting Ch 1-4 axioms (Zinan, in progress)
- **Task 01** dispatched to codex (5.3 spark): extend
  `finiteQBinomialTheorem` from `n ≤ 1` to all `n`. Reply file:
  `HANDOFF/outbox/01-qbinomial-induction-reply.md`.

## 2026-05-01

### Tasks 62-76 Verification & Implementation
- Verified tasks 62-64, 66-74 and 76 are correctly implemented in their respective Lean files.
- Implemented task 75 in `QseriesFormalization/Chapter08.lean`.
- Created reply files for all verified/implemented tasks in `HANDOFF/outbox/`.
- Ran `lake build` to ensure the project builds correctly without new warnings/errors.

### Notes
- The PDF series side in Chan's Theorem 2.1 uses `q^{n^2}`, not
  `q^{triangular(n)}`. Our existing `jacobiSeriesTrunc` uses triangular
  numbers — this is a different normalization variant of JTP. To resolve
  before finishing Ch 2.
- Generalized q-Pochhammer `(a; q)_n = ∏_{k=0}^{n-1}(1 - a q^k)` is what
  Chan uses pervasively (Eq 1.5). Our current `qPochhammer q n` only
  encodes `(q; q)_n`. We should add a general version
  `qPoch (a q : R) (n : Nat) : R` and rephrase later chapters around it.
- Ch 2 / Ch 4 axioms for `jacobiInfiniteProduct` etc. need either a
  `tprod`-based analytic definition (under |q|<1 assumption with topology)
  or a formal Laurent-series-in-`z` approach. To revisit after Ch 3.

## 2026-05-06

### Ch09 Bailey N=6 maintenance
- Fixed `BaileyTransform_six_qpoch_ratio_ten_eleven`: for
  `qPoch (a * q) q n`, the adjacent ratio from `10` to `11` is
  `1 - a * q ^ 11`.
- Removed redundant `ring` calls after `field_simp` in two small q-Pochhammer
  ratio lemmas.
- Added `BaileyTransformAlpha_rrAlpha_six`, completing the explicit RR-seed
  transform evaluations through `n = 6`.
- Added the remaining `N = 6` transformed-α coefficient infrastructure:
  α₀/α₁/α₂/α₃/α₄ support ratios, common-denominator identities, and
  coefficient identities, completing all seven α₀..α₆ coefficient cases.
- Added `BaileyBeta_transformAlpha_six_terms_linear`,
  `BaileyTransform_preserves_pair_six_of_nonzero`, and
  `BaileyTransform_preserves_pair_upTo_six_of_nonzero`, so the finite
  Bailey-transform preservation package now reaches `N = 6`.
- Validation: `lake env lean QseriesFormalization/Chapter09.lean`;
  `lake build` completed successfully, with only the pre-existing Chapter02
  `jacobiTripleProduct` `sorry` warning.

### Ch02 Jacobi Triple Product convergence foundations
- Added `summable_jacobiSeries_nat` and
  `summable_jacobiInfiniteSeries_terms`, proving summability of the one-sided
  and bilateral Jacobi series for `‖q‖ < 1`.
- Added geometric norm helpers and `multipliable_jacobiInfiniteProduct_factors`,
  proving the infinite product side is multipliable for `‖q‖ < 1`.
- Added `hasProd_jacobiInfiniteProduct_factors` and
  `hasSum_jacobiInfiniteSeries_terms`, connecting the definitions directly to
  Mathlib's `HasProd`/`HasSum` semantics. The remaining Ch02 gap is now the
  equality proof, not basic convergence of either side.
- Added `jacobiInfiniteSeries_qsq_mul`, the bilateral series functional
  equation `F(q²z) = q⁻¹ z⁻¹ F(z)` for `q,z ≠ 0`, using integer reindexing
  through `Equiv.addRight`.
- Added `jacobiInfiniteProduct_zero`, `jacobiInfiniteSeries_zero`, and
  `jacobiTripleProduct_q_zero`, closing the degenerate `q = 0` case of JTP.
- Added Nat-indexed product-side factors
  `jacobiProductEvenFactor`, `jacobiProductOddFactor`,
  `jacobiProductNatFactor`, plus
  `jacobiInfiniteProduct_eq_tprod_natFactor`, exposing the product as a
  zero-based `ℕ` tprod for the next product functional-equation step.
- Added component multipliability and splitting lemmas
  `multipliable_jacobiProductEvenFactor`,
  `multipliable_jacobiProductOddFactor`, and
  `jacobiInfiniteProduct_eq_tprod_components`.
- Added `jacobiInfiniteProduct_qsq_mul_uncancelled`, the product-side
  functional equation
  `(1 + z*q) P(q²z) = (1 + z⁻¹*q⁻¹) P(z)` for `q ≠ 0`, avoiding a
  nonzero assumption on `1 + z*q`.
- Added `jacobiInfiniteProduct_zero_of_one_add_z_mul_q_eq_zero` and the
  cancelled product-side functional equation `jacobiInfiniteProduct_qsq_mul`,
  matching the series-side equation `P(q²z) = q⁻¹ z⁻¹ P(z)` for `q,z ≠ 0`.
- Added finite-limit interfaces for both sides:
  `jacobiProductPartial`, `jacobiProductPartial_eq_qPoch`,
  `multipliable_jacobiProductNatFactor`, `hasProd_jacobiProductNatFactor`,
  `tendsto_jacobiProductPartial`, `jacobiSeriesSymmetricPartial`, and
  `tendsto_jacobiSeriesSymmetricPartial`.
- Added the symmetric nonzero-pair expansion of the series partials:
  `jacobiSeriesSymmetricPairTerm`, `jacobiSeriesSymmetricPairPartial`,
  `jacobiSeriesSymmetricPartial_succ`,
  `jacobiSeriesSymmetricPartial_eq_one_add_pairPartial`, and
  `tendsto_jacobiSeriesSymmetricPairPartial`.
- Added the symmetric nonzero-pair tail package:
  `jacobiSeriesSymmetricPairTail`,
  `jacobiSeriesSymmetricPairPartial_eq_add_tail`,
  `jacobiSeriesSymmetricPairNormMajorant`,
  `summable_jacobiSeriesSymmetricPairTerm_neg`,
  `summable_jacobiSeriesSymmetricPairTerm_pos`,
  `summable_jacobiSeriesSymmetricPairTerm`,
  `summable_jacobiSeriesSymmetricPairNormMajorant`,
  `norm_jacobiSeriesSymmetricPairTerm_le_majorant`,
  `hasSum_jacobiSeriesSymmetricPairTerm`,
  `hasSum_jacobiSeriesSymmetricPairTerm_tail`, and
  `tsum_jacobiSeriesSymmetricPairTerm_tail`, identifying the pair tail from
  index `M` with `jacobiInfiniteSeries - jacobiSeriesSymmetricPartial M`.
- Added the product-minus-series difference package:
  `jacobiDifference`, `jacobiDifference_qsq_mul`,
  `jacobiDifference_qsq_mul_iterate`, and
  `jacobiDifference_qsq_mul_iterate_eq_zero_iff`, giving propagation and
  zero-invariance along nonzero `q²`-orbits.
- Added the even-factor q-Pochhammer/normalization package:
  `jacobiProductEvenFactor_ne_zero`,
  `qPochhammer_qsq_eq_jacobiProductEvenPartial`,
  `qPoch_qsq_eq_jacobiProductEvenPartial`, `tendsto_qPoch_qsq`, and
  `tprod_jacobiProductEvenFactor_ne_zero`.
- Added the Ch03 bridge
  `jacobiProductPartial_eq_qPoch_mul_finiteJTPRHS`, connecting the Ch02
  finite product partials to Chapter 3's finite JTP RHS under
  `q ↦ q²`, `z ↦ -zq`.
- Added the Ch03 weighted Laurent finite-sum form:
  `finiteJTPSummand_qsq_neg_zq`, `finiteJTPRHS_qsq_neg_zq`, and
  `jacobiProductPartial_eq_qPoch_mul_weightedLaurentSum`, rewriting the
  substituted finite JTP RHS as Gaussian factors times `z^l q^{l²}`.
- Added centered Gaussian coefficient q-Pochhammer product forms:
  `gaussianBinom_center_add_mul_qPochhammer_eq` and
  `gaussianBinom_center_sub_mul_qPochhammer_eq`, specializing
  `[2N, N±r]_q (q;q)_{N±r} (q;q)_{N∓r} = (q;q)_{2N}`.
- Added the centered Gaussian finite-limit coefficient package:
  `qPochhammer_qsq_ne_zero`,
  `qPoch_mul_gaussian_center_add_eq_ratio`,
  `qPoch_mul_gaussian_center_sub_eq_ratio`,
  `tendsto_qPoch_qsq_two_mul`,
  `tendsto_qPoch_mul_gaussian_center_add`, and
  `tendsto_qPoch_mul_gaussian_center_sub`.
- Added fixed symmetric-pair finite-limit interfaces:
  `tendsto_qPoch_mul_gaussian_center_pair`,
  `gaussianWeightedPairTerm`, `gaussianWeightedPairPartial`, and
  `tendsto_qPoch_mul_gaussianWeightedPairPartial`, proving that any fixed
  finite block of Gaussian-weighted pairs converges to Ch02's symmetric
  series pair partial after multiplying by `(q²;q²)_N`.
- Added finite tail splitting interfaces:
  `gaussianWeightedPairTail`, `gaussianWeightedPairPartial_eq_add_tail`, and
  `gaussianWeightedSymmetricPartial_eq_add_tail`, separating the full
  `N`-pair centered Gaussian block into a fixed first `M` block plus the
  remaining finite nonzero-pair tail.
- Added `tendsto_qPoch_mul_gaussianWeightedPairTail`, proving convergence of
  every fixed finite Gaussian tail block to the corresponding Chapter 2
  finite symmetric pair tail.
- Added zero-extended shifted Gaussian tail infrastructure:
  `tendsto_qPoch_mul_gaussianWeightedPairTerm`,
  `gaussianWeightedTailSummand`, `tendsto_gaussianWeightedTailSummand`,
  `qPoch_mul_gaussianWeightedPairTail_eq_shiftedRange_sum`,
  `qPoch_mul_gaussianWeightedPairTail_eq_shiftedTailSummand_sum`, and
  `tsum_gaussianWeightedTailSummand`, rewriting the moving tail as a `tsum`
  over a zero-extended shifted summand family.
- Added the fixed symmetric-partial wrapper:
  `gaussianWeightedSymmetricPartial` and
  `tendsto_qPoch_mul_gaussianWeightedSymmetricPartial`, adding the centered
  `l = 0` term to the fixed pair block and proving convergence to
  `jacobiSeriesSymmetricPartial`.
- Added weighted Laurent reindexing infrastructure:
  `natSum_eq_sum_range`, `gaussianWeightedLaurentSummand`, and
  `gaussianWeightedSymmetricPartial_eq_weightedLaurentNatSum`, proving that
  the finite-JTP `k = 0..2N` weighted Laurent sum is exactly the centered
  symmetric block with its terms reordered.
- Added `jacobiProductPartial_eq_qPoch_mul_gaussianWeightedSymmetricPartial`,
  restating the Ch02 finite product partial directly in the centered
  symmetric-block form used by the fixed symmetric partial convergence
  theorem.
- Added `jacobiProductPartial_eq_qPoch_mul_fixedSymmetricPartial_add_tail`,
  exposing the finite product partial as the fixed centered symmetric block
  plus the remaining finite Gaussian pair tail.
- Added `jacobiTripleProduct_of_gaussianWeightedTail_tendsto`, reducing the
  nonzero-`q` JTP proof to the single remaining analytic claim that the
  Gaussian finite tail converges to the bilateral series tail.
- Added `jacobiTripleProduct_of_gaussianWeightedTail_tendsto_tsum`, the same
  reduction with the target expressed as the `tsum` of the Chapter 2
  symmetric pair tail.
- Added `jacobiTripleProduct_of_gaussianWeightedTail_dominated`, applying
  Mathlib's Tannery theorem to reduce the remaining JTP proof to a summable
  domination bound for `gaussianWeightedTailSummand`.
- Added `jacobiTripleProduct_of_gaussianWeightedTail_norm_le_seriesTail`,
  reducing that domination bound further to a constant multiple of the Chapter
  2 symmetric pair-tail norm, whose summability follows from the existing
  pair-term summability theorem.
- Added `jacobiTripleProduct_of_gaussianWeightedTail_norm_le_pairMajorant`,
  replacing the cancellation-sensitive pair-tail norm by a summable two-term
  norm majorant.
- Added the final Gaussian-tail domination package:
  `exists_qPoch_mul_gaussian_center_norm_bound`,
  `exists_gaussianWeightedTailSummand_pairMajorant_bound`, and
  `jacobiTripleProduct_via_finiteJTP`.
- Removed the Chapter 2 placeholder `sorry` and exported the completed theorem
  as `Ch02.jacobiTripleProduct` from Chapter 3, avoiding an import cycle while
  keeping the theorem in the Chapter 2 namespace.
- Added the first Chapter 4 post-JTP bridge:
  `eulerPentagonalJacobiSeries` and `eulerPentagonalProduct_eq_jacobiSeries`,
  connecting the existing `z = -1` specialization to the completed
  `Ch02.jacobiTripleProduct`.
- Added explicit bilateral theta forms for that specialization:
  `eulerPentagonalProduct_eq_jacobi_tsum` and
  `eulerPentagonalJacobiSeries_eq_tsum`,
  `summable_eulerPentagonal_jacobi_terms`, and
  `hasSum_eulerPentagonal_jacobi_terms`.
- Added the matching product-side specialization:
  `eulerPentagonalJacobiProductFactor`,
  `eulerPentagonalProduct_eq_tprod_natFactor`, and
  `hasProd_eulerPentagonal_jacobi_factors`.
- Added the product-side algebra for Chan's actual Euler pentagonal
  substitution, parameterized by `Q^2 = q^3` and `z = -Q/q^2`:
  `eulerPentagonalCubicProductFactor`, the three factor-level substitution
  lemmas, `jacobiProductNatFactor_eulerPentagonal_substitution`,
  `jacobiInfiniteProduct_eulerPentagonal_substitution_eq_tprod`, and
  `hasProd_eulerPentagonal_cubic_factors`.
- Added the finite residue-class product skeleton
  `eulerPentagonalCubicProduct_partial_eq_qPochhammer`, proving that the first
  `N` cubic factors multiply to `(q;q)_{3N}`.
- Added the direct finite interface
  `jacobiProductPartial_eulerPentagonal_substitution`, rewriting Ch02's
  `jacobiProductPartial` under the same Euler substitution to `(q;q)_{3N}`.
- Added the series-side algebra for the same substitution:
  `jacobiSeriesTerm_eulerPentagonal_substitution`,
  `jacobiInfiniteSeries_eulerPentagonal_substitution_eq_tsum_minus`,
  `eulerPentagonal_tsum_minus_eq_plus`, and
  `jacobiInfiniteSeries_eulerPentagonal_substitution_eq_tsum_plus`.
- Added `eulerPentagonal_cubicProduct_eq_tsum`, combining the product-side
  substitution, completed JTP, and series-side reindexing into the cubic
  residue product identity with Chan's exponent `j(3j+1)/2`.
- Added the ordinary Euler product layer:
  `eulerPentagonalProductFactor`, `eulerPentagonalInfiniteProduct`,
  `multipliable_eulerPentagonalProductFactor`,
  `hasProd_eulerPentagonalProductFactor`,
  `eulerPentagonalProductFactor_partial_eq_qPochhammer`, and
  `tendsto_eulerPentagonalProductTrunc`.
- Added independent convergence for the cubic residue product and the product
  regrouping theorem
  `eulerPentagonalInfiniteProduct_eq_tprod_cubicProductFactor`, using the
  shared subsequence limit `(q;q)_{3N}`.
- Added `eulerPentagonalInfiniteProduct_eq_tsum_of_sq`, combining ordinary
  Euler product regrouping with the JTP substitution identity under a chosen
  `Q` satisfying `Q^2 = q^3`.
- Added `exists_eulerPentagonal_substitution_sqrt` and the final
  `eulerPentagonalInfiniteProduct_eq_tsum`, removing the auxiliary `Q` by
  choosing a complex square root of `q^3` and proving it remains in the open
  unit disc.
- Added the quintuple product left-side infinite product interface:
  `quintupleProductFactor`, `quintupleProductLHS`,
  `quintupleProductFactor_partial_eq_trunc`,
  `multipliable_quintupleProductFactor`, `hasProd_quintupleProductFactor`,
  and `tendsto_quintupleProductLHSTrunc`.
- Added Chapter 4 exercise wrappers for the quintuple product left-side finite
  and convergence interfaces.
- Added the quintuple product right-side Jacobi-series interface:
  `quintupleProductSeriesTerm`, `quintupleProductRHS`,
  `summable_quintupleProductSeriesTerm`, and
  `hasSum_quintupleProductSeriesTerm`, reusing Ch02 bilateral Jacobi-series
  summability with base `q^3`.
- Added Chapter 4 exercise wrappers for the new quintuple RHS summability and
  `HasSum` interfaces.
- Added `quintupleProductRHS_eq_jacobiSeries_sub` and
  `quintupleProductRHS_eq_jacobiProduct_sub`, rewriting the quintuple RHS as
  a difference of two Jacobi bilateral series and then, under `q,z ≠ 0`, as a
  difference of two Jacobi triple products.
- Added Chapter 4 exercise wrappers for both RHS-to-JTP bridges.
- Added explicit Nat-indexed JTP product factors for the quintuple product
  proof: `quintupleJacobiLeftFactor`, `quintupleJacobiRightFactor`, the two
  `jacobiProductNatFactor_quintuple_*_substitution` lemmas, and
  `quintupleProductRHS_eq_explicitProduct_sub`.
- Added a Chapter 4 exercise wrapper for the explicit-product RHS bridge.
- Added finite partial products for the two explicit JTP factor families:
  `quintupleJacobiLeftPartial`, `quintupleJacobiRightPartial`, their
  `jacobiProductPartial_quintuple_*_substitution` bridges, multipliability
  packages, and `tendsto_quintupleJacobi*Partial`.
- Added Chapter 4 exercise wrappers for the new explicit JTP partial and
  convergence interfaces.
- Verified the PDF statement of Eq. (2.12) and Theorem 4.4. Added the
  Theorem 4.4 product-side interface `theorem44ProductFactor` and
  `theorem44ProductLHS`, plus factor-level and infinite-product bridges
  showing that the substitution `q ↦ q^2`, `z ↦ z/q` gives the existing
  Eq. (2.12) quintuple product side.
- Added Chapter 4 exercise wrappers for the Theorem 4.4 substitution bridges.
- Added the substituted Theorem 4.4 series-side interface:
  `theorem44SubstitutedQuadraticIndex`, `theorem44SubstitutedSeriesTerm`,
  and `theorem44SubstitutedSeriesRHS`, plus term-level and `tsum` bridges to
  the existing Eq. (2.12) RHS `quintupleProductRHS`.
- Added Chapter 4 exercise wrappers for the substituted Theorem 4.4
  series-side bridges.
- Added `summable_theorem44SubstitutedSeriesTerm` and
  `hasSum_theorem44SubstitutedSeriesTerm`, inherited from the Eq. (2.12) RHS
  summability through the substituted-series bridge.
- Added Chapter 4 exercise wrappers for these substituted Theorem 4.4
  series convergence interfaces.
- Added the Theorem 4.4 product partial/convergence interface:
  `theorem44ProductPartial`,
  `theorem44ProductPartial_substitution_eq_quintuple`,
  `multipliable_theorem44ProductFactor`, `hasProd_theorem44ProductFactor`,
  and `tendsto_theorem44ProductPartial`.
- Added Chapter 4 exercise wrappers for the new Theorem 4.4 product partial
  and convergence interfaces.
- Added `theorem44ProductPartial_eq_qPoch`, rewriting the finite Theorem 4.4
  product partial as the five finite q-Pochhammer factors used in Chan's
  proof.
- Added a Chapter 4 exercise wrapper for the Theorem 4.4 finite q-Pochhammer
  product rewrite.
- Added Theorem 4.4 double-sum regrouping arithmetic:
  `theorem44DoubleSumZIndex`, `theorem44DoubleSumSignIndex`,
  `theorem44DoubleSumSixExponent`, `theorem44CoeffSixExponent`, their
  reindexing lemmas, the residue condition `(3 : Int) ∣ l + k`, and the
  `z`-power/sign combination lemmas used in coefficient extraction.
- Added Chapter 4 exercise wrappers for the new regrouping arithmetic lemmas.
- Added residue-class simplification lemmas for Theorem 4.4 coefficient
  extraction: `theorem44CoeffSixExponent_residue_zero`,
  `theorem44CoeffSixExponent_residue_one`,
  `theorem44CoeffSixExponent_residue_two`, the three
  `theorem44CoeffResidueCondition_*` lemmas, and the three
  `theorem44_sign_residue_*` lemmas.
- Added Chapter 4 exercise wrappers for the residue-class exponent, residue,
  and sign simplification lemmas.
- Added reverse residue-condition parametrization lemmas:
  `theorem44CoeffResidueCondition_zero_iff`,
  `theorem44CoeffResidueCondition_one_iff`, and
  `theorem44CoeffResidueCondition_two_iff`, plus matching Chapter 4 exercise
  wrappers.
- Added the natural coefficient exponent layer for Chan's coefficient
  extraction:
  `theorem44CoeffSixExponent_nonneg`,
  `two_dvd_theorem44CoeffSixExponent`,
  `six_dvd_theorem44CoeffSixExponent_of_residue`,
  `theorem44CoeffExponentIndex`,
  `theorem44CoeffExponentIndex_spec`, and the three residue-class index specs,
  plus matching Chapter 4 exercise wrappers.
- Added divided-form exponent simplifications for the two nonzero residue
  branches:
  `theorem44CoeffExponentIndex_residue_zero_eq` and
  `theorem44CoeffExponentIndex_residue_one_eq`, plus matching Chapter 4
  exercise wrappers.
- Added coefficient `q`-power splitting for the two nonzero residue branches:
  `theorem44Coeff_qpow_residue_zero` and
  `theorem44Coeff_qpow_residue_one`, plus matching Chapter 4 exercise wrappers.
- Added signed coefficient term splitting for the two nonzero residue branches:
  `theorem44Coeff_signed_qpow_residue_zero` and
  `theorem44Coeff_signed_qpow_residue_one`, plus matching Chapter 4 exercise
  wrappers.
- Added full coefficient monomial splitting for the two nonzero residue
  branches:
  `theorem44Coeff_monomial_residue_zero` and
  `theorem44Coeff_monomial_residue_one`, plus matching Chapter 4 exercise
  wrappers.
- Added the paired zero/one branch factorization
  `theorem44Coeff_monomial_residue_zero_add_one`, packaging the common
  `q^{r(3r+1)/2}` factor and the bracketed difference used in Chan's
  coefficient extraction, plus a matching Chapter 4 exercise wrapper.
- Added named paired-branch interfaces:
  `theorem44CoeffPairedBranchOuter`, `theorem44CoeffPairedBranchInner`,
  `theorem44CoeffPairedBranchTerm`, and
  `theorem44Coeff_monomial_residue_zero_add_one_eq_pairedTerm`, plus a
  matching Chapter 4 exercise wrapper.
- Added unfold/explicit bridges for the paired-branch interfaces:
  `theorem44CoeffPairedBranchOuter_eq`,
  `theorem44CoeffPairedBranchInner_eq`,
  `theorem44CoeffPairedBranchTerm_eq`, and
  `theorem44CoeffPairedBranchTerm_eq_explicit`, plus matching Chapter 4
  exercise wrappers.
- Added symmetric finite partial sums
  `theorem44CoeffPairedBranchInnerPartial` and
  `theorem44CoeffPairedBranchTermPartial`, plus
  `theorem44CoeffPairedBranchTermPartial_eq_outer_mul_innerPartial`,
  extracting the fixed outer factor from each finite paired-branch block,
  with a matching Chapter 4 exercise wrapper.
- Added left/right theta-like finite partials
  `theorem44CoeffPairedBranchInnerLeftPartial` and
  `theorem44CoeffPairedBranchInnerRightPartial`, with
  `theorem44CoeffPairedBranchInnerPartial_eq_left_sub_right` and
  `theorem44CoeffPairedBranchTermPartial_eq_outer_mul_left_sub_right`,
  plus matching Chapter 4 exercise wrappers.
- Added base theta finite partials
  `theorem44CoeffPairedBranchLeftThetaPartial` and
  `theorem44CoeffPairedBranchRightThetaPartial`, with fixed `z`-power
  extraction lemmas for the left/right inner partials and combined
  inner/term partial forms exposing only base theta sums, plus matching
  Chapter 4 exercise wrappers.
- Added finite symmetric reindexing
  `theorem44CoeffPairedBranchRightThetaPartial_eq_leftThetaPartial`, using
  `j ↦ -j`, and compressed the paired inner/term partials to one base theta
  finite partial via `theorem44CoeffPairedBranchInnerPartial_eq_zpow_sub_zpow_mul_theta`
  and `theorem44CoeffPairedBranchTermPartial_eq_outer_mul_zpow_sub_zpow_mul_theta`,
  plus matching Chapter 4 exercise wrappers.
- Added the raw two-branch finite partial bridge
  `theorem44CoeffMonomialPairPartial`, with
  `theorem44CoeffMonomialPairPartial_eq_pairedBranchTermPartial` and
  `theorem44CoeffMonomialPairPartial_eq_outer_mul_innerPartial`, and the
  single-theta compressed form
  `theorem44CoeffMonomialPairPartial_eq_outer_mul_zpow_sub_zpow_mul_theta`,
  plus matching Chapter 4 exercise wrappers.
- Added the paired-branch theta term/series interface
  `theorem44CoeffPairedBranchThetaTerm` and
  `theorem44CoeffPairedBranchThetaSeries`, identified the finite left theta
  partial as a symmetric partial sum of those terms, bridged the term and
  series to `jacobiInfiniteSeries (q^3) (-q⁻¹)`, and packaged
  `summable_theorem44CoeffPairedBranchThetaTerm` plus
  `hasSum_theorem44CoeffPairedBranchThetaTerm`.
- Added Chapter 4 exercise wrappers for the paired-branch theta term/series,
  Jacobi-series bridge, summability, and `HasSum` interfaces.
- Added the finite-to-infinite convergence layer for the paired nonzero
  residue branches: the base left theta partial is identified with
  `Ch02.jacobiSeriesSymmetricPartial (q^3) (-q⁻¹)`, its `Tendsto` is
  inherited from Ch02, and the inner, packaged term, and raw monomial-pair
  finite partials now converge to the compressed outer times theta-series
  expression.
- Added Chapter 4 exercise wrappers for the new paired-branch symmetric
  partial/Jacobi partial bridge and `Tendsto` interfaces.
- Added the original Chan Theorem 4.4 series-side interface:
  `theorem44SeriesExponentIndex`, `theorem44SeriesTerm`, and
  `theorem44SeriesRHS`, plus bridges showing that `q ↦ q^2`, `z ↦ z/q`
  turns the original term/RHS into the already-developed substituted series.
- Added `summable_theorem44SeriesTerm_substitution` and
  `hasSum_theorem44SeriesTerm_substitution`, inheriting convergence for the
  original Theorem 4.4 series after the Eq. (2.12) substitution.
- Added Chapter 4 exercise wrappers for the original/substituted Theorem 4.4
  series bridges and substituted original-series convergence interfaces.
- Added `theorem44_substitution_identity_iff_quintupleProduct` and the two
  transport directions between the substituted Theorem 4.4 identity and the
  Eq. (2.12) quintuple product identity, making the remaining Ch04 bottleneck
  explicit.
- Added Chapter 4 exercise wrappers for the substituted identity equivalence
  and both transport directions.
- Added `quintupleProductExplicitRHS`, naming the JTP-expanded product
  difference for the Eq. (2.12) RHS, and rewrote
  `quintupleProductRHS_eq_explicitProduct_sub` to target that definition.
- Added `quintupleProduct_identity_iff_explicitProduct` and both transport
  directions, isolating the remaining quintuple identity proof as the explicit
  product algebra `quintupleProductLHS = quintupleProductExplicitRHS`.
- Added Chapter 4 exercise wrappers for the explicit-product bottleneck and
  transport interfaces.
- Added the finite explicit RHS partial
  `quintupleProductExplicitRHSPartial`, proved
  `tendsto_quintupleProductExplicitRHSPartial`, and reduced the explicit
  product identity to proving the finite-difference limit
  `quintupleProductLHSTrunc - quintupleProductExplicitRHSPartial → 0`.
- Added Chapter 4 exercise wrappers for the explicit RHS partial convergence
  and finite-difference-to-identity reduction.
- Added Ch02-product-partial versions of that bottleneck:
  `quintupleProductExplicitRHSPartial_eq_jacobiProductPartial_sub`,
  `quintupleProduct_trunc_sub_explicitPartial_eq_jacobiProductPartial_sub`,
  and `quintupleProduct_explicitProduct_of_tendsto_trunc_sub_jacobiPartials`,
  plus matching Chapter 4 exercise wrappers.
- Added finite q-Pochhammer/finite-JTP versions:
  `quintupleProductLHSTrunc_eq_qPoch`,
  `quintupleProductExplicitRHSPartial_eq_qPoch_mul_finiteJTPRHS_sub`,
  `quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_finiteJTPRHS`, and
  `quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_finiteJTPRHS`,
  plus matching Chapter 4 exercise wrappers.
- Expanded the two finite-JTP sums into named weighted Laurent finite sums:
  `quintupleFiniteJTPLeftWeightedSum`,
  `quintupleFiniteJTPRightWeightedSum`,
  `finiteJTPRHS_quintuple_left_eq_weightedSum`,
  `finiteJTPRHS_quintuple_right_eq_weightedSum`,
  `quintupleProductExplicitRHSPartial_eq_qPoch_mul_weightedSums_sub`,
  `quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_weightedSums`, and
  `quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_weightedSums`,
  plus matching Chapter 4 exercise wrappers.
- Added weighted Laurent monomial power-splitting lemmas
  `quintupleFiniteJTPLeftMonomial_eq_zpow_qpow` and
  `quintupleFiniteJTPRightScaledMonomial_eq_zpow_qpow`, plus matching Chapter
  4 exercise wrappers.
- Added the combined weighted Laurent summand/sum layer:
  `quintupleFiniteJTPLeftWeightedSummand`,
  `quintupleFiniteJTPRightWeightedSummand`,
  `quintupleFiniteJTPCombinedWeightedSummand`,
  `quintupleFiniteJTPCombinedWeightedSum`,
  `quintupleFiniteJTPWeightedSum_sub_eq_combined`,
  `quintupleProductExplicitRHSPartial_eq_qPoch_mul_combinedWeightedSum`,
  `quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_combinedWeightedSum`,
  and
  `quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_combinedWeightedSum`,
  plus matching Chapter 4 exercise wrappers.
- Added the monomial-split combined finite-sum layer:
  `quintupleFiniteJTPCombinedMonomialSummand`,
  `quintupleFiniteJTPCombinedMonomialSum`,
  `quintupleFiniteJTPCombinedWeightedSummand_eq_monomialSummand`,
  `quintupleFiniteJTPCombinedWeightedSum_eq_monomialSum`,
  `quintupleProductExplicitRHSPartial_eq_qPoch_mul_combinedMonomialSum`,
  `quintupleProduct_trunc_sub_explicitPartial_eq_qPoch_combinedMonomialSum`,
  and
  `quintupleProduct_explicitProduct_of_tendsto_trunc_sub_qPoch_combinedMonomialSum`,
  plus matching Chapter 4 exercise wrappers.
- Added the centered monomial-summand bridge to the bilateral RHS term:
  `quintupleProductSeriesTerm_eq_combinedMonomialBracket`,
  `quintupleFiniteJTPCombinedMonomialSummand_eq_gaussian_mul_seriesTerm`,
  `tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSummand_center_add`,
  and
  `tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSummand_center_sub`,
  plus matching Chapter 4 exercise wrappers.
- Added the fixed symmetric-partial layer for the monomial-split combined sum:
  `quintupleProductSeriesSymmetricPairTerm`,
  `quintupleProductSeriesSymmetricPairPartial`,
  `quintupleProductSeriesSymmetricPartial`,
  `quintupleFiniteJTPCombinedMonomialPairTerm`,
  `quintupleFiniteJTPCombinedMonomialPairPartial`,
  `quintupleFiniteJTPCombinedMonomialSymmetricPartial`,
  `tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialPairTerm`,
  `tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialPairPartial`,
  and
  `tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomialSymmetricPartial`,
  plus matching Chapter 4 exercise wrappers.
- Added Theorem 4.4 third-residue zero-factor interfaces:
  `qPoch_one_succ_eq_zero`, `theorem44ResidueTwo_qPoch_one_qsix_zero`, and
  `theorem44ResidueTwo_qPoch_zero_factor`, packaging the finite `(1;q^6)`
  vanishing used in Chan's `k = 3r - 2` coefficient branch.
- Added Chapter 4 exercise wrappers for the new `(1;q^6)` zero-factor
  interfaces.
- Validation: `lake env lean QseriesFormalization/Chapter04.lean`;
  `lake env lean QseriesFormalization/Exercises.lean`;
  `lake build` completed successfully; `rg -n "sorry" QseriesFormalization`
  returns no matches; `git diff --check` is clean.

## 2026-05-13 (continued): Theorem 4.3 progress (Phase 1 + 2 + 3)

T4.3 (Jacobi's identity) split into separate `Chapter04_T43.lean` for fast iteration.

### Phase 1 — series-side derivative ✅ DONE

- `jacobiSeriesT`, `jacobiSeriesT'`: term and termwise derivative
- `hasDerivAt_jacobiSeriesT`: each term differentiable at z ≠ 0
- `summable_jacobiSeriesT'_boundNat` / `_boundInt`: Gaussian-decay uniform bound
- `norm_zpow_le_pow_natAbs`, `norm_jacobiSeriesT'_le`: pointwise bounds
- **`hasDerivAt_jacobiInfiniteSeries`**: bilateral series differentiable on punctured plane,
  derivative = `∑' n : ℤ, jacobiSeriesT' Q n y` via `hasDerivAt_tsum_of_isPreconnected`
  on `Metric.ball y (‖y‖/2)`

### Phase 2 — product-side derivative ⚠️ PARTIAL

- `hasDerivAt_oneAddInvMul_negQ`: `(1 + z⁻¹·Q)' (-Q) = -Q⁻¹`
- `hasDerivAt_mul_of_left_vanish`: slope-based product rule (only needs RHS continuous)
- Local shifted-summability infrastructure (sidesteps ℂ ≠ CommGroup gotcha)
- **`jacobiInfiniteProduct_factor_at_zeroOdd`**: factorize `P = (1+z⁻¹·Q) · P_mod`
- `jacobiProductMod_at_negQ`: `P_mod(-Q) = (∏ even-factor)^3`
- `hasDerivAt_jacobiInfiniteProduct`: derivative transfers from series via JTP S=P
  (no continuity needed for this transfer; congr_of_eventuallyEq on `{z ≠ 0}`)

**Remaining gap**: continuity of `P_mod` at `z = -Q`. Required to identify
`HasDerivAt`-uniqueness derivative `D = -Q⁻¹·(∑'…)` with `-Q⁻¹·P_mod(-Q) = -Q⁻¹·(∏ even)^3`.
This is essentially uniform convergence of partial products on a neighborhood of `-Q`.
Mathlib has `HasProdUniformlyOn` and `hasDerivAt_of_tendstoLocallyUniformlyOn` — combining
them should close it, but is substantial work.

### Phase 3 — series-side reindex ✅ DONE

- `jacobiSeriesT'_at_negQ`: closed form of term at `y = -Q`
- `jacobiSeriesT'_pair_at_negQ`: pair-sum identity `t_n + t_{-(1+n)} = -Q⁻¹·(-1)^n·(2n+1)·Q^{n(n+1)}`
- `summable_jacobiSeriesT'_at` / `_negQ_nat` / `_negQ_neg`: summability lemmas
- `tsum_jacobiSeriesT'_negQ_paired`: bilateral sum = ∑' over pairs
- **`tsum_jacobiSeriesT'_negQ_closed`**: full closed form
  `∑'_{n∈ℤ} = -Q⁻¹ · ∑'_{n∈ℕ} (-1)^n · (2n+1) · Q^{n(n+1)}`

### Phase 4 — wrapper (TODO)

Lift `Q² = q` via `Complex.exists_sq`. Convert `Q^{n(n+1)} = q^{n(n+1)/2}`.
Statement: `(qPoch q q)^3 = ∑'_{n∈ℕ} (-1)^n · (2n+1) · q^{n(n+1)/2}`.

### ℂ-CommMonoid lesson learned

`Multipliable.tprod_eq_zero_mul` (and friends like `multipliable_int_iff_*_add_one`,
`comp_injective`) require `[CommGroup G]`. ℂ has no group inverse for 0, so they
don't directly apply. Workaround: use the `'` variants (`tprod_eq_zero_mul'`) which
require only `CommMonoid` + explicit shifted multipliability. Build shifted
multipliability from `multipliable_one_add_of_summable` and local geometric bounds.

When Lean elaboration hangs at `whnf` with `maxHeartbeats` timeout, suspect
typeclass synthesis for a missing/inappropriate instance. Diagnosis: check that
required structure (here `CommGroup ℂ`) actually exists. If not, find a `CommMonoid`
analogue or rebuild from primitives.
