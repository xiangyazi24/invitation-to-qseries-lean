# TASK round 5 (codex / gpt-5.5): close the UNCONDITIONAL Most Beautiful Identity

## Huge progress already (committed, 0 sorry, clean-3 axioms)
The two §8.3 factor identities are now UNCONDITIONAL:
```lean
section83JTPProductPS_eq_rhs_pair14 (hζ : IsPrimitiveRoot ζ 5) :
  section83JTPProductPS ζ      = section83_rhs_pair14 ζ   -- = section83A + (ζ²+ζ³)·X·section83B
section83JTPProductPS_eq_rhs_pair23 (hζ : IsPrimitiveRoot ζ 5) :
  section83JTPProductPS (ζ^2)  = section83_rhs_pair23 ζ   -- = section83A + (ζ+ζ⁴)·X·section83B
```
where `section83JTPProductPS ζ = (q;q)∞·(ζq;q)∞·(ζ⁻¹q;q)∞`,
`section83A = expand 5 (pentagonal023SeriesPS)` (= A = (q¹⁰,q¹⁵,q²⁵;q²⁵)),
`section83B = expand 5 (pentagonal014SeriesPS)` (= B = (q⁵,q²⁰,q²⁵;q²⁵)).

## Goal: discharge the two remaining obligations → unconditional `most_beautiful_identity`
The wrapper `RamanujanQuintic.most_beautiful_identity_of_compressed_E5_zero_bridge_and_factor_pair_product`
needs `hE0` and `hfactor` (over ℚ). Close BOTH, then instantiate the wrapper with no hypotheses.

### Obligation 1 — hE0 (likely quick; a bridge lemma already exists)
```lean
hE0 : compressedSection5 ℚ 0 (qPochInfPS ℚ) * pentagonal014SeriesPS ℚ
        = expand 5 (by decide) (qPochInfPS ℚ) * pentagonal023SeriesPS ℚ
```
`Ch16MBIProof.E5_zero_eq_expand_compressedSection5_zero_qPochInfPS_rat` (Chapter16_MBI_Proof.lean:2052)
already gives `E5 ℚ 0 = expand 5 (compressedSection5 ℚ 0 (qPochInfPS ℚ))`. Combine with the existing
mod-5 dissection / `qPochInfPS_five_dissection` and the AP-product factorisation
`pentagonalProduct014_mul_pentagonalProduct023_eq_qPochInfPS_mul_expand_five_qPochInfPS_rat`
to get hE0. Search `Ch16MBIProof` for the E0/section-0 lemmas — much of this is already proven; you may
only need to assemble existing pieces.

### Obligation 2 — hfactor (the §8.5 5th-power chain)
```lean
hfactor : ((pentagonal023SeriesPS ℚ)^5 - C β·X·(pentagonal014SeriesPS ℚ)^5) *
          ((pentagonal023SeriesPS ℚ)^5 - C α·X·(pentagonal014SeriesPS ℚ)^5) *
          expand 5 (qPochInfPS ℚ) = (qPochInfPS ℚ)^11
```
with α+β=11, αβ=−1 (use `-quinticPeriodAlpha^5, -quinticPeriodBeta^5` as in
`quintic_factor_pair_mul_eq_core_of_book_periods`). By that lemma, the product of the two factors
= `quinticProductCore`, so hfactor ⟺ `core·E(q⁵) = E(q)^11`.

**Route (Hirschhorn §8.5):** raise the §8.3 identities to the 5th power and take the product over the
five conjugates `ζ^j`. The middle Euler factors collapse: `∏_{j=0}^4 (ζ^j q;q)∞ (ζ^{-j}q;q)∞` telescopes
(use `∏_{j}(1-ζ^j x) = 1-x^5`, i.e. your `prod_sub_scaled_primitive_fifth_powerSeries` /
`quinticCyclotomic_qPochFinitePS_fifth_collapse`), turning `∏_j section83JTPProductPS(ζ^j)` into an
`E(q)^? · E(q⁵)^?` expression; meanwhile `∏_j (A + ζ^{2j}·qB)` collapses via the same root-product
identity to `A^5 − (…)q^5 B^5`-type, and `A=expand5(G), B=expand5(H)` relate to `G^5,H^5` through
`expand` being a ring hom (`expand5(G)^5 = expand5(G^5)`). Reconcile the bases (the `expand 5` /
`X↦X^5` bookkeeping) to land exactly on `core·E(q⁵)=E(q)^11` over ℚ (the ζ's cancel — the identity is
rational; descend ℂ→ℚ by comparing coefficients or via a `ℚ→ℂ` ring-hom injectivity argument).

If the base-reconciliation (q vs q⁵) genuinely needs a lemma the repo lacks, STOP and report the
exact missing statement precisely (don't fake it).

## Rules
- Edit ONLY `RamanujanQuinticJTP.lean` (you may add to it). Do NOT touch `QseriesFormalization.lean`,
  `Audit.lean`, or `Chapter16_MBI_Proof.lean`/`RamanujanQuintic.lean` (reference their lemmas, don't edit).
- NEVER use `native_decide` (it injects `Lean.ofReduceBool`/`trustCompiler` and breaks our clean-3
  axiom invariant) — use `decide`/`rfl`/explicit lemmas. NEVER `lake build`; verify
  `lake env lean QseriesFormalization/Pending/RamanujanQuinticJTP.lean`.
- 0 sorry/axiom/admit; fresh `#print axioms` must be exactly `[propext, Classical.choice, Quot.sound]`.
- If you reach the unconditional `most_beautiful_identity`, state it as a top-level theorem.
- Reply to `HANDOFF/outbox/codex-mbi-final-reply.md` with theorem names + `#print axioms`.
