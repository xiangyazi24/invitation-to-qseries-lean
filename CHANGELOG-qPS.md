# General q-Pfaff–Saalschütz: Proof Changelog

A record of the formal verification of the general q-Pfaff–Saalschütz
(Jackson summation) identity in Lean 4 / Mathlib v4.27.0, as part of
the formalization of Hei-Chi Chan's *An Invitation to q-Series*.

The identity is the kernel of the finite Bailey lemma (Chapter 9):
for all j ≤ n,

  baileyKernelSum(a, q, ρ₁, ρ₂, n, j) = baileyKernelTarget(a, q, ρ₁, ρ₂, n, j)

where `baileyKernelSum` is a filtered sum of Bailey transform coefficients
and `baileyKernelTarget` is an explicit product of q-Pochhammer symbols.

---

## Phase 1: Brute-force attempts (early May 2026)

**Approach.** Try to verify the kernel identity for small (n, j) by direct
expansion: `simp [qPoch, qPochhammer]; field_simp; ring`.

**What worked.** n ≤ 2 (all j): the `ring` tactic terminates within minutes.
The boundary case j = n (`baileyKernelSum_eq_target_n`) is trivially a
single-term sum and was proved for all n.

**What failed.** n = 3, j = 2: `ring` ran for 36 minutes without terminating
(killed). The `qPoch(a*q) q 5` factor at this level produces a polynomial
with too many monomials for `ring` to normalize. An n = 8 attempt ran for
129 minutes CPU before being killed.

**Lesson.** The brute-force ladder hits a wall at n = 3. The only scalable
path is the general inductive proof via q-WZ telescoping.

## Phase 2: Structural reduction (May 12–15, 2026)

**Approach.** Reduce the general identity to a small number of algebraic
sub-identities, verifying all structural/combinatorial steps machine-checkably.

**Verified building blocks (8 theorems):**
1. `baileyTransformCoeff_succ_k` — consecutive-k recurrence for the Bailey
   coefficients (the COEFF identity).
2. `baileyKernelSum_peel` — peels the lowest term k = j off the filtered sum.
3. `baileyKernelSum_summand_shift` — per-term denominator shift relating
   S_j(k) and S_{j+1}(k).
4. `baileyKernelTarget_as_frac` — resolves the nested b^j = (aq)^j/(ρ₁ρ₂)^j
   inside the target into a single explicit fraction.
5. `baileyKernelSum_eq_target_of_step` — downward induction architecture:
   reduces ∀ j ≤ n to the boundary j = n plus one inductive step.
6. `peelTail_telescope` — generic Finset telescoping: Σ(W(k+1) − W(k)) = W(n+1) − W(j+1).
7. `hstep_certified` — assembles the full inductive step from the q-WZ
   certificate (G, W, boundary values).
8. `baileyKernelSum_eq_target_certified` — the general identity for all j ≤ n,
   conditional on per-j certificate data.

**Result.** The entire identity is machine-reduced to exactly TWO pure
algebraic sub-identities, both guaranteed true by the q-WZ certificate:

- **(A)** Per-term telescoping: S_j(k) − G·S_{j+1}(k) = W(k+1) − W(k)
- **(B)** Target shift: KTgt(n,j) = G·KTgt(n,j+1)

Everything else (peel, telescope, induction skeleton) is verified.

## Phase 3: The `field_simp` / `ring` wall (May 15–16, 2026)

**The obstacle.** Both (A) and (B) are rational identities in a, q, ρ₁, ρ₂
and symbolic indices j, k, n. The natural proof attempt —
`unfold; rw [qPoch_succ ...]; field_simp; ring` — fails in two distinct ways:

1. **`field_simp` recombination (B).** After `div_eq_div_iff`, `field_simp`
   clears denominators but *recombines* the opaque `(ρᵢ − aq^{j+1})` factors
   into an expanded product `ρ₁ρ₂ − ρ₁aq^{j+1} − ρ₂aq^{j+1} + a²q^{2j+2}`.
   The factored nonvanishing hypotheses `hX₁ : ρ₁ − aq^{j+1} ≠ 0` cannot
   discharge the expanded form. Tested with every documented mitigation
   (pre-rewriting `1 − aq/ρᵢ·q^j → (ρᵢ − aq·q^j)/ρᵢ`, factored hypotheses,
   `baileyKernelTarget_as_frac`): all fail. This is a fundamental mismatch
   between `field_simp`'s normal form and the natural factored hypotheses.

2. **`ring` non-termination (A and B).** Even when `field_simp` succeeds in
   clearing denominators, the resulting polynomial identity has ~10 variables
   (a, q, ρ₁, ρ₂, plus symbolic q-powers q^j, q^k, q^n) and 10+ binomial
   factors. Lean's `ring` tactic normalizes to a canonical monomial form —
   on these polynomials, it runs for 15+ minutes without terminating.
   The (B) target-shift ring was killed after 15 minutes. Earlier brute
   instances confirm this is the same wall (n = 8 region: 86–129 min CPU).

**Dead ends tested:**
- `linear_combination` — uses `ring` internally, same blowup.
- `div_eq_div_iff` without `field_simp` — structural part works, but the
  terminal `ring` on the cleared polynomial still doesn't terminate.
- Factor-by-factor cancellation — too many manual steps, error-prone.

## Phase 4: The breakthrough — change of variables (May 16, 2026)

**Key insight.** The `ring` blowup comes from Nat subtraction in q-exponents:
expressions like `q^(n−k)`, `q^(k−j)` create opaque atoms that `ring` cannot
relate to `q^n`, `q^k`, `q^j`. After `field_simp`, these produce independent
variables that multiply the monomial count exponentially.

**Solution.** Introduce new variables via existential witnesses:
```
k = j + 1 + d    (so k − j = d + 1, k − j − 1 = d)
n = j + 1 + d + e    (so n − k = e, n − j = d + 1 + e)
```
After `subst`, ALL Nat subtraction disappears. Every q-exponent becomes a
sum: `q^(2j+1+d)`, `q^(d+1+e)`, etc. Then:
```lean
simp only [pow_add, pow_succ, pow_zero, one_mul, pow_mul, pow_one,
           two_mul, Nat.add_eq, Nat.add_zero]
```
normalizes all q-powers to products of `q^j`, `q^d`, `q^e`. Now `ring` sees
a polynomial in ~7 multiplicatively independent atoms and terminates.

**Results:**
- **(A)** `per_term_telescope`: EXIT=0, ~7 min (4 min in `ring`).
- **(B)** `tgt_shift_cleared`: EXIT=0, ~5 min (`field_simp` alone closes it
  after change-of-variables — the polynomial is small enough).
- `tgt_shift_div`: EXIT=0, trivial (derives division form from cleared form).

## Phase 5: The bridge lemma (May 16–17, 2026)

**The problem.** The q-WZ certificate uses two forms of the Gosper function W:
- *Ordinary form*: W(k) = S_j(k) · (explicit factors)
- *Boundary-safe form*: W(k) = S_j(k−1) · (different factors), valid at k = n+1

The `per_term_telescope` theorem outputs `Wbs(k+1) − Word(k)` (mixed forms).
The telescoping framework needs `Wf(k+1) − Wf(k)` for a single function Wf.
Choosing Wf = Wbs (boundary-safe) gives correct boundary values:
- Wf(n+1) = 0 (factor 1 − q⁰ = 0)
- Wf(j+1) = S_j(j) (matching factors cancel)

But requires a **bridge**: Word(k) = Wbs(k).

**The bridge identity.** Reduces to the COEFF recurrence at index k−1:
C(k)·(1 − bq^{n−k}) = C(k−1)·(1 − ρ₁q^{k−1})(1 − ρ₂q^{k−1})·b·(1 − q^{n+1−k}).

After substituting C(k) = C(k−1) · (factors) via the COEFF identity, C(k−1)
cancels from both sides, leaving a polynomial identity.

**`Word_eq_Wbs`**: EXIT=0, ~6 min (same change-of-variables technique,
`ring` on ~10 variables).

## Phase 6: Assembly (May 17, 2026)

**`baileyKernelSum_eq_target_general`**: the unconditional theorem.
Instantiates `baileyKernelSum_eq_target_certified` with:
- Gf = explicit G fraction (inline lambda)
- Wf = boundary-safe W (inline lambda)
- hA: from `per_term_telescope` + `Word_eq_Wbs` bridge
- hWtop: factor (1 − q⁰) = 0
- hWbot: from `Wbs_bot_eq_head` (matching factors cancel)
- hB: from `tgt_shift_div`

No new `ring` computations — purely hypothesis threading with `by omega`
for Nat index arithmetic.

**First attempt failed:** `let` bindings for Gf/Wf are not unfolded by
`dsimp` inside `by` blocks. Fix: inline lambdas directly in the `apply` call.

EXIT=0, ~21 min total compile (dominated by earlier ring proofs).

**`BaileyTransform_preserves_pair_unconditional`**: the unconditional finite
Bailey lemma. Applies `BaileyTransform_preserves_pair_general` with
`baileyKernelSum_eq_target_general` as the kernel hypothesis. Trivial proof.

## Final statistics

| Theorem | CPU time | Technique |
|---------|----------|-----------|
| baileyTransformCoeff_succ_k | < 1 min | unfold + field_simp + ring |
| baileyKernelSum_peel | < 1 min | Finset.sum_insert |
| baileyKernelSum_summand_shift | < 1 min | qPochhammer_succ + field_simp |
| baileyKernelTarget_as_frac | < 1 min | div_pow + mul_div_assoc |
| baileyKernelSum_eq_target_of_step | < 1 min | downward Nat induction |
| peelTail_telescope | < 1 min | Finset.sum_Ico_eq_sum_range + sum_range_sub |
| hstep_certified | < 1 min | sum_congr + sum_add_distrib + ring |
| baileyKernelSum_eq_target_certified | < 1 min | induction + hstep_certified |
| **per_term_telescope (A)** | **~7 min** | **change-of-vars + field_simp + ring** |
| **tgt_shift_cleared (B)** | **~5 min** | **change-of-vars + field_simp** |
| tgt_shift_div | < 1 min | eq_div_iff + tgt_shift_cleared |
| Wbs_bot_eq_head | < 1 min | field_simp + ring |
| **Word_eq_Wbs (bridge)** | **~6 min** | **COEFF substitution + change-of-vars + ring** |
| baileyKernelSum_eq_target_general | ~2 min | hypothesis threading |
| BaileyTransform_preserves_pair_unconditional | < 1 min | apply + exact |

**Total: 17 theorems, 0 sorry, 0 axiom. ~21 min compile.**

## What made this hard

1. **Lean's `ring` tactic and symbolic q-exponents.** The fundamental obstacle
   was not mathematical but computational: `ring` normalizes to a canonical
   monomial form, and Nat subtraction in q-exponents (`q^(n−k)`) creates
   independent atoms that explode the monomial count. The change-of-variables
   trick that eliminated all subtraction was the key breakthrough.

2. **`field_simp` recombination.** The tactic's normal form expands products
   of linear factors, destroying the factored structure needed for nonvanishing
   hypotheses. The workaround (`div_eq_div_iff` for (B), change-of-variables
   for (A)) required understanding exactly where the expansion happens.

3. **Mixed W forms.** The q-WZ certificate naturally produces two forms of
   the Gosper function (ordinary and boundary-safe). Connecting them required
   the bridge lemma `Word_eq_Wbs`, which itself needed the COEFF recurrence —
   a non-obvious algebraic dependency.

4. **Lean `let` binding opacity.** Local `let` definitions in tactic blocks
   are not unfolded by `dsimp`, causing type mismatches when feeding verified
   sub-proofs into the assembly. Solved by inlining as anonymous lambdas.

---

*Formalized by Xiang Huang and Claude (Anthropic), May 2026.*
*Part of the Lean 4 formalization of Chan's "An Invitation to q-Series".*
