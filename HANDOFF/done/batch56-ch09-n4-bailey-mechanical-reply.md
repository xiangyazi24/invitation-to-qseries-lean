# Batch 56: Chapter09 N=4 Bailey Algebra Recon - Reply

## Accomplishments

I have performed a mechanical reconnaissance for extending the finite Bailey-transform preservation package to $N=4$ in `QseriesFormalization/Chapter09.lean`.

### 1. New Expansion and Linear Combination Lemmas
I added several wrapper and expansion lemmas that mirror the existing $N=3$ structure. These are low-risk and compile quickly.

- **`BaileyBeta_four_terms`**: Expresses `BaileyBeta a q α 4` in terms of five simplified summands.
- **`BaileyTransformBeta_of_pair_four_terms`**: Expresses the transformed $\beta$ at $n=4$ in terms of $\alpha_k$ for $k \in \{0, \dots, 4\}$.
- **`BaileyTerm_transformAlpha_four_0..4`**: Individual term expansions for `BaileyBeta` on the transformed $\alpha$ side.
- **`BaileyBeta_transformAlpha_four_terms`**: Sum of the above terms.
- **`BaileyBeta_transformAlpha_four_terms_linear`**: Expresses `BaileyBeta(α')_4` as a linear combination of $\alpha_k$.
- **`BaileyTransform_four_alpha_four_coefficient_identity`**: The trivial identity for the $\alpha_4$ coefficient.

### 2. Identified Existing Theorem Names for Reuse
For the full $N=4$ preservation proof, the following structure (reused from $N=3$) is recommended:
- Use **`IsBaileyPairUpTo.of_four`** (already exists) to package the induction/truncation steps.
- Re-use the pattern of **`BaileyTransform_preserves_pair_upTo_three_of_nonzero`** to define **`BaileyTransform_preserves_pair_upTo_four_of_nonzero`**.

## Missing Pieces (Action Items for Codex)

The full $N=4$ preservation proof requires showing that the coefficients of $\alpha_k$ match between `BaileyTransformBeta_of_pair_four_terms` and `BaileyBeta_transformAlpha_four_terms_linear`.

The following four non-trivial coefficient identities are missing and likely require expensive `ring_nf` or targeted fraction-matching proofs:

1. **`BaileyTransform_four_alpha_zero_coefficient_identity`**:
   Matches the sum of five fractional terms for $\alpha_0$.
2. **`BaileyTransform_four_alpha_one_coefficient_identity`**:
   Matches the sum of four fractional terms for $\alpha_1$.
3. **`BaileyTransform_four_alpha_two_coefficient_identity`**:
   Matches the sum of three fractional terms for $\alpha_2$.
4. **`BaileyTransform_four_alpha_three_coefficient_identity`**:
   Matches the sum of two fractional terms for $\alpha_3$.

(The identity for $\alpha_4$ is already proved as `BaileyTransform_four_alpha_four_coefficient_identity`).

## Verification
- `lake build QseriesFormalization.Chapter09` passed successfully.
- No `sorry`, `axiom`, or `native_decide` were introduced.
