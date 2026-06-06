# Gemini Task: n=7 alpha_zero common-denominator identity for Ch09 Bailey lemma

You are generating Lean 4 / Mathlib v4.27.0 code. Output ONLY Lean code (no
markdown fences, no commentary). The code will be appended to
`QseriesFormalization/Chapter09.lean`. The code must build with
`lake build QseriesFormalization.Chapter09` with no warnings.

## Goal

Write **one** theorem:

  `BaileyTransform_seven_alpha_zero_common_denominator_identity`

This is the n=7 analogue of the existing
`BaileyTransform_six_alpha_zero_common_denominator_identity` (in the same
file, around line 5868). It states the polynomial identity that, after
multiplying through by all denominators, equates the seven α₀ contributions
in the n=7 transformed-β expansion to a single common-denominator form.

## n=6 template (already proven, copy structure exactly)

```lean
/-- The α₀ coefficient identity in the `n = 6` finite Bailey-lemma step after
moving the seven transformed-β contributions to a common denominator. -/
theorem BaileyTransform_six_alpha_zero_common_denominator_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hQ2 : qPochhammer q 2 ≠ 0)
    (hQ3 : qPochhammer q 3 ≠ 0)
    (hQ4 : qPochhammer q 4 ≠ 0)
    (hQ5 : qPochhammer q 5 ≠ 0)
    (hA1 : qPoch (a * q) q 1 ≠ 0)
    (hA2 : qPoch (a * q) q 2 ≠ 0)
    (hA3 : qPoch (a * q) q 3 ≠ 0)
    (hA4 : qPoch (a * q) q 4 ≠ 0)
    (hA5 : qPoch (a * q) q 5 ≠ 0) :
    qPoch (a * q / (ρ₁ * ρ₂)) q 6 +
      (qPoch ρ₁ q 1 * qPoch ρ₂ q 1 * (a * q / (ρ₁ * ρ₂)) *
        qPoch (a * q / (ρ₁ * ρ₂)) q 5 *
          ((1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) *
            ((1 - a * q ^ 2) * (1 - a * q ^ 3) *
              (1 - a * q ^ 4) * (1 - a * q ^ 5) *
              (1 - a * q ^ 6)))) +
      (qPoch ρ₁ q 2 * qPoch ρ₂ q 2 * (a * q / (ρ₁ * ρ₂)) ^ 2 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 4 *
          (((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4)) *
            ((1 - a * q ^ 3) * (1 - a * q ^ 4) *
              (1 - a * q ^ 5) * (1 - a * q ^ 6)))) +
      (qPoch ρ₁ q 3 * qPoch ρ₂ q 3 * (a * q / (ρ₁ * ρ₂)) ^ 3 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 3 *
          (((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2) * (1 + q ^ 3)) *
            ((1 - a * q ^ 4) * (1 - a * q ^ 5) * (1 - a * q ^ 6)))) +
      (qPoch ρ₁ q 4 * qPoch ρ₂ q 4 * (a * q / (ρ₁ * ρ₂)) ^ 4 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 2 *
          (((1 + q + q ^ 2 + q ^ 3 + q ^ 4) * (1 + q ^ 2 + q ^ 4)) *
            ((1 - a * q ^ 5) * (1 - a * q ^ 6)))) +
      (qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1 *
          ((1 + q + q ^ 2 + q ^ 3 + q ^ 4 + q ^ 5) * (1 - a * q ^ 6))) +
      qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 =
        qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 := by
  -- (proof body uses qPoch_functional_eq plus field_simp/ring,
  --  reaching ~400 lines of expansion)
  sorry  -- placeholder; the actual file has the real proof
```

(The actual proof in the file is ~400 lines using `qPoch_functional_eq`,
`field_simp`, and `ring`. You don't need to reproduce it; just use the
matching n=7 statement form.)

## Build out the n=7 statement

The n=7 version has 8 outer terms (k=0..7), with cross-pair structure
(k, 7-k) where the qPochhammer ratio polynomials appear. Each term is

  qPoch ρ₁ q k * qPoch ρ₂ q k * (a*q/(ρ₁*ρ₂))^k *
    qPoch (a*q/(ρ₁*ρ₂)) q (7-k) *
      ((q-binomial [7,k]_q polynomial) *
       ((1 - a*q^(k+1)) * ... * (1 - a*q^7)))

The term-by-term q-binomial polynomials are:
- k=0: just qPoch (a*q/(ρ₁*ρ₂)) q 7 (no extra factor)
- k=1: (1 + q + q² + q³ + q⁴ + q⁵ + q⁶)
- k=2: (1+q+q²+q³+q⁴+q⁵+q⁶) * (1+q²+q⁴)
- k=3: 1 + q + 2q² + 3q³ + 4q⁴ + 4q⁵ + 5q⁶ + 4q⁷ + 4q⁸ + 3q⁹ + 2q¹⁰ + q¹¹ + q¹²
- k=4: same as k=3 (q-binomial symmetry [7,3]=[7,4])
- k=5: (1+q+q²+q³+q⁴+q⁵+q⁶) * (1+q²+q⁴) (same as k=2)
- k=6: (1+q+q²+q³+q⁴+q⁵+q⁶) (same as k=1)
- k=7: just qPoch ρ₁ q 7 * qPoch ρ₂ q 7 * (a*q/(ρ₁*ρ₂))^7 (no extra factor)

The (1 - a*q^j) tail product runs from j=k+1 to j=7 (so for k=0 it's empty
since k=7 case has no qPoch ((aq/ρ₁ρ₂)) factor; rethink: see below).

## Hypotheses to include

Just the natural ones to make the helpers work:
- `(hρ : ρ₁ * ρ₂ ≠ 0)`
- `(hQ1 : qPochhammer q 1 ≠ 0)` through `(hQ6 : qPochhammer q 6 ≠ 0)`  (6 hypotheses)
- `(hA1 : qPoch (a * q) q 1 ≠ 0)` through `(hA6 : qPoch (a * q) q 6 ≠ 0)`  (6 hypotheses)

(NOT hQ7 or hA7 — those don't appear in any sub-helper.)

## Proof body

Use the same structure as the n=6 version:
```lean
  rw [BaileyTransform_seven_alpha_zero_first_ratio a q hQ1 hQ6 hA1,
      BaileyTransform_seven_alpha_zero_second_ratio a q hQ1 hQ2 hQ5 hA2,
      BaileyTransform_seven_alpha_zero_third_ratio a q hQ1 hQ2 hQ3 hQ4 hA3,
      BaileyTransform_seven_alpha_zero_fourth_ratio a q hQ1 hQ2 hQ3 hQ4 hA4,
      BaileyTransform_seven_alpha_zero_fifth_ratio a q hQ1 hQ2 hQ5 hA5,
      BaileyTransform_seven_alpha_zero_sixth_ratio a q hQ1 hQ6 hA6]
  -- This rewrites uses the 6 ratio lemmas, but they're inverted ratios
  -- (LHS has factored polynomials, RHS has the qPochhammer * qPoch (a*q) form).
  -- Use sym variant or .symm to get correct direction.
```

Actually the rewrite direction is wrong above. The ratios are stated as
forward (qPoch * qPoch / denom = polynomial). The common-denominator
identity needs to multiply through. The n=6 version uses
`field_simp` and `ring` to clear denominators after all factors are
expanded.

## Recommended approach

State the common-denominator identity using the polynomial RHS directly
(as in the n=6 statement). Prove via:

1. Combine all the qPochhammer/qPoch (a*q) factors using the ratio
   helpers I've already established (the 6 alpha_zero ratios).
2. Clear remaining qPoch (a*q/(ρ₁*ρ₂)) and qPoch (a*q/ρ_i) using
   qPoch_functional_eq if needed.
3. Apply field_simp with all denominators non-zero.
4. ring.

If `ring` doesn't close due to size, decompose into smaller `have`
statements for each term.

## Constraints

- No `sorry`, no `axiom`.
- Exactly one theorem. No surrounding markdown.
