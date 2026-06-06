# Batch 61 — Ch09 N=6 transformed-alpha alpha5 coefficient identity

## Scope

Touch only:

- `QseriesFormalization/Chapter09.lean`
- `HANDOFF/outbox/batch61-ch09-n6-alpha5-coeff-reply.md`

Do not edit `Exercises.lean` or docs.

## Goal

Add the `N = 6` alpha5 coefficient identity needed for the finite Bailey-transform preservation proof.

Place it near the existing endpoint identities:

- `BaileyTransform_five_alpha_five_coefficient_identity`
- `BaileyTransform_six_alpha_six_coefficient_identity`
- `BaileyTransform_five_alpha_four_common_denominator_identity`
- `BaileyTransform_five_alpha_four_coefficient_identity`

Suggested theorem names:

```lean
theorem BaileyTransform_six_alpha_five_common_denominator_identity ...
theorem BaileyTransform_six_alpha_five_coefficient_identity ...
```

The intended coefficient identity is the `α 5` coefficient in
`BaileyTransformBeta_of_pair_six_terms` after rewriting the right side with
`BaileyBeta_transformAlpha_six_terms`.

Concretely the final coefficient statement should have this shape:

```lean
theorem BaileyTransform_six_alpha_five_coefficient_identity
    (a q ρ₁ ρ₂ : R)
    (hρ : ρ₁ * ρ₂ ≠ 0)
    (hD1 : qPoch (a * q / ρ₁) q 6 ≠ 0)
    (hD2 : qPoch (a * q / ρ₂) q 6 ≠ 0)
    (hD1five : qPoch (a * q / ρ₁) q 5 ≠ 0)
    (hD2five : qPoch (a * q / ρ₂) q 5 ≠ 0)
    (hQ1 : qPochhammer q 1 ≠ 0)
    (hA10 : qPoch (a * q) q 10 ≠ 0)
    (hA11 : qPoch (a * q) q 11 ≠ 0) :
    ((qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 1) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 1)) / qPoch (a * q) q 10 +
      ((qPoch ρ₁ q 6 * qPoch ρ₂ q 6 * (a * q / (ρ₁ * ρ₂)) ^ 6 *
        qPoch (a * q / (ρ₁ * ρ₂)) q 0) /
      (qPoch (a * q / ρ₁) q 6 * qPoch (a * q / ρ₂) q 6 *
        qPochhammer q 0)) /
        (qPochhammer q 1 * qPoch (a * q) q 11) =
      (qPoch ρ₁ q 5 * qPoch ρ₂ q 5 * (a * q / (ρ₁ * ρ₂)) ^ 5 /
        (qPoch (a * q / ρ₁) q 5 * qPoch (a * q / ρ₂) q 5)) /
        (qPochhammer q 1 * qPoch (a * q) q 11)
```

The common-denominator lemma should mirror
`BaileyTransform_five_alpha_four_common_denominator_identity`, replacing
`4,5,8,9` by `5,6,10,11`. You can prove the fractional identity using the
existing generic helper:

```lean
BaileyTransform_two_term_fraction_from_common_ratio
```

## Verification

Run only:

```bash
lake build QseriesFormalization.Chapter09
rg -n "\bsorry\b|\baxiom\b|native_decide" QseriesFormalization/Chapter09.lean
```

No new `sorry`, no `axiom`, no `native_decide`.

## Reply

Write `HANDOFF/outbox/batch61-ch09-n6-alpha5-coeff-reply.md` with:

- files changed
- theorem names added
- build result
- forbidden-token scan result
- any blockers
